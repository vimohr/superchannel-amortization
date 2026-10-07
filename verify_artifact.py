#!/usr/bin/env python3
"""Build only the frozen project closure, audit its type, and replay its kernel proof.

External packages must already be installed at the manifest's pinned revisions.
No project .olean cache is read. Every run creates a new temporary build directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dependency-project", type=Path,
                        help="Lake project providing installed pinned external packages; "
                             "defaults to the frozen artifact/lean project")
    parser.add_argument("--output", type=Path,
                        help="New directory for results; must not already exist")
    args = parser.parse_args()
    release = Path(__file__).resolve().parent
    project = release / "artifact" / "lean"
    provider = (args.dependency_project or project).resolve()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="superchannel-check-"))
    if args.output:
        output.mkdir(parents=True, exist_ok=False)
    fresh = output / "fresh"
    logs = output / "logs"
    fresh.mkdir()
    logs.mkdir()
    manifest = json.loads((release / "artifact" / "source_manifest.json").read_text())
    source_root = release / "artifact"

    def save(name, data):
        (output / name).write_text(json.dumps(data, indent=2) + "\n")

    def run(argv, name, env=None, cwd=provider):
        started = time.monotonic()
        log = logs / (name + ".log")
        with log.open("w") as stream:
            result = subprocess.run([str(a) for a in argv], cwd=cwd, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        record = {"command": [str(a) for a in argv], "exit_code": result.returncode,
                  "seconds": round(time.monotonic() - started, 3),
                  "log": str(log.relative_to(output)), "log_sha256": digest(log)}
        if result.returncode:
            raise RuntimeError(str(record) + "\n" + log.read_text()[-12000:])
        return record

    for module, entry in manifest["sources"].items():
        path = source_root / entry["path"]
        assert digest(path) == entry["sha256"], f"Changed source: {module}"
        body = path.read_text()
        suspicious = re.compile(r"\b(sorry|admit|sorryAx|unsafe|axiom)\b")
        # Comments are removed so historical discussions do not count as declarations.
        uncommented = re.sub(r"/-.*?-/", "", body, flags=re.S)
        uncommented = re.sub(r"--[^\n]*", "", uncommented)
        assert not suspicious.search(uncommented), f"Inspect placeholder/declaration: {module}"

    run(["lake", "env", "printenv", "LEAN_PATH"], "lake_path")
    run(["lake", "env", "lean", "--print-prefix"], "toolchain")
    prefix = Path((logs / "toolchain.log").read_text().strip())
    lean = prefix / "bin" / "lean"
    checker = prefix / "bin" / "leanchecker"
    run([lean, "--version"], "version")
    assert "4.34.1" in (logs / "version.log").read_text(), "Wrong Lean version"
    expected = json.loads((project / "lake-manifest.json").read_text())
    external = []
    excluded = []
    packages_checked = []
    for raw in (logs / "lake_path.log").read_text().strip().split(":"):
        path = (provider / raw).resolve()
        if path == prefix / "lib" / "lean":
            external.append(str(path))
        elif path.is_dir() and "/.lake/packages/" in str(path):
            assert not (path / "OpenQ").exists(), "Project cache in external path"
            assert not list(path.glob("Critic*.olean")), "Scratch cache in external path"
            external.append(str(path))
            package_root = next(p for p in path.parents if p.parent.name == "packages")
            match = next(p for p in expected["packages"] if p["name"] == package_root.name)
            head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package_root,
                                           text=True).strip()
            assert head == match["rev"], f"Wrong revision: {package_root.name}"
            status = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                             cwd=package_root, text=True)
            assert not status, f"Modified dependency: {package_root.name}"
            packages_checked.append({"name": package_root.name, "revision": head,
                                     "tracked_sources_clean": True})
        else:
            excluded.append(str(path))
    assert external
    env = dict(os.environ, LEAN_PATH=":".join([str(fresh), *external]))
    save("environment.json", {"lean_path": env["LEAN_PATH"], "excluded": excluded,
                              "lean_sha256": digest(lean), "leanchecker_sha256": digest(checker),
                              "packages_checked": packages_checked,
                              "external_packages_rebuilt_or_replayed": False})
    options = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3",
               "-Dpp.unicode.fun=true"]
    builds = []
    for number, module in enumerate(manifest["order"], 1):
        binary = fresh / (module.replace(".", "/") + ".olean")
        binary.parent.mkdir(parents=True, exist_ok=True)
        source = source_root / manifest["sources"][module]["path"]
        record = run([lean, *options, "-R", project, "-o", binary, source], module,
                     env, project)
        assert digest(source) == manifest["sources"][module]["sha256"]
        builds.append({"module": module, **record, "olean_sha256": digest(binary)})
        save("builds.json", builds)
        print(f"Compiled {number}/{len(manifest['order'])}: {module}", flush=True)
    audit_source = release / "artifact" / "ProofAudit.lean"
    audit = run([lean, *options, "-R", audit_source.parent, "-o", output / "ProofAudit.olean",
                 audit_source], "proof_audit", env, audit_source.parent)
    audit_log = (logs / "proof_audit.log").read_text()
    assert "EXACT TARGET VERIFIED" in audit_log
    blocks = re.findall(r"depends on axioms:\s*\[([^]]*)\]", audit_log)
    assert len(blocks) >= 6
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for block in blocks:
        assert {x.strip() for x in block.replace("\n", " ").split(",") if x.strip()} <= allowed
    assert "sorryAx" not in audit_log
    save("type_axioms.json", {"audit": audit, "axiom_blocks": blocks,
                             "unfolded_operational_statement_checked": True})
    print("Exact target, operational expansion, and axiom audit passed; kernel replay starting.", flush=True)
    replay = run([checker, *manifest["order"]], "kernel_replay", env, project)
    save("kernel_replay.json", replay)
    assert all(digest(source_root / entry["path"]) == entry["sha256"]
               for entry in manifest["sources"].values())
    save("result.json", {"module_count": len(manifest["order"]), "fresh_source_build": True,
                         "exact_type_and_axioms": True, "kernel_replay": True,
                         "source_unchanged": True, "external_packages_rebuilt_or_replayed": False,
                         "frozen_artifact": True})
    print(f"PASS. Results: {output}", flush=True)


if __name__ == "__main__":
    main()
