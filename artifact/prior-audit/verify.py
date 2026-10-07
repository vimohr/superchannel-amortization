"""Independent review: rebuild project sources in isolation, then replay them."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
AUDIT = Path(__file__).resolve().parent
PROJECT = ROOT / "lean"
NAMESPACE = "OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275"
TARGET = NAMESPACE + ".StabilizedCollapse"
OUTPUT = AUDIT / "fresh"
LOGS = AUDIT / "logs"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, data):
    (AUDIT / name).write_text(json.dumps(data, indent=2) + "\n")


def execute(argv, name, env=None, cwd=PROJECT):
    started = time.monotonic()
    log = LOGS / (name + ".log")
    with log.open("w") as stream:
        result = subprocess.run([str(a) for a in argv], cwd=cwd, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    record = {"command": [str(a) for a in argv], "exit_code": result.returncode,
              "seconds": round(time.monotonic() - started, 3),
              "log": str(log.relative_to(ROOT)), "log_sha256": digest(log)}
    if result.returncode:
        print(log.read_text()[-12000:], flush=True)
        raise RuntimeError(record)
    return record


OUTPUT.mkdir(exist_ok=False)
LOGS.mkdir(exist_ok=False)
execute(["lake", "env", "printenv", "LEAN_PATH"], "lake_path")
execute(["lake", "env", "lean", "--print-prefix"], "toolchain")
toolchain = Path((LOGS / "toolchain.log").read_text().strip())
lean = toolchain / "bin/lean"
checker = toolchain / "bin/leanchecker"
external = []
excluded = []
for entry in (LOGS / "lake_path.log").read_text().strip().split(":"):
    path = (PROJECT / entry).resolve()
    if path.is_dir() and ("/.lake/packages/" in str(path) or path == toolchain / "lib/lean"):
        assert not (path / "OpenQ").exists()
        assert not list(path.glob("Critic*.olean"))
        external.append(str(path))
    else:
        excluded.append(str(path))
assert str(PROJECT / ".lake/build/lib/lean") in excluded
assert external
env = dict(os.environ, LEAN_PATH=":".join([str(OUTPUT), *external]))
save("environment.json", {"lean_path": env["LEAN_PATH"], "excluded": excluded,
                          "lean_sha256": digest(lean), "leanchecker_sha256": digest(checker),
                          "external_package_binaries_retained": True})
execute([lean, "--version"], "version", env)

order = []
sources = {}


def visit(module):
    if module in sources:
        return
    source = PROJECT / (module.replace(".", "/") + ".lean")
    body = source.read_text()
    imports = [word for line in body.splitlines() if re.match(r"^import\s+", line)
               for word in line.split()[1:] if re.fullmatch(r"[A-Za-z0-9_.]+", word)]
    assert not any(word.startswith("Critic") for word in imports)
    sources[module] = {"path": str(source.relative_to(ROOT)), "sha256": digest(source),
                       "imports": imports}
    for dependency in imports:
        if dependency.startswith("OpenQ."):
            visit(dependency)
    order.append(module)


visit(TARGET)
save("source_manifest.json", {"main_module": TARGET, "order": order, "sources": sources})
options = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3",
           "-Dpp.unicode.fun=true"]
builds = []
for number, module in enumerate(order, 1):
    olean = OUTPUT / (module.replace(".", "/") + ".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    source = ROOT / sources[module]["path"]
    record = execute([lean, *options, "-R", PROJECT, "-o", olean, source], module, env)
    assert digest(source) == sources[module]["sha256"], "Source changed during review"
    builds.append({"module": module, **record, "olean_sha256": digest(olean)})
    save("builds.json", builds)
    print(f"Compiled {number}/{len(order)}: {module} ({record['seconds']} s)", flush=True)

audit_source = AUDIT / "ProofAudit.lean"
audit = execute([lean, *options, "-R", AUDIT, "-o", AUDIT / "ProofAudit.olean", audit_source],
                "proof_audit", env, AUDIT)
audit_log = (LOGS / "proof_audit.log").read_text()
assert "EXACT TARGET VERIFIED" in audit_log
axiom_blocks = re.findall(r"depends on axioms:\s*\[([^]]*)\]", audit_log)
assert axiom_blocks
allowed = {"propext", "Classical.choice", "Quot.sound"}
for block in axiom_blocks:
    observed = {value.strip() for value in block.replace("\n", " ").split(",") if value.strip()}
    assert observed <= allowed, observed
assert "sorryAx" not in audit_log
save("type_axioms.json", {"audit": audit, "axiom_blocks": axiom_blocks,
                         "unfolded_operational_statement_checked": True})
print("Exact target, expanded statement, and axiom audit passed; starting kernel replay.", flush=True)
replay = execute([checker, *order], "kernel_replay", env)
save("kernel_replay.json", replay)
unchanged = all(digest(ROOT / value["path"]) == value["sha256"] for value in sources.values())
assert unchanged
save("result.json", {"module_count": len(order), "fresh_source_build": True,
                     "exact_type_and_axioms": True, "kernel_replay": True,
                     "source_unchanged": unchanged,
                     "external_packages_rebuilt_or_replayed": False})
print("PASS: fresh source build, exact target and expanded statement, standard axioms, kernel replay.", flush=True)
