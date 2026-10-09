# How to verify the manuscript and Lean artifact

Verification has two parts: checking the formal proof, and checking that its
statement and definitions express the intended mathematics. This document
gives a route through both. The detailed definitions review is in
[HUMAN-CHECK.md](HUMAN-CHECK.md).

The checks distinguish the **theorem declaration**
`referenceStabilized_collapse`, its **exact theorem type**
`ReferenceStabilizedMainStatement`, and the **expanded theorem statement**
obtained by unfolding the optimization domains. The audit requires a theorem
of exactly that named type, with no additional theorem-level or universe
parameters, and separately checks an independently written expansion.
The full Python verifier also enforces the axiom allowlist, excluding
`sorryAx`, and performs fresh project compilation and kernel replay.

| What you want to examine | Where to start |
| --- | --- |
| Reproduce the formal checks | The commands below and [verify_artifact.py](verify_artifact.py). |
| Understand exactly what was proved | The manuscript's Section 2, [StabilizedStatement.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/StabilizedStatement.lean), and [HUMAN-CHECK.md](HUMAN-CHECK.md). |
| Inspect the mathematical proof | [manuscript.pdf](manuscript.pdf), Sections 3–7; Section 8 maps the argument to Lean declarations. |
| Read the recorded verification evidence | [verification/README.md](verification/README.md) and the latest [release verification](verification/2026-10-09-release/README.md). |
| Check research and proof provenance | [PROVENANCE.md](PROVENANCE.md) and [artifact/prior-audit/source_mapping.json](artifact/prior-audit/source_mapping.json). |

## 1. Run the formal checks yourself

The commands below use a POSIX shell and start in the repository root. Install
Git, Python 3, and Lean's `elan` toolchain manager. The pinned Lean version is
**4.34.1**. The dependency revisions are recorded in
[artifact/lean/lake-manifest.json](artifact/lean/lake-manifest.json); retain
that file when reproducing this release.

First prepare the dependency environment:

```sh
cd artifact/lean
lake build OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedCollapse
cd ../..
```

The first build needs network access and can take substantial time. See the
[README](README.md#set-up-dependencies-and-verify) for the optional dependency
cache command. The bootstrap also builds project modules; the next step checks
them again from sources in a new directory.

Run the verifier with ordinary Python, keeping its assertions enabled:

```sh
python3 verify_artifact.py --output verification-local
```

`verification-local` must not already exist. For another run, choose a new
output directory or omit `--output` to use a newly created temporary directory.
The script excludes existing project proof binaries from its import path.
It checks source hashes, compiles all 43 project modules, checks the exact
theorem type and axiom dependencies, and replays the compiled proof closure using
`leanchecker`.

If you already have the exact pinned dependencies installed in another Lake
project, you may supply that project instead:

```sh
python3 verify_artifact.py --dependency-project /path/to/dependency-project --output verification-local
```

The provider's external package Git revisions and clean tracked sources are
checked. Its project proof caches are excluded.

## 2. Inspect the outcome and its evidence

A successful run exits with status zero and ends with:

```text
Exact target, operational expansion, and axiom audit passed; kernel replay starting.
PASS. Results: ...
```

Inspect the new output directory. Its `result.json` should contain:

```json
{
  "module_count": 43,
  "fresh_source_build": true,
  "exact_type_and_axioms": true,
  "kernel_replay": true,
  "source_unchanged": true,
  "external_packages_rebuilt_or_replayed": false,
  "frozen_artifact": true
}
```

The `false` field describes the external-library trust boundary: the verifier
uses installed external package binaries. It rebuilds and replays the project's
43 modules. `environment.json` identifies the reused packages and revisions.

| Check | Evidence in your output directory |
| --- | --- |
| All 43 project modules compiled successfully | `builds.json` and each module's log in `logs/`. |
| The declaration is a theorem of exactly the expected type, with no additional theorem-level or universe parameters | `type_axioms.json` and `logs/proof_audit.log`, including `EXACT TARGET VERIFIED`. |
| The named type elaborates as the expanded statement with the two stated outer optimization domains | `type_axioms.json` and the explicit example in [artifact/ProofAudit.lean](artifact/ProofAudit.lean). |
| Axiom dependencies stay within the standard set | `type_axioms.json` and the `depends on axioms` messages in `logs/proof_audit.log`. |
| Kernel replay completed successfully | `kernel_replay.json`, its zero exit code, and `logs/kernel_replay.log`. |
| The expected sources and dependency environment were used | [artifact/source_manifest.json](artifact/source_manifest.json), `environment.json`, and the verifier's hash and revision checks. |

The main theorem's recorded axiom set is:

```text
propext
Classical.choice
Quot.sound
```

Inspect every axiom block printed by the audit. Extra axioms, `sorryAx`, or
native-evaluation assumptions require investigation. Lean's official
[axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms)
explains what `#print axioms` reports.

The repository includes a successful dated run under
[verification/2026-10-09-release/](verification/2026-10-09-release/README.md). Reproducing the checks on
your own installation gives you evidence from your environment. If a command
fails, inspect its log and exit code; an incomplete output directory is not a
successful verification record.

## 3. Inspect the statement directly in Lean

After the bootstrap build, run from the repository root:

```sh
cd artifact/lean
lake env lean ../ReadStatement.lean
lake env lean ../ProofAudit.lean
cd ../..
```

[ReadStatement.lean](artifact/ReadStatement.lean) prints the theorem type,
the key definitions, the physical superchannel structure, and the axiom list.
[ProofAudit.lean](artifact/ProofAudit.lean) checks the exact closed theorem type and
applies the theorem to an explicit expansion of the outer suprema. These files
are short enough to inspect yourself. The full verifier additionally controls
the project import path, enforces the axiom allowlist on the printed reports,
and performs fresh compilation and kernel replay. Running `ProofAudit.lean`
alone prints the axioms; it does not itself reject additional axioms.

You can also read the previously printed definitions in
[verification/human-statement.log](verification/human-statement.log).

The theorem declaration is:

```text
OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.referenceStabilized_collapse
```

Its exact theorem type is:

```text
OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ReferenceStabilizedMainStatement
```

Read this proposition and the definitions it uses. Its expanded theorem
statement is checked separately in `ProofAudit.lean`. `Statement.lean` also
contains an older fixed-insertion-type `MainStatement`; the published theorem proves
`ReferenceStabilizedMainStatement` in `StabilizedStatement.lean`.

## 4. Check that the definitions match the mathematics

Start with the manuscript's Section 2 and follow the file-by-file reading map
in [HUMAN-CHECK.md](HUMAN-CHECK.md). Review both explicit theorem hypotheses
and the conditions inside types such as `Channel` and `PhysicalSuperchannel`.

The key points are:

- States are complex positive semidefinite matrices of trace one. Zero
  eigenvalues are permitted.
- Channels are complex-linear, completely positive, trace-preserving maps.
  Physical superchannels use CPTP preprocessing and postprocessing with
  arbitrary positive finite memories.
- The order is every real `1 < α ≤ 2`, and all four system dimensions are
  positive finite integers.
- The inserted reference ranges over every positive finite dimension, and
  insertions are arbitrary joint CPTP maps `AR → BR`.
- Each inner channel amortization independently ranges over its external
  state reference. The outer subtraction uses the entire finite input-channel
  amortized divergence.
- The geometric state divergence uses the intended support inverse and
  spectral power. Unsupported state pairs have value positive infinity.

Compare the exact domains and cost convention with Hirche's Definitions
4.4–4.5, Eqs. (33) and (39), cited in the manuscript. The result concerns that
nested quantity. The larger fully amortized quantity in Eq. (40), `α = 1`,
and arbitrary multi-slot combs are outside its stated scope.

This part requires mathematical judgment. A standard axiom list and a correct
formal proof do not by themselves establish that the definitions describe the
intended physical problem. Lean's documentation discusses this distinction in
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

## 5. Check the correspondence with the manuscript

Section 8 provides a dictionary between the mathematical argument and its
Lean declarations. For the physical interpretation, also read Section 2's
discussion of deterministic superchannel realizations and Proposition 2 on
ordinary reference absorption.

The general physical realization theorem is cited from the literature and
is not reproved by this artifact. Proposition 2 is a conventional argument
in the manuscript and is not a separately formalized export in this release.
A reader comparing the paper's formulations should review those arguments.
Scientific novelty and significance are assessed through the literature and
specialist review; the recorded search is bounded.

The recorded formal checks use Lean 4.34.1, its installed kernel, and pinned
external package binaries. The verifier does not rebuild or replay external
packages. Installation in a completely new dependency environment remains
to be independently reproduced. See [verification/README.md](verification/README.md)
for the recorded environment and scope.

## Continuous integration

The [GitHub workflow](.github/workflows/lean.yml) runs on pushes to `main`,
pull requests targeting `main`, and manual dispatch. It checks all 43 frozen
source hashes, builds `StabilizedCollapse`, runs `ReadStatement.lean` and
`ProofAudit.lean`, and rejects printed axioms outside the standard allowlist.
It retains text logs and a CI result record as downloadable workflow artifacts.

The routine job can use Lake and dependency caches. Its `ci/result.json`
therefore records `fresh_source_build: false` and `kernel_replay: false`;
these fields distinguish its limited checks from a full verifier run.

For the full audit, use GitHub **Actions → Lean verification → Run workflow**
and select the option to freshly compile all 43 modules and replay their
proofs. This additionally runs `verify_artifact.py`; inspect
`full/result.json` and its logs as described above. External dependency
binaries can still be reused, and `external_packages_rebuilt_or_replayed`
remains false. A hosted CI run does not supply specialist mathematical review.

The workflow has been prepared for this repository. Its first GitHub-hosted
run can occur after it is committed and pushed; local validation does not
represent a completed hosted run. No passing CI or DOI badge is claimed here.

## Optional: check the release file hashes

On an unmodified release copy, run this from the repository root:

```sh
python3 - <<'PY'
import hashlib
import json
from pathlib import Path

manifest = json.loads(Path("release-manifest.json").read_text())
for name, expected in manifest["files"].items():
    actual = hashlib.sha256(Path(name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Changed file: {name}")
print(f"All {len(manifest['files'])} release file hashes match.")
PY
```

This identifies the exact files being reviewed. The formal compilation and
definition review establish the proof and its mathematical interpretation.
