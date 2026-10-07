# Amortization collapse for reference stabilized geometric Rényi superchannel divergences

For finite dimensional deterministic physical superchannels and every real
order `1 < α ≤ 2`, the reference stabilized nested amortized geometric Rényi
divergence equals the reference stabilized ordinary divergence.

[Read the manuscript](manuscript.pdf) · [Verify the artifact](VERIFY.md) ·
[Review the definitions](HUMAN-CHECK.md) · [Public source repository](https://github.com/vimohr/superchannel-amortization)

**Manuscript DOI:** [10.5281/zenodo.23215121](https://doi.org/10.5281/zenodo.23215121).

**Author:** Vinícius Mohr · [ORCID: 0009-0001-9239-5673](https://orcid.org/0009-0001-9239-5673).

## Result and scope

The equality concerns arbitrary joint CPTP insertions `AR → BR`, with the
inserted reference ranging over every positive finite dimension. Each inner
channel amortization has its own independent external state reference. The
outer subtraction uses the entire finite input-channel amortized divergence.
Singular states and infinite output values are included.

**Scope:** this is the reference stabilized nested quantity corresponding to
Hirche's Eq. (39) in
[Quantum Network Discrimination](https://quantum-journal.org/papers/q-2023-07-25-1064/).
Collapse of the larger fully amortized quantity in Eq. (40), the endpoint
`α = 1`, and arbitrary multi-slot combs are outside this result.

In the supported case, the proof also identifies the common finite supremum
with the ordinary value at reference dimension `|C| |A| |B|`; see the
manuscript's corollary and `StabilizedProofAlphaMain.regular_alpha`. This is a
bound on the reference dimension needed for the value, without an assertion
that an optimizer is attained.

## Main formal theorem

The theorem declaration is
`OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.referenceStabilized_collapse`.
Its exact theorem type is
`OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ReferenceStabilizedMainStatement`.
Within that namespace, the proved declaration has the form:

```lean
theorem referenceStabilized_collapse :
    ReferenceStabilizedMainStatement :=
  StabilizedProofAlphaMain.referenceStabilizedMainStatement_holds
```

The named type is a proposition. Unfolding it and its divergence definitions
gives the expanded theorem statement: a quantified equality between two
explicit optimization domains. [ProofAudit.lean](artifact/ProofAudit.lean)
checks the exact type and separately elaborates an independently written
expansion of those domains.

| To inspect | Source |
| --- | --- |
| Proved theorem declaration | [StabilizedCollapse.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/StabilizedCollapse.lean). |
| Named proposition and the two outer divergences | [StabilizedStatement.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/StabilizedStatement.lean). |
| Exact type and expanded theorem statement checks | [ProofAudit.lean](artifact/ProofAudit.lean). |
| Readable printed definitions | [ReadStatement.lean](artifact/ReadStatement.lean) and [HUMAN-CHECK.md](HUMAN-CHECK.md). |

`Statement.lean` supplies shared physical and divergence definitions and an
older fixed-insertion-type `MainStatement`. The published theorem proves
`ReferenceStabilizedMainStatement` in `StabilizedStatement.lean`.

## Verification and trust boundaries

Start with [VERIFY.md](VERIFY.md) for commands, expected outputs, and evidence.
The full verifier compiles all **43 required project modules** into a new
directory, requires the main declaration to be a theorem of exactly the named
type with no additional theorem-level or universe parameters, checks the
expanded optimization domains, rejects axiom dependencies outside
`propext`, `Classical.choice`, and `Quot.sound`, and replays the project proof
closure using `leanchecker`. [Recorded runs](verification/README.md) passed
these checks.

These checks use the installed Lean 4.34.1 kernel and pinned external package
binaries. The recorded runs rebuilt and replayed the project's sources;
external packages were retained. Rebuilding and replaying external packages
and reproducing installation in a completely new dependency environment are
separate tasks. The connection between the encoded definitions and the
physical question still requires the mathematical review described in
[HUMAN-CHECK.md](HUMAN-CHECK.md). External specialist review remains pending.

The [CI workflow](.github/workflows/lean.yml) builds the theorem and runs the
statement and axiom checks on pushes and pull requests. Its manual option
also runs the full verifier. See [VERIFY.md](VERIFY.md#continuous-integration)
for the difference between these checks and the recorded audit.

The proof sources and their original module names are preserved byte for
byte, including imports from two other problem directories. Historical source
comments such as “candidate” and “registration candidate” describe the
original research workflow. They are retained to preserve the audited hashes;
they do not report a subsequent human review verdict.

## Mathematical ingredients

| Component | Status and location |
| --- | --- |
| Geometric Rényi channel formulas and transformer estimate | Established ingredients credited to Fang–Fawzi in the manuscript; corresponding matrix arguments are formalized in the artifact. |
| Deterministic physical superchannel realization theorem | Established literature result cited in Section 2; the general representation theorem is not reproved here. |
| Ordinary reference absorption | Conventional correspondence argument in Proposition 2; not a separately formalized export in this release. |
| Singular support, full finite input cost, and tester bounds | Formalized steps connecting the stated domains to the comb/tester proof; see Sections 3–7 and the Section 8 dictionary. |
| Tester completion, common-reference realization, and collapse assembly | The manuscript's proposed contribution, with detailed proof and formal exports. Novelty assessment is bounded by the recorded literature search and awaits specialist review. |

## Set up dependencies and verify

Install Git, Python 3, and Lean's `elan` toolchain manager. The required Lean
version is **4.34.1**. From this repository's root:

```sh
cd artifact/lean
lake build OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedCollapse
cd ../..
python3 verify_artifact.py --output verification-local
```

Lake obtains the external dependency revisions recorded in
`artifact/lean/lake-manifest.json`. Keep that lockfile when reproducing this
release. The first build needs network access and can take substantial time.
Physlib also provides `lake exe get_cache` to download compiled dependency
artifacts before the build; downloading that cache is optional.

The verification output directory must be new. A successful run ends with
`PASS` and writes `result.json`. If the pinned external packages are already
installed in another Lake project, you can use:

```sh
python3 verify_artifact.py --dependency-project /path/to/dependency-project --output verification-local
```

The provider's project proof caches are excluded. Its external package
binaries are reused after checking their Git revisions and clean tracked
sources. See [VERIFY.md](VERIFY.md) for the evidence and interpretation.

## Manuscript and contents

[manuscript.pdf](manuscript.pdf) gives the conventional mathematical proof.
Section 2 fixes the definitions and reference domains; Sections 3–7 give the
proof; Section 8 maps its steps to Lean declarations.

| Path | Purpose |
| --- | --- |
| [manuscript.tex](manuscript.tex), [references.bib](references.bib), `manuscript.bbl` | Editable paper and bibliography. |
| [artifact/lean/](artifact/lean/) | Complete project proof sources, toolchain, and Lake manifests. |
| [artifact/source_manifest.json](artifact/source_manifest.json) | Frozen source hashes, imports, and topological build order. |
| [verify_artifact.py](verify_artifact.py) | Fresh project compilation, type and axiom audit, and kernel replay. |
| [verification/](verification/) | Dated verification records and manuscript build log. |
| [artifact/prior-audit/](artifact/prior-audit/) | Historical audit logs, source mapping, and proof provenance. |
| [comparison.csv](comparison.csv), [literature.json](literature.json) | Prior-result comparison and bounded literature search. |
| [REVIEW.txt](REVIEW.txt), [preparation-status.txt](preparation-status.txt), [publication-plan.md](publication-plan.md) | Assessment and publication preparation records. |
| [PROVENANCE.md](PROVENANCE.md), [provenance/agents-2026-10-07.toml](provenance/agents-2026-10-07.toml) | Contributions and inspected agent-role configuration. |
| [CITATION.cff](CITATION.cff), [.zenodo.json](.zenodo.json) | GitHub citation and Zenodo software-release metadata. |
| [RELEASE_NOTES.md](RELEASE_NOTES.md) | Prepared description for the first GitHub Release, `v1.0.0`. |
| [LICENSE](LICENSE), [RIGHTS.txt](RIGHTS.txt) | MIT License and its scope; external dependencies retain their licenses. |
| [release-manifest.json](release-manifest.json) | SHA-256 hashes of the assembled publication files. |

To rebuild the manuscript, install a LaTeX distribution with `latexmk`, BibTeX,
and the packages used in `manuscript.tex`, then run from the repository root:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
```

## Provenance and AI disclosure

Vinícius Mohr directed AI agents to attempt problems from the
[QIQCOP Zoo](https://qiqc-op.com/) using
[lean-orchestrator](https://github.com/vimohr/lean-orchestrator), which was
built using Claude Opus 5.5. The research and proofs were developed jointly by
GPT-6.1-Sol and Claude Opus 5.5 agents. The inspected configuration assigns
research, supervision, literature, and triage to GPT-6.1-Sol and the critic
role to Claude Opus 5.5; the critic also supplied substantive proof material.
GPT-6.1-Sol wrote the manuscript. [PROVENANCE.md](PROVENANCE.md) and Section 9
give the contribution account and distinguish earlier local proof material
from its registration and subsequent checks.

## Availability and Zenodo release procedure

The public source repository is
[vimohr/superchannel-amortization](https://github.com/vimohr/superchannel-amortization).
The manuscript was first prepared on 5 October 2026; the current PDF is dated
7 October 2026.
The manuscript DOI is
[10.5281/zenodo.23215121](https://doi.org/10.5281/zenodo.23215121), supplied by
the author on 7 October 2026. The software metadata is prepared as version
**`1.0.0`**, for the GitHub tag **`v1.0.0`**. The tagged software archive and
its DOI remain pending; preparing these files does not publish a release.
This GitHub repository contains both the paper and the proof artifact.
The recommended Zenodo setup uses two records: a
GitHub-integrated **software artifact** and a separate **preprint** containing
the final manuscript. This lets the paper cite an immutable proof snapshot.

1. The paper identifier is already recorded in the manuscript and under
   `preferred-citation` in `CITATION.cff`. `.zenodo.json` links the software
   artifact to that paper DOI through `isSupplementTo`. Use the corresponding
   Zenodo preprint draft for the final PDF upload in step 5.
2. Link GitHub to Zenodo and enable this repository in Zenodo's GitHub settings
   **before** publishing a release. Review `.zenodo.json` for the software
   title, human creator, ORCID, ETH Zurich affiliation, MIT license, and AI disclosure.
   Zenodo uses this file in preference to `CITATION.cff`; keep their shared
   metadata consistent. Leave `doi` out of `.zenodo.json` so Zenodo assigns a
   DOI to each new software version. `CITATION.cff`, `.zenodo.json`, and
   `release-manifest.json` now all describe software version `1.0.0`.
3. Review the prepared [release notes](RELEASE_NOTES.md) and the checks below.
   Set the CFF release date when actually releasing. Rebuild the PDF if its
   source changed, refresh the release file hashes, and commit and push the
   reviewed files. Run the full verifier on that intended release commit
   (locally or with CI's manual option), using a new output directory.
4. Publish a GitHub Release for that tag after the checks pass. Zenodo archives
   new published releases; a normal commit push or a tag alone is insufficient.
   Use tag `v1.0.0` and title `v1.0.0 — Formal verification artifact`, with
   the prepared release notes as the description.
   Wait for processing, inspect the archived files and metadata, and copy the
   **specific software-version DOI** into the paper's availability paragraph.
   Retain the matching tag or commit there as an additional source locator.
5. Rebuild and upload the final PDF to the paper's preprint draft, link the
   software DOI there as `isSupplementedBy`, and publish the preprint. Update
   the repository's availability links and CFF software DOI with the actual
   identifiers. The manuscript copy in the first code archive may precede
   this final DOI edit; the separately archived preprint is the final paper.

Zenodo also supplies a concept DOI covering all versions of a software record.
Use the specific version DOI in the paper to identify the exact audited
artifact. Later changes to archived files require a new version. The paper
and software identifiers refer to different outputs; do not give both records
the same DOI. Account linking and publishing are performed in the respective
Zenodo and GitHub accounts.

The official guides cover [enabling the integration](https://help.zenodo.org/docs/github/enable-repository/),
[release archiving](https://help.zenodo.org/docs/github/archive-software/github-upload/),
[metadata precedence](https://help.zenodo.org/docs/github/describe-software/),
[reserving a manuscript DOI](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/),
and [record versions](https://help.zenodo.org/docs/deposit/manage-versions/).

## Checks before tagging

- Check that `CITATION.cff`, `.zenodo.json`, and `release-manifest.json` all
  say `1.0.0`, and that the intended tag is `v1.0.0`. Update all three
  version fields together for subsequent releases.
- Check the human creator name, ORCID `0009-0001-9239-5673`, ETH Zurich
  affiliation, MIT license, manuscript DOI `10.5281/zenodo.23215121`, and
  the `isSupplementTo` link.
  The manuscript DOI belongs to the paper. The software DOI is added after
  the GitHub-integrated archive exists.
- Review the release description's Eq. (39) scope, its Eq. (40) exclusion,
  and its AI/provenance statement against the manuscript and `PROVENANCE.md`.
- Follow [VERIFY.md](VERIFY.md) to verify the intended release commit. All
  43 project sources must match the frozen source manifest, and the full
  verifier must report successful compilation, exact-type and expansion
  checks, allowed axioms, and kernel replay. The existing dated records
  describe the same frozen source hashes; a new run supplies evidence for
  the environment used at release time.
- Check the assembled file hashes with the command in
  [VERIFY.md](VERIFY.md#optional-check-the-release-file-hashes). Confirm that
  the archive contains the intended publication files and excludes `.git`,
  `.lake`, temporary outputs, credentials, and generated proof binaries.

Historical preparation notes, candidate comments, and audit logs retain their
original wording and absolute environment paths as provenance. The active
release description identifies the artifact's current scope and version.
These retained paths do not create a runtime dependency on the original
workspace; use the portable root verifier to reproduce the checks.

After editing existing publication files, refresh their recorded hashes from
the repository root. Add any new publication file paths to `files` first;
exclude `.git`, dependency caches, and generated proof binaries.

```sh
python3 - <<'PY'
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

path = Path("release-manifest.json")
manifest = json.loads(path.read_text())
manifest["files"] = {
    name: hashlib.sha256(Path(name).read_bytes()).hexdigest()
    for name in sorted(manifest["files"])
}
manifest["assembled_utc"] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
PY
```

For GitHub's About settings, the suggested description is “Lean 4 formal
verification artifact for reference-stabilized geometric Rényi superchannel amortization collapse
for 1 < α ≤ 2.” Suggested topics are `lean4`, `formal-verification`,
`quantum-information`, `quantum-information-theory`, `renyi-divergence`,
`superchannels`, `quantum-channels`, `theorem-proving`, and `mathlib`.
These values are prepared for the repository owner's About settings; the
local files do not change GitHub's About panel. Add DOI and passing CI badges
when the corresponding archive and workflow results are available.
