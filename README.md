# Amortization collapse for reference stabilized geometric Rényi superchannel divergences

Standalone publication sources and formal proof artifact for the manuscript by
Vinícius Mohr. The research and proofs were developed jointly by GPT-6.1-Sol and
Claude Opus 5.5 agents in an automated research run initiated by Mohr.
GPT-6.1-Sol wrote the manuscript. The manuscript and [PROVENANCE.md](PROVENANCE.md) explain the
human role, the AI contributions, and the
[lean-orchestrator](https://github.com/vimohr/lean-orchestrator) workflow used to
attempt problems from the [QIQCOP Zoo](https://qiqc-op.com/).

**To verify the result yourself, start with [VERIFY.md](VERIFY.md).** It covers
the commands, expected outputs, evidence files, and mathematical definitions
to review. [HUMAN-CHECK.md](HUMAN-CHECK.md) supplies the detailed reading map.

The theorem concerns finite dimensional deterministic physical superchannels
and every real order `1 < α ≤ 2`. It equates the reference stabilized ordinary
geometric Rényi divergence with the nested amortized quantity in Hirche's
Eq. (39). Its scope excludes the larger fully amortized quantity in Eq. (40).

The source artifact contains all **43 required project modules**, including
shared foundations and imported modules from two other problem directories.
The existing module names are retained so every proof source has the same hash
as the audited source. External dependencies are pinned and obtained through
Lake.

## Contents

| Path | Purpose |
| --- | --- |
| [manuscript.pdf](manuscript.pdf) | Conventional mathematical proof and Lean correspondence. |
| [VERIFY.md](VERIFY.md) | Entry point for reproducing checks and reviewing the theorem's meaning. |
| [manuscript.tex](manuscript.tex), [references.bib](references.bib), `manuscript.bbl` | Editable paper and bibliography. |
| [artifact/lean/](artifact/lean/) | Complete project proof sources, `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. |
| [artifact/source_manifest.json](artifact/source_manifest.json) | Source hashes, imports, and topological build order. |
| [artifact/ProofAudit.lean](artifact/ProofAudit.lean) | Exact theorem type, expanded optimization domains, and axiom checks. |
| [verify_artifact.py](verify_artifact.py) | Fresh compilation of the source closure and kernel replay. |
| [verification/](verification/) | Dated compilation and verification records; see its README. |
| [artifact/prior-audit/](artifact/prior-audit/) | Earlier audit logs, source mapping, and proof provenance. |
| [comparison.csv](comparison.csv), [literature.json](literature.json) | Prior-result comparison and bounded literature search evidence. |
| [REVIEW.txt](REVIEW.txt), [preparation-status.txt](preparation-status.txt), [publication-plan.md](publication-plan.md) | Mathematical assessment and publication preparation records. |
| [PROVENANCE.md](PROVENANCE.md), [RIGHTS.txt](RIGHTS.txt), [CITATION.cff](CITATION.cff) | Contributions, license status, and citation metadata. |
| [LICENSE](LICENSE) | MIT License for the project code, manuscript, and associated publication material. |
| [provenance/agents-2026-10-07.toml](provenance/agents-2026-10-07.toml) | Snapshot of the inspected agent configuration and role assignments. |
| [HUMAN-CHECK.md](HUMAN-CHECK.md), [artifact/ReadStatement.lean](artifact/ReadStatement.lean) | Guide and Lean entry point for checking that the definitions express the intended mathematics. |
| `release-manifest.json` | SHA-256 hashes of the assembled release files. |

## Rebuild the manuscript

Install a LaTeX distribution with `latexmk`, BibTeX, and the packages used in
`manuscript.tex`. From this repository's root, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
```

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

The verification output directory must be new. The verifier creates a fresh
project binary directory, compiles all 43 modules from source, checks the exact
theorem target and reported axioms, and replays the compiled proof closure
with `leanchecker`. A successful run ends with `PASS` and writes `result.json`.
The expected axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

If pinned external packages are already installed in another Lake project,
you can instead run:

```sh
python3 verify_artifact.py --dependency-project /path/to/dependency-project --output verification-local
```

The provider's project proof caches are excluded. This mode reuses its external
package binaries after checking their Git revisions and clean tracked sources.
The verifier uses the installed Lean kernel. It rebuilds and replays the project
proofs; rebuilding and replaying the external dependencies is a separate task.
The recorded runs use existing external binaries. Installation into a new
dependency environment remains to be independently reproduced.

The exact main declaration is:

```text
OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.referenceStabilized_collapse
```

Its literal target is:

```text
OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ReferenceStabilizedMainStatement
```

## Release status

The manuscript was prepared on 5 October 2026; its disclosure was revised on
7 October 2026. This folder can be copied into its own Git repository. It
contains the publication sources and recorded evidence, with generated caches
excluded from the release.

The project code, manuscript, and associated publication material are licensed
under the [MIT License](LICENSE); see [RIGHTS.txt](RIGHTS.txt) for its scope.
External dependencies retain their respective licenses.
After creating the public repository and archive, add
their URLs and the exact artifact version DOI to the manuscript's availability
statement and citation metadata. The bounded literature search and AI reviews
are documented in the evidence; external specialist review remains pending.
