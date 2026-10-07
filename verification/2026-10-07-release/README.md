# Release verification, 7 October 2026

These records describe a new full verifier run from the publication
repository, using the research workspace only to supply clean, pinned
external packages. Existing project proof binaries were excluded from the
import path. The project proof sources were unchanged.

| Check | Evidence | Outcome |
| --- | --- | --- |
| Fresh compilation of all 43 project modules | [builds.json](builds.json) and [logs/](logs/) | Passed |
| Exact closed theorem type, explicit statement expansion, and six axiom reports | [type_axioms.json](type_axioms.json) and [proof audit log](logs/proof_audit.log) | Passed; only `propext`, `Classical.choice`, and `Quot.sound` |
| Installed Lean kernel replay of the project closure | [kernel_replay.json](kernel_replay.json) | Passed, exit code zero |
| Readable theorem and definition inspection | [human-statement-check.json](human-statement-check.json) and [human-statement.log](human-statement.log) | Passed against the fresh closure |
| CFF schema 1.2.0 and `cffconvert --validate` | [metadata-validation.json](metadata-validation.json) and [cff-validation.log](cff-validation.log) | Passed |
| Current official Zenodo metadata deserializer | [zenodo-importer-validation.json](zenodo-importer-validation.json) | Passed, including ORCID, MIT, version, language, and the paper relation |
| Manuscript build and author/DOI text checks | [manuscript-check.json](manuscript-check.json) and [manuscript-build.log](manuscript-build.log) | Passed without LaTeX warnings; title page inspected |
| Local documentation links and CI commands | [documentation-ci-check.json](documentation-ci-check.json) and [action-tags.json](action-tags.json) | Passed; workflow source-hash and axiom commands executed locally |

The aggregate formal result is [result.json](result.json).
[environment.json](environment.json) identifies the toolchain, executable
hashes, pinned external packages, and excluded project caches.

Zenodo's documentation links a legacy JSON Schema that omits `version` and
`language`, although its [deposit metadata documentation](https://developers.zenodo.org/#deposit-metadata)
supports both. The strict legacy schema passed for all other fields.
The complete `.zenodo.json` passed the unmodified current
[official metadata deserializer](https://github.com/zenodo/zenodo-rdm/blob/9370acc127c643aff4c43c59cf163c2982f3201c/site/zenodo_rdm/legacy/deserializers/metadata.py),
loaded in a local Flask application context with DOI identifier validation.
The reports retain the legacy schema discrepancy and identify the importer
commit, source hash, dependencies, input file hash, and transformed metadata.
The software version and language fields were retained.

External dependency binaries were reused; they were not rebuilt or replayed.
Installation in a completely new dependency environment, a GitHub-hosted CI
run, and actual Zenodo publication were not performed by this check.
The local importer check does not run the remote record service or test
account integration. Mathematical interpretation and external specialist
review remain separate from these automated checks.

The release manifest records hashes for these text records and the rebuilt
manuscript. Compiled proof binaries, downloaded validator packages, and
temporary build directories are excluded from the publication archive.
