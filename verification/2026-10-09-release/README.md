# Release verification, 9 October 2026

The current publication copy passed a fresh formal verification run, a clean
LaTeX/BibTeX build, and local release checks. The PDF is dated 9 October 2026;
its extracted text matches the previous PDF apart from the date. All 43 frozen
Lean source hashes are unchanged.

| Check | Evidence | Outcome |
| --- | --- | --- |
| Fresh compilation of all 43 project modules | [builds.json](builds.json) and [logs/](logs/) | Passed |
| Exact closed theorem type, expanded statement, and six axiom reports | [type_axioms.json](type_axioms.json) and [proof audit log](logs/proof_audit.log) | Passed; only `propext`, `Classical.choice`, and `Quot.sound` |
| Installed Lean kernel replay of the project closure | [kernel_replay.json](kernel_replay.json) | Passed, exit code zero |
| Readable theorem and definition inspection against the fresh closure | [human-statement-check.json](human-statement-check.json) and [human-statement.log](human-statement.log) | Passed |
| CFF schema 1.2.0 and `cffconvert --validate` | [metadata-validation.json](metadata-validation.json) and [cff-validation.log](cff-validation.log) | Passed |
| Zenodo metadata through the pinned official deserializer | [zenodo-importer-validation.json](zenodo-importer-validation.json) | Passed; software version, MIT, ORCID, language, and manuscript relation retained |
| Clean manuscript and bibliography build, PDF text, links, and title-page layout | [manuscript-check.json](manuscript-check.json) and [manuscript-build.log](manuscript-build.log) | Passed; 12 pages and no final LaTeX warnings |
| Local documentation links and CI commands | [documentation-ci-check.json](documentation-ci-check.json) | Passed; source-hash and axiom commands executed against the fresh audit |
| Publication contents and shared release metadata | [release-readiness.json](release-readiness.json) | Passed locally |

[result.json](result.json) records the aggregate formal outcome.
[environment.json](environment.json) records Lean 4.34.1, executable hashes,
clean pinned external packages, and the excluded project cache paths. Only
text evidence is retained here; generated proof binaries are excluded.

The metadata check reuses the official Zenodo deserializer pinned in the
[7 October record](../2026-10-07-release/README.md), after checking its source
hash. The historical JSON Schema still omits `version` and `language`; all
other fields passed that schema, and the complete file passed the pinned
importer. Both fields remain documented in the current official
[Zenodo JSON guide](https://help.zenodo.org/docs/github/describe-software/zenodo-json/).
The shared software version, human creator, ORCID, affiliation, license, and
paper DOI are consistent across the metadata files. The paper DOI is the
author-provided identifier; its public deposit could not be confirmed through
the web tool during this check.

External dependency binaries were reused; they were not rebuilt or replayed.
This is local evidence for the current publication files. It does not record
a GitHub-hosted workflow run, independent dependency installation, a remote
Zenodo record-service test, or publication. Account integration and the first
software DOI remain pending. Mathematical interpretation and external
specialist review remain separate from these formal checks.

The [repository release procedure](../../README.md#availability-and-zenodo-release-procedure)
describes the remaining account steps: commit and push the checked files,
enable Zenodo integration, publish GitHub Release `v1.0.0`, inspect the software
archive and its version DOI, and finalize the separately identified manuscript
record. The [prepared release notes](../../RELEASE_NOTES.md) can be used for
that release. Set the CFF release date when publishing.
