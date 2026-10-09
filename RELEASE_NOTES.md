# v1.0.0 — Formal verification artifact

Frozen formal verification artifact accompanying the manuscript
“Amortization collapse for reference stabilized geometric Rényi superchannel
divergences” by [Vinícius Mohr](https://orcid.org/0009-0001-9239-5673), manuscript DOI
[10.5281/zenodo.23215121](https://doi.org/10.5281/zenodo.23215121).

For finite dimensional deterministic physical superchannels and every real
order `1 < α ≤ 2`, the theorem equates the reference stabilized nested
amortized geometric Rényi divergence with the ordinary reference stabilized
divergence. This is the nested quantity corresponding to Hirche's Eq. (39).
Collapse of the larger fully amortized quantity in Eq. (40), the endpoint
`α = 1`, and arbitrary multi-slot combs are outside the theorem's scope.

The artifact contains all 43 required project proof modules, pinned Lean and
Lake dependency versions, verification scripts, source manifests, audit
records, and supporting documentation. A manuscript copy and editable sources
are included for context. The manuscript DOI identifies the paper;
GitHub--Zenodo integration assigns a separate DOI to the software archive.

The theorem declaration is `referenceStabilized_collapse` in the namespace
`OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275`.
Its exact theorem type is `ReferenceStabilizedMainStatement`.
`ProofAudit.lean` separately checks an explicit expansion of that proposition
into the two optimization domains.

- [VERIFY.md](https://github.com/vimohr/superchannel-amortization/blob/v1.0.0/VERIFY.md) gives reproduction commands, expected results, and
  the evidence for fresh project compilation, type and axiom checks, and
  kernel replay.
- [HUMAN-CHECK.md](https://github.com/vimohr/superchannel-amortization/blob/v1.0.0/HUMAN-CHECK.md) maps the definitions for a mathematical
  review of what was proved.
- [PROVENANCE.md](https://github.com/vimohr/superchannel-amortization/blob/v1.0.0/PROVENANCE.md) records the human role, agent assignments,
  and proof-source history.

The dated verification records passed fresh compilation and kernel replay of
the frozen project sources using Lean 4.34.1. The reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Those runs retained pinned
external dependency binaries; external dependencies were not rebuilt or
replayed. Formal checks and the mathematical interpretation of the definitions
are distinct tasks, and external specialist review remains pending.

The latest local verification on 9 October 2026 passed all 43 fresh project
compilations, exact statement and axiom checks, and kernel replay. The
manuscript and bibliography were rebuilt from source without final LaTeX
warnings; citation and Zenodo metadata checks passed. The dated evidence is
available through VERIFY.md.

Vinícius Mohr initiated and directed the automated research. GPT-6.1-Sol and
Claude Opus 5.5 agents jointly developed the research and proofs;
GPT-6.1-Sol wrote the manuscript. The detailed contribution and AI disclosure
is in the manuscript and provenance record. The human creator, affiliation, and ORCID
are recorded in the citation and archive metadata.

Project code and original associated publication material use the MIT License.
External dependencies retain their respective licenses.
