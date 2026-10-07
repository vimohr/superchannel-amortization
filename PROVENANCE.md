# Research and proof provenance

The research and proofs were developed jointly by GPT-6.1-Sol and Claude Opus
5.5 agents. Vinícius Mohr's role in the discovery was to direct the AI agents to
attempt open problems listed on the
[Quantum Information and Quantum Computation Open Problem Zoo](https://qiqc-op.com/)
using the [lean-orchestrator repository](https://github.com/vimohr/lean-orchestrator),
which was also built using Claude Opus 5.5. He subsequently requested verification,
manuscript preparation, and assembly of this publication repository. This account
of his role and the orchestrator's development was supplied by Mohr on
7 October 2026.

The inspected `agents.toml` assigns the roles as follows:

| Agent role | Model | Assigned work |
| --- | --- | --- |
| Researcher | GPT-6.1-Sol | Research steps, proofs, Lean files, and experiments. |
| Critic | Claude Opus 5.5 | Adversarial claim review; the preserved records also show substantive proof contributions. |
| Supervisor | GPT-6.1-Sol | Planning and progress assessment. |
| Literature | GPT-6.1-Sol | Checking problem status and gathering references. |
| Triage | GPT-6.1-Sol | Scoring candidate problems for selection. |

An exact snapshot of the configuration inspected on 7 October 2026 is preserved
in [provenance/agents-2026-10-07.toml](provenance/agents-2026-10-07.toml). It
records configured role assignments; the proof source mapping and audit records
provide the evidence for the contributions to this theorem.

The agents jointly performed the mathematical exploration, Lean formalization,
proof development, critical review, and literature work. GPT-6.1-Sol wrote this
manuscript, including the conventional proof exposition reconstructed from the
formal sources. The paper's contributions and AI disclosure statement gives
the same account. The mathematical ingredients from Fang–Fawzi and the physical
superchannel realization theorem are credited in the manuscript.

Earlier audit records are preserved verbatim and reflect the attribution
requested at that time. The manuscript's contribution statement revised on
7 October 2026 records the joint research and proof work described here.

The registered theorem incorporates 16 modules ported from earlier local
critic-agent material from iterations `e002-i01` and `e002-i02`. Its final
registration wrapper applies the previously assembled proof. The source mapping
and earlier review records are preserved in `artifact/prior-audit/`.

The 43 project proof sources were copied verbatim from the frozen publication
artifact prepared on 5 October 2026. Their SHA-256 hashes, import graph, and
build order are in `artifact/source_manifest.json`. The theorem declaration and
its exact type are listed in the repository README and checked by
`artifact/ProofAudit.lean`.

The preserved audit scripts and logs record earlier runs and may contain the
original workspace paths. Use the root `verify_artifact.py` and the README's
commands to reproduce the artifact in another location. The dated verification
records distinguish historical evidence from checks of this copied package.

Recorded verification builds the project sources and uses installed Lean and
pinned external package binaries. The external packages are obtained from
their upstream repositories; their revisions are locked in the Lake manifest.
They are not vendored in this source release. Formal verification uses the
installed Lean kernel and the standard axioms listed in the manuscript.

The AI reviews and bounded search do not establish scientific priority,
external specialist endorsement, or journal acceptance. The manuscript keeps
the theorem's reference domains and order range explicit, credits established
ingredients, and records the limits of the novelty search.
