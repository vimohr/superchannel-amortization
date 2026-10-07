# Checking that Lean proved the intended statement

For setup commands, expected results, and an overview of the evidence, start
with [VERIFY.md](VERIFY.md). This document focuses on the mathematical meaning
of the encoded statement.

Lean checks the proof of the proposition encoded in the source. The human task
is to establish that this proposition, including the definitions it uses,
expresses the mathematical claim in the paper and the intended source problem.
Checking only the theorem's name and its axiom list leaves that task unfinished.
For example, defining both divergences to be zero would make a collapse theorem
easy to prove while changing the mathematics completely.

This distinction is described in Lean's official documentation on
[validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

## 1. Check the exact theorem and its assumptions

Start with the manuscript's Section 2 and the three definitions in
[StabilizedStatement.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/StabilizedStatement.lean):

- `referenceStabilizedOrdinaryDivergence`
- `referenceStabilizedAmortizedDivergence`
- `ReferenceStabilizedMainStatement`

The target quantifies **all** positive finite dimensions `a, b, c, d`, every
**real** order `1 < α ≤ 2`, and every ordered pair of `PhysicalSuperchannel`s
with those dimensions. It concludes equality of the nested amortized and
ordinary reference stabilized quantities in `EReal`, the extended reals.
There is no additional channel-collapse premise or invertibility assumption.

`∀` means “for every”; `∃` means “there exists”; `sSup` denotes the supremum;
`⊤` in `EReal` is positive infinity. Products of dimensions, such as `a * r`,
encode tensor product spaces in a fixed basis.

The final theorem in
[StabilizedCollapse.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/StabilizedCollapse.lean)
has the exact theorem type `ReferenceStabilizedMainStatement`. The checks in
[ProofAudit.lean](artifact/ProofAudit.lean) also require that it is a closed
theorem with that exact type and no universe parameters. The audit separately
elaborates an explicit expansion of its two outer optimization domains and
applies the proved theorem to that expansion. This checks the target's
definition-level connection to those domains. The human still checks that
those domains express the intended mathematics.

## 2. Read the mathematical definitions behind the names

| Concept to check | Source and declarations | What the reviewer should confirm |
| --- | --- | --- |
| Quantum states | [Basic.lean](artifact/lean/OpenQ/Foundations/Basic.lean), `IsDensityMatrix` | Complex positive semidefinite matrices with trace one. |
| Quantum channels | [ChannelCorrespondence.lean](artifact/lean/OpenQ/Problems/EqualWeightLowChoiRank_523ed7/ChannelCorrespondence.lean), `IsCompletelyPositive`, `IsCPTP`; [Statement.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/Statement.lean), `Channel` | Complex-linear maps; positivity after every finite reference extension; trace preservation. |
| Physical superchannels | `Statement.lean`, `PhysicalSuperchannel`, `PhysicalSuperchannel.act` | CPTP preprocessing and postprocessing with an arbitrary positive finite memory. The two superchannels can have different memories. |
| Geometric state divergence | `Statement.lean`, `RangeIncluded`, `supportInvSqrt`, `hermitianPower`, `geometricMoment`, `geometricStateDivergence` | The correct support condition, spectral powers, inverse square root on the support, trace expression, base-two logarithm, and factor `1 / (α - 1)`. Unsupported pairs have value positive infinity. |
| Inner channel amortization | `Statement.lean`, `amortizedChannelDivergence` | Two density matrices and every positive finite external reference; subtraction of the exact finite state-divergence cost. |
| Inserted reference action | [StabilizedAction.lean](artifact/lean/OpenQ/Problems/AmortizationCollapseSuperchannelDivergences_148275/StabilizedAction.lean), `referenceRealization`, `referenceAct`, `referenceOnChannel` | The physical teeth are tensored with the reference identity; the reference is permuted past the inaccessible memory; the inserted map acts on the entire joint system. |
| Two outer divergences | `StabilizedStatement.lean`, the two divergence definitions | The full reference domains, arbitrary joint CPTP insertions, correct state tests, and complete finite input-channel cost. |

Inspect definitions and the conditions in bundled types as well as the visible
theorem hypotheses. A hidden restriction on what counts as a channel or state
can weaken a theorem even when its axiom list is standard. For this artifact,
the relevant local definitions occupy a handful of files; a reviewer need not
read all 43 modules' proof tactics to examine the target.

## 3. Compare the reference domains and cost convention carefully

This is the most delicate part of the interpretation for this result:

- The inserted reference `R` ranges over every positive finite dimension. The
  insertions are arbitrary joint channels `AR → BR`, not just `N ⊗ id_R`.
- Each inner channel-amortized divergence independently ranges over every
  positive finite external state reference `S`. It is separate from `R`.
- The ordinary outer definition directly optimizes density matrices on `CR`
  and compares their outputs on `DR` after a common insertion.
- The outer cost witness `t : ℝ` equals the **entire input-channel amortized
  divergence**. The definition subtracts that value exactly. It excludes
  infinite subtracted costs and retains every finite difference.
- Check singular supported states and unsupported pairs as well as full-rank
  states. The theorem permits infinite values on the output side.

Compare those definitions with Hirche's Definitions 4.4–4.5, Eqs. (33) and
(39), and with the manuscript's explicit finite-cost convention. The cited
paper is [Quantum Network Discrimination](https://quantum-journal.org/papers/q-2023-07-25-1064/).
The result does not assert collapse of the larger fully amortized quantity in
Eq. (40), the endpoint `α = 1`, or arbitrary multi-slot combs.

`Statement.lean` also contains an older fixed-insertion-type `MainStatement`.
The theorem published here targets `ReferenceStabilizedMainStatement` in
`StabilizedStatement.lean`. Check the target actually used by the final theorem.

## 4. Check axioms and reproduce the proof

`#print axioms referenceStabilized_collapse` reports the theorem's transitive
axiom dependencies. The recorded set is:

```text
propext
Classical.choice
Quot.sound
```

These are Lean's standard principles of propositional extensionality,
classical choice, and quotient equality. The important check is that no extra
assumption, `sorryAx`, or native-evaluation axiom was used. An axiom audit does
not examine ordinary theorem hypotheses or certify the physical interpretation
of definitions. See Lean's [axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms).

Follow the repository README to run `verify_artifact.py`. It compiles all 43
project modules into a new directory, checks the exact target and axioms,
and replays the project proof closure with the installed Lean kernel. Its
environment record states which pinned external package binaries were reused.

For readable Lean output after the dependency setup and bootstrap build, run
from this repository's root:

```sh
cd artifact/lean
lake env lean ../ReadStatement.lean
```

[ReadStatement.lean](artifact/ReadStatement.lean) prints the target, the key
definitions, and the axiom list. The source code and these expanded definitions
are the evidence for a human interpretation check.

## 5. Review the correspondence with the paper

The formal model uses finite matrix spaces and physical preprocessing/memory/
postprocessing realizations. Interpreting this as covering all finite
dimensional deterministic physical superchannels relies on the published
realization theorem cited in the manuscript. That representation theorem is
not reproved by this artifact.

The manuscript also proves a reference-absorption correspondence in Proposition
2, relating its ordinary output-channel formulation to the direct state
supremum. That proposition is presented as a conventional argument and is not
a separately formalized export in this release. A human reviewer should read
it when comparing the paper's formulations. Other informal claims, including
novelty and significance, need their own assessment.

## How much human work is involved?

The axiom and exact-type checks are automatic once the environment is set up.
The mathematical interpretation requires a reader familiar with quantum
channels, geometric Rényi divergence, and the intended superchannel definitions.
That reader can concentrate on Section 2, the definitions listed above, and
the model correspondence, rather than verifying every proof step by hand.

The reference systems, singular support convention, and subtraction of the
full channel cost make this a substantive definitions review. Passing Lean's
checks gives strong evidence for the encoded equality; a domain expert's
definitions review supplies the connection to the physical claim.
