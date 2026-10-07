# Publication preparation for geometric Rényi superchannel amortization collapse

Prepared 5 October 2026 for the owner of the Lean research workspace.

The reference stabilized geometric Rényi superchannel equality registered as C31 is a credible candidate for a research paper. The independent audit supports the correctness of the precise formal statement. A bounded literature search found no earlier published proof of that statement. Scientific priority and the significance of the contribution still need specialist assessment, and a manuscript and reproducible release remain to be prepared.

This document lists the remaining work and the evidence that should show each step is complete. The recommendations are specific to the present result. Venue requirements are identified separately.

## Current evidence and remaining gaps

| Item | Evidence as of 5 October 2026 | Remaining work |
| --- | --- | --- |
| Formal correctness | An independent build of all 43 project modules, exact target and axiom checks, and a separate kernel replay passed. | Preserve the audited sources and reproduce the publication release in a clean environment. |
| Mathematical scope | The audit compared the physical model and optimization domains with the intended source definitions. | Present the correspondence explicitly in a readable manuscript and have a domain expert scrutinize it. |
| Novelty | Twelve primary sources were inspected; no earlier published match was located. The search had indexing and retrieval limits. | Complete a focused citation and terminology search and obtain specialist feedback. |
| Scientific value | The equality removes the nested amortization advantage for the stated geometric divergence. | Explain the advance over known channel results and assess its importance for the intended venue. |
| Proof presentation | A Lean proof and internal review records exist. | Write a conventional mathematical proof, notation guide, and correspondence with Lean declarations. |
| Contributions and disclosure | The registered proof incorporates earlier local critic scratch. | Establish accurate human contributions, acknowledgments, AI disclosure, and release licenses. |
| Submission materials | No publication package was prepared in this review. | Prepare the manuscript, artifact release, bibliography, and venue specific materials. |

The [independent audit](../lean_run/problems/amortization-collapse-for-superchannel-divergences-148275/work/user_audit_20261005/REVIEW.txt) is the source for these verification findings. Internal acceptance by the orchestrator records a successful review of the locked theorem. It does not establish scientific priority or acceptance by a journal.

## Step 1 Preserve the audited result and fix the publication scope

Before further editing, make a dated copy of the proof and audit evidence outside the orchestrator workspace. Copy the full project import closure, definitions, toolchain and dependency manifests, source hashes, verification scripts, and logs. The 43 audited modules include shared foundations and imports from other problem directories, so copying only this problem's directory would be insufficient. Use the audited file manifest; a Git commit alone may omit relevant uncommitted files in the live workspace. Check the copied source hashes against the audit. Keep subsequent manuscript and release preparation in a separate directory or repository.

Use the audited statement as the starting point for the manuscript:

> For all finite complex Hilbert spaces A, B, C, D of positive dimensions a, b, c, d, every real 1 < α ≤ 2, and every ordered pair of physical deterministic superchannels taking channels A → B to channels C → D, the reference stabilized nested amortized divergence equals the reference stabilized ordinary divergence for the geometric Rényi state divergence. The equality is in the extended real numbers, with the reference quantifiers and finite input cost conventions specified below.

The definitions must retain all of the following features:

- Each superchannel has its own arbitrary positive finite realization memory.
- The inserted reference R ranges over every positive finite dimension, and inserted channels are arbitrary joint CPTP maps AR → BR. CPTP means completely positive and trace preserving.
- Each inner amortized channel divergence independently quantifies every positive finite external state reference S.
- The full finite real input channel divergence is subtracted exactly. Negative differences remain admissible, and unsupported state pairs have divergence +∞. The optimization never requires subtracting infinity from infinity.
- The final theorem has no additional support, invertibility, rational order, reference dimension, or assumed channel collapse hypothesis.

The intended source correspondence is Hirche's Definition 4.4, Eq. (33), for the ordinary quantity and Definition 4.5, Eq. (39), for nested amortization. The larger fully amortized quantity in Eq. (40) is outside this theorem. [Quantum Network Discrimination](https://quantum-journal.org/papers/q-2023-07-25-1064/pdf/).

Keep the distinction visible in the title, abstract, introduction, and theorem. General multi-slot combs and the endpoint α = 1 are also outside the audited statement. No proof of these extensions is needed to publish the current scoped result.

**Completion evidence:** a dated source snapshot with matching hashes and a one page statement of the publication theorem, its definitions, and its relation to the source equations.

## Step 2 Establish novelty and identify the new contribution

Expand the earlier search before asserting that the theorem is new. Follow citations both backward and forward from Hirche and Fang–Fawzi, inspect the latest versions of relevant preprints, and search under alternative terminology: geometric or maximal Rényi divergence, quantum strategies, combs, process tensors, supermaps, and higher order channels. Inspect theorem statements and assumptions, rather than relying on titles or abstracts.

Make a comparison table for the closest results. Record whether each covers ordinary channels or superchannels, its order range, inserted and external references, support assumptions, cost convention, and which amortized quantity it treats. Check whether an existing general theorem already implies this equality, even if it uses different terminology.

Fang–Fawzi supplies important established ingredients, including geometric channel formulas, chain rules, amortization collapse, and an operator transformer inequality. The publication must identify the additional argument that reaches the superchannel equality. [Geometric Rényi Divergence and its Applications in Quantum Channel Capacities](https://arxiv.org/abs/1909.05758).

Ask a researcher familiar with channel or strategy divergences to assess the precise statement and the comparison table. The important questions are whether the equality is already known, whether it is an immediate consequence of prior work, and which part of the proof constitutes a substantive advance. Record the response and any references it supplies.

If an earlier proof is found, revise the contribution accordingly: a new proof, formalization, clarification, or extension may still be valuable, but the paper's priority claim must match the evidence. An open problem catalogue label is useful context and cannot establish novelty by itself.

**Completion evidence:** an updated search record, a comparison table citing exact theorems, and a defensible statement of what is new. Expert feedback should be sought; journal peer review remains a separate process.

## Step 3 Write the mathematical proof and explain the model correspondence

Produce a proof that a quantum information referee can read without running Lean. Organize it around the mathematical ideas and label established ingredients with their sources. A useful outline, based on the audited proof, is:

1. Define geometric state divergence, channel amortization, physical superchannels, and the two reference stabilized superchannel quantities. Explain supports, singular inverse powers, and the extended real conventions.
2. Establish the matrix perspective and transformer estimates for every real 1 < α < 2, including the integral argument. Treat α = 2 explicitly.
3. Obtain the comb moment and tester bounds that control arbitrary inserted and external references. Show where the entire finite input channel cost enters the bound.
4. Explain tester completion and physical realization. In the supported case, the audited construction uses a sufficient reference dimension r = c × a × b; this is derived within the proof. State precisely what this dimension bound establishes.
5. Handle singular testers and unsupported comb pairs. Explain why the latter give +∞ for the ordinary quantity and hence for the amortized quantity.
6. Combine the upper bound with the lower bound obtained from equal insertions, whose input divergence cost is zero.

Give particular attention to the translation between the mathematical statement and the formal model. Explain why preprocessing and postprocessing with finite memory represent deterministic physical superchannels, and cite the established realization theorem. That representation theorem is not newly proved by the registered Lean result. [Chiribella, D'Ariano, and Perinotti, Transforming quantum operations](https://arxiv.org/abs/0804.0180).

Explain how tensor reordering implements the reference extension, why arbitrary joint insertions are permitted, and how reference absorption relates the state based ordinary definition to the output channel form used in the proof. Track the independent reference quantifiers carefully.

Avoid claiming that every supremum is attained. The audited tester characterization uses a least upper bound; an optimizer claim would require its own argument. Likewise, retain singular and unsupported cases rather than silently specializing the theorem to invertible matrices.

Create a short dictionary linking the paper's main theorem and decisive lemmas to their Lean declarations. Verify any additional corollaries separately. Operational claims about arbitrary adaptive protocols or the stronger Eq. (40) do not follow merely from stating the present equality.

**Completion evidence:** a complete mathematical proof, explicit treatment of boundary cases, and a manuscript to Lean correspondence table.

## Step 4 Obtain specialist review and assess significance

Have someone with relevant quantum information expertise read the theorem, definitions, and mathematical proof. Prefer a reader who did not originate the local proof. Ask for scrutiny of the reference domains, physical realization argument, complete input cost subtraction, real order range, singular support cases, and exact relation to Hirche's definitions.

Separately, ask whether the contribution is substantial enough for the proposed venue. The introduction should explain what superchannel difficulty the proof resolves beyond ordinary channel collapse and what useful conclusion the equality supplies. A precise optimization interpretation is worthwhile even if no further operational application is claimed. Only include stronger consequences after proving them.

These are recommendations for resolving the present uncertainties. They are not universal requirements to obtain an external endorsement before submitting a paper. For example, Quantum evaluates significant technical or conceptual contributions, and a correct incremental result can fall below its threshold. [Quantum editorial policies](https://quantum-journal.org/editorial-policies/).

**Completion evidence:** review comments, written responses and revisions, and a clear explanation of the result's contribution and appropriate venue.

## Step 5 Prepare a reproducible formal artifact

Create a standalone source release that a reader can verify without the running orchestrator, critic scratch directories, or shared project build caches. Include:

- All required project sources, the exact theorem and definition entry points, and a manifest of file hashes.
- The Lean toolchain, Lake configuration, dependency revisions, and any local dependency modifications needed for reproduction.
- A portable verification script with documented commands and expected outputs. Adapt the existing audit harness so it has no hard coded dependence on `/scratch/vimohr/lean_run`.
- Checks for the precise theorem type, reported axioms, proof placeholders, and kernel replay, with an explicit description of what each check covers.
- A guide to the main lemmas and a short explanation of the mathematical definitions.
- Appropriate licenses and attribution for the released sources and reused dependencies.

Have another person reproduce the release in a clean checkout or environment. Build the project from sources and confirm that it does not load old project proof binaries. Record how external dependencies are obtained and which versions were verified. If release preparation changes proof sources or definitions, rerun the relevant formal checks and reconcile the manuscript with the release.

The completed audit used Lean 4.34.1 and these dependency source revisions:

```text
Mathlib  d13f23b723b8a846827a245b89c10fc7d3f11612
Physlib  44c66d54be78db4693be9f8f92bd3b5ad124ed6f
```

It rebuilt and replayed all 43 project modules, while retaining installed Lean and external package binaries. It did not rebuild or replay the external packages. The checker used the installed Lean kernel; it was not an independently implemented kernel. Describe that trust boundary accurately. A further rebuild or broader replay of dependencies can strengthen assurance and should be identified as additional work if performed.

Use a versioned artifact with a stable public reference when publishing. A permanent archive identifier is useful. Retain verification logs and hashes with that exact version so the paper's evidence remains reproducible after the research workspace changes.

**Completion evidence:** a portable release, successful reproduction from a clean environment, and a version identifier tied to the manuscript.

## Step 6 Record contributions and proof provenance

Prepare an accurate account of the work before deciding the author list and contribution statement. Identify the responsible human contributors and their roles in mathematical reasoning, formalization, verification, literature review, and writing. Credit established mathematical ingredients and any reused source material appropriately.

The registered result incorporates 16 modules ported from earlier local critic scratch in iterations e002-i01 and e002-i02. Its final wrapper applies the earlier assembled proof. Registration should not be described as a second independently discovered mathematical proof. Preserve this history in the contribution record and make the public account of the methods accurate.

Describe AI assistance according to its actual role. If agents produced mathematical arguments, Lean code, or review material, a disclosure limited to proofreading would be incomplete. The human authors need to understand and take responsibility for the published claims. If Quantum is selected, its current instructions require a contribution statement and disclosure of the scope of AI use. [Quantum author instructions](https://quantum-journal.org/instructions/authors/).

**Completion evidence:** an agreed author and contribution record, acknowledgments, an accurate methods disclosure, and confirmed licenses for the release.

## Step 7 Assemble the manuscript and prepare submission

Draft the manuscript around the final contribution established by Steps 2–4. A suitable working title is “Amortization collapse for reference stabilized geometric Rényi superchannel divergences.” Adjust it if the novelty assessment changes the contribution.

Include an abstract giving the order range and scope, an introduction explaining the relation to prior work, precise definitions, the mathematical proof, the formal verification methods and trust boundary, limitations, artifact availability, contributions, and references. State the main result and assumptions early. Check every claimed corollary against its proof and every citation against the original source.

Choose the journal based on the contribution and expert feedback. Quantum is one possible venue to assess, and acceptance is not established by the audit. If chosen, its current process requires an arXiv preprint posted to or cross-listed in `quant-ph`, permits supplementary files, and requires consent from all co-authors and relevant right holders. It also prohibits concurrent journal consideration. Recheck these instructions when submitting. [Quantum author instructions](https://quantum-journal.org/instructions/authors/).

For an arXiv preprint, prepare the LaTeX sources, bibliography, figures if used, metadata, and artifact links, and inspect the processed PDF. Check whether the submitting author's account needs endorsement in the intended category. Endorsement is a submission eligibility step, not scientific peer review. [arXiv submission overview](https://info.arxiv.org/help/submit/index.html), [arXiv endorsement guidance](https://info.arxiv.org/help/endorsement.html).

After submission, address referee comments and update the manuscript and formal artifact together when changes affect the mathematics. Preserve version correspondence. Public posting, researcher correspondence, and journal submission are subsequent actions for the authors to initiate.

**Completion evidence:** a checked manuscript and source bundle, a matching artifact release, completed venue requirements, and agreement of all authors to submit.

## Final check before public submission

- [ ] The exact publication theorem and reference domains are fixed and match the released Lean definitions.
- [ ] The novelty comparison is current and the contribution is stated accurately.
- [ ] The proof is readable and all mathematical and scope concerns have been addressed.
- [ ] The manuscript explains the significance without claiming unproved extensions.
- [ ] A clean environment reproduction verifies the released artifact.
- [ ] Attribution, contributions, AI disclosure, and licenses are complete.
- [ ] The manuscript, artifact version, bibliography, and submission metadata agree.
- [ ] The intended venue's current requirements have been checked and all authors agree to submission.

Additional examples, a sharper reference dimension bound, stronger divergences, or a general comb extension may improve a future paper. They are separate research tasks and are not prerequisites for presenting the audited scoped equality.

## Technical evidence for publication preparation

The exact formal declaration is:

```text
OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.referenceStabilized_collapse
```

Its literal target type is:

```text
OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ReferenceStabilizedMainStatement
```

The reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The existing audit directory is:

```text
/scratch/vimohr/lean_run/problems/amortization-collapse-for-superchannel-divergences-148275/work/user_audit_20261005/
```

Start with `REVIEW.txt`, `result.json`, `literature.json`, `source_manifest.json`, `builds.json`, `type_axioms.json`, and `kernel_replay.json`. `verify.py` and `ProofAudit.lean` contain the verification procedure. Preserve the associated environment records and logs when freezing the evidence.

This plan is intended for `/scratch/vimohr/publication-notes/`, outside the configured orchestrator workspace. It should remain outside the portfolio, problem dossiers, agent prompts, and orchestrator registrations.
