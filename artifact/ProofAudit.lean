import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedCollapse

open Lean Elab Command
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

elab "#review_exact_type" : command => do
  let env ← getEnv
  let some (.thmInfo info) := env.find?
    `OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.referenceStabilized_collapse
    | throwError "Expected theorem"
  unless info.levelParams.isEmpty && info.type == mkConst
    `OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ReferenceStabilizedMainStatement do
    throwError "Unexpected theorem parameters or target"
  logInfo "EXACT TARGET VERIFIED"

#review_exact_type

-- Check an independently written operational expansion by ordinary elaboration.
example : ∀ (a b c d : ℕ), 0 < a → 0 < b → 0 < c → 0 < d →
    ∀ (α : ℝ), 1 < α → α ≤ 2 →
    ∀ (Θ₁ Θ₂ : PhysicalSuperchannel a b c d),
      sSup {v : EReal | ∃ (r : ℕ) (_ : 0 < r)
        (N M : Channel (a * r) (b * r)) (t : ℝ),
          amortizedChannelDivergence (geometricStateDivergence α) N M = (t : EReal) ∧
          v = amortizedChannelDivergence (geometricStateDivergence α)
            (Θ₁.referenceOnChannel r N) (Θ₂.referenceOnChannel r M) - (t : EReal)} =
      sSup {v : EReal | ∃ (r : ℕ) (_ : 0 < r)
        (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))),
          OpenQ.IsDensityMatrix ρ ∧
          v = geometricStateDivergence α (Fin (d * r))
            (Θ₁.referenceAct r N.val ρ) (Θ₂.referenceAct r N.val ρ)} :=
  referenceStabilized_collapse

#print axioms referenceStabilized_collapse
#print axioms StabilizedProofAlpha.transformer_alpha
#print axioms StabilizedProofAlpha.qform_integral
#print axioms StabilizedProofAlphaMain.realized_alpha
#print axioms StabilizedProofAlphaMain.cost_bound_alpha
#print axioms StabilizedProofAlphaMain.collapse_alpha
#print ReferenceStabilizedMainStatement
#print PhysicalSuperchannel
#print geometricStateDivergence
#print amortizedChannelDivergence
