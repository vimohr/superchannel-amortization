import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedAction

/-!
Source target: Hirche, Quantum Network Discrimination, Definitions 4.4 and 4.5,
Eqs. (33) and (39), specialized to the locked geometric Rényi state divergence.
The inserted reference R and each inner state reference S are distinct.
The ordinary definition is directly the state supremum in Eq. (33).
The fully amortized quantity in Eq. (40) is not defined or asserted here.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

open scoped Classical

noncomputable section

/-- Eq. (33): optimize over every positive finite inserted reference, every
joint complex CPTP insertion, and every density matrix on C ⊗ R.
There is no extra external state-reference optimization in this definition. -/
def referenceStabilizedOrdinaryDivergence (D : StateDivergence) {a b c d : ℕ}
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : EReal :=
  sSup {v : EReal | ∃ (r : ℕ) (_hr : 0 < r)
    (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))),
      OpenQ.IsDensityMatrix ρ ∧
      v = D (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
        (Θ₂.referenceAct r N.val ρ)}

/-- Eq. (39): both joint insertions share R; each channel-amortized divergence
independently optimizes every positive finite external state reference S.
The real witness t is the value of the entire input-channel amortized supremum.
It excludes infinite subtracted costs and retains all finite negative terms. -/
def referenceStabilizedAmortizedDivergence (D : StateDivergence) {a b c d : ℕ}
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : EReal :=
  sSup {v : EReal | ∃ (r : ℕ) (_hr : 0 < r)
    (N M : Channel (a * r) (b * r)) (t : ℝ),
      amortizedChannelDivergence D N M = (t : EReal) ∧
      v = amortizedChannelDivergence D (Θ₁.referenceOnChannel r N)
        (Θ₂.referenceOnChannel r M) - (t : EReal)}

/-- The corrected universal geometric Rényi target. Each physical realization
has its own positive finite inaccessible memory. No collapse or data-processing
premise is imposed. Singular supports and infinite output values are included. -/
def ReferenceStabilizedMainStatement : Prop :=
  ∀ (a b c d : ℕ), 0 < a → 0 < b → 0 < c → 0 < d →
    ∀ (α : ℝ), 1 < α → α ≤ 2 →
      ∀ (Θ₁ Θ₂ : PhysicalSuperchannel a b c d),
        referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
          referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂

/-- Explicit expansion of the target's two outer optimization domains. -/
theorem referenceStabilizedMainStatement_expanded :
    ReferenceStabilizedMainStatement ↔
      ∀ (a b c d : ℕ), 0 < a → 0 < b → 0 < c → 0 < d →
        ∀ (α : ℝ), 1 < α → α ≤ 2 →
          ∀ (Θ₁ Θ₂ : PhysicalSuperchannel a b c d),
            sSup {v : EReal | ∃ (r : ℕ) (_hr : 0 < r)
              (N M : Channel (a * r) (b * r)) (t : ℝ),
                amortizedChannelDivergence (geometricStateDivergence α) N M =
                  (t : EReal) ∧
                v = amortizedChannelDivergence (geometricStateDivergence α)
                  (Θ₁.referenceOnChannel r N) (Θ₂.referenceOnChannel r M) -
                    (t : EReal)} =
            sSup {v : EReal | ∃ (r : ℕ) (_hr : 0 < r)
              (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))),
                OpenQ.IsDensityMatrix ρ ∧
                v = geometricStateDivergence α (Fin (d * r))
                  (Θ₁.referenceAct r N.val ρ) (Θ₂.referenceAct r N.val ρ)} :=
  Iff.rfl

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
