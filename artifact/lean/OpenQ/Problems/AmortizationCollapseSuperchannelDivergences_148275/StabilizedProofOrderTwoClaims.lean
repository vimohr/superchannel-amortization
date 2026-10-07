/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticClaimsE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

One theorem with the content of the reviewed claim c1, on the locked definitions of
`StabilizedStatement` at order two, for a positive definite denominator comb operator.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwoClaims

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofLiteral
open scoped ComplexOrder Kronecker Matrix

noncomputable section

variable {a b c d : ℕ}

/-- **Claim c1.** Positive dimensions `a`, `b`, `c` (and any `d`), physical superchannels
with arbitrary memories, comb operator `J₂` positive definite. Then:

1. the locked nested-amortized and ordinary quantities at order two are one real number `y`;
2. the ordinary supremum restricted to the inserted reference dimension `c a b` equals `y`;
3. `2^y` is the least upper bound of `Re Tr(W Γᵀ)`, `W = Tr_D(J₁ J₂⁻¹ J₁)`, over feasible
   testers `Γ`;
4. every pair of joint insertions with finite entire channel-amortized cost has supported
   Choi matrices, and for every bound `q > 0` of the spectrum of `Tr_{B R}(J_N J_M⁺ J_N)`,
   every external reference and every supported pair of density matrices, the outputs are
   supported and `m₂(ω₁, ω₂) ≤ 2^y q m₂(ρ, σ)`. -/
theorem claim_c1 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (hPD : (combJ Θ₂).PosDef) :
    ∃ y : ℝ,
      referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = (y : EReal) ∧
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = (y : EReal) ∧
      ordinaryAt Θ₁ Θ₂ (c * a * b) = (y : EReal) ∧
      IsLUB {x : ℝ | ∃ Γ, Feasible c a b Γ ∧ x = pairing
        (OpenQ.partialTraceRight (combJ Θ₁ * (combJ Θ₂)⁻¹ * combJ Θ₁)) Γ} ((2 : ℝ) ^ y) ∧
      ∀ (r : ℕ), 0 < r → ∀ (N M : Channel (a * r) (b * r)) (t : ℝ),
        amortizedChannelDivergence (geometricStateDivergence 2) N M = (t : EReal) →
        RangeIncluded (choi N.val) (choi M.val) ∧
        ∀ (q : ℝ), 0 < q →
          (∀ x ∈ spectrum ℝ
            (OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val)), x ≤ q) →
          ∀ (s : ℕ) (ρ σ : Operator (Fin s × Fin (c * r))),
            OpenQ.IsDensityMatrix ρ → OpenQ.IsDensityMatrix σ → RangeIncluded ρ σ →
            RangeIncluded (amplification s (Θ₁.referenceAct r N.val) ρ)
                (amplification s (Θ₂.referenceAct r M.val) σ) ∧
              geometricMoment 2 (amplification s (Θ₁.referenceAct r N.val) ρ)
                  (amplification s (Θ₂.referenceAct r M.val) σ) ≤
                (2 : ℝ) ^ y * q * geometricMoment 2 ρ σ := by
  have hunit : IsUnit (combJ Θ₂).det := (Matrix.isUnit_iff_isUnit_det _).1 hPD.isUnit
  have hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂) :=
    (rangeIncluded_iff_exists_mul _ _).2 ⟨(combJ Θ₂)⁻¹ * combJ Θ₁, by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]⟩
  obtain ⟨y, h1, h2, h3, h4⟩ := regular_alpha2 ha hb hc Θ₁ Θ₂ hsupp
  have h4' := h4
  rw [Wop_posDef Θ₁ Θ₂ hPD] at h4'
  refine ⟨y, h1, h2, h3, h4', ?_⟩
  intro r hr N M t ht
  obtain ⟨hRNM, -⟩ := cost_bound (Nat.mul_pos ha hr) N M ht
  refine ⟨hRNM, ?_⟩
  intro q hq hspec s ρ σ hρ hσ hR
  obtain ⟨hR', hle⟩ := moment_chain_lambda hb Θ₁ Θ₂ hsupp (Q := (2 : ℝ) ^ y)
    (fun Γ hΓ => h4.1 ⟨Γ, hΓ, rfl⟩) N M hRNM hq hspec hρ hσ hR
  refine ⟨hR', hle.trans (le_of_eq ?_)⟩
  ring

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwoClaims

#print axioms OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwoClaims.claim_c1
#print axioms OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue.channel_value
#print axioms OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue.transformer_le
#print axioms OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue.transformer_eq
#print axioms OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue.channel_amortized_le
