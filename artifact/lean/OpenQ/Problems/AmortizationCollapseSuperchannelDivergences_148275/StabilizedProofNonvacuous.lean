/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticNonvacuousE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwoClaims

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Non-vacuity of the hypothesis of the reviewed claim: for all positive dimensions the
superchannel with completely depolarizing teeth and memory one is physical and its comb
operator is `1 / (a d)`, positive definite. Hence `claim_c1` applies to every physical
numerator `Θ₁` against this denominator.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofNonvacuous

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7
  (IsCPTP choiLinearEquiv ofChoiMatrix choiLinearEquiv_ofChoiMatrix isCPTP_iff_isChannelChoi
    IsChannelChoi)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwoClaims
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-- Choi matrix of the completely depolarizing map `X ↦ Tr(X) 1 / q`. -/
def depolChoi (p q : ℕ) : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ :=
  (((q : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)

theorem depolChoi_channel (p : ℕ) {q : ℕ} (hq : 0 < q) : IsChannelChoi (depolChoi p q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨Matrix.PosSemidef.one.smul (Complex.zero_le_real.2 (inv_nonneg.2 hq'.le)), ?_⟩
  rw [depolChoi, ptr_smul, ptr_one, Fintype.card_fin, smul_smul]
  have : ((((q : ℝ)⁻¹ : ℝ) : ℂ)) * (q : ℂ) = 1 := by
    push_cast
    field_simp
  rw [this, one_smul]

/-- The completely depolarizing channel. -/
def depol (p : ℕ) {q : ℕ} (hq : 0 < q) : Channel p q :=
  ⟨ofChoiMatrix (depolChoi p q), (isCPTP_iff_isChannelChoi _).2 (by
    rw [choiLinearEquiv_ofChoiMatrix]; exact depolChoi_channel p hq)⟩

theorem choi_depol (p : ℕ) {q : ℕ} (hq : 0 < q) : choi (depol p hq).val = depolChoi p q :=
  choiLinearEquiv_ofChoiMatrix _

/-- Completely depolarizing teeth with memory one. -/
def depolSC (a b c d : ℕ) (ha : 0 < a) (hd : 0 < d) : PhysicalSuperchannel a b c d where
  memory := 1
  memory_pos := Nat.one_pos
  pre := (depol c (Nat.mul_pos ha Nat.one_pos)).val
  post := (depol (b * 1) hd).val
  pre_cptp := (depol c (Nat.mul_pos ha Nat.one_pos)).property
  post_cptp := (depol (b * 1) hd).property

theorem combJ_depolSC (a b c d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    combJ (depolSC a b c d ha hd) =
      ((((a : ℝ) * d)⁻¹ : ℝ) : ℂ) • (1 : Matrix (X4 c a b d) (X4 c a b d) ℂ) := by
  ext ⟨⟨⟨c₀, a₀⟩, b₀⟩, d₀⟩ ⟨⟨⟨c₁, a₁⟩, b₁⟩, d₁⟩
  have h : combJ (depolSC a b c d ha hd) (((c₀, a₀), b₀), d₀) (((c₁, a₁), b₁), d₁) =
      ∑ e₀ : Fin 1, ∑ e₁ : Fin 1,
        choi (depol c (Nat.mul_pos ha Nat.one_pos)).val (c₀, finProdFinEquiv (a₀, e₀))
            (c₁, finProdFinEquiv (a₁, e₁)) *
          choi (depol (b * 1) hd).val (finProdFinEquiv (b₀, e₀), d₀)
            (finProdFinEquiv (b₁, e₁), d₁) := rfl
  rw [h, choi_depol, choi_depol]
  simp only [Fin.sum_univ_one, depolChoi, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, and_true]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases h1 : c₀ = c₁ <;> by_cases h2 : a₀ = a₁ <;> by_cases h3 : b₀ = b₁ <;>
    by_cases h4 : d₀ = d₁ <;> simp [h1, h2, h3, h4]
  field_simp

theorem combJ_depolSC_posDef (a b c d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (combJ (depolSC a b c d ha hd)).PosDef := by
  rw [combJ_depolSC]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (inv_pos.2 (mul_pos ha' hd')))

/-- The hypothesis class of the reviewed claim is not empty in any positive dimensions,
and the theorem applies to every physical numerator. -/
theorem claim_c1_nonvacuous (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (Θ₁ : PhysicalSuperchannel a b c d) :
    ∃ y : ℝ,
      referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁
        (depolSC a b c d ha hd) = (y : EReal) ∧
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁
        (depolSC a b c d ha hd) = (y : EReal) := by
  obtain ⟨y, h1, h2, -⟩ := claim_c1 ha hb hc Θ₁ (depolSC a b c d ha hd)
    (combJ_depolSC_posDef a b c d ha hd)
  exact ⟨y, h1, h2⟩

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofNonvacuous

#print axioms OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofNonvacuous.claim_c1_nonvacuous
