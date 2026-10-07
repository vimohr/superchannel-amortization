/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticAlphaMainE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlphaChain
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofNonvacuous

/-!
Critic scratch (amortization problem, e002-i02). Side probe after the review, not part
of the research record.

The comb chain theorem at every order `1 < α ≤ 2` on the locked definitions of
`StabilizedStatement`, by the same route as at order two, with the order-`α` perspective
`Gp α` and its transformer inequality in place of block positivity.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlphaMain

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
  (one_le_geometricMoment)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofTrivial
  (exists_density)
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofRealize OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlpha OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlphaChain
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-! ### A generic eigenvalue bound from trace tests -/

/-- If `Re Tr(E η) ≤ q` for every positive definite `η` of trace one, then `E ≤ q · 1`. -/
theorem psd_of_trace_tests {p : ℕ} (hp : 0 < p) {E : Matrix (Fin p) (Fin p) ℂ}
    (hE : E.PosSemidef) {qq : ℝ} (hq : 0 < qq)
    (hall : ∀ η : Matrix (Fin p) (Fin p) ℂ, η.PosDef → Matrix.trace η = 1 →
      (Matrix.trace (E * η)).re ≤ qq) :
    ((qq : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - E).PosSemidef := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hherm : ((qq : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - E).IsHermitian := by
    refine Matrix.IsHermitian.sub ?_ hE.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  obtain ⟨hn2, hn2nn⟩ := nonneg_eq_ofReal (dotProduct_star_self_nonneg x)
  obtain ⟨heE, heEnn⟩ := nonneg_eq_ofReal (hE.dotProduct_mulVec_nonneg x)
  obtain ⟨n2, hn2def⟩ : ∃ n2 : ℝ, n2 = (star x ⬝ᵥ x).re := ⟨_, rfl⟩
  obtain ⟨eE, heEdef⟩ : ∃ eE : ℝ, eE = (star x ⬝ᵥ E.mulVec x).re := ⟨_, rfl⟩
  rw [← hn2def] at hn2 hn2nn
  rw [← heEdef] at heE heEnn
  have hform : star x ⬝ᵥ ((qq : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - E).mulVec x =
      ((qq * n2 - eE : ℝ) : ℂ) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hn2, heE]
    push_cast
    ring
  rw [hform]
  apply Complex.zero_le_real.2
  rw [sub_nonneg]
  by_cases hx : n2 = 0
  · have hx0 : x = 0 := by
      apply dotProduct_star_self_eq_zero.1
      rw [hn2, hx, Complex.ofReal_zero]
    have : eE = 0 := by
      rw [heEdef, hx0]
      simp
    rw [this, hx, mul_zero]
  · have hn2pos : 0 < n2 := lt_of_le_of_ne hn2nn (Ne.symm hx)
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = eE / n2 := ⟨_, rfl⟩
    have hA : qq < A := by
      rw [hAdef, lt_div_iff₀ hn2pos]
      exact hlt
    have hApos : 0 < A := lt_trans hq hA
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (A - qq) / (2 * A) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by
      rw [hεdef]
      exact div_pos (by linarith) (by linarith)
    have hε1 : ε < 1 := by
      rw [hεdef, div_lt_one (by linarith)]
      linarith
    have hεA : ε * A = (A - qq) / 2 := by
      rw [hεdef]
      field_simp
    have hηpd : (((((1 - ε) / n2 : ℝ)) : ℂ) • Matrix.vecMulVec x (star x) +
        (((ε / p : ℝ)) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)).PosDef :=
      Matrix.PosDef.posSemidef_add
        ((Matrix.posSemidef_vecMulVec_self_star x).smul
          (Complex.zero_le_real.2 (div_nonneg (by linarith) hn2pos.le)))
        (Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (div_pos hε0 hp')))
    have hηtr : Matrix.trace (((((1 - ε) / n2 : ℝ)) : ℂ) • Matrix.vecMulVec x (star x) +
        (((ε / p : ℝ)) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)) = 1 := by
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_vecMulVec,
        Matrix.trace_one, Fintype.card_fin, dotProduct_comm, hn2, smul_eq_mul, smul_eq_mul]
      push_cast
      field_simp
      ring
    have h1 := hall _ hηpd hηtr
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, trace_mul_vecMulVec, Matrix.mul_one, heE, smul_eq_mul, smul_eq_mul,
      Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re] at h1
    have h2 : 0 ≤ (Matrix.trace E).re := (Complex.nonneg_iff.1 hE.trace_nonneg).1
    have h3 : (1 - ε) / n2 * eE = A - ε * A := by
      rw [hAdef]
      field_simp
    have h4 : 0 ≤ ε / p * (Matrix.trace E).re := mul_nonneg (div_nonneg hε0.le hp'.le) h2
    rw [h3, hεA] at h1
    linarith

/-! ### The order-`α` divergence -/

section div
variable {n : Type} [Fintype n] [DecidableEq n]

theorem div_of_supported (α : ℝ) {ρ σ : Matrix n n ℂ} (hR : RangeIncluded ρ σ) :
    geometricStateDivergence α n ρ σ =
      ((log₂ (geometricMoment α ρ σ) / (α - 1) : ℝ) : EReal) := by
  unfold geometricStateDivergence
  simp only [eq_true hR, ↓reduceIte]

theorem div_real {α : ℝ} {ρ σ : Matrix n n ℂ} {t : ℝ}
    (h : geometricStateDivergence α n ρ σ = (t : EReal)) :
    RangeIncluded ρ σ ∧ t = log₂ (geometricMoment α ρ σ) / (α - 1) := by
  by_cases hR : RangeIncluded ρ σ
  · refine ⟨hR, ?_⟩
    rw [div_of_supported α hR] at h
    exact (EReal.coe_eq_coe_iff.1 h).symm
  · rw [geometricStateDivergence_unsupported α ρ σ hR] at h
    exact absurd h.symm (EReal.coe_ne_top t)

theorem div_le_real {α : ℝ} (h1 : 1 < α) {ρ σ : Matrix n n ℂ} {t : ℝ}
    (hpos : 0 < geometricMoment α ρ σ) (hR : RangeIncluded ρ σ)
    (h : geometricStateDivergence α n ρ σ ≤ (t : EReal)) :
    geometricMoment α ρ σ ≤ (2 : ℝ) ^ ((α - 1) * t) := by
  rw [div_of_supported α hR, EReal.coe_le_coe_iff, div_le_iff₀ (by linarith), log₂_eq_logb] at h
  rw [mul_comm]
  exact (Real.logb_le_iff_le_rpow (by norm_num) hpos).1 h

end div

variable {p q s : ℕ}

/-! ### Data processing and equal channels -/

theorem data_processing_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (N : Channel p q)
    {ρ σ : Operator (Fin s × Fin p)} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hR : RangeIncluded ρ σ) :
    RangeIncluded (amplification s N.val ρ) (amplification s N.val σ) ∧
      geometricMoment α (amplification s N.val ρ) (amplification s N.val σ) ≤
        geometricMoment α ρ σ := by
  have hJ := choi_psd N.property
  obtain ⟨h3, h4⟩ := chainC_alpha (s := s) h1 h2 hJ hJ subset_rfl hρ hσ hR
  rw [← amp_choi, ← amp_choi] at h3 h4
  refine ⟨h3, h4.trans ?_⟩
  rw [Gp_self (by linarith) hJ, ← amp_choi, amplification_trace N.val N.property,
    moment_eq_trace α ρ hσ]

theorem amortized_self_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (hp : 0 < p) (N : Channel p q) :
    amortizedChannelDivergence (geometricStateDivergence α) N N = 0 := by
  unfold amortizedChannelDivergence
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨s, hs, ρ, σ, hρ, hσ, t, ht, rfl⟩
    obtain ⟨hR, rfl⟩ := div_real ht
    obtain ⟨hR', hle⟩ := data_processing_alpha h1 h2 N hρ.1 hσ.1 hR
    rw [div_of_supported α hR']
    have h3 : 1 ≤ geometricMoment α (amplification s N.val ρ) (amplification s N.val σ) :=
      one_le_geometricMoment (amplification_isDensityMatrix N hs ρ hρ)
        (amplification_isDensityMatrix N hs σ hσ) hR' α h1.le
    have h4 : log₂ (geometricMoment α (amplification s N.val ρ) (amplification s N.val σ)) ≤
        log₂ (geometricMoment α ρ σ) := by
      rw [log₂_eq_logb, log₂_eq_logb]
      exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hle
    rw [← EReal.coe_sub]
    have h5 : log₂ (geometricMoment α (amplification s N.val ρ) (amplification s N.val σ)) /
        (α - 1) - log₂ (geometricMoment α ρ σ) / (α - 1) ≤ 0 := by
      rw [← sub_div]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact_mod_cast h5
  · obtain ⟨τ, hτ⟩ := exists_density (a := p) hp
    apply le_sSup
    refine ⟨1, Nat.one_pos, τ, τ, hτ, hτ, 0, ?_, ?_⟩
    · rw [geometricStateDivergence_self hτ α (by linarith), EReal.coe_zero]
    · rw [geometricStateDivergence_self (amplification_isDensityMatrix N Nat.one_pos τ hτ) α
        (by linarith), EReal.coe_zero, sub_zero]

/-! ### Finite entire input cost at order `α` -/

/-- If the locked channel-amortized divergence of `(N, M)` at order `α` is the real number
`t`, then `J_N ≪ J_M` and `Tr_out G_α(J_N, J_M) ≤ 2^{(α-1) t} · 1`. -/
theorem cost_bound_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (hp : 0 < p) (N M : Channel p q)
    {t : ℝ} (ht : amortizedChannelDivergence (geometricStateDivergence α) N M = (t : EReal)) :
    RangeIncluded (choi N.val) (choi M.val) ∧
      ((((2 : ℝ) ^ ((α - 1) * t) : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        OpenQ.partialTraceRight (Gp α (choi N.val) (choi M.val))).PosSemidef := by
  have hJN := choi_psd N.property
  have hJM := choi_psd M.property
  have htest : ∀ {K K' : Matrix (Fin p) (Fin p) ℂ}, K' * K = 1 → K * K' = 1 →
      Matrix.trace (Kᴴ * K) = 1 →
      RangeIncluded (choi N.val) (choi M.val) ∧
        (RangeIncluded (choi N.val) (choi M.val) →
          (Matrix.trace (OpenQ.partialTraceRight (Gp α (choi N.val) (choi M.val)) * (Kᴴ * K))).re ≤
            (2 : ℝ) ^ ((α - 1) * t)) := by
    intro K K' hK1 hK2 htr
    have hτ : OpenQ.IsDensityMatrix (pureState K) :=
      ⟨pureState_psd K, by rw [pureState_trace, Matrix.trace_mul_comm, htr]⟩
    have hle : geometricStateDivergence α (Fin p × Fin q) (amplification p N.val (pureState K))
        (amplification p M.val (pureState K)) ≤ (t : EReal) := by
      rw [← ht]
      unfold amortizedChannelDivergence
      apply le_sSup
      refine ⟨p, hp, pureState K, pureState K, hτ, hτ, 0, ?_, ?_⟩
      · rw [geometricStateDivergence_self hτ α (by linarith), EReal.coe_zero]
      · rw [EReal.coe_zero, sub_zero]
    have hdN := amplification_isDensityMatrix N hp _ hτ
    have hdM := amplification_isDensityMatrix M hp _ hτ
    rw [amp_pureState] at hdN hdM
    rw [amp_pureState, amp_pureState] at hle
    have e1 : (K' ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) = 1 := by
      rw [kron_one_mul, hK1, Matrix.one_kronecker_one]
    have e2 : (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * (K' ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) = 1 := by
      rw [kron_one_mul, hK2, Matrix.one_kronecker_one]
    have hRout : RangeIncluded
        ((K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * choi N.val * (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ)
        ((K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * choi M.val * (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ) := by
      by_contra h
      rw [geometricStateDivergence_unsupported α _ _ h] at hle
      exact absurd (top_le_iff.1 hle) (EReal.coe_ne_top t)
    have hR : RangeIncluded (choi N.val) (choi M.val) := by
      by_contra h
      exact not_rangeIncluded_conj _ _ e1 e2 h hRout
    refine ⟨hR, fun _ => ?_⟩
    have hpos := one_le_geometricMoment hdN hdM hRout α h1.le
    have hb := div_le_real h1 (by linarith) hRout hle
    rw [(moment_conj_alpha h1 h2 hJN hJM hR _ _ e1 e2).2, trace_kron_conj] at hb
    exact hb
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hη0 : ((((p : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (inv_pos.2 hp'))
  have htr0 : Matrix.trace ((((p : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)) = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    field_simp
  obtain ⟨K0, K0', a1, a2, a3⟩ := exists_factor hη0
  have hR := (htest a1 a2 (by rw [a3]; exact htr0)).1
  refine ⟨hR, ?_⟩
  refine psd_of_trace_tests hp (ptr_psd (Gp_psd α hJN hJM))
    (Real.rpow_pos_of_pos (by norm_num) _) ?_
  intro η hη htr
  obtain ⟨K, K', b1, b2, b3⟩ := exists_factor hη
  have h := (htest b1 b2 (by rw [b3]; exact htr)).2 hR
  rwa [b3] at h

/-! ### The comb chain inequality and the upper bound -/

variable {a b c d : ℕ}

/-- `W_α = Tr_D G_α(J₁, J₂)` on `C ⊗ A ⊗ B`. -/
def Wα (α : ℝ) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : Matrix (X3 c a b) (X3 c a b) ℂ :=
  OpenQ.partialTraceRight (Gp α (combJ Θ₁) (combJ Θ₂))

theorem Wα_psd (α : ℝ) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : (Wα α Θ₁ Θ₂).PosSemidef :=
  ptr_psd (Gp_psd α (combJ_psd Θ₁) (combJ_psd Θ₂))

/-- Global moment inequality at order `α`. -/
theorem moment_chain_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (hb : 0 < b) (ha : 0 < a)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) {Q : ℝ}
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (Wα α Θ₁ Θ₂) Γ ≤ Q)
    {r : ℕ} (hr : 0 < r) (N M : Channel (a * r) (b * r)) {t : ℝ}
    (ht : amortizedChannelDivergence (geometricStateDivergence α) N M = (t : EReal))
    {s : ℕ} {ρ σ : Operator (Fin s × Fin (c * r))}
    (hρ : OpenQ.IsDensityMatrix ρ) (hσ : OpenQ.IsDensityMatrix σ) (hR : RangeIncluded ρ σ) :
    RangeIncluded (amplification s (Θ₁.referenceAct r N.val) ρ)
        (amplification s (Θ₂.referenceAct r M.val) σ) ∧
      geometricMoment α (amplification s (Θ₁.referenceAct r N.val) ρ)
          (amplification s (Θ₂.referenceAct r M.val) σ) ≤
        (2 : ℝ) ^ ((α - 1) * t) * geometricMoment α ρ σ * Q := by
  obtain ⟨hRNM, hE⟩ := cost_bound_alpha h1 h2 (Nat.mul_pos ha hr) N M ht
  have hJN := choi_psd N.property
  have hJM := choi_psd M.property
  obtain ⟨hRout, hle⟩ := chainS_alpha h1 h2 (combJ_psd Θ₁) (combJ_psd Θ₂) hsupp hJN hJM hRNM
    hρ.1 hσ.1 hR
  rw [amp_refAct, amp_refAct]
  refine ⟨hRout, hle.trans ?_⟩
  have hm1 : 1 ≤ geometricMoment α ρ σ := one_le_geometricMoment hρ hσ hR α h1.le
  have hH := Gp_psd α hρ.1 hσ.1
  have hmH : Matrix.trace (Gp α ρ σ) = ((geometricMoment α ρ σ : ℝ) : ℂ) := by
    rw [moment_eq_trace α ρ hσ.1]
    exact (nonneg_eq_ofReal hH.trace_nonneg).1
  exact chain_trace_bound hb (Gp_psd α (combJ_psd Θ₁) (combJ_psd Θ₂)) (Gp_psd α hJN hJM) hH
    (Real.rpow_pos_of_pos (by norm_num) _) (by linarith) hE hmH hQ

/-- Upper bound for the nested-amortized quantity at order `α`. -/
theorem amortized_le_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (hb : 0 < b) (ha : 0 < a)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) {Q : ℝ}
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (Wα α Θ₁ Θ₂) Γ ≤ Q) :
    referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ ≤
      ((log₂ Q / (α - 1) : ℝ) : EReal) := by
  have hκ : 0 < α - 1 := by linarith
  unfold referenceStabilizedAmortizedDivergence
  apply sSup_le
  rintro v ⟨r, hr, N, M, t, ht, rfl⟩
  have key : amortizedChannelDivergence (geometricStateDivergence α)
      (Θ₁.referenceOnChannel r N) (Θ₂.referenceOnChannel r M) ≤
      ((log₂ Q / (α - 1) + t : ℝ) : EReal) := by
    unfold amortizedChannelDivergence
    apply sSup_le
    rintro w ⟨s, hs, ρ, σ, hρ, hσ, u, hu, rfl⟩
    obtain ⟨hR, rfl⟩ := div_real hu
    obtain ⟨hRout, hle⟩ := moment_chain_alpha h1 h2 hb ha Θ₁ Θ₂ hsupp hQ hr N M ht hρ hσ hR
    have hd1 := amplification_isDensityMatrix (Θ₁.referenceOnChannel r N) hs ρ hρ
    have hd2 := amplification_isDensityMatrix (Θ₂.referenceOnChannel r M) hs σ hσ
    have hRout' : RangeIncluded (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ) := hRout
    have hout1 := one_le_geometricMoment hd1 hd2 hRout' α h1.le
    have hm1 : 1 ≤ geometricMoment α ρ σ := one_le_geometricMoment hρ hσ hR α h1.le
    have hq : (0 : ℝ) < (2 : ℝ) ^ ((α - 1) * t) := Real.rpow_pos_of_pos (by norm_num) _
    have hle' : geometricMoment α (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ) ≤
        (2 : ℝ) ^ ((α - 1) * t) * geometricMoment α ρ σ * Q := hle
    have hQpos : 0 < Q := by
      by_contra hneg
      rw [not_lt] at hneg
      have : (2 : ℝ) ^ ((α - 1) * t) * geometricMoment α ρ σ * Q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hq.le (by linarith)) hneg
      linarith
    rw [div_of_supported α hRout', ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h3 : log₂ (geometricMoment α (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ)) ≤
        log₂ ((2 : ℝ) ^ ((α - 1) * t) * geometricMoment α ρ σ * Q) := by
      rw [log₂_eq_logb, log₂_eq_logb]
      exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hle'
    have h4 : log₂ ((2 : ℝ) ^ ((α - 1) * t) * geometricMoment α ρ σ * Q) =
        (α - 1) * t + log₂ (geometricMoment α ρ σ) + log₂ Q := by
      rw [log₂_eq_logb, log₂_eq_logb, log₂_eq_logb,
        Real.logb_mul (mul_pos hq (by linarith)).ne' hQpos.ne',
        Real.logb_mul hq.ne' (by linarith : geometricMoment α ρ σ ≠ 0),
        Real.logb_rpow (by norm_num) (by norm_num)]
    have h5 : log₂ (geometricMoment α (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ)) / (α - 1) ≤
        ((α - 1) * t + log₂ (geometricMoment α ρ σ) + log₂ Q) / (α - 1) :=
      div_le_div_of_nonneg_right (h3.trans (le_of_eq h4)) hκ.le
    have h6 : ((α - 1) * t + log₂ (geometricMoment α ρ σ) + log₂ Q) / (α - 1) =
        t + log₂ (geometricMoment α ρ σ) / (α - 1) + log₂ Q / (α - 1) := by
      field_simp
    linarith
  calc amortizedChannelDivergence (geometricStateDivergence α)
        (Θ₁.referenceOnChannel r N) (Θ₂.referenceOnChannel r M) - (t : EReal)
      ≤ ((log₂ Q / (α - 1) + t : ℝ) : EReal) - (t : EReal) := EReal.sub_le_sub key le_rfl
    _ = ((log₂ Q / (α - 1) : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        congr 1
        ring

/-- The ordinary quantity is at most the nested-amortized one at order `α`. -/
theorem ordinary_le_amortized_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (ha : 0 < a)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) :
    referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂ ≤
      referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ := by
  unfold referenceStabilizedOrdinaryDivergence
  apply sSup_le
  rintro v ⟨r, hr, N, ρ, hρ, rfl⟩
  have hin := amortized_self_alpha h1 h2 (Nat.mul_pos ha hr) N
  refine le_trans ?_ (le_sSup ⟨r, hr, N, N, 0, by rw [hin, EReal.coe_zero], rfl⟩)
  rw [EReal.coe_zero, sub_zero]
  let e : Fin 1 × Fin (c * r) ≃ Fin (c * r) := Equiv.uniqueProd (Fin (c * r)) (Fin 1)
  let e' : Fin 1 × Fin (d * r) ≃ Fin (d * r) := Equiv.uniqueProd (Fin (d * r)) (Fin 1)
  have hρ' : OpenQ.IsDensityMatrix (ρ.submatrix e e) :=
    ⟨hρ.1.submatrix e, (OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex.trace_submatrix e ρ).trans hρ.2⟩
  have hamp : ∀ Ψ : ChannelMap (c * r) (d * r),
      amplification 1 Ψ (ρ.submatrix e e) = (Ψ ρ).submatrix e' e' := by
    intro Ψ
    ext ⟨s₀, β⟩ ⟨s₁, γ⟩
    rfl
  have hd1 := amplification_isDensityMatrix (Θ₁.referenceOnChannel r N) Nat.one_pos _ hρ'
  have hd2 := amplification_isDensityMatrix (Θ₂.referenceOnChannel r N) Nat.one_pos _ hρ'
  have hP1 : (Θ₁.referenceAct r N.val ρ).PosSemidef := by
    have := hd1.1
    rw [show (Θ₁.referenceOnChannel r N).val = Θ₁.referenceAct r N.val from rfl, hamp] at this
    exact (Matrix.posSemidef_submatrix_equiv e').1 this
  have hP2 : (Θ₂.referenceAct r N.val ρ).PosSemidef := by
    have := hd2.1
    rw [show (Θ₂.referenceOnChannel r N).val = Θ₂.referenceAct r N.val from rfl, hamp] at this
    exact (Matrix.posSemidef_submatrix_equiv e').1 this
  unfold amortizedChannelDivergence
  apply le_sSup
  refine ⟨1, Nat.one_pos, ρ.submatrix e e, ρ.submatrix e e, hρ', hρ', 0, ?_, ?_⟩
  · rw [geometricStateDivergence_self hρ' α (by linarith), EReal.coe_zero]
  · rw [EReal.coe_zero, sub_zero]
    rw [show (Θ₁.referenceOnChannel r N).val = Θ₁.referenceAct r N.val from rfl,
      show (Θ₂.referenceOnChannel r N).val = Θ₂.referenceAct r N.val from rfl, hamp, hamp]
    exact (OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex.divergence_submatrix α e' hP1.1 hP2.1).symm

/-! ### Realized values and the theorem at every order -/

theorem realized_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) {r : ℕ} (eR : Fin r ≃ X3 c a b)
    {Γ : Matrix (X3 c a b) (X3 c a b) ℂ} (h : FeasiblePD c a b Γ) :
    ∃ (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))), OpenQ.IsDensityMatrix ρ ∧
      (RangeIncluded (combJ Θ₁) (combJ Θ₂) →
        geometricStateDivergence α (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
            (Θ₂.referenceAct r N.val ρ) =
            ((log₂ (pairing (Wα α Θ₁ Θ₂) Γ) / (α - 1) : ℝ) : EReal) ∧
          1 ≤ pairing (Wα α Θ₁ Θ₂) Γ) ∧
      (¬ RangeIncluded (combJ Θ₁) (combJ Θ₂) →
        geometricStateDivergence α (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
            (Θ₂.referenceAct r N.val ρ) = ⊤) := by
  obtain ⟨D, hD⟩ := exists_data ha hb hc eR h
  refine ⟨D.chan, D.rho, D.rho_density, ?_, ?_⟩
  · intro hsupp
    obtain ⟨hR, hm⟩ := moment_conj_alpha h1 h2 (combJ_psd Θ₁) (combJ_psd Θ₂) hsupp (D.KT d)
      (D.KT' d) D.KT'_mul_KT D.KT_mul_KT'
    rw [← D.output Θ₁, ← D.output Θ₂] at hR hm
    have hval : geometricMoment α (Θ₁.referenceAct r D.chan.val D.rho)
        (Θ₂.referenceAct r D.chan.val D.rho) = pairing (Wα α Θ₁ Θ₂) Γ := by
      rw [hm, D.trace_conj, hD]
      rfl
    have hd1 : OpenQ.IsDensityMatrix (Θ₁.referenceAct r D.chan.val D.rho) :=
      ⟨by rw [D.output]; exact (combJ_psd Θ₁).mul_mul_conjTranspose_same _,
        ((Θ₁.referenceAct_isCPTP r _ D.chan.property).2 D.rho).trans D.rho_density.2⟩
    have hd2 : OpenQ.IsDensityMatrix (Θ₂.referenceAct r D.chan.val D.rho) :=
      ⟨by rw [D.output]; exact (combJ_psd Θ₂).mul_mul_conjTranspose_same _,
        ((Θ₂.referenceAct_isCPTP r _ D.chan.property).2 D.rho).trans D.rho_density.2⟩
    refine ⟨?_, ?_⟩
    · rw [div_of_supported α hR, hval]
    · rw [← hval]
      exact one_le_geometricMoment hd1 hd2 hR α h1.le
  · intro hns
    apply geometricStateDivergence_unsupported
    rw [D.output Θ₁, D.output Θ₂]
    exact not_rangeIncluded_conj _ _ D.KT'_mul_KT D.KT_mul_KT' hns

/-- The locked ordinary quantity at order `α` restricted to one inserted reference dimension. -/
def ordinaryAtα (α : ℝ) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (r : ℕ) : EReal :=
  sSup {v : EReal | ∃ (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))),
    OpenQ.IsDensityMatrix ρ ∧
    v = geometricStateDivergence α (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
      (Θ₂.referenceAct r N.val ρ)}

theorem ordinaryAtα_le (α : ℝ) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) {r : ℕ} (hr : 0 < r) :
    ordinaryAtα α Θ₁ Θ₂ r ≤
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂ := by
  unfold ordinaryAtα referenceStabilizedOrdinaryDivergence
  apply sSup_le_sSup
  rintro v ⟨N, ρ, hρ, rfl⟩
  exact ⟨r, hr, N, ρ, hρ, rfl⟩

/-- **Comb chain theorem at every order `1 < α ≤ 2`** on the locked definitions, for
supported comb operators: both quantities equal one real number `y`, the ordinary
supremum at the inserted reference dimension `c a b` has the same value, and
`2^{(α-1) y}` is the least upper bound of `Re Tr(W_α Γᵀ)` over feasible testers. -/
theorem regular_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) :
    ∃ y : ℝ,
      referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ = (y : EReal) ∧
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂ = (y : EReal) ∧
      ordinaryAtα α Θ₁ Θ₂ (c * a * b) = (y : EReal) ∧
      IsLUB {x : ℝ | ∃ Γ, Feasible c a b Γ ∧ x = pairing (Wα α Θ₁ Θ₂) Γ}
        ((2 : ℝ) ^ ((α - 1) * y)) := by
  have hκ : 0 < α - 1 := by linarith
  have hW := Wα_psd α Θ₁ Θ₂
  have hr : 0 < c * a * b := Nat.mul_pos (Nat.mul_pos hc ha) hb
  have hreal : ∀ Γ, FeasiblePD c a b Γ →
      ((log₂ (pairing (Wα α Θ₁ Θ₂) Γ) / (α - 1) : ℝ) : EReal) ≤ ordinaryAtα α Θ₁ Θ₂ (c * a * b) ∧
        1 ≤ pairing (Wα α Θ₁ Θ₂) Γ := by
    intro Γ hΓ
    obtain ⟨N, ρ, hρ, h3, -⟩ := realized_alpha h1 h2 ha hb hc Θ₁ Θ₂ (eStar c a b) hΓ
    obtain ⟨h4, h5⟩ := h3 hsupp
    refine ⟨?_, h5⟩
    rw [← h4]
    exact le_sSup ⟨N, ρ, hρ, rfl⟩
  have hU'U := ordinaryAtα_le α Θ₁ Θ₂ hr
  have hUA := ordinary_le_amortized_alpha h1 h2 ha Θ₁ Θ₂
  have hbound := amortized_le_alpha h1 h2 hb ha Θ₁ Θ₂ hsupp (fun Γ hΓ => pairing_le_bound hW hΓ)
  have hstar := hreal _ (gammaStar_feasiblePD hb hc)
  have hU'top : ordinaryAtα α Θ₁ Θ₂ (c * a * b) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hU'U.trans (hUA.trans hbound))
  have hU'bot : ordinaryAtα α Θ₁ Θ₂ (c * a * b) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hstar.1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, ordinaryAtα α Θ₁ Θ₂ (c * a * b) = (y : EReal) :=
    ⟨_, (EReal.coe_toReal hU'top hU'bot).symm⟩
  have hPD : ∀ Γ, FeasiblePD c a b Γ → pairing (Wα α Θ₁ Θ₂) Γ ≤ (2 : ℝ) ^ ((α - 1) * y) := by
    intro Γ hΓ
    obtain ⟨h3, h4⟩ := hreal Γ hΓ
    rw [hy, EReal.coe_le_coe_iff, div_le_iff₀ hκ, log₂_eq_logb] at h3
    rw [mul_comm]
    exact (Real.logb_le_iff_le_rpow (by norm_num) (by linarith)).1 h3
  have hq : (0 : ℝ) < (2 : ℝ) ^ ((α - 1) * y) := Real.rpow_pos_of_pos (by norm_num) _
  have hall := pairing_le_of_PD hb hc hW hq hPD
  have hAy : referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ ≤
      (y : EReal) := by
    have h := amortized_le_alpha h1 h2 hb ha Θ₁ Θ₂ hsupp hall
    rwa [log₂_eq_logb, Real.logb_rpow (by norm_num) (by norm_num), mul_div_cancel_left₀ _ hκ.ne']
      at h
  have hUy : referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
      (y : EReal) := le_antisymm (hUA.trans hAy) (hy ▸ hU'U)
  have hAeq : referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
      (y : EReal) := le_antisymm hAy (hUy ▸ hUA)
  refine ⟨y, hAeq, hUy, hy, ?_, ?_⟩
  · rintro x ⟨Γ, hΓ, rfl⟩
    exact hall Γ hΓ
  · intro Q' hQ'
    have h3 : 1 ≤ Q' :=
      le_trans hstar.2 (hQ' ⟨_, (gammaStar_feasiblePD hb hc).feasible, rfl⟩)
    have h4 := amortized_le_alpha h1 h2 hb ha Θ₁ Θ₂ hsupp (fun Γ hΓ => hQ' ⟨Γ, hΓ, rfl⟩)
    rw [hAeq, EReal.coe_le_coe_iff, le_div_iff₀ hκ, log₂_eq_logb] at h4
    rw [mul_comm]
    exact (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).1 h4

/-- Collapse at every order `1 < α ≤ 2` for every physical pair. -/
theorem collapse_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) :
    referenceStabilizedAmortizedDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂ := by
  by_cases hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)
  · obtain ⟨y, h3, h4, -, -⟩ := regular_alpha h1 h2 ha hb hc Θ₁ Θ₂ hsupp
    rw [h3, h4]
  · have hr : 0 < c * a * b := Nat.mul_pos (Nat.mul_pos hc ha) hb
    obtain ⟨N, ρ, hρ, -, h3⟩ := realized_alpha h1 h2 ha hb hc Θ₁ Θ₂ (eStar c a b)
      (gammaStar_feasiblePD hb hc)
    have hU : referenceStabilizedOrdinaryDivergence (geometricStateDivergence α) Θ₁ Θ₂ = ⊤ := by
      apply top_le_iff.1
      rw [← h3 hsupp]
      exact le_sSup ⟨c * a * b, hr, N, ρ, hρ, rfl⟩
    have hA := ordinary_le_amortized_alpha h1 h2 ha Θ₁ Θ₂
    rw [hU] at hA ⊢
    exact top_le_iff.1 hA

/-- **The locked target.** `ReferenceStabilizedMainStatement` holds. -/
theorem referenceStabilizedMainStatement_holds : ReferenceStabilizedMainStatement :=
  fun _ _ _ _ ha hb hc _ _ h1 h2 Θ₁ Θ₂ => collapse_alpha h1 h2 ha hb hc Θ₁ Θ₂

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlphaMain
