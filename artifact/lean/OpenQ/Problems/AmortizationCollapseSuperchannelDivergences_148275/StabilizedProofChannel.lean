/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticChannelE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofTrivial

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Channel-level facts at order two on the locked definitions: amplification in Choi
form, data processing for supported pairs (hence the entire channel-amortized cost of
equal channels is zero), and the consequences of a finite entire input cost `t`:
`J_N ≪ J_M` and `Tr_out(J_N J_M⁺ J_N) ≤ 2^t`.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
  (one_le_geometricMoment)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofTrivial
  (exists_density)
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-! ### The order-two divergence -/

section div
variable {n : Type} [Fintype n] [DecidableEq n]

theorem log₂_eq_logb (x : ℝ) : log₂ x = Real.logb 2 x := rfl

theorem div_two_of_supported {ρ σ : Matrix n n ℂ} (hR : RangeIncluded ρ σ) :
    geometricStateDivergence 2 n ρ σ = ((log₂ (geometricMoment 2 ρ σ) : ℝ) : EReal) := by
  unfold geometricStateDivergence
  simp only [eq_true hR, ↓reduceIte]
  norm_num

theorem div_two_real {ρ σ : Matrix n n ℂ} {t : ℝ}
    (h : geometricStateDivergence 2 n ρ σ = (t : EReal)) :
    RangeIncluded ρ σ ∧ t = log₂ (geometricMoment 2 ρ σ) := by
  by_cases hR : RangeIncluded ρ σ
  · refine ⟨hR, ?_⟩
    rw [div_two_of_supported hR] at h
    exact (EReal.coe_eq_coe_iff.1 h).symm
  · rw [geometricStateDivergence_unsupported 2 ρ σ hR] at h
    exact absurd h.symm (EReal.coe_ne_top t)

theorem div_two_le_real {ρ σ : Matrix n n ℂ} {t : ℝ}
    (hpos : 0 < geometricMoment 2 ρ σ)
    (h : geometricStateDivergence 2 n ρ σ ≤ (t : EReal)) :
    RangeIncluded ρ σ ∧ geometricMoment 2 ρ σ ≤ (2 : ℝ) ^ t := by
  by_cases hR : RangeIncluded ρ σ
  · refine ⟨hR, ?_⟩
    rw [div_two_of_supported hR] at h
    have h1 : log₂ (geometricMoment 2 ρ σ) ≤ t := by exact_mod_cast h
    rw [log₂_eq_logb] at h1
    exact (Real.logb_le_iff_le_rpow (by norm_num) hpos).1 h1
  · rw [geometricStateDivergence_unsupported 2 ρ σ hR] at h
    exact absurd (top_le_iff.1 h) (EReal.coe_ne_top t)

end div

/-! ### Amplification in Choi form and data processing -/

variable {p q s : ℕ}

def embC (p q s : ℕ) : Fin p × (Fin s × Fin q) → (Fin p × Fin q) × (Fin s × Fin p) :=
  fun w => ((w.1, w.2.2), (w.2.1, w.1))

/-- Contraction of a Choi matrix with an operator on `S ⊗ (input)`. -/
def contrC (JN : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (ρ : Matrix (Fin s × Fin p) (Fin s × Fin p) ℂ) :
    Matrix (Fin s × Fin q) (Fin s × Fin q) ℂ :=
  bsum ((JN ⊗ₖ ρ).submatrix (embC p q s) (embC p q s))

theorem amp_choi (N : ChannelMap p q) (ρ : Operator (Fin s × Fin p)) :
    amplification s N ρ = contrC (choi N) ρ := by
  ext ⟨s₀, β⟩ ⟨s₁, γ⟩
  refine (map_expand N (fun i j => ρ (s₀, i) (s₁, j)) β γ).trans ?_
  simp only [contrC, bsum_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, embC, mul_comm]

theorem contrC_dom {JM JN F : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ}
    {σ ρ H : Matrix (Fin s × Fin p) (Fin s × Fin p) ℂ}
    (h₂ : Dom JM JN F) (h₃ : Dom σ ρ H) :
    Dom (contrC JM σ) (contrC JN ρ) (contrC F H) :=
  ((h₂.kron h₃).submatrix _).bsum

/-- Data processing of the order-two moment for supported pairs, with every external
reference and no invertibility. -/
theorem data_processing (N : Channel p q) {ρ σ : Operator (Fin s × Fin p)}
    (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef) (hR : RangeIncluded ρ σ) :
    RangeIncluded (amplification s N.val ρ) (amplification s N.val σ) ∧
      geometricMoment 2 (amplification s N.val ρ) (amplification s N.val σ) ≤
        geometricMoment 2 ρ σ := by
  have d := contrC_dom (s := s) (dom_self (choi_psd N.property)) (dom_base hσ hρ hR)
  rw [← amp_choi, ← amp_choi, ← amp_choi] at d
  obtain ⟨h1, h2⟩ := moment_le_of_dom d d.left
  refine ⟨h1, h2.trans ?_⟩
  rw [amplification_trace N.val N.property, geometricMoment_two hρ hσ hR]

/-- The entire channel-amortized cost of equal channels is zero. -/
theorem amortized_self (hp : 0 < p) (N : Channel p q) :
    amortizedChannelDivergence (geometricStateDivergence 2) N N = 0 := by
  unfold amortizedChannelDivergence
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨s, hs, ρ, σ, hρ, hσ, t, ht, rfl⟩
    obtain ⟨hR, rfl⟩ := div_two_real ht
    obtain ⟨hR', hle⟩ := data_processing N hρ.1.1 hσ.1 hR
    rw [div_two_of_supported hR']
    have h1 : 1 ≤ geometricMoment 2 (amplification s N.val ρ) (amplification s N.val σ) :=
      one_le_geometricMoment (amplification_isDensityMatrix N hs ρ hρ)
        (amplification_isDensityMatrix N hs σ hσ) hR' 2 (by norm_num)
    have h2 : log₂ (geometricMoment 2 (amplification s N.val ρ) (amplification s N.val σ)) ≤
        log₂ (geometricMoment 2 ρ σ) := by
      rw [log₂_eq_logb, log₂_eq_logb]
      exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hle
    rw [← EReal.coe_sub]
    exact_mod_cast sub_nonpos.2 h2
  · obtain ⟨τ, hτ⟩ := exists_density (a := p) hp
    apply le_sSup
    refine ⟨1, Nat.one_pos, τ, τ, hτ, hτ, 0, ?_, ?_⟩
    · rw [geometricStateDivergence_self hτ 2 (by norm_num), EReal.coe_zero]
    · rw [geometricStateDivergence_self (amplification_isDensityMatrix N Nat.one_pos τ hτ) 2
        (by norm_num), EReal.coe_zero, sub_zero]

/-! ### Finite entire input cost -/

/-- Pure state on `(reference) ⊗ (input)` with amplitude matrix `K`. -/
def pureState (K : Matrix (Fin p) (Fin p) ℂ) : Operator (Fin p × Fin p) :=
  Matrix.vecMulVec (fun x : Fin p × Fin p => K x.1 x.2) (star fun x : Fin p × Fin p => K x.1 x.2)

theorem pureState_apply (K : Matrix (Fin p) (Fin p) ℂ) (x y : Fin p × Fin p) :
    pureState K x y = K x.1 x.2 * star (K y.1 y.2) := rfl

theorem pureState_psd (K : Matrix (Fin p) (Fin p) ℂ) : (pureState K).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem pureState_trace (K : Matrix (Fin p) (Fin p) ℂ) :
    Matrix.trace (pureState K) = Matrix.trace (K * Kᴴ) := by
  simp only [Matrix.trace, Matrix.diag_apply, pureState_apply, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The output of a pure test is a congruence of the Choi matrix. -/
theorem amp_pureState (N : ChannelMap p q) (K : Matrix (Fin p) (Fin p) ℂ) :
    amplification p N (pureState K) =
      (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * choi N *
        (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ := by
  ext ⟨i, β⟩ ⟨j, γ⟩
  refine (map_expand N (fun k l => pureState K (i, k) (j, l)) β γ).trans ?_
  simp only [pureState_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, apply_ite (star : ℂ → ℂ), star_zero, star_one, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem kron_one_mul (A B : Matrix (Fin p) (Fin p) ℂ) :
    (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * (B ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) =
      (A * B) ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Trace of a perspective under the congruence `K ⊗ 1`. -/
theorem trace_kron_conj (F : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (K : Matrix (Fin p) (Fin p) ℂ) :
    Matrix.trace ((K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * F *
        (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ) =
      Matrix.trace (OpenQ.partialTraceRight F * (Kᴴ * K)) := by
  rw [Matrix.trace_mul_cycle, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    kron_one_mul, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, OpenQ.partialTraceRight, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- A positive definite matrix is `Kᴴ K` for an invertible `K`. -/
theorem exists_factor {η : Matrix (Fin p) (Fin p) ℂ} (hη : η.PosDef) :
    ∃ K K' : Matrix (Fin p) (Fin p) ℂ, K' * K = 1 ∧ K * K' = 1 ∧ Kᴴ * K = η := by
  have hS : (supportInvSqrt η).IsHermitian := (supportInvSqrt_posSemidef η).1
  have hunit : IsUnit η.det := (Matrix.isUnit_iff_isUnit_det η).1 hη.isUnit
  have h1 : supportInvSqrt η * η * supportInvSqrt η = 1 := by
    rw [sandwich_eq_supp hη.posSemidef]
    have : pinv η = η⁻¹ := pinv_eq_inv hη
    rw [this, Matrix.mul_nonsing_inv η hunit]
  refine ⟨supportInvSqrt η * η, supportInvSqrt η, mul_eq_one_comm.1 h1, h1, ?_⟩
  rw [Matrix.conjTranspose_mul, hS.eq, hη.1.eq]
  calc η * supportInvSqrt η * (supportInvSqrt η * η) = η * pinv η * η := by
        unfold pinv; simp only [Matrix.mul_assoc]
    _ = η := penrose1 hη.posSemidef

/-- Every equal-state test of the pair, with any external reference, has divergence at
most `t`. -/
def EqualTests (N M : Channel p q) (t : ℝ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ τ : Operator (Fin k × Fin p), OpenQ.IsDensityMatrix τ →
    geometricStateDivergence 2 (Fin k × Fin q) (amplification k N.val τ)
      (amplification k M.val τ) ≤ (t : EReal)

theorem equal_test (N M : Channel p q) {t : ℝ}
    (ht : amortizedChannelDivergence (geometricStateDivergence 2) N M = (t : EReal)) :
    EqualTests N M t := by
  intro k hk τ hτ
  rw [← ht]
  unfold amortizedChannelDivergence
  apply le_sSup
  refine ⟨k, hk, τ, τ, hτ, hτ, 0, ?_, ?_⟩
  · rw [geometricStateDivergence_self hτ 2 (by norm_num), EReal.coe_zero]
  · rw [EReal.coe_zero, sub_zero]

/-- A pure test with invertible amplitude matrix: support of the Choi pair and the value
of the output moment. -/
theorem factor_test (hp : 0 < p) (N M : Channel p q) {t : ℝ} (ht : EqualTests N M t)
    {K K' : Matrix (Fin p) (Fin p) ℂ} (h1 : K' * K = 1) (h2 : K * K' = 1)
    (htr : Matrix.trace (Kᴴ * K) = 1) :
    RangeIncluded (choi N.val) (choi M.val) ∧
      (Matrix.trace (OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val) *
        (Kᴴ * K))).re ≤ (2 : ℝ) ^ t := by
  have hτ : OpenQ.IsDensityMatrix (pureState K) :=
    ⟨pureState_psd K, by rw [pureState_trace, Matrix.trace_mul_comm, htr]⟩
  have hle := ht p hp _ hτ
  have hdN := amplification_isDensityMatrix N hp _ hτ
  have hdM := amplification_isDensityMatrix M hp _ hτ
  rw [amp_pureState] at hdN hdM
  rw [amp_pureState, amp_pureState] at hle
  have e1 : (K' ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) = 1 := by
    rw [kron_one_mul, h1, Matrix.one_kronecker_one]
  have e2 : (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * (K' ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) = 1 := by
    rw [kron_one_mul, h2, Matrix.one_kronecker_one]
  have hJN := choi_psd N.property
  have hJM := choi_psd M.property
  have hRout : RangeIncluded
      ((K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * choi N.val * (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ)
      ((K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) * choi M.val * (K ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ) := by
    by_contra h
    rw [geometricStateDivergence_unsupported 2 _ _ h] at hle
    exact absurd (top_le_iff.1 hle) (EReal.coe_ne_top t)
  have hR : RangeIncluded (choi N.val) (choi M.val) := by
    by_contra h
    exact not_rangeIncluded_conj _ _ e1 e2 h hRout
  refine ⟨hR, ?_⟩
  have hpos := one_le_geometricMoment hdN hdM hRout 2 (by norm_num)
  have hb := (div_two_le_real (by linarith) hle).2
  rw [(moment_conj_eq hJM hJN.1 hR _ _ e1 e2).2, trace_kron_conj] at hb
  exact hb

theorem eta_test (hp : 0 < p) (N M : Channel p q) {t : ℝ} (ht : EqualTests N M t)
    {η : Matrix (Fin p) (Fin p) ℂ} (hη : η.PosDef) (htr : Matrix.trace η = 1) :
    RangeIncluded (choi N.val) (choi M.val) ∧
      (Matrix.trace (OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val) *
        η)).re ≤ (2 : ℝ) ^ t := by
  obtain ⟨K, K', h1, h2, h3⟩ := exists_factor hη
  have h := factor_test hp N M ht h1 h2 (by rw [h3]; exact htr)
  rwa [h3] at h

theorem nonneg_eq_ofReal {z : ℂ} (h : 0 ≤ z) : z = ((z.re : ℝ) : ℂ) ∧ 0 ≤ z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
  exact ⟨Complex.ext rfl (by simpa using h2.symm), h1⟩

theorem trace_mul_vecMulVec {n : Type} [Fintype n] (E : Matrix n n ℂ) (x : n → ℂ) :
    Matrix.trace (E * Matrix.vecMulVec x (star x)) = star x ⬝ᵥ E.mulVec x := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- If every equal-state test of `(N, M)` has divergence at most the real number `t`, then
`J_N ≪ J_M` and `Tr_out(J_N J_M⁺ J_N) ≤ 2^t · 1`. -/
theorem cost_bound_of_tests (hp : 0 < p) (N M : Channel p q) {t : ℝ} (ht : EqualTests N M t) :
    RangeIncluded (choi N.val) (choi M.val) ∧
      ((((2 : ℝ) ^ t : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val)).PosSemidef := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hη0 : ((((p : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (inv_pos.2 hp'))
  have htr0 : Matrix.trace ((((p : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)) = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    field_simp
  have hR := (eta_test hp N M ht hη0 htr0).1
  refine ⟨hR, ?_⟩
  obtain ⟨E, hEdef⟩ : ∃ E : Matrix (Fin p) (Fin p) ℂ,
      E = OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val) := ⟨_, rfl⟩
  rw [← hEdef]
  have hF := (dom_base (choi_psd M.property) (choi_psd N.property).1 hR).right
  have hE : E.PosSemidef := by rw [hEdef]; exact ptr_psd hF
  have hq : (0 : ℝ) < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hall : ∀ η : Matrix (Fin p) (Fin p) ℂ, η.PosDef → Matrix.trace η = 1 →
      (Matrix.trace (E * η)).re ≤ (2 : ℝ) ^ t := by
    intro η hη htr
    rw [hEdef]
    exact (eta_test hp N M ht hη htr).2
  have hherm : ((((2 : ℝ) ^ t : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - E).IsHermitian := by
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
  have hform : star x ⬝ᵥ ((((2 : ℝ) ^ t : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - E).mulVec x =
      (((2 : ℝ) ^ t * n2 - eE : ℝ) : ℂ) := by
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
    have hA : (2 : ℝ) ^ t < A := by
      rw [hAdef, lt_div_iff₀ hn2pos]
      exact hlt
    have hApos : 0 < A := lt_trans hq hA
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (A - (2 : ℝ) ^ t) / (2 * A) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by
      rw [hεdef]
      exact div_pos (by linarith) (by linarith)
    have hε1 : ε < 1 := by
      rw [hεdef, div_lt_one (by linarith)]
      linarith
    have hεA : ε * A = (A - (2 : ℝ) ^ t) / 2 := by
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

/-- **Finite entire input cost.** If the locked channel-amortized divergence of `(N, M)`
at order two is the real number `t`, then `J_N ≪ J_M` and
`Tr_out(J_N J_M⁺ J_N) ≤ 2^t · 1`. Only equal-state tests are used. -/
theorem cost_bound (hp : 0 < p) (N M : Channel p q) {t : ℝ}
    (ht : amortizedChannelDivergence (geometricStateDivergence 2) N M = (t : EReal)) :
    RangeIncluded (choi N.val) (choi M.val) ∧
      ((((2 : ℝ) ^ t : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val)).PosSemidef :=
  cost_bound_of_tests hp N M (equal_test N M ht)

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel
