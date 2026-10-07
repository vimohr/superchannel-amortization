/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticChannelValueE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofLiteral

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

The cited channel ingredients at order two on the locked definitions, with singular
supported pairs (reviewed note, Sections 2 and 7; Fang and Fawzi, Lemmas 5 and 47):

* `transformer_le`, `transformer_eq`: `G(KXKᴴ, KYKᴴ) ≤ K G(X, Y) Kᴴ` for every rectangular
  `K`, with equality for invertible `K`, where `G(X, Y) = X Y⁺ X` on supported pairs.
* `channel_amortized_le`: the channel chain bound `D^A(N‖M) ≤ log₂ q` when
  `Tr_out(J_N J_M⁺ J_N) ≤ q`.
* `channel_value`: both the ordinary and the channel-amortized divergence of a supported
  pair equal `log₂ λ_max Tr_out(J_N J_M⁺ J_N)` (closed form and amortization collapse).
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofOrthogonal
  (trace_mul_nonneg)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
  (one_le_geometricMoment ordinaryChannelDivergence_nonneg)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofTrivial
  (ordinaryCh_le_amortizedCh_geometric)
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofLiteral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-! ### Transformer inequality with support inverses -/

section transformer
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- `G(KXKᴴ, KYKᴴ) ≤ K G(X, Y) Kᴴ` for supported pairs and every rectangular `K`. -/
theorem transformer_le {σ ρ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hρ : ρ.IsHermitian)
    (hR : RangeIncluded ρ σ) (K : Matrix m n ℂ) :
    (K * (ρ * pinv σ * ρ) * Kᴴ -
      (K * ρ * Kᴴ) * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ)).PosSemidef :=
  dom_schur ((dom_base hσ hρ hR).conj K) (hσ.mul_mul_conjTranspose_same K)

/-- Equality for invertible `K`. -/
theorem transformer_eq {σ ρ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hρ : ρ.IsHermitian)
    (hR : RangeIncluded ρ σ) (K : Matrix m n ℂ) (K' : Matrix n m ℂ)
    (hK1 : K' * K = 1) (hK2 : K * K' = 1) :
    (K * ρ * Kᴴ) * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ) = K * (ρ * pinv σ * ρ) * Kᴴ := by
  have h1 := transformer_le hσ hρ hR K
  have hσ' : (K * σ * Kᴴ).PosSemidef := hσ.mul_mul_conjTranspose_same K
  have hρ' : (K * ρ * Kᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose K hρ
  obtain ⟨hR', hm⟩ := moment_conj_eq hσ hρ hR K K' hK1 hK2
  rw [geometricMoment_two hρ' hσ' hR'] at hm
  have htr : Matrix.trace (K * (ρ * pinv σ * ρ) * Kᴴ -
      (K * ρ * Kᴴ) * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ)) = 0 := by
    have h2 := (nonneg_eq_ofReal h1.trace_nonneg).1
    rw [h2, Matrix.trace_sub, Complex.sub_re, hm, sub_self, Complex.ofReal_zero]
  have h0 := (h1.trace_eq_zero_iff).1 htr
  exact (sub_eq_zero.1 h0).symm

end transformer

/-! ### Channel chain bound and closed form -/

variable {p q s : ℕ}

theorem ptl_psd {m n : Type} [Fintype m] [Fintype n] {M : Matrix (m × n) (m × n) ℂ}
    (h : M.PosSemidef) : (OpenQ.partialTraceLeft M).PosSemidef := by
  have e : OpenQ.partialTraceLeft M =
      ∑ k : m, M.submatrix (fun i : n => (k, i)) (fun i => (k, i)) := by
    ext i j
    simp only [OpenQ.partialTraceLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [e]
  exact Matrix.posSemidef_sum _ fun k _ => Matrix.PosSemidef.submatrix h _

theorem trace_ptl {m n : Type} [Fintype m] [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace (OpenQ.partialTraceLeft M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, OpenQ.partialTraceLeft, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Trace of the channel contraction: the pairing of the two marginals. -/
theorem trace_contrC (F : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
    (H : Matrix (Fin s × Fin p) (Fin s × Fin p) ℂ) :
    Matrix.trace (contrC F H) =
      ∑ i, ∑ j, OpenQ.partialTraceRight F i j * OpenQ.partialTraceLeft H i j := by
  have hL : Matrix.trace (contrC F H) = ∑ s₀ : Fin s, ∑ β : Fin q, ∑ i : Fin p, ∑ j : Fin p,
      F (i, β) (j, β) * H (s₀, i) (s₀, j) := by
    simp only [Matrix.trace, Matrix.diag_apply, contrC, bsum_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, embC, Fintype.sum_prod_type]
  rw [hL]
  refine (sum4_rev _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [OpenQ.partialTraceRight, OpenQ.partialTraceLeft, Finset.sum_mul_sum]

/-- **Channel chain bound** at order two for a supported pair of Choi matrices. -/
theorem channel_amortized_le (N M : Channel p q)
    (hR : RangeIncluded (choi N.val) (choi M.val)) {x : ℝ} (hx : 0 < x)
    (hE : ((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
      OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val)).PosSemidef) :
    amortizedChannelDivergence (geometricStateDivergence 2) N M ≤ ((log₂ x : ℝ) : EReal) := by
  unfold amortizedChannelDivergence
  apply sSup_le
  rintro v ⟨s, hs, ρ, σ, hρ, hσ, u, hu, rfl⟩
  obtain ⟨hRs, rfl⟩ := div_two_real hu
  have d2 := dom_base (choi_psd M.property) (choi_psd N.property).1 hR
  have d3 := dom_base hσ.1 hρ.1.1 hRs
  have dd := contrC_dom (s := s) d2 d3
  rw [← amp_choi, ← amp_choi] at dd
  obtain ⟨hRout, hle⟩ := moment_le_of_dom dd dd.left
  have hHs := (ptl_psd d3.right).transpose
  have htr : (Matrix.trace (contrC (choi N.val * pinv (choi M.val) * choi N.val)
      (ρ * pinv σ * ρ))).re ≤ x * geometricMoment 2 ρ σ := by
    rw [trace_contrC, ← regularComb_fullTranspose_pairing]
    have h0 := trace_mul_nonneg hE hHs
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_transpose, trace_ptl, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h0
    rw [geometricMoment_two hρ.1.1 hσ.1 hRs]
    linarith
  have hd1 := amplification_isDensityMatrix N hs ρ hρ
  have hd2 := amplification_isDensityMatrix M hs σ hσ
  have hout1 := one_le_geometricMoment hd1 hd2 hRout 2 (by norm_num)
  have hm1 : 1 ≤ geometricMoment 2 ρ σ := one_le_geometricMoment hρ hσ hRs 2 (by norm_num)
  rw [div_two_of_supported hRout, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have h1 : log₂ (geometricMoment 2 (amplification s N.val ρ) (amplification s M.val σ)) ≤
      log₂ (x * geometricMoment 2 ρ σ) := by
    rw [log₂_eq_logb, log₂_eq_logb]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (hle.trans htr)
  have h2 : log₂ (x * geometricMoment 2 ρ σ) = log₂ x + log₂ (geometricMoment 2 ρ σ) := by
    rw [log₂_eq_logb, log₂_eq_logb, log₂_eq_logb,
      Real.logb_mul hx.ne' (by linarith : geometricMoment 2 ρ σ ≠ 0)]
  linarith

/-- An eigenvalue of a Hermitian matrix is at most any scalar that dominates it. -/
theorem spectrum_le_of_psd {n : Type} [Fintype n] [DecidableEq n] {E : Matrix n n ℂ}
    (hE : E.IsHermitian) {y : ℝ} (h : ((y : ℂ) • (1 : Matrix n n ℂ) - E).PosSemidef) :
    ∀ x ∈ spectrum ℝ E, x ≤ y := by
  intro x hx
  rw [hE.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix n n ℂ, U = (hE.eigenvectorUnitary : Matrix n n ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by rw [hUdef]; exact Unitary.coe_star_mul_self _
  have hspec : E = U * Matrix.diagonal (fun j => (hE.eigenvalues j : ℂ)) * Uᴴ := by
    have h0 := hE.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h0
    rw [hUdef]
    exact h0
  have h1 := h.conjTranspose_mul_mul_same U
  have e : Uᴴ * ((y : ℂ) • (1 : Matrix n n ℂ) - E) * U =
      (y : ℂ) • (1 : Matrix n n ℂ) - Matrix.diagonal (fun j => (hE.eigenvalues j : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU1]
    congr 1
    conv_lhs => rw [hspec]
    calc Uᴴ * (U * Matrix.diagonal (fun j => (hE.eigenvalues j : ℂ)) * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal (fun j => (hE.eigenvalues j : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun j => (hE.eigenvalues j : ℂ)) := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one]
  rw [e] at h1
  have h2 := h1.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
    smul_eq_mul, mul_one] at h2
  have h3 : (0 : ℂ) ≤ ((y - hE.eigenvalues i : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]
    exact h2
  exact sub_nonneg.1 (Complex.zero_le_real.1 h3)

/-- **Closed form and amortization collapse for channels at order two**, on the locked
definitions, for a supported pair of Choi matrices (singular `J_M` allowed): both
divergences equal `log₂` of the largest eigenvalue of `Tr_out(J_N J_M⁺ J_N)`. -/
theorem channel_value (hp : 0 < p) (N M : Channel p q)
    (hR : RangeIncluded (choi N.val) (choi M.val)) {x : ℝ} (hx0 : 0 < x)
    (hx : IsGreatest (spectrum ℝ
      (OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val))) x) :
    amortizedChannelDivergence (geometricStateDivergence 2) N M = ((log₂ x : ℝ) : EReal) ∧
      ordinaryChannelDivergence (geometricStateDivergence 2) N M = ((log₂ x : ℝ) : EReal) := by
  have hF := (dom_base (choi_psd M.property) (choi_psd N.property).1 hR).right
  have hEh := (ptr_psd hF).1
  have hA := channel_amortized_le N M hR hx0 (psd_of_spectrum_le hEh hx.2)
  have hOA := ordinaryCh_le_amortizedCh_geometric 2 (by norm_num) N M
  have hO0 := ordinaryChannelDivergence_nonneg 2 (by norm_num) hp N M
  have hOtop : ordinaryChannelDivergence (geometricStateDivergence 2) N M ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hOA.trans hA)
  have hObot : ordinaryChannelDivergence (geometricStateDivergence 2) N M ≠ ⊥ :=
    ne_bot_of_le_ne_bot EReal.zero_ne_bot hO0
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ordinaryChannelDivergence (geometricStateDivergence 2) N M = (t : EReal) :=
    ⟨_, (EReal.coe_toReal hOtop hObot).symm⟩
  have htests : EqualTests N M t := by
    intro k hk τ hτ
    rw [← ht]
    exact le_sSup ⟨k, hk, τ, hτ, rfl⟩
  have hb := (cost_bound_of_tests hp N M htests).2
  have hxt : x ≤ (2 : ℝ) ^ t := spectrum_le_of_psd hEh hb x hx.1
  have hlog : log₂ x ≤ t := by
    rw [log₂_eq_logb]
    exact (Real.logb_le_iff_le_rpow (by norm_num) hx0).2 hxt
  have hO : ordinaryChannelDivergence (geometricStateDivergence 2) N M = ((log₂ x : ℝ) : EReal) := by
    apply le_antisymm (hOA.trans hA)
    rw [ht]
    exact_mod_cast hlog
  exact ⟨le_antisymm hA (hO ▸ hOA), hO⟩

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue
