import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofLiteral
import Mathlib.Analysis.MeanInequalitiesPow

/-!
Critic scratch (amortization problem, e001-i01). Junk-value exclusion for the logarithm in `geometricStateDivergence`: on every
supported pair of density matrices and every order `α ≥ 1` the geometric moment
is at least one (Jensen's inequality in the eigenbasis of the sandwich), so
`Real.log` is only evaluated at positive reals and the divergence is nonnegative.
Consequently the ordinary channel and superchannel quantities take values in
`[0, +∞]`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

theorem one_le_geometricMoment {ρ σ : Matrix n n ℂ} (hρ : OpenQ.IsDensityMatrix ρ)
    (hσ : OpenQ.IsDensityMatrix σ) (hR : RangeIncluded ρ σ) (α : ℝ) (hα : 1 ≤ α) :
    1 ≤ geometricMoment α ρ σ := by
  have hX0 : (supportInvSqrt σ * ρ * supportInvSqrt σ).PosSemidef :=
    support_sandwich_posSemidef ρ σ hρ.1
  obtain ⟨X, hXdef⟩ : ∃ X, X = supportInvSqrt σ * ρ * supportInvSqrt σ := ⟨_, rfl⟩
  have hX : X.PosSemidef := by rw [hXdef]; exact hX0
  have hXh := hX.1
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix n n ℂ, U = (hXh.eigenvectorUnitary : Matrix n n ℂ) :=
    ⟨_, rfl⟩
  have hU1 : U.conjTranspose * U = 1 := by
    rw [hUdef]; exact Unitary.coe_star_mul_self _
  have hU2 : U * U.conjTranspose = 1 := by
    rw [hUdef]; exact Unitary.coe_mul_star_self _
  have hspec : X = U * Matrix.diagonal (fun k => ((hXh.eigenvalues k : ℝ) : ℂ)) *
      U.conjTranspose := by
    have h := hXh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef]
    exact h
  have hpow : hermitianPower X α =
      U * Matrix.diagonal (fun k => (((hXh.eigenvalues k) ^ α : ℝ) : ℂ)) *
        U.conjTranspose := by
    unfold hermitianPower
    conv_lhs => rw [hspec]
    exact hsf_spectral_form _ U hXh.eigenvalues hU1 hU2
  -- trace against a function of `X`
  have htrace : ∀ d : n → ℝ,
      Matrix.trace (σ * (U * Matrix.diagonal (fun k => ((d k : ℝ) : ℂ)) * U.conjTranspose)) =
        ∑ i, ((d i : ℝ) : ℂ) * (U.conjTranspose * σ * U) i i := by
    intro d
    have e : σ * (U * Matrix.diagonal (fun k => ((d k : ℝ) : ℂ)) * U.conjTranspose) =
        (σ * U * Matrix.diagonal (fun k => ((d k : ℝ) : ℂ))) * U.conjTranspose := by
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    have e2 : U.conjTranspose * (σ * U * Matrix.diagonal (fun k => ((d k : ℝ) : ℂ))) =
        (U.conjTranspose * σ * U) * Matrix.diagonal (fun k => ((d k : ℝ) : ℂ)) := by
      simp only [Matrix.mul_assoc]
    rw [e2]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  -- the weights
  have hWpsd : (U.conjTranspose * σ * U).PosSemidef := hσ.1.conjTranspose_mul_mul_same U
  have hwre : ∀ i, (U.conjTranspose * σ * U) i i =
      ((((U.conjTranspose * σ * U) i i).re : ℝ) : ℂ) := by
    intro i
    have h := Complex.nonneg_iff.1 (hWpsd.diag_nonneg (i := i))
    apply Complex.ext
    · simp
    · simp [← h.2]
  have hw0 : ∀ i, 0 ≤ ((U.conjTranspose * σ * U) i i).re :=
    fun i => (Complex.nonneg_iff.1 (hWpsd.diag_nonneg (i := i))).1
  have hwsum : ∑ i, ((U.conjTranspose * σ * U) i i).re = 1 := by
    have h1 : Matrix.trace (U.conjTranspose * σ * U) = 1 := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU2, Matrix.mul_one]
      exact hσ.2
    have h2 := congrArg Complex.re h1
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.one_re] at h2
    exact h2
  -- first moment
  have hfirst : ∑ i, ((U.conjTranspose * σ * U) i i).re * hXh.eigenvalues i = 1 := by
    have h1 : Matrix.trace (σ * X) = 1 := by
      rw [hXdef]
      have e : σ * (supportInvSqrt σ * ρ * supportInvSqrt σ) =
          (σ * supportInvSqrt σ * ρ) * supportInvSqrt σ := by
        simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm]
      have e2 : supportInvSqrt σ * (σ * supportInvSqrt σ * ρ) =
          (supportInvSqrt σ * σ * supportInvSqrt σ) * ρ := by
        simp only [Matrix.mul_assoc]
      rw [e2, sandwich_eq_supp hσ.1, supp_mul_of_rangeIncluded hσ.1 hR]
      exact hρ.2
    have h2 : Matrix.trace (σ * X) =
        ∑ i, ((hXh.eigenvalues i : ℝ) : ℂ) * (U.conjTranspose * σ * U) i i := by
      conv_lhs => rw [hspec]
      exact htrace hXh.eigenvalues
    have h3 := congrArg Complex.re (h2.symm.trans h1)
    rw [Complex.re_sum, Complex.one_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.re_ofReal_mul]
    ring
  -- the moment as a weighted power sum
  have hmoment : geometricMoment α ρ σ =
      ∑ i, ((U.conjTranspose * σ * U) i i).re * (hXh.eigenvalues i) ^ α := by
    unfold geometricMoment
    rw [← hXdef, hpow, htrace (fun k => (hXh.eigenvalues k) ^ α), Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.re_ofReal_mul]
    ring
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun i => ((U.conjTranspose * σ * U) i i).re) hXh.eigenvalues
    (fun i _ => hw0 i) hwsum (fun i _ => hX.eigenvalues_nonneg i) hα
  rw [hfirst, Real.one_rpow] at hJ
  rw [hmoment]
  exact hJ

/-- The state divergence is nonnegative on density matrices for orders above one. -/
theorem geometricStateDivergence_nonneg {ρ σ : Matrix n n ℂ} (hρ : OpenQ.IsDensityMatrix ρ)
    (hσ : OpenQ.IsDensityMatrix σ) (α : ℝ) (hα : 1 < α) :
    0 ≤ geometricStateDivergence α n ρ σ := by
  unfold geometricStateDivergence
  by_cases hR : RangeIncluded ρ σ
  · simp only [eq_true hR, ↓reduceIte]
    have h1 := one_le_geometricMoment hρ hσ hR α hα.le
    have h2 : 0 ≤ log₂ (geometricMoment α ρ σ) / (α - 1) := by
      apply div_nonneg
      · unfold log₂
        exact div_nonneg (Real.log_nonneg h1) (Real.log_nonneg (by norm_num))
      · linarith
    exact_mod_cast h2
  · simp only [eq_false hR, ↓reduceIte]
    exact le_top

/-- The ordinary channel divergence is nonnegative (for a nonzero input dimension). -/
theorem ordinaryChannelDivergence_nonneg (α : ℝ) (hα : 1 < α) {a b : ℕ} (ha : 1 ≤ a)
    (N M : Channel a b) : 0 ≤ ordinaryChannelDivergence (geometricStateDivergence α) N M := by
  obtain ⟨τ, hτ⟩ := OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofLiteral.exists_state ha
  unfold ordinaryChannelDivergence
  refine le_trans ?_ (le_sSup ⟨1, Nat.one_pos, τ, hτ, rfl⟩)
  exact geometricStateDivergence_nonneg (amplification_isDensityMatrix N Nat.one_pos τ hτ)
    (amplification_isDensityMatrix M Nat.one_pos τ hτ) α hα

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
