import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Portable proof: the order-3/2 moment of a qubit pair in closed form

Everything is stated for the locked
`geometricMoment` of `Statement.lean`.

* `hermitianPower_three_halves`: for a positive semidefinite 2-by-2 matrix `X`
  with `T = tr X`, `q = √(det X)` and `T + 2q > 0`,
  `X^(3/2) = ((T + q) X - q² 1)/√(T + 2q)` (Eq. (14) of the proof note).
* `geometricMoment_closed`: for positive definite `σ` and positive semidefinite
  `ρ` (2-by-2), `M = ((T + q) tr ρ - q² tr σ)/√(T + 2q)` with
  `T = tr(σ⁻¹ ρ)`, `q = √(det ρ / det σ)`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofQubitMoment

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open scoped ComplexOrder

section general

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Functional calculus of an affine function. -/
theorem cfc_affine (α β : ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => α * x + β) X = (α : ℂ) • X + (β : ℂ) • (1 : Matrix n n ℂ) := by
  have hsa : IsSelfAdjoint X := hX
  have h1 := cfc_add (a := X) (fun x : ℝ => α * x) (fun _ : ℝ => β) (contOn _ _) (contOn _ _)
  have h2 := cfc_const_mul α (fun x : ℝ => x) X (contOn _ _)
  have h3 := cfc_const β X hsa
  rw [h1, h2, cfc_id_eq hX, h3, Algebra.algebraMap_eq_smul_one]
  rfl

/-- For positive definite `σ` the support sandwich of `σ` with itself is the identity. -/
theorem sandwich_self_posDef {σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    supportInvSqrt σ * σ * supportInvSqrt σ = 1 := by
  rw [sandwich_self hσ.posSemidef]
  have : cfc (fun x : ℝ => x * x⁻¹) σ = cfc (fun _ : ℝ => (1 : ℝ)) σ := by
    apply cfc_congr
    intro x hx
    exact mul_inv_cancel₀ (posDef_spectrum_pos hσ x hx).ne'
  rw [this]
  have h := cfc_const (1 : ℝ) σ (ha := hσ.1)
  simpa using h

/-- Trace of the sandwich against the reference, positive definite reference. -/
theorem trace_mul_sandwich {ρ σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    Matrix.trace (σ * (supportInvSqrt σ * ρ * supportInvSqrt σ)) = Matrix.trace ρ := by
  have h1 : σ * (supportInvSqrt σ * ρ * supportInvSqrt σ)
      = (σ * supportInvSqrt σ * ρ) * supportInvSqrt σ := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : supportInvSqrt σ * (σ * supportInvSqrt σ * ρ)
      = (supportInvSqrt σ * σ * supportInvSqrt σ) * ρ := by
    simp only [Matrix.mul_assoc]
  rw [h2, sandwich_self_posDef hσ, Matrix.one_mul]

theorem trace_sandwich {ρ σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    Matrix.trace (supportInvSqrt σ * ρ * supportInvSqrt σ) = Matrix.trace (σ⁻¹ * ρ) := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, pinv_eq_inv hσ]

theorem det_sandwich {ρ σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    Matrix.det (supportInvSqrt σ * ρ * supportInvSqrt σ) = (Matrix.det σ)⁻¹ * Matrix.det ρ := by
  rw [Matrix.det_mul, Matrix.det_mul]
  have h : Matrix.det (supportInvSqrt σ) * Matrix.det (supportInvSqrt σ) = (Matrix.det σ)⁻¹ := by
    rw [← Matrix.det_mul, pinv_eq_inv hσ, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [← h]
  ring

end general

section qubit

/-- Scalar identity behind `X^(3/2)` on a root of `x² - T x + q²`. -/
theorem rpow_three_halves_of_quadratic {x T q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (hT : 0 < T + 2 * q) (h : x ^ 2 - T * x + q ^ 2 = 0) :
    x ^ (3 / 2 : ℝ) = (Real.sqrt (T + 2 * q))⁻¹ * (T + q) * x
      + -((Real.sqrt (T + 2 * q))⁻¹ * q ^ 2) := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = Real.sqrt (T + 2 * q) := ⟨_, rfl⟩
  rw [← hwdef]
  have hw : 0 < w := by rw [hwdef]; exact Real.sqrt_pos.2 hT
  have hw2 : w ^ 2 = T + 2 * q := by rw [hwdef]; exact Real.sq_sqrt hT.le
  have hs : Real.sqrt x = (x + q) / w := by
    have h0 : 0 ≤ (x + q) / w := by positivity
    have h1 : (x + q) / w * ((x + q) / w) = x := by
      field_simp
      nlinarith
    calc Real.sqrt x = Real.sqrt ((x + q) / w * ((x + q) / w)) := by rw [h1]
      _ = (x + q) / w := Real.sqrt_mul_self h0
  have h32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx (by norm_num), Real.rpow_one]
  rw [h32, hs]
  field_simp
  nlinarith

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

theorem trace_det_eigen {X : M2} (hX : X.IsHermitian) :
    X.trace = ((hX.eigenvalues 0 + hX.eigenvalues 1 : ℝ) : ℂ) ∧
      X.det = ((hX.eigenvalues 0 * hX.eigenvalues 1 : ℝ) : ℂ) := by
  constructor
  · rw [hX.trace_eq_sum_eigenvalues, Fin.sum_univ_two]
    push_cast
    rfl
  · rw [hX.det_eq_prod_eigenvalues, Fin.prod_univ_two]
    push_cast
    rfl

/-- Every point of the spectrum of a Hermitian 2-by-2 matrix is a root of
`x² - (tr X) x + det X`. -/
theorem spectrum_quadratic {X : M2} (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) :
    x ^ 2 - (X.trace).re * x + (X.det).re = 0 := by
  rw [hX.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨ht, hd⟩ := trace_det_eigen hX
  rw [ht, hd, Complex.ofReal_re, Complex.ofReal_re]
  fin_cases i
  · show hX.eigenvalues 0 ^ 2 - _ * hX.eigenvalues 0 + _ = 0
    ring
  · show hX.eigenvalues 1 ^ 2 - _ * hX.eigenvalues 1 + _ = 0
    ring

/-- A Hermitian 2-by-2 matrix with nonnegative trace and determinant is PSD. -/
theorem posSemidef_of_trace_det {X : M2} (hX : X.IsHermitian) (ht : 0 ≤ (X.trace).re)
    (hd : 0 ≤ (X.det).re) : X.PosSemidef := by
  rw [hX.posSemidef_iff_eigenvalues_nonneg]
  obtain ⟨ht', hd'⟩ := trace_det_eigen hX
  rw [ht', Complex.ofReal_re] at ht
  rw [hd', Complex.ofReal_re] at hd
  intro i
  fin_cases i
  · show 0 ≤ hX.eigenvalues 0
    by_contra hcon
    push Not at hcon
    nlinarith
  · show 0 ≤ hX.eigenvalues 1
    by_contra hcon
    push Not at hcon
    nlinarith

/-- A Hermitian 2-by-2 matrix with nonnegative trace and positive determinant is PD. -/
theorem posDef_of_trace_det {X : M2} (hX : X.IsHermitian) (ht : 0 ≤ (X.trace).re)
    (hd : 0 < (X.det).re) : X.PosDef := by
  rw [hX.posDef_iff_eigenvalues_pos]
  obtain ⟨ht', hd'⟩ := trace_det_eigen hX
  rw [ht', Complex.ofReal_re] at ht
  rw [hd', Complex.ofReal_re] at hd
  intro i
  fin_cases i
  · show 0 < hX.eigenvalues 0
    by_contra hcon
    push Not at hcon
    nlinarith
  · show 0 < hX.eigenvalues 1
    by_contra hcon
    push Not at hcon
    nlinarith

theorem det_re_nonneg {X : M2} (hX : X.PosSemidef) : 0 ≤ (X.det).re := by
  obtain ⟨_, hd⟩ := trace_det_eigen hX.1
  rw [hd, Complex.ofReal_re]
  exact mul_nonneg (hX.eigenvalues_nonneg 0) (hX.eigenvalues_nonneg 1)

theorem trace_re_nonneg {X : M2} (hX : X.PosSemidef) : 0 ≤ (X.trace).re := by
  obtain ⟨ht, _⟩ := trace_det_eigen hX.1
  rw [ht, Complex.ofReal_re]
  exact add_nonneg (hX.eigenvalues_nonneg 0) (hX.eigenvalues_nonneg 1)

/-- Eq. (14) of the proof note on the locked `hermitianPower`. -/
theorem hermitianPower_three_halves {X : M2} (hX : X.PosSemidef)
    (hT : 0 < (X.trace).re + 2 * Real.sqrt (X.det).re) :
    hermitianPower X (3 / 2) =
      (((Real.sqrt ((X.trace).re + 2 * Real.sqrt (X.det).re))⁻¹
          * ((X.trace).re + Real.sqrt (X.det).re) : ℝ) : ℂ) • X
        + ((-((Real.sqrt ((X.trace).re + 2 * Real.sqrt (X.det).re))⁻¹
          * Real.sqrt (X.det).re ^ 2) : ℝ) : ℂ) • (1 : M2) := by
  rw [hermitianPower_eq_cfc, ← cfc_affine _ _ hX.1]
  apply cfc_congr
  intro x hx
  have hx0 := psd_spectrum_nonneg hX x hx
  have hquad := spectrum_quadratic hX.1 hx
  have hq2 : Real.sqrt (X.det).re ^ 2 = (X.det).re := Real.sq_sqrt (det_re_nonneg hX)
  exact rpow_three_halves_of_quadratic hx0 (Real.sqrt_nonneg _) hT (by rw [hq2]; exact hquad)

/-- Closed form of the locked order-3/2 moment for a positive definite 2-by-2
reference and a positive semidefinite numerator. -/
theorem geometricMoment_closed {ρ σ : M2} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (T q : ℝ) (hTdef : T = (Matrix.trace (σ⁻¹ * ρ)).re)
    (hqdef : q = Real.sqrt ((Matrix.det σ)⁻¹ * Matrix.det ρ).re) (hT : 0 < T + 2 * q) :
    geometricMoment (3 / 2) ρ σ =
      ((T + q) * (Matrix.trace ρ).re - q ^ 2 * (Matrix.trace σ).re) / Real.sqrt (T + 2 * q) := by
  have hX := support_sandwich_posSemidef ρ σ hρ
  have htr := trace_sandwich (ρ := ρ) hσ
  have hdet := det_sandwich (ρ := ρ) hσ
  have hT' : 0 < (Matrix.trace (supportInvSqrt σ * ρ * supportInvSqrt σ)).re
      + 2 * Real.sqrt (Matrix.det (supportInvSqrt σ * ρ * supportInvSqrt σ)).re := by
    rw [htr, hdet, ← hTdef, ← hqdef]; exact hT
  unfold geometricMoment
  rw [hermitianPower_three_halves hX hT', htr, hdet, ← hTdef, ← hqdef]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, trace_mul_sandwich hσ]
  simp only [smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
  have hw : 0 < Real.sqrt (T + 2 * q) := Real.sqrt_pos.2 hT
  field_simp
  ring

end qubit

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofQubitMoment
