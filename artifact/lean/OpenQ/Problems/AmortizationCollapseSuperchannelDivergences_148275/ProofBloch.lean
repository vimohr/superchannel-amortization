import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofQubitMoment

/-!
# Portable proof: qubit density matrices in Bloch form

* `blochMat n = (1 + n·σ)/2` for `n : Fin 3 → ℝ`; trace one, Hermitian,
  `det = (1 - |n|²)/4`, positive semidefinite iff `|n|² ≤ 1` (one direction and
  `density_eq_blochMat` for the other), positive definite if `|n|² < 1`.
* `moment_bloch`: the locked order-3/2 moment of a Bloch pair with `|s|² < 1`,
  `|m|² ≤ 1` equals `G m s = (T + q - q²)/√(T + 2q)` with
  `T = 2 (1 - m·s)/(1 - |s|²)`, `q² = (1 - |m|²)/(1 - |s|²)`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofBloch

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofQubitMoment
open scoped ComplexOrder

/-- Euclidean inner product on `ℝ³`, written out. -/
def dot (m s : Fin 3 → ℝ) : ℝ := m 0 * s 0 + m 1 * s 1 + m 2 * s 2

/-- The Hermitian trace-one matrix with Bloch vector `n`. -/
noncomputable def blochMat (n : Fin 3 → ℝ) : M2 :=
  !![(((1 + n 2) / 2 : ℝ) : ℂ), ((n 0 / 2 : ℝ) : ℂ) - ((n 1 / 2 : ℝ) : ℂ) * Complex.I;
     ((n 0 / 2 : ℝ) : ℂ) + ((n 1 / 2 : ℝ) : ℂ) * Complex.I, (((1 - n 2) / 2 : ℝ) : ℂ)]

theorem blochMat_isHermitian (n : Fin 3 → ℝ) : (blochMat n).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochMat, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem blochMat_trace (n : Fin 3 → ℝ) : Matrix.trace (blochMat n) = 1 := by
  simp only [blochMat, Matrix.trace_fin_two_of]
  apply Complex.ext <;> simp <;> ring

theorem blochMat_det (n : Fin 3 → ℝ) :
    Matrix.det (blochMat n) = (((1 - dot n n) / 4 : ℝ) : ℂ) := by
  simp only [blochMat, Matrix.det_fin_two_of, dot]
  apply Complex.ext <;> simp <;> ring

theorem trace_adjugate_mul (m s : Fin 3 → ℝ) :
    Matrix.trace (Matrix.adjugate (blochMat s) * blochMat m) = (((1 - dot m s) / 2 : ℝ) : ℂ) := by
  simp only [blochMat, Matrix.adjugate_fin_two_of, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, dot]
  apply Complex.ext <;> simp <;> ring

theorem blochMat_posSemidef {n : Fin 3 → ℝ} (h : dot n n ≤ 1) : (blochMat n).PosSemidef := by
  apply posSemidef_of_trace_det (blochMat_isHermitian n)
  · rw [blochMat_trace]; simp
  · rw [blochMat_det, Complex.ofReal_re]; linarith

theorem blochMat_posDef {n : Fin 3 → ℝ} (h : dot n n < 1) : (blochMat n).PosDef := by
  apply posDef_of_trace_det (blochMat_isHermitian n)
  · rw [blochMat_trace]; simp
  · rw [blochMat_det, Complex.ofReal_re]; linarith

theorem blochMat_density {n : Fin 3 → ℝ} (h : dot n n ≤ 1) :
    OpenQ.IsDensityMatrix (blochMat n) :=
  ⟨blochMat_posSemidef h, blochMat_trace n⟩

/-- Bloch matrices are affine in the Bloch vector. -/
theorem blochMat_mix (θ : ℝ) (m m' : Fin 3 → ℝ) :
    blochMat ((1 - θ) • m + θ • m') =
      ((1 - θ : ℝ) : ℂ) • blochMat m + ((θ : ℝ) : ℂ) • blochMat m' := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMat] <;> ring

/-- Every 2-by-2 density matrix is a Bloch matrix with a vector in the closed unit ball. -/
theorem density_eq_blochMat {κ : M2} (hκ : OpenQ.IsDensityMatrix κ) :
    ∃ n : Fin 3 → ℝ, dot n n ≤ 1 ∧ κ = blochMat n := by
  obtain ⟨hpsd, htr⟩ := hκ
  have hH := hpsd.1
  have h00 : (κ 0 0).im = 0 := by
    have := hH.apply 0 0
    have h2 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  have h11 : (κ 1 1).im = 0 := by
    have := hH.apply 1 1
    have h2 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  have h01 : κ 0 1 = star (κ 1 0) := (hH.apply 0 1).symm
  rw [Matrix.trace_fin_two] at htr
  have htr_re : (κ 0 0).re + (κ 1 1).re = 1 := by
    have := congrArg Complex.re htr
    simpa using this
  let n : Fin 3 → ℝ := ![2 * (κ 1 0).re, 2 * (κ 1 0).im, (κ 0 0).re - (κ 1 1).re]
  have hκ : κ = blochMat n := by
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext
      · simp [blochMat, n]; linarith
      · simp [blochMat, n, h00]
    · show κ 0 1 = _
      rw [h01]
      apply Complex.ext <;> simp [blochMat, n]
    · apply Complex.ext <;> simp [blochMat, n]
    · apply Complex.ext
      · simp [blochMat, n]; linarith
      · simp [blochMat, n, h11]
  refine ⟨n, ?_, hκ⟩
  have hd := det_re_nonneg hpsd
  rw [hκ, blochMat_det, Complex.ofReal_re] at hd
  linarith

/-- Cauchy-Schwarz in the form needed: the denominator of `T` is positive. -/
theorem dot_lt_one {m s : Fin 3 → ℝ} (hm : dot m m ≤ 1) (hs : dot s s < 1) : dot m s < 1 := by
  unfold dot at *
  nlinarith [sq_nonneg (m 0 - s 0), sq_nonneg (m 1 - s 1), sq_nonneg (m 2 - s 2)]

/-- The closed form of the moment as a function of the two Bloch vectors. -/
noncomputable def G (m s : Fin 3 → ℝ) : ℝ :=
  (2 * (1 - dot m s) / (1 - dot s s) + Real.sqrt ((1 - dot m m) / (1 - dot s s))
      - (1 - dot m m) / (1 - dot s s))
    / Real.sqrt (2 * (1 - dot m s) / (1 - dot s s)
      + 2 * Real.sqrt ((1 - dot m m) / (1 - dot s s)))

/-- The locked order-3/2 moment of a Bloch pair with positive definite reference. -/
theorem moment_bloch {m s : Fin 3 → ℝ} (hm : dot m m ≤ 1) (hs : dot s s < 1) :
    geometricMoment (3 / 2) (blochMat m) (blochMat s) = G m s := by
  have hσ := blochMat_posDef hs
  have hρ := blochMat_posSemidef hm
  have hss : 0 < 1 - dot s s := by linarith
  have hms : 0 < 1 - dot m s := by linarith [dot_lt_one hm hs]
  have hmm : 0 ≤ 1 - dot m m := by linarith
  have hdetne : (((1 - dot s s) / 4 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : ((1 - dot s s) / 4 : ℝ) ≠ 0)
  have hT : (Matrix.trace ((blochMat s)⁻¹ * blochMat m)).re = 2 * (1 - dot m s) / (1 - dot s s) := by
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, trace_adjugate_mul, blochMat_det,
      Ring.inverse_eq_inv', smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    field_simp
    ring
  have hq : ((Matrix.det (blochMat s))⁻¹ * Matrix.det (blochMat m)).re
      = (1 - dot m m) / (1 - dot s s) := by
    rw [blochMat_det, blochMat_det, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp
  have hq0 : 0 ≤ Real.sqrt ((1 - dot m m) / (1 - dot s s)) := Real.sqrt_nonneg _
  have hTpos : 0 < 2 * (1 - dot m s) / (1 - dot s s) := by positivity
  rw [geometricMoment_closed hρ hσ (2 * (1 - dot m s) / (1 - dot s s))
    (Real.sqrt ((1 - dot m m) / (1 - dot s s))) hT.symm (by rw [hq]) (by linarith)]
  rw [blochMat_trace, blochMat_trace, Real.sq_sqrt (by positivity)]
  simp only [Complex.one_re, mul_one]
  rfl

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofBloch
