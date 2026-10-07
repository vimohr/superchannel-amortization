import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral

/-!
Critic scratch (amortization problem, e001-i01). What the two spectral ingredients of `geometricStateDivergence` are, stated
without Mathlib's chosen eigenbasis:

* `pinv σ := supportInvSqrt σ * supportInvSqrt σ` satisfies the four Penrose
  equations for positive semidefinite `σ`, and any matrix satisfying them equals
  it (`penrose_unique`). So `supportInvSqrt σ` is a positive semidefinite square
  root of the Moore-Penrose inverse: the inverse square root on the support,
  zero on the kernel. For positive definite `σ` it squares to `σ⁻¹`.
* `hermitianPower X 2 = X * X`, `hermitianPower X 1 = X` on Hermitian `X`.
* Self-normalisation `geometricStateDivergence α ρ ρ = 0` on density matrices.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

theorem psd_spectrum_nonneg {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    ∀ x ∈ spectrum ℝ σ, 0 ≤ x := by
  intro x hx
  rw [hσ.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hσ.eigenvalues_nonneg i

theorem cfc_id_eq {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x) X = X := cfc_id' ℝ X hX

theorem cfc_mul2 (f g : ℝ → ℝ) (X : Matrix n n ℂ) :
    cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (contOn f X) (contOn g X)).symm

theorem cfc_isHermitian (f : ℝ → ℝ) (X : Matrix n n ℂ) : (cfc f X).IsHermitian :=
  cfc_predicate f X

/-- A function that is nonnegative on the spectrum gives a PSD matrix. -/
theorem cfc_posSemidef (f : ℝ → ℝ) (X : Matrix n n ℂ)
    (hf : ∀ x ∈ spectrum ℝ X, 0 ≤ f x) : (cfc f X).PosSemidef := by
  have h1 : cfc f X = cfc (fun x => Real.sqrt (f x) * Real.sqrt (f x)) X := by
    apply cfc_congr
    intro x hx
    exact (Real.mul_self_sqrt (hf x hx)).symm
  rw [h1, ← cfc_mul2]
  have h2 := cfc_isHermitian (fun x => Real.sqrt (f x)) X
  have h3 := Matrix.posSemidef_conjTranspose_mul_self (cfc (fun x => Real.sqrt (f x)) X)
  rwa [h2.eq] at h3

/-- The scalar function is the reciprocal square root with Lean's `0⁻¹ = 0`. -/
theorem supportInvSqrtScalar_eq (x : ℝ) : supportInvSqrtScalar x = (Real.sqrt x)⁻¹ := by
  unfold supportInvSqrtScalar
  split_ifs with h
  · simp [h]
  · rfl

theorem supportInvSqrtScalar_nonneg (x : ℝ) : 0 ≤ supportInvSqrtScalar x := by
  rw [supportInvSqrtScalar_eq]
  exact inv_nonneg.2 (Real.sqrt_nonneg x)

theorem supportInvSqrt_eq_cfc (σ : Matrix n n ℂ) :
    supportInvSqrt σ = cfc supportInvSqrtScalar σ := hsf_eq_cfc _ _

/-- The square of the support inverse square root. -/
noncomputable def pinv (σ : Matrix n n ℂ) : Matrix n n ℂ :=
  supportInvSqrt σ * supportInvSqrt σ

theorem pinv_eq_cfc {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    pinv σ = cfc (fun x : ℝ => x⁻¹) σ := by
  unfold pinv
  rw [supportInvSqrt_eq_cfc, cfc_mul2]
  apply cfc_congr
  intro x hx
  have hx0 := psd_spectrum_nonneg hσ x hx
  simp only [supportInvSqrtScalar_eq]
  rw [← mul_inv, Real.mul_self_sqrt hx0]

theorem supportInvSqrt_posSemidef (σ : Matrix n n ℂ) : (supportInvSqrt σ).PosSemidef := by
  rw [supportInvSqrt_eq_cfc]
  exact cfc_posSemidef _ _ (fun x _ => supportInvSqrtScalar_nonneg x)

theorem penrose1 {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : σ * pinv σ * σ = σ := by
  have hid := cfc_id_eq hσ.1
  calc σ * pinv σ * σ
      = cfc (fun x : ℝ => x) σ * cfc (fun x : ℝ => x⁻¹) σ * cfc (fun x : ℝ => x) σ := by
        rw [hid, pinv_eq_cfc hσ]
    _ = cfc (fun x : ℝ => x * x⁻¹ * x) σ := by rw [cfc_mul2, cfc_mul2]
    _ = cfc (fun x : ℝ => x) σ := by
        apply cfc_congr
        intro x _
        by_cases hx : x = 0
        · simp [hx]
        · simp [hx]
    _ = σ := hid

theorem penrose2 {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : pinv σ * σ * pinv σ = pinv σ := by
  have hid := cfc_id_eq hσ.1
  calc pinv σ * σ * pinv σ
      = cfc (fun x : ℝ => x⁻¹) σ * cfc (fun x : ℝ => x) σ * cfc (fun x : ℝ => x⁻¹) σ := by
        rw [hid, pinv_eq_cfc hσ]
    _ = cfc (fun x : ℝ => x⁻¹ * x * x⁻¹) σ := by rw [cfc_mul2, cfc_mul2]
    _ = cfc (fun x : ℝ => x⁻¹) σ := by
        apply cfc_congr
        intro x _
        by_cases hx : x = 0
        · simp [hx]
        · simp [hx]
    _ = pinv σ := (pinv_eq_cfc hσ).symm

/-- The support projector `σ σ⁺`. -/
theorem mul_pinv_eq_cfc {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    σ * pinv σ = cfc (fun x : ℝ => x * x⁻¹) σ := by
  have hid := cfc_id_eq hσ.1
  calc σ * pinv σ = cfc (fun x : ℝ => x) σ * cfc (fun x : ℝ => x⁻¹) σ := by
        rw [hid, pinv_eq_cfc hσ]
    _ = cfc (fun x : ℝ => x * x⁻¹) σ := by rw [cfc_mul2]

theorem pinv_mul_eq_cfc {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    pinv σ * σ = cfc (fun x : ℝ => x * x⁻¹) σ := by
  have hid := cfc_id_eq hσ.1
  calc pinv σ * σ = cfc (fun x : ℝ => x⁻¹) σ * cfc (fun x : ℝ => x) σ := by
        rw [hid, pinv_eq_cfc hσ]
    _ = cfc (fun x : ℝ => x⁻¹ * x) σ := by rw [cfc_mul2]
    _ = cfc (fun x : ℝ => x * x⁻¹) σ := by
        apply cfc_congr
        intro x _
        exact mul_comm _ _

theorem penrose3 {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : (σ * pinv σ).IsHermitian := by
  rw [mul_pinv_eq_cfc hσ]
  exact cfc_isHermitian _ _

theorem penrose4 {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : (pinv σ * σ).IsHermitian := by
  rw [pinv_mul_eq_cfc hσ]
  exact cfc_isHermitian _ _

/-- Uniqueness of the Moore-Penrose inverse (Penrose 1955), for any square complex matrix. -/
theorem penrose_unique (A B C : Matrix n n ℂ)
    (b1 : A * B * A = A) (b2 : B * A * B = B) (b3 : (A * B).IsHermitian)
    (b4 : (B * A).IsHermitian)
    (c1 : A * C * A = A) (c2 : C * A * C = C) (c3 : (A * C).IsHermitian)
    (c4 : (C * A).IsHermitian) : B = C := by
  have hAB : A * B = A * C := by
    calc A * B = (A * C * A) * B := by rw [c1]
      _ = (A * C) * (A * B) := by simp only [Matrix.mul_assoc]
      _ = (A * C).conjTranspose * (A * B).conjTranspose := by rw [c3.eq, b3.eq]
      _ = ((A * B) * (A * C)).conjTranspose := (Matrix.conjTranspose_mul (A * B) (A * C)).symm
      _ = ((A * B * A) * C).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = (A * C).conjTranspose := by rw [b1]
      _ = A * C := c3.eq
  have hBA : B * A = C * A := by
    calc B * A = B * (A * C * A) := by rw [c1]
      _ = (B * A) * (C * A) := by simp only [Matrix.mul_assoc]
      _ = (B * A).conjTranspose * (C * A).conjTranspose := by rw [c4.eq, b4.eq]
      _ = ((C * A) * (B * A)).conjTranspose := (Matrix.conjTranspose_mul (C * A) (B * A)).symm
      _ = (C * (A * B * A)).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = (C * A).conjTranspose := by rw [b1]
      _ = C * A := c4.eq
  calc B = B * A * B := b2.symm
    _ = B * (A * B) := by rw [Matrix.mul_assoc]
    _ = B * (A * C) := by rw [hAB]
    _ = (B * A) * C := by rw [Matrix.mul_assoc]
    _ = (C * A) * C := by rw [hBA]
    _ = C := c2

/-- Any Moore-Penrose inverse of a PSD `σ` is the square of `supportInvSqrt σ`. -/
theorem pinv_characterisation {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (B : Matrix n n ℂ)
    (b1 : σ * B * σ = σ) (b2 : B * σ * B = B) (b3 : (σ * B).IsHermitian)
    (b4 : (B * σ).IsHermitian) : supportInvSqrt σ * supportInvSqrt σ = B :=
  penrose_unique σ (pinv σ) B (penrose1 hσ) (penrose2 hσ) (penrose3 hσ) (penrose4 hσ)
    b1 b2 b3 b4

theorem posDef_spectrum_pos {σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    ∀ x ∈ spectrum ℝ σ, 0 < x := by
  intro x hx
  rw [hσ.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hσ.eigenvalues_pos i

/-- For positive definite `σ` the square of `supportInvSqrt σ` is the matrix inverse. -/
theorem pinv_eq_inv {σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    supportInvSqrt σ * supportInvSqrt σ = σ⁻¹ := by
  have h1 : σ * pinv σ = 1 := by
    rw [mul_pinv_eq_cfc hσ.posSemidef]
    have : cfc (fun x : ℝ => x * x⁻¹) σ = cfc (fun _ : ℝ => (1 : ℝ)) σ := by
      apply cfc_congr
      intro x hx
      exact mul_inv_cancel₀ (posDef_spectrum_pos hσ x hx).ne'
    rw [this]
    have h := cfc_const (1 : ℝ) σ (ha := hσ.1)
    simpa using h
  exact (Matrix.inv_eq_right_inv h1).symm

theorem hermitianPower_eq_cfc (X : Matrix n n ℂ) (α : ℝ) :
    hermitianPower X α = cfc (fun x : ℝ => x ^ α) X := hsf_eq_cfc _ _

theorem hermitianPower_two {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    hermitianPower X 2 = X * X := by
  have hid := cfc_id_eq hX
  calc hermitianPower X 2 = cfc (fun x : ℝ => x * x) X := by
        rw [hermitianPower_eq_cfc]
        apply cfc_congr
        intro x _
        show x ^ (2 : ℝ) = x * x
        rw [Real.rpow_two]; ring
    _ = cfc (fun x : ℝ => x) X * cfc (fun x : ℝ => x) X := by rw [cfc_mul2]
    _ = X * X := by rw [hid]

theorem hermitianPower_one {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    hermitianPower X 1 = X := by
  have hid := cfc_id_eq hX
  calc hermitianPower X 1 = cfc (fun x : ℝ => x) X := by
        rw [hermitianPower_eq_cfc]
        apply cfc_congr
        intro x _
        show x ^ (1 : ℝ) = x
        rw [Real.rpow_one]
    _ = X := hid

/-- The support sandwich of a PSD matrix with itself is its support projector. -/
theorem sandwich_self {τ : Matrix n n ℂ} (hτ : τ.PosSemidef) :
    supportInvSqrt τ * τ * supportInvSqrt τ = cfc (fun x : ℝ => x * x⁻¹) τ := by
  have hid := cfc_id_eq hτ.1
  calc supportInvSqrt τ * τ * supportInvSqrt τ
      = cfc supportInvSqrtScalar τ * cfc (fun x : ℝ => x) τ * cfc supportInvSqrtScalar τ := by
        rw [hid, supportInvSqrt_eq_cfc]
    _ = cfc (fun x : ℝ => supportInvSqrtScalar x * x * supportInvSqrtScalar x) τ := by
        rw [cfc_mul2, cfc_mul2]
    _ = cfc (fun x : ℝ => x * x⁻¹) τ := by
        apply cfc_congr
        intro x hx
        have hx0 := psd_spectrum_nonneg hτ x hx
        simp only [supportInvSqrtScalar_eq]
        calc (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹
            = x * ((Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹) := by ring
          _ = x * x⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hx0]

/-- Self-normalisation at the level of the moment, for every nonzero order. -/
theorem geometricMoment_self {τ : Matrix n n ℂ} (hτ : τ.PosSemidef) (α : ℝ) (hα : α ≠ 0) :
    geometricMoment α τ τ = (Matrix.trace τ).re := by
  have hid := cfc_id_eq hτ.1
  have hP : hermitianPower (supportInvSqrt τ * τ * supportInvSqrt τ) α =
      cfc (fun x : ℝ => x * x⁻¹) τ := by
    rw [sandwich_self hτ, hermitianPower_eq_cfc]
    have hg : ContinuousOn (fun x : ℝ => x ^ α)
        ((fun x : ℝ => x * x⁻¹) '' spectrum ℝ τ) := by
      rw [← cfc_map_spectrum (fun x : ℝ => x * x⁻¹) τ hτ.1 (contOn _ _)]
      exact contOn _ _
    have hc := cfc_comp (fun x : ℝ => x ^ α) (fun x : ℝ => x * x⁻¹) τ hτ.1 hg (contOn _ _)
    rw [← hc]
    apply cfc_congr
    intro x _
    show (x * x⁻¹) ^ α = x * x⁻¹
    by_cases hx : x = 0
    · simp [hx, Real.zero_rpow hα]
    · simp [hx]
  have hprod : τ * cfc (fun x : ℝ => x * x⁻¹) τ = τ := by
    calc τ * cfc (fun x : ℝ => x * x⁻¹) τ
        = cfc (fun x : ℝ => x) τ * cfc (fun x : ℝ => x * x⁻¹) τ := by rw [hid]
      _ = cfc (fun x : ℝ => x * (x * x⁻¹)) τ := by rw [cfc_mul2]
      _ = cfc (fun x : ℝ => x) τ := by
          apply cfc_congr
          intro x _
          by_cases hx : x = 0
          · simp [hx]
          · simp [hx]
      _ = τ := hid
  unfold geometricMoment
  rw [hP, hprod]

/-- Self-normalisation of the state divergence on density matrices. -/
theorem geometricStateDivergence_self {τ : Matrix n n ℂ} (hτ : OpenQ.IsDensityMatrix τ)
    (α : ℝ) (hα : α ≠ 0) : geometricStateDivergence α n τ τ = 0 := by
  have hR : RangeIncluded τ τ := subset_rfl
  have hm : geometricMoment α τ τ = 1 := by
    rw [geometricMoment_self hτ.1 α hα, hτ.2]; rfl
  simp only [geometricStateDivergence, eq_true hR, ↓reduceIte, hm, log₂, Real.log_one, zero_div]
  rfl

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
