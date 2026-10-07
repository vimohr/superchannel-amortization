import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Matrix.Order

/-!
# Portable proof: orthogonal additivity of the locked moment

On a finite spectrum a real function is a polynomial (Lagrange interpolation),
so the locked `hermitianSpectralFunction f` of Hermitian matrices `A`, `B`
with `A * B = 0` is additive when `f 0 = 0`, and annihilators of `A` annihilate
`f(A)`. Consequences for the locked `geometricMoment`:

* `moment_add_orth`: `M(A₁ + A₂, B₁ + B₂) = M(A₁, B₁) + M(A₂, B₂)` when the two
  pairs live on orthogonal supports;
* `moment_zero_left`, `moment_nonneg`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofOrthogonal

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open scoped ComplexOrder
open Polynomial

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Polynomial form of the spectral function -/

theorem hsf_eq_aeval (f : ℝ → ℝ) (S : Finset ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hS : ∀ x ∈ spectrum ℝ A, x ∈ S) :
    hermitianSpectralFunction f A = aeval A (Lagrange.interpolate S id f) := by
  have hsa : IsSelfAdjoint A := hA
  rw [hsf_eq_cfc, ← cfc_polynomial (Lagrange.interpolate S id f) A hsa]
  apply cfc_congr
  intro x hx
  exact (Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) (hS x hx)).symm

theorem interpolate_coeff_zero (f : ℝ → ℝ) (hf : f 0 = 0) (S : Finset ℝ) (h0 : (0 : ℝ) ∈ S) :
    (Lagrange.interpolate S id f).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  have := Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) h0
  simpa [hf] using this

/-- The finite node set of a Hermitian matrix. -/
noncomputable def nodes {A : Matrix n n ℂ} (hA : A.IsHermitian) : Finset ℝ :=
  Finset.univ.image hA.eigenvalues

theorem mem_nodes {A : Matrix n n ℂ} (hA : A.IsHermitian) : ∀ x ∈ spectrum ℝ A, x ∈ nodes hA := by
  intro x hx
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- A common polynomial for three Hermitian matrices, without constant term. -/
theorem exists_poly3 (f : ℝ → ℝ) (hf : f 0 = 0) {A B C : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    ∃ p : ℝ[X], p.coeff 0 = 0 ∧ hermitianSpectralFunction f A = aeval A p ∧
      hermitianSpectralFunction f B = aeval B p ∧ hermitianSpectralFunction f C = aeval C p := by
  refine ⟨Lagrange.interpolate (nodes hA ∪ nodes hB ∪ nodes hC ∪ {0}) id f, ?_, ?_, ?_, ?_⟩
  · exact interpolate_coeff_zero f hf _ (by simp)
  · exact hsf_eq_aeval f _ hA (fun x hx => by
      simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (mem_nodes hA x hx))))
  · exact hsf_eq_aeval f _ hB (fun x hx => by
      simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (mem_nodes hB x hx))))
  · exact hsf_eq_aeval f _ hC (fun x hx => by
      simp only [Finset.mem_union]; exact Or.inl (Or.inr (mem_nodes hC x hx)))

theorem exists_poly1 (f : ℝ → ℝ) (hf : f 0 = 0) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ p : ℝ[X], p.coeff 0 = 0 ∧ hermitianSpectralFunction f A = aeval A p := by
  obtain ⟨p, h0, h1, -, -⟩ := exists_poly3 f hf hA hA hA
  exact ⟨p, h0, h1⟩

/-! ### Orthogonal pairs -/

theorem add_pow_orth {A B : Matrix n n ℂ} (h1 : A * B = 0) (h2 : B * A = 0) (k : ℕ) :
    (A + B) ^ (k + 1) = A ^ (k + 1) + B ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : A ^ (k + 1) * B = 0 := by rw [pow_succ, mul_assoc, h1, mul_zero]
    have e2 : B ^ (k + 1) * A = 0 := by rw [pow_succ, mul_assoc, h2, mul_zero]
    rw [pow_succ, ih, add_mul, mul_add, mul_add, e1, e2, add_zero, zero_add, ← pow_succ,
      ← pow_succ]

theorem aeval_add_orth {A B : Matrix n n ℂ} (h1 : A * B = 0) (h2 : B * A = 0) (p : ℝ[X])
    (hp : p.coeff 0 = 0) : aeval (A + B) p = aeval A p + aeval B p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hp]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [add_pow_orth h1 h2, smul_add]

theorem mul_aeval_eq_zero {Z A : Matrix n n ℂ} (h : Z * A = 0) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    Z * aeval A p = 0 := by
  rw [aeval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hp]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [Matrix.mul_smul, pow_succ', ← mul_assoc, h, zero_mul, smul_zero]

theorem aeval_mul_eq_zero {Z A : Matrix n n ℂ} (h : A * Z = 0) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    aeval A p * Z = 0 := by
  rw [aeval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hp]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [Matrix.smul_mul, pow_succ, mul_assoc, h, mul_zero, smul_zero]

theorem mul_comm_zero {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A * B = 0) : B * A = 0 := by
  have := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.conjTranspose_zero] at this

/-- Additivity of the locked spectral function on orthogonal Hermitian pairs. -/
theorem hsf_add_orth (f : ℝ → ℝ) (hf : f 0 = 0) {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A * B = 0) :
    hermitianSpectralFunction f (A + B)
      = hermitianSpectralFunction f A + hermitianSpectralFunction f B := by
  obtain ⟨p, h0, h1, h2, h3⟩ := exists_poly3 f hf hA hB (hA.add hB)
  rw [h1, h2, h3, aeval_add_orth h (mul_comm_zero hA hB h) p h0]

theorem mul_hsf_eq_zero (f : ℝ → ℝ) (hf : f 0 = 0) {Z A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : Z * A = 0) : Z * hermitianSpectralFunction f A = 0 := by
  obtain ⟨p, h0, h1⟩ := exists_poly1 f hf hA
  rw [h1, mul_aeval_eq_zero h p h0]

theorem hsf_mul_eq_zero (f : ℝ → ℝ) (hf : f 0 = 0) {Z A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : A * Z = 0) : hermitianSpectralFunction f A * Z = 0 := by
  obtain ⟨p, h0, h1⟩ := exists_poly1 f hf hA
  rw [h1, aeval_mul_eq_zero h p h0]

theorem hsf_zero (f : ℝ → ℝ) (hf : f 0 = 0) :
    hermitianSpectralFunction f (0 : Matrix n n ℂ) = 0 := by
  have h := mul_hsf_eq_zero f hf (Z := (1 : Matrix n n ℂ)) (A := 0) Matrix.isHermitian_zero
    (by simp)
  simpa using h

/-! ### The locked moment -/

theorem sandwich_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n n ℂ) :
    (supportInvSqrt B * A * supportInvSqrt B).IsHermitian := by
  have hS := (supportInvSqrt_posSemidef B).1
  have := Matrix.isHermitian_mul_mul_conjTranspose (supportInvSqrt B) hA
  rwa [hS.eq] at this

theorem rpow_zero_ne (α : ℝ) (hα : α ≠ 0) : (fun x : ℝ => Real.rpow x α) 0 = 0 :=
  Real.zero_rpow hα

/-- Orthogonal additivity of the locked moment. -/
theorem moment_add_orth (α : ℝ) (hα : α ≠ 0) {A₁ A₂ B₁ B₂ : Matrix n n ℂ}
    (hA₁ : A₁.IsHermitian) (hA₂ : A₂.IsHermitian) (hB₁ : B₁.IsHermitian) (hB₂ : B₂.IsHermitian)
    (hBB : B₁ * B₂ = 0) (h12 : B₁ * A₂ = 0) (h21 : B₂ * A₁ = 0) :
    geometricMoment α (A₁ + A₂) (B₁ + B₂)
      = geometricMoment α A₁ B₁ + geometricMoment α A₂ B₂ := by
  have hs0 : supportInvSqrtScalar 0 = 0 := supportInvSqrtScalar_zero
  have hS₁ := (supportInvSqrt_posSemidef B₁).1
  have hS₂ := (supportInvSqrt_posSemidef B₂).1
  have hBB' : B₂ * B₁ = 0 := mul_comm_zero hB₁ hB₂ hBB
  have hS : supportInvSqrt (B₁ + B₂) = supportInvSqrt B₁ + supportInvSqrt B₂ :=
    hsf_add_orth _ hs0 hB₁ hB₂ hBB
  -- annihilation relations
  have e1 : supportInvSqrt B₁ * A₂ = 0 := hsf_mul_eq_zero _ hs0 hB₁ h12
  have e2 : supportInvSqrt B₂ * A₁ = 0 := hsf_mul_eq_zero _ hs0 hB₂ h21
  have e1' : A₂ * supportInvSqrt B₁ = 0 := mul_comm_zero hS₁ hA₂ e1
  have e2' : A₁ * supportInvSqrt B₂ = 0 := mul_comm_zero hS₂ hA₁ e2
  have e3 : B₁ * supportInvSqrt B₂ = 0 := mul_hsf_eq_zero _ hs0 hB₂ hBB
  have e4 : B₂ * supportInvSqrt B₁ = 0 := mul_hsf_eq_zero _ hs0 hB₁ hBB'
  have e5 : supportInvSqrt B₁ * supportInvSqrt B₂ = 0 := hsf_mul_eq_zero _ hs0 hB₁ e3
  have hX : (supportInvSqrt B₁ + supportInvSqrt B₂) * (A₁ + A₂)
        * (supportInvSqrt B₁ + supportInvSqrt B₂)
      = supportInvSqrt B₁ * A₁ * supportInvSqrt B₁
        + supportInvSqrt B₂ * A₂ * supportInvSqrt B₂ := by
    simp only [add_mul, mul_add, e1, e2, mul_assoc, e1', e2', zero_mul, mul_zero, add_zero,
      zero_add]
  have hX₁ := sandwich_isHermitian hA₁ B₁
  have hX₂ := sandwich_isHermitian hA₂ B₂
  have hXX : (supportInvSqrt B₁ * A₁ * supportInvSqrt B₁)
      * (supportInvSqrt B₂ * A₂ * supportInvSqrt B₂) = 0 := by
    calc (supportInvSqrt B₁ * A₁ * supportInvSqrt B₁) * (supportInvSqrt B₂ * A₂ * supportInvSqrt B₂)
        = supportInvSqrt B₁ * A₁ * (supportInvSqrt B₁ * supportInvSqrt B₂) * A₂
          * supportInvSqrt B₂ := by simp only [mul_assoc]
      _ = 0 := by rw [e5]; simp
  have hr0 := rpow_zero_ne α hα
  have hP : hermitianPower (supportInvSqrt B₁ * A₁ * supportInvSqrt B₁
        + supportInvSqrt B₂ * A₂ * supportInvSqrt B₂) α
      = hermitianPower (supportInvSqrt B₁ * A₁ * supportInvSqrt B₁) α
        + hermitianPower (supportInvSqrt B₂ * A₂ * supportInvSqrt B₂) α :=
    hsf_add_orth _ hr0 hX₁ hX₂ hXX
  have c1 : B₁ * hermitianPower (supportInvSqrt B₂ * A₂ * supportInvSqrt B₂) α = 0 := by
    apply mul_hsf_eq_zero _ hr0 hX₂
    rw [← mul_assoc, ← mul_assoc, e3]; simp
  have c2 : B₂ * hermitianPower (supportInvSqrt B₁ * A₁ * supportInvSqrt B₁) α = 0 := by
    apply mul_hsf_eq_zero _ hr0 hX₁
    rw [← mul_assoc, ← mul_assoc, e4]; simp
  unfold geometricMoment
  rw [hS, hX, hP, add_mul, mul_add, mul_add, c1, c2, add_zero, zero_add, Matrix.trace_add,
    Complex.add_re]

theorem moment_zero_left (α : ℝ) (hα : α ≠ 0) (B : Matrix n n ℂ) :
    geometricMoment α 0 B = 0 := by
  unfold geometricMoment hermitianPower
  rw [mul_zero, zero_mul, hsf_zero _ (rpow_zero_ne α hα), mul_zero, Matrix.trace_zero,
    Complex.zero_re]

/-- Trace of a product of positive semidefinite matrices. -/
theorem trace_mul_nonneg {B P : Matrix n n ℂ} (hB : B.PosSemidef) (hP : P.PosSemidef) :
    0 ≤ (Matrix.trace (B * P)).re := by
  obtain ⟨U, d, hU1, hU2, hPeq, hd⟩ := OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation.exists_spectral hP.1
  have hd0 : ∀ i, 0 ≤ d i := fun i => psd_spectrum_nonneg hP _ (hd i)
  have hC := hB.conjTranspose_mul_mul_same U
  have htr : Matrix.trace (B * P)
      = Matrix.trace (U.conjTranspose * B * U * Matrix.diagonal (fun i => (d i : ℂ))) := by
    conv_lhs => rw [hPeq]
    rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc]
  rw [htr]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have hii := (Complex.nonneg_iff.1 (hC.diag_nonneg (i := i)))
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg hii.1 (hd0 i)

theorem hermitianPower_posSemidef {X : Matrix n n ℂ} (hX : X.PosSemidef) (α : ℝ) :
    (hermitianPower X α).PosSemidef := by
  rw [hermitianPower_eq_cfc]
  exact cfc_posSemidef _ _ (fun x hx => Real.rpow_nonneg (psd_spectrum_nonneg hX x hx) α)

theorem moment_nonneg (α : ℝ) {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ geometricMoment α A B :=
  trace_mul_nonneg hB (hermitianPower_posSemidef (support_sandwich_posSemidef A B hA) α)

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofOrthogonal
