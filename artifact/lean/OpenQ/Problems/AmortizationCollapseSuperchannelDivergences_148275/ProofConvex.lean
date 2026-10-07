import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.OperatorGeometricMean
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Portable proof: joint convexity of the locked order-3/2 moment

`moment_convex_pd`: for positive semidefinite `A₁, A₂` and positive definite
`B₁, B₂` of any finite size and `θ ∈ [0, 1]`,

  `M((1-θ)A₁ + θA₂, (1-θ)B₁ + θB₂) ≤ (1-θ) M(A₁, B₁) + θ M(A₂, B₂)`

for the locked `geometricMoment (3/2)`. The operator inequality is Physlib's
joint convexity of the generalized perspective (Ebadian, Nikoufar, Gordji,
Theorem 2.5, with the operator convexity of `x ↦ x^(3/2)`); it is transported
to matrices through `Matrix.toEuclideanCLM` and traced.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofConvex

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open LownerHeinzTheorem GeneralizedPerspectiveFunction
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Matrices as operators on Euclidean space. -/
noncomputable abbrev toOp :
    Matrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

theorem toOp_continuous : Continuous (toOp (n := n)) :=
  LinearMap.continuous_of_finiteDimensional (toOp (n := n)).toAlgEquiv.toLinearMap

theorem toOp_isSelfAdjoint {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    IsSelfAdjoint (toOp X) := by
  have hsa : IsSelfAdjoint X := hX
  exact hsa.map toOp

theorem toOp_cfc (f : ℝ → ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    toOp (cfc f X) = cfc f (toOp X) := by
  have hsa : IsSelfAdjoint X := hX
  exact StarAlgHomClass.map_cfc (S := ℂ) toOp f X (contOn f X) toOp_continuous hsa
    (toOp_isSelfAdjoint hX)

theorem toOp_real_smul (r : ℝ) (X : Matrix n n ℂ) : toOp (r • X) = r • toOp X := by
  rw [← Complex.coe_smul r X, ← Complex.coe_smul r (toOp X), map_smul]

theorem toOp_spectrum (X : Matrix n n ℂ) : spectrum ℝ (toOp X) = spectrum ℝ X :=
  AlgEquiv.spectrum_eq ((toOp (n := n)).toAlgEquiv.restrictScalars ℝ) X

theorem posSemidef_of_toOp_nonneg {X : Matrix n n ℂ} (h : 0 ≤ toOp X) : X.PosSemidef := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ← ContinuousLinearMap.isPositive_toLinearMap_iff,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.isPositive_toEuclideanLin_iff] at h
  exact h

/-- The operator perspective of `x ↦ x^(3/2)` as a matrix. -/
noncomputable def Φ (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2)) B
    * cfc (fun x : ℝ => x ^ (3 / 2 : ℝ))
      (cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B * A
        * cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B)
    * cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2)) B

theorem toOp_Φ {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    toOp (Φ A B) = GeneralizedPerspective (fun x : ℝ => x ^ (3 / 2 : ℝ))
      (fun x : ℝ => x ^ (1 : ℝ)) (toOp A) (toOp B) := by
  have hRi := cfc_isHermitian (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B
  have hmid : (cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B * A
      * cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B).IsHermitian := by
    have := Matrix.isHermitian_mul_mul_conjTranspose
      (cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B) hA
    rwa [hRi.eq] at this
  unfold Φ GeneralizedPerspective hSqrt hInvSqrt
  rw [map_mul, map_mul, toOp_cfc _ hmid, map_mul, map_mul, toOp_cfc _ hB, toOp_cfc _ hB]

/-- The locked moment is the trace of the matrix perspective, positive definite reference. -/
theorem moment_eq_trace_Φ {A B : Matrix n n ℂ} (hB : B.PosDef) :
    geometricMoment (3 / 2) A B = (Matrix.trace (Φ A B)).re := by
  have hRi : supportInvSqrt B = cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)) B := by
    rw [supportInvSqrt_eq_cfc]
    apply cfc_congr
    intro x hx
    have hx0 := posDef_spectrum_pos hB x hx
    show supportInvSqrtScalar x = (x ^ (1 : ℝ)) ^ ((-1 : ℝ) / 2)
    rw [supportInvSqrtScalar_eq, Real.rpow_one, Real.sqrt_eq_rpow, ← Real.rpow_neg hx0.le]
    norm_num
  have hRR : cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2)) B
      * cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2)) B = B := by
    rw [cfc_mul2]
    have : cfc (fun x : ℝ => (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2) * (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2)) B
        = cfc (fun x : ℝ => x) B := by
      apply cfc_congr
      intro x hx
      have hx0 := posDef_spectrum_pos hB x hx
      show (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2) * (x ^ (1 : ℝ)) ^ ((1 : ℝ) / 2) = x
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt hx0.le]
    rw [this, cfc_id_eq hB.1]
  have e : ∀ R W : Matrix n n ℂ, Matrix.trace (R * W * R) = Matrix.trace (R * R * W) := by
    intro R W
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  unfold geometricMoment Φ
  rw [hermitianPower_eq_cfc, hRi, e, hRR]

theorem rpow_three_halves_condIciAll :
    JensenOperatorInequality.CondIciAll.{0} (fun x : ℝ => x ^ (3 / 2 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ _ _
    exact power_Icc_one_two_operatorConvexOn_Ici (ℋ := K) (3 / 2) ⟨by norm_num, by norm_num⟩
  · intro x hx
    exact (Real.continuousAt_rpow_const x (3 / 2) (Or.inr (by norm_num))).continuousWithinAt
  · simp

/-- Joint convexity of the locked order-3/2 moment on PSD numerators and
positive definite references, any finite dimension. -/
theorem moment_convex_pd [Nonempty n] {A₁ A₂ B₁ B₂ : Matrix n n ℂ} (hA₁ : A₁.PosSemidef)
    (hA₂ : A₂.PosSemidef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    geometricMoment (3 / 2) ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)
      ≤ (1 - θ) * geometricMoment (3 / 2) A₁ B₁ + θ * geometricMoment (3 / 2) A₂ B₂ := by
  have : Nontrivial (EuclideanSpace ℂ n) := inferInstance
  have hconv := theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici (ℋ := EuclideanSpace ℂ n)
    (f := fun x : ℝ => x ^ (3 / 2 : ℝ)) (h := fun x : ℝ => x ^ (1 : ℝ))
    rpow_three_halves_condIciAll
    (by
      intro A B t hA hB ht0 ht1 hAs hBs
      exact power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := EuclideanSpace ℂ n) 1
        ⟨by norm_num, le_refl _⟩ hA hB ht0 ht1
        (hAs.trans Set.Ioi_subset_Ici_self) (hBs.trans Set.Ioi_subset_Ici_self))
    (by
      intro x hx
      exact (Real.continuousAt_rpow_const x 1 (Or.inl (ne_of_gt hx))).continuousWithinAt)
    (fun x hx => Real.rpow_pos_of_pos hx 1)
  have psd_mem : ∀ {A : Matrix n n ℂ}, A.PosSemidef → toOp A ∈ psdSet (ℋ := EuclideanSpace ℂ n) := by
    intro A hA
    refine ⟨toOp_isSelfAdjoint hA.1, ?_⟩
    rw [toOp_spectrum]
    exact fun x hx => psd_spectrum_nonneg hA x hx
  have pd_mem : ∀ {B : Matrix n n ℂ}, B.PosDef → toOp B ∈ pdSet (ℋ := EuclideanSpace ℂ n) := by
    intro B hB
    refine ⟨toOp_isSelfAdjoint hB.1, ?_⟩
    rw [toOp_spectrum]
    exact fun x hx => posDef_spectrum_pos hB x hx
  have hop := hconv (psd_mem hA₁) (psd_mem hA₂) (pd_mem hB₁) (pd_mem hB₂) h0 h1
  -- mixtures
  have hAmixH : ((1 - θ) • A₁ + θ • A₂).IsHermitian :=
    ((hA₁.smul (sub_nonneg.2 h1)).add (hA₂.smul h0)).1
  have hBmix : ((1 - θ) • B₁ + θ • B₂).PosDef := by
    rcases eq_or_lt_of_le h0 with hθ | hθ
    · rw [← hθ]; simpa using hB₁
    · exact Matrix.PosDef.posSemidef_add (hB₁.posSemidef.smul (sub_nonneg.2 h1)) (hB₂.smul hθ)
  simp only [] at hop
  rw [← toOp_real_smul, ← toOp_real_smul, ← map_add, ← toOp_real_smul, ← toOp_real_smul,
    ← map_add, ← toOp_Φ hAmixH hBmix.1, ← toOp_Φ hA₁.1 hB₁.1, ← toOp_Φ hA₂.1 hB₂.1,
    ← toOp_real_smul, ← toOp_real_smul, ← map_add, ← sub_nonneg, ← map_sub] at hop
  have hpsd := posSemidef_of_toOp_nonneg hop
  have htr := hpsd.trace_nonneg
  rw [moment_eq_trace_Φ hBmix, moment_eq_trace_Φ hB₁, moment_eq_trace_Φ hB₂]
  have hre : 0 ≤ (Matrix.trace ((1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂
      - Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂))).re :=
    (Complex.nonneg_iff.1 htr).1
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul] at hre
  simp only [Complex.sub_re, Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul] at hre
  linarith

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofConvex
