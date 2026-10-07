import OpenQ.Problems.EqualWeightLowChoiRank_523ed7.Statement
import QuantumInfo.Channels.MatrixMap

/-!
# The input-first linear Choi correspondence

For arbitrary natural dimensions `a,b`, including zero, this module identifies
complex-linear maps `M_a(ℂ) → M_b(ℂ)` with the locked `ChoiMatrix a b`.
The matrix units are unnormalized and the input factor comes first.

We reuse Physlib's `MatrixMap.choi_equiv`, swapping its output-first factors.
The Kronecker-sum formula, explicit inverse, both inverse identities, ordinary
trace criterion, and uniform-sum transport are certified below. No positivity,
Hermiticity, rank, or invertibility assumption enters these identities.

These are classical identities: Watrous, *The Theory of Quantum Information*
(2018), Section 2.2.2, equations (2.65)-(2.66) and Theorem 2.26, after swapping
his output-first tensor factors. The complete-positivity theorem and the
channel-level equivalence with `MainStatement` remain pending.
-/

namespace OpenQ.Problems.EqualWeightLowChoiRank_523ed7

open scoped BigOperators Kronecker

/-- Unnormalized matrix units span every complex input matrix. This is the
matrix-unit reconstruction used in the other problem's `DecompositionConverse`. -/
theorem matrix_eq_sum_matrixUnits {a : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) :
    X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
  ext i j
  simp [Matrix.single_apply, Matrix.sum_apply, ite_and]

/-- The complex-linear Choi equivalence, with input-first indices. -/
noncomputable def choiLinearEquiv (a b : ℕ) :
    (Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) ≃ₗ[ℂ]
      ChoiMatrix a b :=
  MatrixMap.choi_equiv.trans
    (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodComm (Fin b) (Fin a))
      (Equiv.prodComm (Fin b) (Fin a)))

/-- The input row and column select the matrix unit, without a transpose,
conjugation, or dimension normalization. -/
@[simp] theorem choiLinearEquiv_apply {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin a) (β γ : Fin b) :
    choiLinearEquiv a b Φ (i, β) (j, γ) = Φ (Matrix.single i j 1) β γ :=
  rfl

/-- The forward map is precisely the unnormalized, input-first Choi sum. -/
theorem choiLinearEquiv_eq_sum {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    choiLinearEquiv a b Φ =
      ∑ i : Fin a, ∑ j : Fin a, Matrix.single i j (1 : ℂ) ⊗ₖ
        Φ (Matrix.single i j 1) := by
  ext ⟨i, β⟩ ⟨j, γ⟩
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single, ite_and, ite_mul]

/-- The inverse correspondence `R_J`, as a complex-linear map. -/
noncomputable def ofChoiMatrix {a b : ℕ} (J : ChoiMatrix a b) :
    Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ :=
  (choiLinearEquiv a b).symm J

/-- The explicit inverse sums against the entries `X_ij`, with no transpose
or conjugation of these coefficients. -/
@[simp] theorem ofChoiMatrix_apply {a b : ℕ} (J : ChoiMatrix a b)
    (X : Matrix (Fin a) (Fin a) ℂ) (β γ : Fin b) :
    ofChoiMatrix J X β γ = ∑ i : Fin a, ∑ j : Fin a,
      X i j * J (i, β) (j, γ) :=
  rfl

/-- The same explicit formula for the inverse of the bundled equivalence. -/
theorem choiLinearEquiv_symm_apply {a b : ℕ} (J : ChoiMatrix a b)
    (X : Matrix (Fin a) (Fin a) ℂ) (β γ : Fin b) :
    (choiLinearEquiv a b).symm J X β γ = ∑ i : Fin a, ∑ j : Fin a,
      X i j * J (i, β) (j, γ) :=
  rfl

/-- Reconstruction is a left inverse on all complex-linear maps. -/
@[simp] theorem ofChoiMatrix_choiLinearEquiv {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    ofChoiMatrix (choiLinearEquiv a b Φ) = Φ :=
  (choiLinearEquiv a b).symm_apply_apply Φ

/-- Reconstruction is a right inverse on all complex Choi matrices. -/
@[simp] theorem choiLinearEquiv_ofChoiMatrix {a b : ℕ} (J : ChoiMatrix a b) :
    choiLinearEquiv a b (ofChoiMatrix J) = J :=
  (choiLinearEquiv a b).apply_symm_apply J

/-- Every marginal entry is the ordinary complex trace of the image of a
matrix unit. -/
theorem partialTraceRight_choiLinearEquiv_apply {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (i j : Fin a) :
    OpenQ.partialTraceRight (choiLinearEquiv a b Φ) i j =
      Matrix.trace (Φ (Matrix.single i j 1)) :=
  rfl

/-- Trace preservation on every complex matrix is equivalent to the output
marginal being `I_a`. There are no positivity assumptions. -/
theorem tracePreserving_iff_partialTraceRight {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    (∀ X : Matrix (Fin a) (Fin a) ℂ, Matrix.trace (Φ X) = Matrix.trace X) ↔
      OpenQ.partialTraceRight (choiLinearEquiv a b Φ) =
        (1 : Matrix (Fin a) (Fin a) ℂ) := by
  have hunitTrace (i j : Fin a) :
      Matrix.trace (Matrix.single i j (1 : ℂ)) =
        (1 : Matrix (Fin a) (Fin a) ℂ) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  constructor
  · intro h
    ext i j
    rw [partialTraceRight_choiLinearEquiv_apply, h, hunitTrace]
  · intro h X
    have hunit (i j : Fin a) :
        Matrix.trace (Φ (Matrix.single i j 1)) =
          Matrix.trace (Matrix.single i j (1 : ℂ)) := by
      rw [← partialTraceRight_choiLinearEquiv_apply, h, hunitTrace]
    rw [matrix_eq_sum_matrixUnits X]
    simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul, hunit]

/-- Exactly `b` uniformly weighted complex-linear maps transport to exactly
the same `b` Choi matrices. The inverse is taken after casting `b` to `ℂ`. -/
theorem uniformSum_iff_choi_uniformSum {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (Ψ : Fin b → (Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)) :
    Φ = (b : ℂ)⁻¹ • ∑ r : Fin b, Ψ r ↔
      choiLinearEquiv a b Φ =
        (b : ℂ)⁻¹ • ∑ r : Fin b, choiLinearEquiv a b (Ψ r) := by
  constructor
  · intro h
    rw [h, map_smul, map_sum]
  · intro h
    apply (choiLinearEquiv a b).injective
    simpa only [map_smul, map_sum] using h

end OpenQ.Problems.EqualWeightLowChoiRank_523ed7
