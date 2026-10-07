import OpenQ.Problems.EqualWeightLowChoiRank_523ed7.ChoiCorrespondence
import OpenQ.Problems.EqualWeightLowChoiRank_523ed7.Statement
import QuantumInfo.Channels.Unbundled

/-!
# Amplification positivity and the channel formulation

Complete positivity below is defined on all positive semidefinite matrices by
the block action of `id_k ⊗ Φ`, independently of the Choi matrix. Swapping both
tensor factors connects it to Physlib's `Φ ⊗ id_k` convention. The auxiliary
dimension zero is treated explicitly. Choi positivity then follows from the
audited library Choi theorem and a separate permutation of its Choi indices.

These are classical correspondences, not a proof of the decomposition
conjecture. See Watrous, *The Theory of Quantum Information* (2018), Section
2.2.2, Theorems 2.22 and 2.26. All map correspondences allow zero maps and
singular Choi matrices; no invertibility or Hermiticity premise is used.
-/

namespace OpenQ.Problems.EqualWeightLowChoiRank_523ed7

open scoped BigOperators ComplexOrder

/-- The amplification `id_k ⊗ Φ`, specified on every matrix by its blocks. -/
noncomputable def amplification {a b : ℕ} (k : ℕ)
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ →ₗ[ℂ]
      Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ where
  toFun X p q := Φ (fun i j => X (p.1, i) (q.1, j)) p.2 q.2
  map_add' X Y := by
    ext ⟨s, β⟩ ⟨t, γ⟩
    exact congrArg (fun M => M β γ) (Φ.map_add
      (fun i j => X (s, i) (t, j)) (fun i j => Y (s, i) (t, j)))
  map_smul' c X := by
    ext ⟨s, β⟩ ⟨t, γ⟩
    exact congrArg (fun M => M β γ) (Φ.map_smul c (fun i j => X (s, i) (t, j)))

/-- Certified full-matrix block formula, with no assumption on `X`. -/
@[simp] theorem amplification_apply {a b k : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ)
    (s t : Fin k) (β γ : Fin b) :
    amplification k Φ X (s, β) (t, γ) =
      Φ (fun i j => X (s, i) (t, j)) β γ := rfl

/-- Swap both matrix indices, the permutation congruence for tensor order. -/
def tensorSwap {m n : ℕ}
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  X.submatrix (Equiv.prodComm (Fin n) (Fin m)) (Equiv.prodComm (Fin n) (Fin m))

@[simp] theorem tensorSwap_tensorSwap {m n : ℕ}
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    tensorSwap (tensorSwap X) = X := rfl

/-- Positive semidefiniteness is invariant under the tensor permutation. -/
theorem tensorSwap_posSemidef_iff {m n : ℕ}
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (tensorSwap X).PosSemidef ↔ X.PosSemidef :=
  Matrix.posSemidef_submatrix_equiv (Equiv.prodComm (Fin n) (Fin m))

/-- Swapping the input and output factors converts `Φ ⊗ id_k` into the
block-defined amplification, on all matrices, not only simple tensors. -/
theorem amplification_eq_tensorSwap_kron_tensorSwap {a b k : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    amplification k Φ X = tensorSwap
      ((MatrixMap.kron Φ (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ))
        (tensorSwap X)) := by
  ext ⟨s, β⟩ ⟨t, γ⟩
  change Φ (fun i j => X (s, i) (t, j)) β γ =
    (MatrixMap.kron Φ (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ))
      (tensorSwap X) (β, s) (γ, t)
  rw [MatrixMap.kron_def]
  conv_lhs => rw [matrix_eq_sum_matrixUnits (fun i j => X (s, i) (t, j))]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.single_apply, tensorSwap, Matrix.submatrix_apply, ite_and, mul_comm]

/-- Complete positivity in the requested auxiliary-first convention.
Every positive auxiliary dimension and every PSD input matrix are tested. -/
def IsCompletelyPositive {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
      X.PosSemidef → (amplification k Φ X).PosSemidef

/-- The library's auxiliary dimension zero imposes no condition: its output
matrix has an empty index type and is the zero matrix. -/
theorem kron_id_zero_isPositive {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    (MatrixMap.kron Φ (LinearMap.id : MatrixMap (Fin 0) (Fin 0) ℂ)).IsPositive := by
  intro X _
  have hzero :
      (MatrixMap.kron Φ (LinearMap.id : MatrixMap (Fin 0) (Fin 0) ℂ)) X = 0 := by
    ext ⟨β, s⟩
    exact Fin.elim0 s
  rw [hzero]
  exact Matrix.PosSemidef.zero

/-- Bridge from auxiliary-first amplification for positive dimensions to
Physlib's map-first amplification for all natural dimensions, including zero. -/
theorem isCompletelyPositive_iff_matrixMap {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    IsCompletelyPositive Φ ↔ MatrixMap.IsCompletelyPositive Φ := by
  constructor
  · intro h n X hX
    by_cases hn : 0 < n
    · have hY := h n hn (tensorSwap X) ((tensorSwap_posSemidef_iff X).2 hX)
      rw [amplification_eq_tensorSwap_kron_tensorSwap, tensorSwap_tensorSwap] at hY
      exact (tensorSwap_posSemidef_iff _).1 hY
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      exact kron_id_zero_isPositive Φ hX
  · intro h k _ X hX
    rw [amplification_eq_tensorSwap_kron_tensorSwap]
    exact (tensorSwap_posSemidef_iff _).2
      (h k ((tensorSwap_posSemidef_iff X).2 hX))

/-- The locked input-first Choi matrix is the tensor swap of Physlib's
output-first Choi matrix. -/
theorem choiLinearEquiv_eq_tensorSwap_choi_matrix {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    choiLinearEquiv a b Φ = tensorSwap (MatrixMap.choi_matrix Φ) := rfl

/-- Separate PSD transport for the Choi convention, without map assumptions. -/
theorem choiLinearEquiv_posSemidef_iff {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    (choiLinearEquiv a b Φ).PosSemidef ↔ (MatrixMap.choi_matrix Φ).PosSemidef := by
  rw [choiLinearEquiv_eq_tensorSwap_choi_matrix]
  exact tensorSwap_posSemidef_iff _

/-- Choi's CP criterion in the locked convention, for every complex-linear
map, including zero, and every natural pair of dimensions. -/
theorem isCompletelyPositive_iff_choi_posSemidef {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    IsCompletelyPositive Φ ↔ (choiLinearEquiv a b Φ).PosSemidef :=
  (isCompletelyPositive_iff_matrixMap Φ).trans
    ((MatrixMap.choi_PSD_iff_CP_map Φ).trans (choiLinearEquiv_posSemidef_iff Φ).symm)

/-- CPTP uses the independent amplification predicate and ordinary complex
trace preservation on every input matrix. -/
def IsCPTP {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) : Prop :=
  IsCompletelyPositive Φ ∧
    ∀ X : Matrix (Fin a) (Fin a) ℂ, Matrix.trace (Φ X) = Matrix.trace X

/-- The channel conditions coincide with the locked Choi conditions. -/
theorem isCPTP_iff_isChannelChoi {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    IsCPTP Φ ↔ IsChannelChoi (choiLinearEquiv a b Φ) := by
  exact and_congr (isCompletelyPositive_iff_choi_posSemidef Φ)
    (tracePreserving_iff_partialTraceRight Φ)

/-- Exactly `b` CPTP maps, each of complex Choi rank at most `a`, with
uniform weight `1/b`. Repeated maps are permitted. -/
def HasUniformChannelDecomposition {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) : Prop :=
  ∃ Ψ : Fin b → (Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ),
    (∀ r, IsCPTP (Ψ r) ∧ (choiLinearEquiv a b (Ψ r)).rank ≤ a) ∧
    Φ = (b : ℂ)⁻¹ • ∑ r : Fin b, Ψ r

/-- Transport the exact term count, complex rank bound, and uniform average
in both directions. The target map need not itself be a channel. -/
theorem hasUniformChannelDecomposition_iff_hasUniformDecomposition {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    HasUniformChannelDecomposition Φ ↔
      HasUniformDecomposition (choiLinearEquiv a b Φ) := by
  constructor
  · rintro ⟨Ψ, hΨ, havg⟩
    refine ⟨fun r => choiLinearEquiv a b (Ψ r), ?_,
      (uniformSum_iff_choi_uniformSum Φ Ψ).1 havg⟩
    intro r
    have hr := (isCPTP_iff_isChannelChoi (Ψ r)).1 (hΨ r).1
    exact ⟨hr.1, hr.2, (hΨ r).2⟩
  · rintro ⟨K, hK, havg⟩
    refine ⟨fun r => ofChoiMatrix (K r), ?_, ?_⟩
    · intro r
      constructor
      · apply (isCPTP_iff_isChannelChoi _).2
        simpa only [choiLinearEquiv_ofChoiMatrix] using
          (show IsChannelChoi (K r) from ⟨(hK r).1, (hK r).2.1⟩)
      · simpa only [choiLinearEquiv_ofChoiMatrix] using (hK r).2.2
    · apply (uniformSum_iff_choi_uniformSum Φ (fun r => ofChoiMatrix (K r))).2
      simpa only [choiLinearEquiv_ofChoiMatrix] using havg

/-- The universally quantified channel conjecture over positive complex
input and output dimensions. This definition asserts no existence theorem. -/
def ChannelMainStatement : Prop :=
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ,
      IsCPTP Φ → HasUniformChannelDecomposition Φ

/-- Equivalence of the amplification-defined channel conjecture and the
unchanged locked matrix conjecture, including singular Choi matrices. -/
theorem channelMainStatement_iff_mainStatement :
    ChannelMainStatement ↔ MainStatement := by
  constructor
  · intro h a b ha hb J hJ
    have hΦ : IsCPTP (ofChoiMatrix J) := (isCPTP_iff_isChannelChoi _).2 (by
      simpa only [choiLinearEquiv_ofChoiMatrix] using hJ)
    have hdec := (hasUniformChannelDecomposition_iff_hasUniformDecomposition
      (ofChoiMatrix J)).1 (h a b ha hb (ofChoiMatrix J) hΦ)
    simpa only [choiLinearEquiv_ofChoiMatrix] using hdec
  · intro h a b ha hb Φ hΦ
    exact (hasUniformChannelDecomposition_iff_hasUniformDecomposition Φ).2
      (h a b ha hb (choiLinearEquiv a b Φ) ((isCPTP_iff_isChannelChoi Φ).1 hΦ))

end OpenQ.Problems.EqualWeightLowChoiRank_523ed7
