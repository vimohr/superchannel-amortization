/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticDomE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Matrix.Order

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Order-two perspective `ρ σ⁺ ρ` on the locked definitions (`pinv`, `RangeIncluded`,
`geometricMoment`), through block domination: `Dom Y X T` says that the block
matrix `[[Y, X], [X, T]]` is positive semidefinite. It is closed under congruence,
relabelling, Kronecker products and block sums, holds for `(σ, ρ, ρ σ⁺ ρ)` on
supported pairs, and implies both range inclusion and `X Y⁺ X ≤ T`. No
invertibility is assumed anywhere.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open scoped ComplexOrder Kronecker Matrix

variable {m n k z p : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k] [Fintype z] [DecidableEq z] [Fintype p] [DecidableEq p]

/-- Block domination: the matrix `[[Y, X], [X, T]]` is positive semidefinite. -/
def Dom (Y X T : Matrix n n ℂ) : Prop := (Matrix.fromBlocks Y X X T).PosSemidef

theorem Dom.herm {Y X T : Matrix n n ℂ} (h : Dom Y X T) : X.IsHermitian := by
  have h1 := h.1
  rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose] at h1
  exact (Matrix.fromBlocks_inj.1 h1).2.1

theorem Dom.left {Y X T : Matrix n n ℂ} (h : Dom Y X T) : Y.PosSemidef := by
  have h1 : (Matrix.fromBlocks Y X X T).submatrix (Sum.inl : n → n ⊕ n) Sum.inl = Y := by
    ext i j; rfl
  rw [← h1]
  exact Matrix.PosSemidef.submatrix h _

theorem Dom.right {Y X T : Matrix n n ℂ} (h : Dom Y X T) : T.PosSemidef := by
  have h1 : (Matrix.fromBlocks Y X X T).submatrix (Sum.inr : n → n ⊕ n) Sum.inr = T := by
    ext i j; rfl
  rw [← h1]
  exact Matrix.PosSemidef.submatrix h _

/-- Gram form. -/
theorem dom_gram (V W : Matrix n k ℂ) (h : V * Wᴴ = W * Vᴴ) :
    Dom (V * Vᴴ) (W * Vᴴ) (W * Wᴴ) := by
  have e : Matrix.fromBlocks (V * Vᴴ) (W * Vᴴ) (W * Vᴴ) (W * Wᴴ) =
      Matrix.fromRows V W * (Matrix.fromRows V W)ᴴ := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul_fromCols, h]
  unfold Dom
  rw [e]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- A positive semidefinite matrix dominates itself. -/
theorem dom_self {J : Matrix n n ℂ} (hJ : J.PosSemidef) : Dom J J J := by
  have e : Matrix.fromBlocks J J J J =
      (Matrix.fromRows (1 : Matrix n n ℂ) 1) * J * (Matrix.fromRows (1 : Matrix n n ℂ) 1)ᴴ := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    simp
  unfold Dom
  rw [e]
  exact hJ.mul_mul_conjTranspose_same _

/-- The supported order-two perspective dominates. -/
theorem dom_base {σ ρ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hρ : ρ.IsHermitian)
    (h : RangeIncluded ρ σ) : Dom σ ρ (ρ * pinv σ * ρ) := by
  have hS : (supportInvSqrt σ).IsHermitian := (supportInvSqrt_posSemidef σ).1
  have hP : (pinv σ).IsHermitian := pinv_isHermitian σ
  have h1 : σ * pinv σ * ρ = ρ := supp_mul_of_rangeIncluded hσ h
  have h2 : ρ * pinv σ * σ = ρ := by
    have := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hρ.eq, hP.eq, hσ.1.eq,
      ← Matrix.mul_assoc] at this
    exact this
  have eV : (σ * supportInvSqrt σ) * (σ * supportInvSqrt σ)ᴴ = σ := by
    rw [Matrix.conjTranspose_mul, hS.eq, hσ.1.eq]
    calc σ * supportInvSqrt σ * (supportInvSqrt σ * σ) = σ * pinv σ * σ := by
          unfold pinv; simp only [Matrix.mul_assoc]
      _ = σ := penrose1 hσ
  have eWV : (ρ * supportInvSqrt σ) * (σ * supportInvSqrt σ)ᴴ = ρ := by
    rw [Matrix.conjTranspose_mul, hS.eq, hσ.1.eq]
    calc ρ * supportInvSqrt σ * (supportInvSqrt σ * σ) = ρ * pinv σ * σ := by
          unfold pinv; simp only [Matrix.mul_assoc]
      _ = ρ := h2
  have eVW : (σ * supportInvSqrt σ) * (ρ * supportInvSqrt σ)ᴴ = ρ := by
    rw [Matrix.conjTranspose_mul, hS.eq, hρ.eq]
    calc σ * supportInvSqrt σ * (supportInvSqrt σ * ρ) = σ * pinv σ * ρ := by
          unfold pinv; simp only [Matrix.mul_assoc]
      _ = ρ := h1
  have eW : (ρ * supportInvSqrt σ) * (ρ * supportInvSqrt σ)ᴴ = ρ * pinv σ * ρ := by
    rw [Matrix.conjTranspose_mul, hS.eq, hρ.eq]
    unfold pinv; simp only [Matrix.mul_assoc]
  have hg := dom_gram (σ * supportInvSqrt σ) (ρ * supportInvSqrt σ) (eVW.trans eWV.symm)
  rwa [eV, eWV, eW] at hg

/-- Congruence. -/
theorem Dom.conj {Y X T : Matrix n n ℂ} (h : Dom Y X T) (K : Matrix m n ℂ) :
    Dom (K * Y * Kᴴ) (K * X * Kᴴ) (K * T * Kᴴ) := by
  have e : Matrix.fromBlocks (K * Y * Kᴴ) (K * X * Kᴴ) (K * X * Kᴴ) (K * T * Kᴴ) =
      Matrix.fromBlocks K 0 0 K * Matrix.fromBlocks Y X X T *
        (Matrix.fromBlocks K (0 : Matrix m n ℂ) (0 : Matrix m n ℂ) K)ᴴ := by
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
  unfold Dom
  rw [e]
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same h _

/-- Relabelling or restriction of the basis (any index map). -/
theorem Dom.submatrix {Y X T : Matrix n n ℂ} (h : Dom Y X T) (f : m → n) :
    Dom (Y.submatrix f f) (X.submatrix f f) (T.submatrix f f) := by
  have e : Matrix.fromBlocks (Y.submatrix f f) (X.submatrix f f) (X.submatrix f f)
      (T.submatrix f f) = (Matrix.fromBlocks Y X X T).submatrix (Sum.map f f) (Sum.map f f) := by
    ext (i | i) (j | j) <;> rfl
  unfold Dom
  rw [e]
  exact Matrix.PosSemidef.submatrix h _

/-- Kronecker products. -/
theorem Dom.kron {Y₁ X₁ T₁ : Matrix m m ℂ} {Y₂ X₂ T₂ : Matrix n n ℂ}
    (h₁ : Dom Y₁ X₁ T₁) (h₂ : Dom Y₂ X₂ T₂) :
    Dom (Y₁ ⊗ₖ Y₂) (X₁ ⊗ₖ X₂) (T₁ ⊗ₖ T₂) := by
  let g : (m × n) ⊕ (m × n) → (m ⊕ m) × (n ⊕ n) :=
    Sum.elim (fun q => (Sum.inl q.1, Sum.inl q.2)) (fun q => (Sum.inr q.1, Sum.inr q.2))
  have e : Matrix.fromBlocks (Y₁ ⊗ₖ Y₂) (X₁ ⊗ₖ X₂) (X₁ ⊗ₖ X₂) (T₁ ⊗ₖ T₂) =
      (Matrix.fromBlocks Y₁ X₁ X₁ T₁ ⊗ₖ Matrix.fromBlocks Y₂ X₂ X₂ T₂).submatrix g g := by
    ext (i | i) (j | j) <;> rfl
  unfold Dom
  rw [e]
  exact Matrix.PosSemidef.submatrix (Matrix.PosSemidef.kronecker h₁ h₂) _

/-- Sum of all blocks over a link index: `(bsum M) i j = ∑ u v, M (u, i) (v, j)`. -/
def bsum (M : Matrix (z × p) (z × p) ℂ) : Matrix p p ℂ :=
  Matrix.of fun i j => ∑ u, ∑ v, M (u, i) (v, j)

theorem bsum_apply (M : Matrix (z × p) (z × p) ℂ) (i j : p) :
    bsum M i j = ∑ u, ∑ v, M (u, i) (v, j) := rfl

/-- The row of identity blocks. -/
def brow (z p : Type) [DecidableEq p] : Matrix p (z × p) ℂ :=
  Matrix.of fun i q => if q.2 = i then 1 else 0

theorem bsum_eq (M : Matrix (z × p) (z × p) ℂ) : bsum M = brow z p * M * (brow z p)ᴴ := by
  ext i j
  simp only [bsum_apply, brow, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, apply_ite (star : ℂ → ℂ), star_one, star_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]

theorem psd_bsum {M : Matrix (z × p) (z × p) ℂ} (h : M.PosSemidef) : (bsum M).PosSemidef := by
  rw [bsum_eq]
  exact h.mul_mul_conjTranspose_same _

theorem Dom.bsum {Y X T : Matrix (z × p) (z × p) ℂ} (h : Dom Y X T) :
    Dom (bsum Y) (bsum X) (bsum T) := by
  rw [bsum_eq, bsum_eq, bsum_eq]
  exact h.conj _

/-- Schur complement with the support inverse. -/
theorem dom_schur {Y X T : Matrix n n ℂ} (h : Dom Y X T) (hY : Y.PosSemidef) :
    (T - X * pinv Y * X).PosSemidef := by
  have hX := h.herm
  have hP : (pinv Y).IsHermitian := pinv_isHermitian Y
  have h2 : pinv Y * Y * pinv Y = pinv Y := penrose2 hY
  have key : (Matrix.fromRows (-(pinv Y * X)) (1 : Matrix n n ℂ))ᴴ * Matrix.fromBlocks Y X X T *
      Matrix.fromRows (-(pinv Y * X)) (1 : Matrix n n ℂ) = T - X * pinv Y * X := by
    rw [Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hX.eq, hP.eq,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_add, neg_neg, Matrix.mul_assoc]
    have e : X * (pinv Y * (Y * (pinv Y * X))) = X * (pinv Y * X) := by
      calc X * (pinv Y * (Y * (pinv Y * X))) = X * (pinv Y * Y * pinv Y) * X := by
            simp only [Matrix.mul_assoc]
        _ = X * (pinv Y * X) := by rw [h2, Matrix.mul_assoc]
    rw [e]
    abel
  rw [← key]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same h _

/-- Block positivity forces range inclusion of the off-diagonal block. -/
theorem dom_range {Y X T : Matrix n n ℂ} (h : Dom Y X T) (hY : Y.PosSemidef) :
    RangeIncluded X Y := by
  refine (rangeIncluded_iff_ker h.herm hY).2 ?_
  intro v hv
  have hM : (Matrix.fromBlocks Y X X T).mulVec (Sum.elim v 0) =
      Sum.elim (Y.mulVec v) (X.mulVec v) := by
    rw [Matrix.fromBlocks_mulVec]
    have e1 : (Sum.elim v (0 : n → ℂ)) ∘ Sum.inl = v := rfl
    have e2 : (Sum.elim v (0 : n → ℂ)) ∘ Sum.inr = 0 := rfl
    rw [e1, e2, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, add_zero]
  have h0 : star (Sum.elim v (0 : n → ℂ)) ⬝ᵥ
      (Matrix.fromBlocks Y X X T).mulVec (Sum.elim v 0) = 0 := by
    rw [hM, hv]
    simp [dotProduct, Fintype.sum_sum_type]
  have h1 := (Matrix.PosSemidef.dotProduct_mulVec_zero_iff h).1 h0
  rw [hM] at h1
  funext i
  exact congrFun h1 (Sum.inr i)

/-- Domination bounds the locked order-two moment and gives the support condition. -/
theorem moment_le_of_dom {σ ρ T : Matrix n n ℂ} (h : Dom σ ρ T) (hσ : σ.PosSemidef) :
    RangeIncluded ρ σ ∧ geometricMoment 2 ρ σ ≤ (Matrix.trace T).re := by
  have hR := dom_range h hσ
  refine ⟨hR, ?_⟩
  rw [geometricMoment_two h.herm hσ hR]
  have hs := (dom_schur h hσ).trace_nonneg
  rw [Matrix.trace_sub] at hs
  have := (Complex.nonneg_iff.1 hs).1
  rw [Complex.sub_re] at this
  linarith

/-- Range inclusion is preserved by a congruence with a left inverse. -/
theorem rangeIncluded_conj_leftInv {A B : Matrix n n ℂ} (K : Matrix m n ℂ) (K' : Matrix n m ℂ)
    (hK : K' * K = 1) (h : RangeIncluded A B) :
    RangeIncluded (K * A * Kᴴ) (K * B * Kᴴ) := by
  obtain ⟨Y, rfl⟩ := (rangeIncluded_iff_exists_mul A B).1 h
  rw [rangeIncluded_iff_exists_mul]
  refine ⟨K'ᴴ * Y * Kᴴ, ?_⟩
  have h1 : Kᴴ * K'ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hK, Matrix.conjTranspose_one]
  calc K * (B * Y) * Kᴴ = K * B * (Kᴴ * K'ᴴ) * Y * Kᴴ := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = K * B * Kᴴ * (K'ᴴ * Y * Kᴴ) := by simp only [Matrix.mul_assoc]

/-- Equality in the transformer inequality for an invertible congruence, with
singular supported pairs: the moment of the congruent pair is the trace of the
congruent perspective. -/
theorem moment_conj_eq {σ ρ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hρ : ρ.IsHermitian)
    (hR : RangeIncluded ρ σ) (K : Matrix m n ℂ) (K' : Matrix n m ℂ)
    (hK1 : K' * K = 1) (hK2 : K * K' = 1) :
    RangeIncluded (K * ρ * Kᴴ) (K * σ * Kᴴ) ∧
      geometricMoment 2 (K * ρ * Kᴴ) (K * σ * Kᴴ) =
        (Matrix.trace (K * (ρ * pinv σ * ρ) * Kᴴ)).re := by
  have d1 := (dom_base hσ hρ hR).conj K
  have hσ' : (K * σ * Kᴴ).PosSemidef := hσ.mul_mul_conjTranspose_same K
  have hρ' : (K * ρ * Kᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose K hρ
  obtain ⟨hR', hle⟩ := moment_le_of_dom d1 hσ'
  refine ⟨hR', le_antisymm hle ?_⟩
  have d3 := (dom_base hσ' hρ' hR').conj K'
  have h1 : Kᴴ * K'ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hK1, Matrix.conjTranspose_one]
  have h2 : K'ᴴ * Kᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hK2, Matrix.conjTranspose_one]
  have back : ∀ A : Matrix n n ℂ, K' * (K * A * Kᴴ) * K'ᴴ = A := by
    intro A
    calc K' * (K * A * Kᴴ) * K'ᴴ = (K' * K) * A * (Kᴴ * K'ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [hK1, h1, Matrix.one_mul, Matrix.mul_one]
  rw [back σ, back ρ] at d3
  have s1 := (dom_schur d3 hσ).mul_mul_conjTranspose_same K
  have e : K * (K' * (K * ρ * Kᴴ * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ)) * K'ᴴ -
      ρ * pinv σ * ρ) * Kᴴ =
      K * ρ * Kᴴ * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ) - K * (ρ * pinv σ * ρ) * Kᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    calc K * (K' * (K * ρ * Kᴴ * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ)) * K'ᴴ) * Kᴴ
        = (K * K') * (K * ρ * Kᴴ * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ)) * (K'ᴴ * Kᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = K * ρ * Kᴴ * pinv (K * σ * Kᴴ) * (K * ρ * Kᴴ) := by
          rw [hK2, h2, Matrix.one_mul, Matrix.mul_one]
  rw [e] at s1
  have hs := s1.trace_nonneg
  rw [Matrix.trace_sub] at hs
  have := (Complex.nonneg_iff.1 hs).1
  rw [Complex.sub_re] at this
  rw [geometricMoment_two hρ' hσ' hR']
  linarith

/-- Contrapositive for unsupported pairs. -/
theorem not_rangeIncluded_conj {σ ρ : Matrix n n ℂ} (K : Matrix m n ℂ) (K' : Matrix n m ℂ)
    (hK1 : K' * K = 1) (hK2 : K * K' = 1) (h : ¬ RangeIncluded ρ σ) :
    ¬ RangeIncluded (K * ρ * Kᴴ) (K * σ * Kᴴ) := by
  intro h'
  apply h
  have h3 := rangeIncluded_conj_leftInv K' K hK2 h'
  have h1 : Kᴴ * K'ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hK1, Matrix.conjTranspose_one]
  have back : ∀ A : Matrix n n ℂ, K' * (K * A * Kᴴ) * K'ᴴ = A := by
    intro A
    calc K' * (K * A * Kᴴ) * K'ᴴ = (K' * K) * A * (Kᴴ * K'ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [hK1, h1, Matrix.one_mul, Matrix.mul_one]
  rwa [back ρ, back σ] at h3

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom
