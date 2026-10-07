/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticAlphaChainE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlpha

/-!
Critic scratch (amortization problem, e002-i02). Side probe after the review, not part
of the research record.

Order-`α` perspective: Kronecker multiplicativity, value on equal arguments, and the
chain inequalities for the two contractions (comb with insertion and state; channel with
state) at every order `1 < α ≤ 2`, obtained from the operator transformer inequality
after writing each contraction as a congruence.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlphaChain

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation
  (hsf_kronecker)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlpha
open scoped ComplexOrder Kronecker Matrix

noncomputable section

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-! ### Kronecker products -/

theorem S_kron {Y₁ : Matrix m m ℂ} {Y₂ : Matrix n n ℂ} (h₁ : Y₁.PosSemidef) (h₂ : Y₂.PosSemidef) :
    supportInvSqrt (Y₁ ⊗ₖ Y₂) = supportInvSqrt Y₁ ⊗ₖ supportInvSqrt Y₂ := by
  unfold supportInvSqrt
  apply hsf_kronecker _ h₁.1 h₂.1
  intro x hx y _
  rw [supportInvSqrtScalar_eq, supportInvSqrtScalar_eq, supportInvSqrtScalar_eq,
    Real.sqrt_mul (psd_spectrum_nonneg h₁ x hx), mul_inv]

/-- The perspective of a Kronecker product is the Kronecker product of the perspectives. -/
theorem Gp_kron (α : ℝ) {X₁ Y₁ : Matrix m m ℂ} {X₂ Y₂ : Matrix n n ℂ}
    (hX₁ : X₁.PosSemidef) (hY₁ : Y₁.PosSemidef) (hX₂ : X₂.PosSemidef) (hY₂ : Y₂.PosSemidef) :
    Gp α (X₁ ⊗ₖ X₂) (Y₁ ⊗ₖ Y₂) = Gp α X₁ Y₁ ⊗ₖ Gp α X₂ Y₂ := by
  have hS := S_kron hY₁ hY₂
  have hA : sand (X₁ ⊗ₖ X₂) (Y₁ ⊗ₖ Y₂) = sand X₁ Y₁ ⊗ₖ sand X₂ Y₂ := by
    unfold sand
    rw [hS, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have hRk : sqrtS (Y₁ ⊗ₖ Y₂) = sqrtS Y₁ ⊗ₖ sqrtS Y₂ := by
    unfold sqrtS
    rw [hS, ← Matrix.mul_kronecker_mul]
  have hP : hermitianPower (sand X₁ Y₁ ⊗ₖ sand X₂ Y₂) α =
      hermitianPower (sand X₁ Y₁) α ⊗ₖ hermitianPower (sand X₂ Y₂) α := by
    unfold hermitianPower
    apply hsf_kronecker _ (sand_psd Y₁ hX₁).1 (sand_psd Y₂ hX₂).1
    intro x hx y hy
    show (x * y) ^ α = x ^ α * y ^ α
    exact Real.mul_rpow (psd_spectrum_nonneg (sand_psd Y₁ hX₁) x hx)
      (psd_spectrum_nonneg (sand_psd Y₂ hX₂) y hy)
  unfold Gp
  rw [hA, hRk, hP, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem rangeIncluded_kron' {A B : Matrix m m ℂ} {V W : Matrix n n ℂ} (h1 : RangeIncluded A B)
    (h2 : RangeIncluded V W) : RangeIncluded (A ⊗ₖ V) (B ⊗ₖ W) := by
  obtain ⟨Y, rfl⟩ := (rangeIncluded_iff_exists_mul A B).1 h1
  obtain ⟨Z, rfl⟩ := (rangeIncluded_iff_exists_mul V W).1 h2
  rw [rangeIncluded_iff_exists_mul]
  exact ⟨Y ⊗ₖ Z, Matrix.mul_kronecker_mul B Y W Z⟩

/-- On equal arguments the perspective is the argument. -/
theorem Gp_self {α : ℝ} (hα : α ≠ 0) {J : Matrix n n ℂ} (hJ : J.PosSemidef) : Gp α J J = J := by
  have hP : hermitianPower (supportInvSqrt J * J * supportInvSqrt J) α =
      cfc (fun x : ℝ => x * x⁻¹) J := by
    rw [sandwich_self hJ, hermitianPower_eq_cfc]
    have hg : ContinuousOn (fun x : ℝ => x ^ α)
        ((fun x : ℝ => x * x⁻¹) '' spectrum ℝ J) := by
      rw [← cfc_map_spectrum (fun x : ℝ => x * x⁻¹) J hJ.1 (contOn _ _)]
      exact contOn _ _
    have hc := cfc_comp (fun x : ℝ => x ^ α) (fun x : ℝ => x * x⁻¹) J hJ.1 hg (contOn _ _)
    rw [← hc]
    apply cfc_congr
    intro x _
    show (x * x⁻¹) ^ α = x * x⁻¹
    by_cases hx : x = 0
    · simp [hx, Real.zero_rpow hα]
    · simp [hx]
  unfold Gp sand
  rw [hP, ← mul_pinv_eq_cfc hJ]
  have h1 : sqrtS J * (J * pinv J) = sqrtS J := sqrtS_mul_suppP hJ
  rw [h1, sqrtS_sq hJ]

/-! ### Contractions as congruences -/

/-- Selection matrix of an index map. -/
def sel {p q : Type} [DecidableEq q] (f : p → q) : Matrix p q ℂ :=
  Matrix.of fun i j => if f i = j then 1 else 0

theorem submatrix_eq_conj {p q : Type} [Fintype q] [DecidableEq q] (f : p → q)
    (M : Matrix q q ℂ) : M.submatrix f f = sel f * M * (sel f)ᴴ := by
  ext i j
  simp only [sel, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, mul_ite, mul_one, mul_zero]

/-- A block sum of a relabelled matrix is a congruence. -/
theorem bsum_submatrix_eq_conj {z p q : Type} [Fintype z] [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] [DecidableEq z] (f : z × p → q) (M : Matrix q q ℂ) :
    bsum (M.submatrix f f) = (brow z p * sel f) * M * (brow z p * sel f)ᴴ := by
  rw [bsum_eq, submatrix_eq_conj, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **Chain inequality under a congruence** at order `1 < α ≤ 2`. -/
theorem chain_conj {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hR : RangeIncluded X Y) (K : Matrix m n ℂ) :
    RangeIncluded (K * X * Kᴴ) (K * Y * Kᴴ) ∧
      geometricMoment α (K * X * Kᴴ) (K * Y * Kᴴ) ≤ (Matrix.trace (K * Gp α X Y * Kᴴ)).re := by
  refine ⟨conj_supported hX hY hR K, ?_⟩
  rw [moment_eq_trace α _ (hY.mul_mul_conjTranspose_same K)]
  have h := (transformer_alpha h1 h2 hX hY hR K).trace_nonneg
  rw [Matrix.trace_sub] at h
  have h' := (Complex.nonneg_iff.1 h).1
  rw [Complex.sub_re] at h'
  linarith

/-- Equality of moments for a congruence with a two-sided inverse. -/
theorem moment_conj_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hR : RangeIncluded X Y)
    (K : Matrix m n ℂ) (K' : Matrix n m ℂ) (hK1 : K' * K = 1) (hK2 : K * K' = 1) :
    RangeIncluded (K * X * Kᴴ) (K * Y * Kᴴ) ∧
      geometricMoment α (K * X * Kᴴ) (K * Y * Kᴴ) = (Matrix.trace (K * Gp α X Y * Kᴴ)).re := by
  refine ⟨conj_supported hX hY hR K, ?_⟩
  rw [moment_eq_trace α _ (hY.mul_mul_conjTranspose_same K), Gp_conj_eq h1 h2 hX hY hR K K' hK1 hK2]

variable {a b c d r s p q : ℕ}

/-- Chain inequality for the comb contraction with insertion and state. -/
theorem chainS_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2)
    {J₁ J₂ : Matrix (X4 c a b d) (X4 c a b d) ℂ}
    {JN JM : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ}
    {ρ σ : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ}
    (hJ₁ : J₁.PosSemidef) (hJ₂ : J₂.PosSemidef) (hRJ : RangeIncluded J₁ J₂)
    (hN : JN.PosSemidef) (hM : JM.PosSemidef) (hRN : RangeIncluded JN JM)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hRρ : RangeIncluded ρ σ) :
    RangeIncluded (contrS J₁ JN ρ) (contrS J₂ JM σ) ∧
      geometricMoment α (contrS J₁ JN ρ) (contrS J₂ JM σ) ≤
        (Matrix.trace (contrS (Gp α J₁ J₂) (Gp α JN JM) (Gp α ρ σ))).re := by
  have hX := (hJ₁.kronecker hN).kronecker hρ
  have hY := (hJ₂.kronecker hM).kronecker hσ
  have hR := rangeIncluded_kron' (rangeIncluded_kron' hRJ hRN) hRρ
  have hG : Gp α ((J₁ ⊗ₖ JN) ⊗ₖ ρ) ((J₂ ⊗ₖ JM) ⊗ₖ σ) =
      (Gp α J₁ J₂ ⊗ₖ Gp α JN JM) ⊗ₖ Gp α ρ σ := by
    rw [Gp_kron α (hJ₁.kronecker hN) (hJ₂.kronecker hM) hρ hσ, Gp_kron α hJ₁ hJ₂ hN hM]
  have h := chain_conj h1 h2 hX hY hR (brow (Z4 c a b r) (Fin s × Fin (d * r)) * sel (embS c a b d r s))
  rw [hG] at h
  unfold contrS
  rw [bsum_submatrix_eq_conj, bsum_submatrix_eq_conj, bsum_submatrix_eq_conj]
  exact h

/-- Chain inequality for the channel contraction with a state. -/
theorem chainC_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2)
    {JN JM : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ}
    {ρ σ : Matrix (Fin s × Fin p) (Fin s × Fin p) ℂ}
    (hN : JN.PosSemidef) (hM : JM.PosSemidef) (hRN : RangeIncluded JN JM)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hRρ : RangeIncluded ρ σ) :
    RangeIncluded (contrC JN ρ) (contrC JM σ) ∧
      geometricMoment α (contrC JN ρ) (contrC JM σ) ≤
        (Matrix.trace (contrC (Gp α JN JM) (Gp α ρ σ))).re := by
  have hX := hN.kronecker hρ
  have hY := hM.kronecker hσ
  have hR := rangeIncluded_kron' hRN hRρ
  have hG := Gp_kron α hN hM hρ hσ
  have h := chain_conj h1 h2 hX hY hR (brow (Fin p) (Fin s × Fin q) * sel (embC p q s))
  rw [hG] at h
  unfold contrC
  rw [bsum_submatrix_eq_conj, bsum_submatrix_eq_conj, bsum_submatrix_eq_conj]
  exact h

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlphaChain
