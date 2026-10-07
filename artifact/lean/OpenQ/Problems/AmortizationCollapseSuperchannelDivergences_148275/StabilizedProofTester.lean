/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticTesterE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.RegularCombAlgebra
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofOrthogonal

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Tester algebra of the reviewed note, Section 3: the trace of the contracted perspective
is the full-transpose pairing of `W = Tr_D G` with a contracted tester; the tester is
positive, its `B` marginal is at most `q Y_C ⊗ 1_A`, and its completion by
`Δ ⊗ 1_B / b` is `q m` times a feasible tester. The three registered lemmas
`regularComb_fullTranspose_pairing`, `regularComb_completion_positive` and
`regularComb_completion_marginal` are used here.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofOrthogonal
  (trace_mul_nonneg)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-! ### Full-transpose pairing -/

/-- `Re ∑_{x,y} W_xy Γ_xy = Re Tr(W Γᵀ)`. -/
def pairing {n : Type} [Fintype n] (W Γ : Matrix n n ℂ) : ℝ := (∑ x, ∑ y, W x y * Γ x y).re

section pairing
variable {n : Type} [Fintype n] [DecidableEq n]

theorem pairing_eq_trace (W Γ : Matrix n n ℂ) : pairing W Γ = (Matrix.trace (W * Γᵀ)).re := by
  rw [pairing, regularComb_fullTranspose_pairing]

theorem pairing_nonneg {W Γ : Matrix n n ℂ} (hW : W.PosSemidef) (hΓ : Γ.PosSemidef) :
    0 ≤ pairing W Γ := by
  rw [pairing_eq_trace]
  exact trace_mul_nonneg hW hΓ.transpose

theorem pairing_add (W Γ₁ Γ₂ : Matrix n n ℂ) :
    pairing W (Γ₁ + Γ₂) = pairing W Γ₁ + pairing W Γ₂ := by
  simp only [pairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem pairing_smul (t : ℝ) (W Γ : Matrix n n ℂ) :
    pairing W ((t : ℂ) • Γ) = t * pairing W Γ := by
  have h : ∑ x, ∑ y, W x y * ((t : ℂ) * Γ x y) = (t : ℂ) * ∑ x, ∑ y, W x y * Γ x y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  simp only [pairing, Matrix.smul_apply, smul_eq_mul]
  rw [h, Complex.re_ofReal_mul]

theorem pairing_mono {W Γ₁ Γ₂ : Matrix n n ℂ} (hW : W.PosSemidef)
    (h : (Γ₂ - Γ₁).PosSemidef) : pairing W Γ₁ ≤ pairing W Γ₂ := by
  have h1 := pairing_nonneg hW h
  have h2 : pairing W Γ₂ = pairing W Γ₁ + pairing W (Γ₂ - Γ₁) := by
    rw [← pairing_add]
    congr 1
    abel
  linarith

end pairing

/-! ### Partial traces as sums of principal submatrices -/

theorem ptr_eq_sum {m n : Type} [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    OpenQ.partialTraceRight M = ∑ k : n, M.submatrix (fun i : m => (i, k)) (fun i => (i, k)) := by
  ext i j
  simp only [OpenQ.partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]

theorem ptr_psd {m n : Type} [Fintype m] [Fintype n] {M : Matrix (m × n) (m × n) ℂ}
    (h : M.PosSemidef) : (OpenQ.partialTraceRight M).PosSemidef := by
  rw [ptr_eq_sum]
  exact Matrix.posSemidef_sum _ fun k _ => Matrix.PosSemidef.submatrix h _

theorem ptr_smul {m n : Type} [Fintype n] (z : ℂ) (M : Matrix (m × n) (m × n) ℂ) :
    OpenQ.partialTraceRight (z • M) = z • OpenQ.partialTraceRight M := by
  ext i j
  simp only [OpenQ.partialTraceRight, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem trace_ptr {m n : Type} [Fintype m] [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace (OpenQ.partialTraceRight M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, OpenQ.partialTraceRight, Fintype.sum_prod_type]

/-! ### Feasible testers -/

/-- Feasible testers: `Γ ≥ 0` on `C ⊗ A ⊗ B` with `Tr_B Γ = τ_C ⊗ 1_A`, `τ_C ≥ 0`,
`Tr τ_C = 1`. -/
def Feasible (c a b : ℕ) (Γ : Matrix (X3 c a b) (X3 c a b) ℂ) : Prop :=
  Γ.PosSemidef ∧ ∃ τ : Matrix (Fin c) (Fin c) ℂ, τ.PosSemidef ∧ τ.trace = 1 ∧
    OpenQ.partialTraceRight Γ = τ ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)

variable {a b c d r s : ℕ}

/-! ### The contracted tester -/

def embT (c a b r s : ℕ) (t : Fin r) (s₀ : Fin s) :
    Fin r × X3 c a b → (Fin (a * r) × Fin (b * r)) × (Fin s × Fin (c * r)) :=
  fun q => ((finProdFinEquiv (q.2.1.2, q.1), finProdFinEquiv (q.2.2, t)),
    (s₀, finProdFinEquiv (q.2.1.1, q.1)))

/-- Contracted tester of a perspective `F` on `(A R) ⊗ (B R)` and `H` on `S ⊗ (C R)`:
trace over the output reference and over `S`, link over the input reference. -/
def tester (F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    Matrix (X3 c a b) (X3 c a b) ℂ :=
  ∑ t : Fin r, ∑ s₀ : Fin s,
    bsum ((F ⊗ₖ H).submatrix (embT c a b r s t s₀) (embT c a b r s t s₀))

theorem tester_apply (F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) (x y : X3 c a b) :
    tester F H x y = ∑ t : Fin r, ∑ s₀ : Fin s, ∑ u : Fin r, ∑ v : Fin r,
      F (finProdFinEquiv (x.1.2, u), finProdFinEquiv (x.2, t))
        (finProdFinEquiv (y.1.2, v), finProdFinEquiv (y.2, t)) *
      H (s₀, finProdFinEquiv (x.1.1, u)) (s₀, finProdFinEquiv (y.1.1, v)) := by
  simp only [tester, Matrix.sum_apply, bsum_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, embT]

theorem tester_psd {F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ}
    {H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ}
    (hF : F.PosSemidef) (hH : H.PosSemidef) : (tester (c := c) F H).PosSemidef := by
  unfold tester
  exact Matrix.posSemidef_sum _ fun t _ => Matrix.posSemidef_sum _ fun s₀ _ =>
    psd_bsum (Matrix.PosSemidef.submatrix (Matrix.PosSemidef.kronecker hF hH) _)

/-- The trace of the contraction is the pairing of `Tr_D G` with the tester. -/
theorem trace_contrS (GJ : Matrix (X4 c a b d) (X4 c a b d) ℂ)
    (F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    Matrix.trace (contrS GJ F H) =
      ∑ x, ∑ y, OpenQ.partialTraceRight GJ x y * tester F H x y := by
  have hL : Matrix.trace (contrS GJ F H) =
      ∑ s₀ : Fin s, ∑ d₀ : Fin d, ∑ t₀ : Fin r, ∑ x : X3 c a b, ∑ u : Fin r,
        ∑ y : X3 c a b, ∑ v : Fin r,
          GJ (x, d₀) (y, d₀) *
            F (finProdFinEquiv (x.1.2, u), finProdFinEquiv (x.2, t₀))
              (finProdFinEquiv (y.1.2, v), finProdFinEquiv (y.2, t₀)) *
            H (s₀, finProdFinEquiv (x.1.1, u)) (s₀, finProdFinEquiv (y.1.1, v)) := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₀ _ => ?_
    rw [sum_fin_prod]
    refine Finset.sum_congr rfl fun d₀ _ => ?_
    refine Finset.sum_congr rfl fun t₀ _ => ?_
    rw [Matrix.diag_apply, contrS_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hL]
  refine (sum7_trace _).trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tester_apply]
  simp only [OpenQ.partialTraceRight, Finset.sum_mul, Finset.mul_sum]
  refine (sum5_rot _).trans ?_
  refine Finset.sum_congr rfl fun t₀ _ => ?_
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.sum_congr rfl fun d₀ _ => ?_
  ring

/-! ### Marginals -/

/-- `Y_C = Tr_{S R} H`. -/
def stateMarg (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    Matrix (Fin c) (Fin c) ℂ :=
  ∑ s₀ : Fin s, ∑ u : Fin r,
    H.submatrix (fun c₀ : Fin c => (s₀, finProdFinEquiv (c₀, u)))
      (fun c₀ : Fin c => (s₀, finProdFinEquiv (c₀, u)))

theorem stateMarg_apply (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ)
    (c₀ c₁ : Fin c) :
    stateMarg H c₀ c₁ = ∑ s₀ : Fin s, ∑ u : Fin r,
      H (s₀, finProdFinEquiv (c₀, u)) (s₀, finProdFinEquiv (c₁, u)) := by
  simp only [stateMarg, Matrix.sum_apply, Matrix.submatrix_apply]

theorem stateMarg_psd {H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ}
    (hH : H.PosSemidef) : (stateMarg H).PosSemidef := by
  unfold stateMarg
  exact Matrix.posSemidef_sum _ fun s₀ _ => Matrix.posSemidef_sum _ fun u _ =>
    Matrix.PosSemidef.submatrix hH _

theorem trace_stateMarg (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    Matrix.trace (stateMarg H) = Matrix.trace H := by
  have h1 : Matrix.trace (stateMarg H) = ∑ c₀ : Fin c, ∑ s₀ : Fin s, ∑ u : Fin r,
      H (s₀, finProdFinEquiv (c₀, u)) (s₀, finProdFinEquiv (c₀, u)) := by
    simp only [Matrix.trace, Matrix.diag_apply, stateMarg_apply]
  have h2 : Matrix.trace H = ∑ s₀ : Fin s, ∑ c₀ : Fin c, ∑ u : Fin r,
      H (s₀, finProdFinEquiv (c₀, u)) (s₀, finProdFinEquiv (c₀, u)) := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₀ _ => ?_
    rw [sum_fin_prod]
    rfl
  rw [h1, h2]
  exact sum3_rot _

def embE (c a r s : ℕ) (s₀ : Fin s) :
    Fin r × (Fin c × Fin a) → Fin (a * r) × (Fin s × Fin (c * r)) :=
  fun q => (finProdFinEquiv (q.2.2, q.1), (s₀, finProdFinEquiv (q.2.1, q.1)))

/-- Contraction of an operator on `A R` with `H` over the inserted reference. -/
def margOf (E : Matrix (Fin (a * r)) (Fin (a * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    Matrix (Fin c × Fin a) (Fin c × Fin a) ℂ :=
  ∑ s₀ : Fin s, bsum ((E ⊗ₖ H).submatrix (embE c a r s s₀) (embE c a r s s₀))

theorem margOf_apply (E : Matrix (Fin (a * r)) (Fin (a * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) (x y : Fin c × Fin a) :
    margOf E H x y = ∑ s₀ : Fin s, ∑ u : Fin r, ∑ v : Fin r,
      E (finProdFinEquiv (x.2, u)) (finProdFinEquiv (y.2, v)) *
        H (s₀, finProdFinEquiv (x.1, u)) (s₀, finProdFinEquiv (y.1, v)) := by
  simp only [margOf, Matrix.sum_apply, bsum_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, embE]

theorem margOf_psd {E : Matrix (Fin (a * r)) (Fin (a * r)) ℂ}
    {H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ}
    (hE : E.PosSemidef) (hH : H.PosSemidef) : (margOf (c := c) E H).PosSemidef := by
  unfold margOf
  exact Matrix.posSemidef_sum _ fun s₀ _ =>
    psd_bsum (Matrix.PosSemidef.submatrix (Matrix.PosSemidef.kronecker hE hH) _)

theorem margOf_sub (E₁ E₂ : Matrix (Fin (a * r)) (Fin (a * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    margOf (c := c) (E₁ - E₂) H = margOf E₁ H - margOf E₂ H := by
  ext x y
  simp only [margOf_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem margOf_smul (z : ℂ) (E : Matrix (Fin (a * r)) (Fin (a * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    margOf (c := c) (z • E) H = z • margOf E H := by
  ext x y
  simp only [margOf_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The `B` marginal of the tester. -/
theorem ptr_tester (F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ)
    (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    OpenQ.partialTraceRight (tester (c := c) F H) = margOf (OpenQ.partialTraceRight F) H := by
  ext ⟨c₀, a₀⟩ ⟨c₁, a₁⟩
  rw [margOf_apply]
  simp only [OpenQ.partialTraceRight, tester_apply]
  refine (sum5_marg _).trans ?_
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [sum_fin_prod, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b₀ _ => ?_
  rw [Finset.sum_mul]

/-- With the identity on `A R` the contraction is `Y_C ⊗ 1_A`. -/
theorem margOf_one (H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    margOf (a := a) (1 : Matrix (Fin (a * r)) (Fin (a * r)) ℂ) H =
      stateMarg H ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ) := by
  ext ⟨c₀, a₀⟩ ⟨c₁, a₁⟩
  rw [margOf_apply, Matrix.kroneckerMap_apply, stateMarg_apply]
  simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h : a₀ = a₁
  · subst h
    simp only [true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, mul_one]
  · simp only [h, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero, mul_zero]

/-! ### Completion and the bound -/

/-- **Chain bound for the trace.** If `Tr_{B R} F ≤ q`, `Tr H = m` and every feasible
tester has pairing at most `Q` with `W = Tr_D G`, then `Tr K(G ⊗ F ⊗ H)K† ≤ q m Q`. -/
theorem chain_trace_bound (hb : 0 < b)
    {GJ : Matrix (X4 c a b d) (X4 c a b d) ℂ} (hG : GJ.PosSemidef)
    {F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ} (hF : F.PosSemidef)
    {H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ} (hH : H.PosSemidef)
    {q m Q : ℝ} (hq : 0 < q) (hm : 0 < m)
    (hE : ((q : ℂ) • (1 : Matrix (Fin (a * r)) (Fin (a * r)) ℂ) -
      OpenQ.partialTraceRight F).PosSemidef)
    (hmH : Matrix.trace H = (m : ℂ))
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (OpenQ.partialTraceRight GJ) Γ ≤ Q) :
    (Matrix.trace (contrS GJ F H)).re ≤ q * m * Q := by
  have hW : (OpenQ.partialTraceRight GJ).PosSemidef := ptr_psd hG
  have hT : (tester (c := c) F H).PosSemidef := tester_psd hF hH
  -- marginal slack
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : Matrix (Fin c × Fin a) (Fin c × Fin a) ℂ,
      Δ = (q : ℂ) • (stateMarg H ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) -
        OpenQ.partialTraceRight (tester (c := c) F H) := ⟨_, rfl⟩
  have hΔ : Δ.PosSemidef := by
    have e : Δ = margOf ((q : ℂ) • (1 : Matrix (Fin (a * r)) (Fin (a * r)) ℂ) -
        OpenQ.partialTraceRight F) H := by
      rw [hΔdef, margOf_sub, margOf_smul, margOf_one, ptr_tester]
    rw [e]
    exact margOf_psd hE hH
  -- normalized identity on B
  obtain ⟨β, hβdef⟩ : ∃ β : Matrix (Fin b) (Fin b) ℂ,
      β = (((b : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin b) (Fin b) ℂ) := ⟨_, rfl⟩
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hβ : β.PosSemidef := by
    rw [hβdef]
    exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.2 (inv_nonneg.2 hb'.le))
  have hβtr : Matrix.trace β = 1 := by
    rw [hβdef, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    field_simp
  -- completion
  have hcomp := regularComb_completion_positive (tester (c := c) F H) Δ β hT hΔ hβ
  have hmarg : OpenQ.partialTraceRight (tester (c := c) F H + Δ ⊗ₖ β) =
      (q : ℂ) • (stateMarg H ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) := by
    rw [hΔdef]
    exact regularComb_completion_marginal (tester (c := c) F H) _ β hβtr
  have hqm : 0 < q * m := mul_pos hq hm
  -- the normalized completed tester is feasible
  have hfeas : Feasible c a b ((((q * m)⁻¹ : ℝ) : ℂ) • (tester (c := c) F H + Δ ⊗ₖ β)) := by
    refine ⟨hcomp.1.smul (Complex.zero_le_real.2 (inv_nonneg.2 hqm.le)),
      (((m⁻¹ : ℝ) : ℂ)) • stateMarg H,
      (stateMarg_psd hH).smul (Complex.zero_le_real.2 (inv_nonneg.2 hm.le)), ?_, ?_⟩
    · rw [Matrix.trace_smul, trace_stateMarg, hmH, smul_eq_mul]
      push_cast
      field_simp
    · rw [ptr_smul, hmarg, smul_smul, Matrix.smul_kronecker]
      congr 1
      push_cast
      field_simp
  have h1 := hQ _ hfeas
  rw [pairing_smul] at h1
  have h2 : pairing (OpenQ.partialTraceRight GJ) (tester (c := c) F H) ≤
      pairing (OpenQ.partialTraceRight GJ) (tester (c := c) F H + Δ ⊗ₖ β) :=
    pairing_mono hW hcomp.2
  have h3 : (Matrix.trace (contrS GJ F H)).re =
      pairing (OpenQ.partialTraceRight GJ) (tester (c := c) F H) := by
    rw [trace_contrS]
    rfl
  rw [h3]
  have h4 : pairing (OpenQ.partialTraceRight GJ) (tester (c := c) F H + Δ ⊗ₖ β) ≤ q * m * Q := by
    have := mul_le_mul_of_nonneg_left h1 hqm.le
    rwa [← mul_assoc, mul_inv_cancel₀ hqm.ne', one_mul] at this
  linarith

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester
