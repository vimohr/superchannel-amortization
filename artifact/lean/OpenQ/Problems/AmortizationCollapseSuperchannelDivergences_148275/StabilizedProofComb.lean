/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticCombE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedStatement

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Comb Choi operator of a locked `PhysicalSuperchannel` (from the Choi matrices of its
two teeth, linked over the memory) and the contraction formula for the locked
`referenceAct`: entry formula (4) of the reviewed note.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7
  (IsCPTP amplification choiLinearEquiv ofChoiMatrix ofChoiMatrix_choiLinearEquiv
    isCPTP_iff_isChannelChoi)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General (insertSlot insertSlot_formula)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.Preparation (basisMap basisMap_apply)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-- Index type of `C ⊗ A ⊗ B`, left nested. -/
abbrev X3 (c a b : ℕ) := (Fin c × Fin a) × Fin b

/-- Index type of `C ⊗ A ⊗ B ⊗ D`, left nested. -/
abbrev X4 (c a b d : ℕ) := X3 c a b × Fin d

/-- Input-first unnormalized Choi matrix `J (i, β) (j, γ) = F(|i⟩⟨j|) β γ` (locked). -/
abbrev choi {p q : ℕ} (F : ChannelMap p q) : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ :=
  choiLinearEquiv p q F

theorem choi_apply {p q : ℕ} (F : ChannelMap p q) (i j : Fin p) (β γ : Fin q) :
    choi F (i, β) (j, γ) = F (Matrix.single i j 1) β γ := rfl

/-- A linear map is the contraction of its Choi matrix with the input entries. -/
theorem map_expand {p q : ℕ} (F : ChannelMap p q) (M : Operator (Fin p)) (β γ : Fin q) :
    F M β γ = ∑ i, ∑ j, M i j * choi F (i, β) (j, γ) := by
  conv_lhs => rw [← ofChoiMatrix_choiLinearEquiv F]
  rfl

theorem sum_fin_prod {x e : ℕ} (f : Fin (x * e) → ℂ) :
    ∑ i, f i = ∑ k : Fin x, ∑ u : Fin e, f (finProdFinEquiv (k, u)) := by
  rw [← Equiv.sum_comp finProdFinEquiv f, Fintype.sum_prod_type]

/-- Slot insertion in Choi form, with no matrix-valued lambda in the statement. -/
theorem insertSlot_expand {p q : ℕ} (e : ℕ) (N : ChannelMap p q) (Y : Operator (Fin (p * e)))
    (k l : Fin q) (u v : Fin e) :
    insertSlot e N Y (finProdFinEquiv (k, u)) (finProdFinEquiv (l, v)) =
      ∑ i, ∑ j, Y (finProdFinEquiv (i, u)) (finProdFinEquiv (j, v)) * choi N (i, k) (j, l) :=
  (insertSlot_formula N Y (k, u) (l, v)).trans (map_expand N _ k l)

/-- Comb Choi operator on `C ⊗ A ⊗ B ⊗ D`: the link product of the Choi matrices
of the two teeth over the memory. With Kraus operators `p^k`, `q^l` of the teeth it is
`∑_{k,l} |v^{kl}⟩⟨v^{kl}|`, `v^{kl}(c,a,b,d) = ∑_e p^k_{(a,e),c} q^l_{d,(b,e)}`. -/
def combJ {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d) :
    Matrix (X4 c a b d) (X4 c a b d) ℂ :=
  Matrix.of fun x y => ∑ e₀ : Fin Θ.memory, ∑ e₁ : Fin Θ.memory,
    choi Θ.pre (x.1.1.1, finProdFinEquiv (x.1.1.2, e₀)) (y.1.1.1, finProdFinEquiv (y.1.1.2, e₁)) *
    choi Θ.post (finProdFinEquiv (x.1.2, e₀), x.2) (finProdFinEquiv (y.1.2, e₁), y.2)

theorem combJ_apply {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d) (x y : X4 c a b d) :
    combJ Θ x y = ∑ e₀ : Fin Θ.memory, ∑ e₁ : Fin Θ.memory,
      choi Θ.pre (x.1.1.1, finProdFinEquiv (x.1.1.2, e₀)) (y.1.1.1, finProdFinEquiv (y.1.1.2, e₁)) *
      choi Θ.post (finProdFinEquiv (x.1.2, e₀), x.2) (finProdFinEquiv (y.1.2, e₁), y.2) := rfl

theorem choi_psd {p q : ℕ} {F : ChannelMap p q} (hF : IsCPTP F) : (choi F).PosSemidef :=
  ((isCPTP_iff_isChannelChoi F).1 hF).1

theorem choi_marginal {p q : ℕ} {F : ChannelMap p q} (hF : IsCPTP F) :
    OpenQ.partialTraceRight (choi F) = 1 :=
  ((isCPTP_iff_isChannelChoi F).1 hF).2

/-- The comb operator is a block sum over the memory of a relabelled Kronecker product. -/
theorem combJ_eq {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d) :
    combJ Θ = bsum ((choi Θ.pre ⊗ₖ choi Θ.post).submatrix
      (fun q : Fin Θ.memory × X4 c a b d =>
        ((q.2.1.1.1, finProdFinEquiv (q.2.1.1.2, q.1)), (finProdFinEquiv (q.2.1.2, q.1), q.2.2)))
      (fun q : Fin Θ.memory × X4 c a b d =>
        ((q.2.1.1.1, finProdFinEquiv (q.2.1.1.2, q.1)), (finProdFinEquiv (q.2.1.2, q.1), q.2.2)))) := by
  ext x y
  rfl

theorem combJ_psd {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d) : (combJ Θ).PosSemidef := by
  rw [combJ_eq]
  exact psd_bsum (Matrix.PosSemidef.submatrix
    (Matrix.PosSemidef.kronecker (choi_psd Θ.pre_cptp) (choi_psd Θ.post_cptp)) _)

/-- Reordering of ten nested finite sums (the order produced by expanding the circuit
against the order of the contraction formula). -/
theorem sum10_reorder {α₀ α₁ α₂ α₃ α₄ α₅ α₆ α₇ α₈ α₉ : Type}
    [Fintype α₀] [Fintype α₁] [Fintype α₂] [Fintype α₃] [Fintype α₄] [Fintype α₅] [Fintype α₆]
    [Fintype α₇] [Fintype α₈] [Fintype α₉]
    (F : α₀ → α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → α₈ → α₉ → ℂ) :
    (∑ b0, ∑ e0, ∑ b1, ∑ e1, ∑ a0, ∑ u0, ∑ a1, ∑ u1, ∑ c0, ∑ c1,
        F b0 e0 b1 e1 a0 u0 a1 u1 c0 c1) =
      ∑ c0, ∑ a0, ∑ b0, ∑ u0, ∑ c1, ∑ a1, ∑ b1, ∑ u1, ∑ e0, ∑ e1,
        F b0 e0 b1 e1 a0 u0 a1 u1 c0 c1 := by
  have hL : (∑ b0, ∑ e0, ∑ b1, ∑ e1, ∑ a0, ∑ u0, ∑ a1, ∑ u1, ∑ c0, ∑ c1,
        F b0 e0 b1 e1 a0 u0 a1 u1 c0 c1) =
      ∑ w : α₀ × α₁ × α₂ × α₃ × α₄ × α₅ × α₆ × α₇ × α₈ × α₉,
        F w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2.1 w.2.2.2.2.2.2.1
          w.2.2.2.2.2.2.2.1 w.2.2.2.2.2.2.2.2.1 w.2.2.2.2.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have hR : (∑ c0, ∑ a0, ∑ b0, ∑ u0, ∑ c1, ∑ a1, ∑ b1, ∑ u1, ∑ e0, ∑ e1,
        F b0 e0 b1 e1 a0 u0 a1 u1 c0 c1) =
      ∑ v : α₈ × α₄ × α₀ × α₅ × α₉ × α₆ × α₂ × α₇ × α₁ × α₃,
        F v.2.2.1 v.2.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2 v.2.1
          v.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2.2.1 v.1 v.2.2.2.2.1 := by
    simp only [Fintype.sum_prod_type]
  rw [hL, hR]
  exact Fintype.sum_equiv
    { toFun := fun w => (w.2.2.2.2.2.2.2.2.1, w.2.2.2.2.1, w.1, w.2.2.2.2.2.1,
        w.2.2.2.2.2.2.2.2.2, w.2.2.2.2.2.2.1, w.2.2.1, w.2.2.2.2.2.2.2.1, w.2.1, w.2.2.2.1)
      invFun := fun v => (v.2.2.1, v.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2,
        v.2.1, v.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.2.1, v.1, v.2.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun _ => rfl)

/-- **Contraction formula** for the locked extended action, entry by entry, for an
arbitrary complex-linear joint insertion and an arbitrary matrix. -/
theorem refAct_entry {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d) (r : ℕ)
    (N : ChannelMap (a * r) (b * r)) (X : Operator (Fin (c * r))) (d₀ d₁ : Fin d) (t₀ t₁ : Fin r) :
    Θ.referenceAct r N X (finProdFinEquiv (d₀, t₀)) (finProdFinEquiv (d₁, t₁)) =
      ∑ z : X3 c a b × Fin r, ∑ z' : X3 c a b × Fin r,
        combJ Θ (z.1, d₀) (z'.1, d₁) *
        choi N (finProdFinEquiv (z.1.1.2, z.2), finProdFinEquiv (z.1.2, t₀))
               (finProdFinEquiv (z'.1.1.2, z'.2), finProdFinEquiv (z'.1.2, t₁)) *
        X (finProdFinEquiv (z.1.1.1, z.2)) (finProdFinEquiv (z'.1.1.1, z'.2)) := by
  rw [Θ.referenceAct_formula]
  simp only [LinearMap.comp_apply, insertSlot_expand, sum_fin_prod, basisMap_apply,
    memoryReferenceEquiv_symm_apply, memoryReferenceEquiv_apply, Finset.sum_mul,
    Fintype.sum_prod_type, combJ_apply]
  refine (sum10_reorder _).trans ?_
  refine Finset.sum_congr rfl fun c0 _ => ?_
  refine Finset.sum_congr rfl fun a0 _ => ?_
  refine Finset.sum_congr rfl fun b0 _ => ?_
  refine Finset.sum_congr rfl fun u0 _ => ?_
  refine Finset.sum_congr rfl fun c1 _ => ?_
  refine Finset.sum_congr rfl fun a1 _ => ?_
  refine Finset.sum_congr rfl fun b1 _ => ?_
  refine Finset.sum_congr rfl fun u1 _ => ?_
  refine Finset.sum_congr rfl fun e0 _ => ?_
  refine Finset.sum_congr rfl fun e1 _ => ?_
  ring

/-- Link index of the contraction: `(c, a, b)` and the inserted reference label. -/
abbrev Z4 (c a b r : ℕ) := X3 c a b × Fin r

/-- Index embedding of the contraction with an external state reference `S`. -/
def embS (c a b d r s : ℕ) :
    Z4 c a b r × (Fin s × Fin (d * r)) →
      (X4 c a b d × (Fin (a * r) × Fin (b * r))) × (Fin s × Fin (c * r)) :=
  fun q => (((q.1.1, (finProdFinEquiv.symm q.2.2).1),
      (finProdFinEquiv (q.1.1.1.2, q.1.2),
        finProdFinEquiv (q.1.1.2, (finProdFinEquiv.symm q.2.2).2))),
    (q.2.1, finProdFinEquiv (q.1.1.1.1, q.1.2)))

/-- Contraction of a comb operator, a joint Choi matrix on `(A R) ⊗ (B R)` and an
operator on `S ⊗ (C R)`: a block sum of a relabelled Kronecker product. -/
def contrS {a b c d r s : ℕ} (J : Matrix (X4 c a b d) (X4 c a b d) ℂ)
    (JN : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ)
    (ρ : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ) :
    Matrix (Fin s × Fin (d * r)) (Fin s × Fin (d * r)) ℂ :=
  bsum (((J ⊗ₖ JN) ⊗ₖ ρ).submatrix (embS c a b d r s) (embS c a b d r s))

theorem contrS_apply {a b c d r s : ℕ} (J : Matrix (X4 c a b d) (X4 c a b d) ℂ)
    (JN : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ)
    (ρ : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ)
    (s₀ s₁ : Fin s) (d₀ d₁ : Fin d) (t₀ t₁ : Fin r) :
    contrS J JN ρ (s₀, finProdFinEquiv (d₀, t₀)) (s₁, finProdFinEquiv (d₁, t₁)) =
      ∑ z : Z4 c a b r, ∑ z' : Z4 c a b r,
        J (z.1, d₀) (z'.1, d₁) *
        JN (finProdFinEquiv (z.1.1.2, z.2), finProdFinEquiv (z.1.2, t₀))
           (finProdFinEquiv (z'.1.1.2, z'.2), finProdFinEquiv (z'.1.2, t₁)) *
        ρ (s₀, finProdFinEquiv (z.1.1.1, z.2)) (s₁, finProdFinEquiv (z'.1.1.1, z'.2)) := by
  simp only [contrS, bsum_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, embS,
    Equiv.symm_apply_apply]

/-- The amplified output of the locked extended action is the contraction of the comb
operator, the Choi matrix of the insertion and the input operator. -/
theorem amp_refAct {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d) (r s : ℕ)
    (N : ChannelMap (a * r) (b * r)) (ρ : Operator (Fin s × Fin (c * r))) :
    amplification s (Θ.referenceAct r N) ρ = contrS (combJ Θ) (choi N) ρ := by
  ext ⟨s₀, k⟩ ⟨s₁, l⟩
  obtain ⟨⟨d₀, t₀⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨d₁, t₁⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [contrS_apply]
  exact refAct_entry Θ r N (fun i j => ρ (s₀, i) (s₁, j)) d₀ d₁ t₀ t₁

/-- Domination passes through the contraction. -/
theorem contrS_dom {a b c d r s : ℕ} {J₂ J₁ GJ : Matrix (X4 c a b d) (X4 c a b d) ℂ}
    {JM JN F : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ}
    {σ ρ H : Matrix (Fin s × Fin (c * r)) (Fin s × Fin (c * r)) ℂ}
    (h₁ : Dom J₂ J₁ GJ) (h₂ : Dom JM JN F) (h₃ : Dom σ ρ H) :
    Dom (contrS J₂ JM σ) (contrS J₁ JN ρ) (contrS GJ F H) :=
  (((h₁.kron h₂).kron h₃).submatrix _).bsum

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb
