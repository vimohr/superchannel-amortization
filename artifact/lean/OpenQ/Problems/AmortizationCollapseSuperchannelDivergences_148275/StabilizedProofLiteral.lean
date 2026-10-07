/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticLiteralE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Literal forms and known answers for the definitions used in the scratch proof.

* `combJ_kraus`: for Kraus operators of the two teeth the scratch comb operator is the
  Gram matrix `∑_{k,l} |v^{kl}⟩⟨v^{kl}|`, `v^{kl}(c,a,b,d) = ∑_e p^k_{(a,e),c} q^l_{d,(b,e)}`,
  the definition of the reviewed claim.
* `ptr_combJ`, `ptr_Hpre`, `trace_combJ`: the causal constraints `Tr_D J = H ⊗ 1_B`,
  `Tr_A H = 1_C` and the normalization `Tr J = c b`.
* `self_pairing`, `self_value`: for equal superchannels every feasible tester has
  objective one and both locked quantities are zero.
* `psd_of_spectrum_le`, `moment_chain_lambda`: the moment inequality with any upper
  bound of the spectrum of `Tr_{B R}(J_N J_M⁺ J_N)`, in particular its largest eigenvalue.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofLiteral

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation
  (exists_spectral)
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofRealize OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums
open scoped ComplexOrder Kronecker Matrix

noncomputable section

variable {a b c d : ℕ}

/-! ### Kraus form -/

/-- Choi matrix of a map given by Kraus operators. -/
theorem choi_kraus {p q : ℕ} {κ : Type} [Fintype κ] (F : ChannelMap p q)
    (K : κ → Matrix (Fin q) (Fin p) ℂ) (hF : ∀ X, F X = ∑ k, K k * X * (K k)ᴴ)
    (i j : Fin p) (β γ : Fin q) :
    choi F (i, β) (j, γ) = ∑ k, K k β i * star (K k γ j) := by
  rw [choi_apply, hF, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- **The scratch comb operator is the Gram matrix of the reviewed claim.** -/
theorem combJ_kraus {κ ι : Type} [Fintype κ] [Fintype ι] (Θ : PhysicalSuperchannel a b c d)
    (P : κ → Matrix (Fin (a * Θ.memory)) (Fin c) ℂ)
    (Qm : ι → Matrix (Fin d) (Fin (b * Θ.memory)) ℂ)
    (hP : ∀ X, Θ.pre X = ∑ k, P k * X * (P k)ᴴ)
    (hQ : ∀ Y, Θ.post Y = ∑ l, Qm l * Y * (Qm l)ᴴ) (x y : X4 c a b d) :
    combJ Θ x y = ∑ k, ∑ l,
      (∑ e, P k (finProdFinEquiv (x.1.1.2, e)) x.1.1.1 * Qm l x.2 (finProdFinEquiv (x.1.2, e))) *
      star (∑ e, P k (finProdFinEquiv (y.1.1.2, e)) y.1.1.1 *
        Qm l y.2 (finProdFinEquiv (y.1.2, e))) := by
  rw [combJ_apply]
  simp only [choi_kraus Θ.pre P hP, choi_kraus Θ.post Qm hQ, star_sum, Finset.sum_mul_sum]
  refine (sum4_pairs _).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun e₀ _ => Finset.sum_congr rfl fun e₁ _ => ?_
  rw [star_mul']
  ring

/-! ### Causal constraints -/

/-- `H = Tr_E J_pre` on `C ⊗ A`. -/
def Hpre (Θ : PhysicalSuperchannel a b c d) : Matrix (Fin c × Fin a) (Fin c × Fin a) ℂ :=
  Matrix.of fun x y => ∑ e : Fin Θ.memory,
    choi Θ.pre (x.1, finProdFinEquiv (x.2, e)) (y.1, finProdFinEquiv (y.2, e))

/-- `Tr_D J = H ⊗ 1_B`. -/
theorem ptr_combJ (Θ : PhysicalSuperchannel a b c d) :
    OpenQ.partialTraceRight (combJ Θ) = Hpre Θ ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) := by
  ext ⟨⟨c₀, a₀⟩, b₀⟩ ⟨⟨c₁, a₁⟩, b₁⟩
  have hpost : ∀ e₀ e₁ : Fin Θ.memory, ∑ d₀ : Fin d,
      choi Θ.post (finProdFinEquiv (b₀, e₀), d₀) (finProdFinEquiv (b₁, e₁), d₀) =
      if b₀ = b₁ ∧ e₀ = e₁ then 1 else 0 := by
    intro e₀ e₁
    have h := congrFun (congrFun (choi_marginal Θ.post_cptp) (finProdFinEquiv (b₀, e₀)))
      (finProdFinEquiv (b₁, e₁))
    rw [Matrix.one_apply] at h
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
    exact h
  have h1 : OpenQ.partialTraceRight (combJ Θ) ((c₀, a₀), b₀) ((c₁, a₁), b₁) =
      ∑ e₀ : Fin Θ.memory, ∑ e₁ : Fin Θ.memory,
        choi Θ.pre (c₀, finProdFinEquiv (a₀, e₀)) (c₁, finProdFinEquiv (a₁, e₁)) *
          ∑ d₀ : Fin d, choi Θ.post (finProdFinEquiv (b₀, e₀), d₀) (finProdFinEquiv (b₁, e₁), d₀) := by
    simp only [OpenQ.partialTraceRight, combJ_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e₀ _ => ?_
    rw [Finset.sum_comm]
  rw [h1, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [hpost, Hpre, Matrix.of_apply]
  by_cases hb : b₀ = b₁
  · simp [hb]
  · simp [hb]

/-- `Tr_A H = 1_C`. -/
theorem ptr_Hpre (Θ : PhysicalSuperchannel a b c d) :
    OpenQ.partialTraceRight (Hpre Θ) = 1 := by
  ext c₀ c₁
  have h := congrFun (congrFun (choi_marginal Θ.pre_cptp) c₀) c₁
  rw [← h]
  simp only [OpenQ.partialTraceRight, Hpre, Matrix.of_apply]
  exact (sum_fin_prod (fun i => choi Θ.pre (c₀, i) (c₁, i))).symm

/-- `Tr J = c b`: the comb operator is unnormalized. -/
theorem trace_combJ (Θ : PhysicalSuperchannel a b c d) :
    Matrix.trace (combJ Θ) = (c : ℂ) * b := by
  rw [← trace_ptr, ptr_combJ, Matrix.trace_kronecker, ← trace_ptr, ptr_Hpre, Matrix.trace_one,
    Matrix.trace_one, Fintype.card_fin, Fintype.card_fin]

/-! ### Known answer: equal superchannels -/

theorem rangeIncluded_self {n : Type} [Fintype n] (A : Matrix n n ℂ) : RangeIncluded A A :=
  subset_rfl

theorem Wop_self (Θ : PhysicalSuperchannel a b c d) :
    Wop Θ Θ = Hpre Θ ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) := by
  rw [Wop, penrose1 (combJ_psd Θ), ptr_combJ]

/-- For equal superchannels every feasible tester has objective one. -/
theorem self_pairing (Θ : PhysicalSuperchannel a b c d)
    {Γ : Matrix (X3 c a b) (X3 c a b) ℂ} (h : Feasible c a b Γ) :
    pairing (Wop Θ Θ) Γ = 1 := by
  obtain ⟨-, τ, -, hτ, hm⟩ := h
  have hmarg : ∀ x y : Fin c × Fin a, ∑ b₀ : Fin b, Γ (x, b₀) (y, b₀) =
      τ x.1 y.1 * (1 : Matrix (Fin a) (Fin a) ℂ) x.2 y.2 := by
    intro x y
    have := congrFun (congrFun hm x) y
    rw [Matrix.kroneckerMap_apply] at this
    exact this
  have h1 : (∑ x : X3 c a b, ∑ y : X3 c a b, Wop Θ Θ x y * Γ x y) =
      ∑ x : Fin c × Fin a, ∑ y : Fin c × Fin a,
        Hpre Θ x y * (τ x.1 y.1 * (1 : Matrix (Fin a) (Fin a) ℂ) x.2 y.2) := by
    rw [Wop_self, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Fintype.sum_prod_type (f := fun y : X3 c a b => _)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hmarg, Finset.mul_sum]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h2 : (∑ x : Fin c × Fin a, ∑ y : Fin c × Fin a,
        Hpre Θ x y * (τ x.1 y.1 * (1 : Matrix (Fin a) (Fin a) ℂ) x.2 y.2)) =
      ∑ c₀ : Fin c, ∑ c₁ : Fin c, OpenQ.partialTraceRight (Hpre Θ) c₀ c₁ * τ c₀ c₁ := by
    simp only [Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, OpenQ.partialTraceRight, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c₀ _ => ?_
    rw [Finset.sum_comm]
  rw [pairing, h1, h2, ptr_Hpre]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  have : ∑ c₀ : Fin c, τ c₀ c₀ = 1 := hτ
  rw [this, Complex.one_re]

/-- Known answer of the headline theorem: equal superchannels have value zero. -/
theorem self_value (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (Θ : PhysicalSuperchannel a b c d) :
    referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ Θ = 0 ∧
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ Θ = 0 := by
  obtain ⟨y, h1, h2, -, h4⟩ := regular_alpha2 ha hb hc Θ Θ (rangeIncluded_self _)
  have hset : {x : ℝ | ∃ Γ, Feasible c a b Γ ∧ x = pairing (Wop Θ Θ) Γ} = {1} := by
    ext x
    constructor
    · rintro ⟨Γ, hΓ, rfl⟩
      exact self_pairing Θ hΓ
    · rintro rfl
      exact ⟨_, (gammaStar_feasiblePD hb hc).feasible,
        (self_pairing Θ (gammaStar_feasiblePD hb hc).feasible).symm⟩
  rw [hset] at h4
  have h5 : (2 : ℝ) ^ y = 1 := h4.unique isLUB_singleton
  have hy : y = 0 := by
    have := congrArg (Real.logb 2) h5
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_one] at this
  rw [h1, h2, hy]
  exact ⟨rfl, rfl⟩

/-! ### The largest eigenvalue as channel factor -/

/-- A Hermitian matrix is dominated by any upper bound of its spectrum. -/
theorem psd_of_spectrum_le {n : Type} [Fintype n] [DecidableEq n] {E : Matrix n n ℂ}
    (hE : E.IsHermitian) {q : ℝ} (h : ∀ x ∈ spectrum ℝ E, x ≤ q) :
    ((q : ℂ) • (1 : Matrix n n ℂ) - E).PosSemidef := by
  obtain ⟨U, dd, hU1, hU2, hEeq, hd⟩ := exists_spectral hE
  have e1 : Matrix.diagonal (fun i => ((q - dd i : ℝ) : ℂ)) =
      (q : ℂ) • (1 : Matrix n n ℂ) - Matrix.diagonal (fun i => (dd i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have e2 : (q : ℂ) • (1 : Matrix n n ℂ) - E =
      U * Matrix.diagonal (fun i => ((q - dd i : ℝ) : ℂ)) * Uᴴ := by
    rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU2, ← hEeq]
  rw [e2]
  exact (Matrix.PosSemidef.diagonal
    (fun i => Complex.zero_le_real.2 (sub_nonneg.2 (h _ (hd i))))).mul_mul_conjTranspose_same U

/-- The moment inequality of the reviewed claim with any upper bound `q > 0` of the
spectrum of `Tr_{B R}(J_N J_M⁺ J_N)`, for instance its largest eigenvalue. -/
theorem moment_chain_lambda (hb : 0 < b) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) {Q : ℝ}
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (Wop Θ₁ Θ₂) Γ ≤ Q)
    {r : ℕ} (N M : Channel (a * r) (b * r))
    (hRNM : RangeIncluded (choi N.val) (choi M.val)) {q : ℝ} (hq : 0 < q)
    (hspec : ∀ x ∈ spectrum ℝ
      (OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val)), x ≤ q)
    {s : ℕ} {ρ σ : Operator (Fin s × Fin (c * r))}
    (hρ : OpenQ.IsDensityMatrix ρ) (hσ : OpenQ.IsDensityMatrix σ) (hR : RangeIncluded ρ σ) :
    RangeIncluded (amplification s (Θ₁.referenceAct r N.val) ρ)
        (amplification s (Θ₂.referenceAct r M.val) σ) ∧
      geometricMoment 2 (amplification s (Θ₁.referenceAct r N.val) ρ)
          (amplification s (Θ₂.referenceAct r M.val) σ) ≤
        q * geometricMoment 2 ρ σ * Q := by
  have hF := (dom_base (choi_psd M.property) (choi_psd N.property).1 hRNM).right
  exact moment_chain_q hb Θ₁ Θ₂ hsupp hQ N M hRNM hq
    (psd_of_spectrum_le (ptr_psd hF).1 hspec) hρ hσ hR

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofLiteral
