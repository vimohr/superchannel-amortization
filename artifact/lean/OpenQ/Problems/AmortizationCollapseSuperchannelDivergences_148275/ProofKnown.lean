import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence

/-!
Critic scratch (amortization problem, e001-i01). Known answers for `geometricStateDivergence`:

* commuting (diagonal) pairs: the classical Rényi divergence
  `(α-1)⁻¹ log₂ Σ q_i (p_i/q_i)^α`, with `+∞` exactly when some `q_i = 0 < p_i`
  (`geometricStateDivergence_diagonal`), and two numerical instances that show
  the orientation of the arguments;
* the support test in three equivalent forms (`rangeIncluded_iff_exists_mul`,
  `rangeIncluded_iff_ker`);
* order two: `Tr[ρ σ⁺ ρ]`, and `Tr[ρ σ⁻¹ ρ]` for positive definite `σ`
  (`geometricMoment_two`, `geometricMoment_two_posDef`).
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

theorem sandwich_scalar (q p : ℝ) (hq : 0 ≤ q) :
    supportInvSqrtScalar q * p * supportInvSqrtScalar q = p / q := by
  rw [supportInvSqrtScalar_eq]
  calc (Real.sqrt q)⁻¹ * p * (Real.sqrt q)⁻¹
      = p * ((Real.sqrt q)⁻¹ * (Real.sqrt q)⁻¹) := by ring
    _ = p * q⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hq]
    _ = p / q := (div_eq_mul_inv p q).symm

/-- Moment of a commuting pair. Terms with `q i = 0` vanish (`x / 0 = 0`). -/
theorem geometricMoment_diagonal (α : ℝ) (p q : n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    geometricMoment α (Matrix.diagonal (fun i => (p i : ℂ)))
        (Matrix.diagonal (fun i => (q i : ℂ))) =
      ∑ i, q i * (p i / q i) ^ α := by
  have h1 : Matrix.diagonal (fun i => ((supportInvSqrtScalar (q i) : ℝ) : ℂ)) *
      Matrix.diagonal (fun i => (p i : ℂ)) *
      Matrix.diagonal (fun i => ((supportInvSqrtScalar (q i) : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => ((p i / q i : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← sandwich_scalar (q i) (p i) (hq i)]
    push_cast
    ring
  have h2 := hsf_diagonal supportInvSqrtScalar q
  have h3 := hsf_diagonal (fun x : ℝ => Real.rpow x α) (fun i => p i / q i)
  unfold geometricMoment hermitianPower supportInvSqrt
  rw [h2, h1, h3, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

theorem rangeIncluded_diagonal (p q : n → ℝ) :
    RangeIncluded (Matrix.diagonal (fun i => (p i : ℂ)))
        (Matrix.diagonal (fun i => (q i : ℂ))) ↔ ∀ i, q i = 0 → p i = 0 := by
  unfold RangeIncluded
  constructor
  · intro h i hqi
    have hmem : (Matrix.diagonal (fun i => (p i : ℂ))).mulVec (Pi.single i 1) ∈
        Set.range (fun v : n → ℂ => (Matrix.diagonal (fun i => (p i : ℂ))).mulVec v) :=
      ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := h hmem
    have h2 := congrFun hw i
    simp only [Matrix.mulVec_diagonal, Pi.single_eq_same, mul_one, hqi, Complex.ofReal_zero,
      zero_mul] at h2
    exact_mod_cast h2.symm
  · intro h x hx
    obtain ⟨v, rfl⟩ := hx
    refine ⟨fun i => (p i : ℂ) * v i / (q i : ℂ), ?_⟩
    funext i
    simp only [Matrix.mulVec_diagonal]
    by_cases hqi : q i = 0
    · simp [hqi, h i hqi]
    · have hc : (q i : ℂ) ≠ 0 := by exact_mod_cast hqi
      field_simp

/-- Classical Rényi divergence on commuting pairs, base two, with the standard
support convention. -/
theorem geometricStateDivergence_diagonal (α : ℝ) (p q : n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    geometricStateDivergence α n (Matrix.diagonal (fun i => (p i : ℂ)))
        (Matrix.diagonal (fun i => (q i : ℂ))) =
      if (∀ i, q i = 0 → p i = 0) then
        ((Real.logb 2 (∑ i, q i * (p i / q i) ^ α) / (α - 1) : ℝ) : EReal)
      else ⊤ := by
  unfold geometricStateDivergence
  simp only [rangeIncluded_diagonal, geometricMoment_diagonal α p q hq]
  rfl

/-- Orientation: `p = (1/2, 1/2)`, `q = (1/4, 3/4)`, order two gives `log₂ (4/3)`. -/
theorem known_classical_instance :
    geometricStateDivergence 2 (Fin 2)
        (Matrix.diagonal (fun i => ((![1/2, 1/2] : Fin 2 → ℝ) i : ℂ)))
        (Matrix.diagonal (fun i => ((![1/4, 3/4] : Fin 2 → ℝ) i : ℂ))) =
      ((Real.logb 2 (4 / 3) : ℝ) : EReal) := by
  rw [geometricStateDivergence_diagonal 2 _ _ (by intro i; fin_cases i <;> norm_num)]
  have hs : (∀ i : Fin 2, (![1/4, 3/4] : Fin 2 → ℝ) i = 0 → (![1/2, 1/2] : Fin 2 → ℝ) i = 0) := by
    intro i; fin_cases i <;> norm_num
  simp only [eq_true hs, ↓reduceIte]
  have hsum : (∑ i : Fin 2, (![1/4, 3/4] : Fin 2 → ℝ) i *
      ((![1/2, 1/2] : Fin 2 → ℝ) i / (![1/4, 3/4] : Fin 2 → ℝ) i) ^ (2 : ℝ)) = 4 / 3 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_two]
    norm_num
  rw [hsum]
  norm_num

/-- The reversed pair gives `log₂ (5/4)`: the second argument is the reference. -/
theorem known_classical_instance_reversed :
    geometricStateDivergence 2 (Fin 2)
        (Matrix.diagonal (fun i => ((![1/4, 3/4] : Fin 2 → ℝ) i : ℂ)))
        (Matrix.diagonal (fun i => ((![1/2, 1/2] : Fin 2 → ℝ) i : ℂ))) =
      ((Real.logb 2 (5 / 4) : ℝ) : EReal) := by
  rw [geometricStateDivergence_diagonal 2 _ _ (by intro i; fin_cases i <;> norm_num)]
  have hs : (∀ i : Fin 2, (![1/2, 1/2] : Fin 2 → ℝ) i = 0 → (![1/4, 3/4] : Fin 2 → ℝ) i = 0) := by
    intro i; fin_cases i <;> norm_num
  simp only [eq_true hs, ↓reduceIte]
  have hsum : (∑ i : Fin 2, (![1/2, 1/2] : Fin 2 → ℝ) i *
      ((![1/4, 3/4] : Fin 2 → ℝ) i / (![1/2, 1/2] : Fin 2 → ℝ) i) ^ (2 : ℝ)) = 5 / 4 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_two]
    norm_num
  rw [hsum]
  norm_num

/-- Unsupported commuting pair: `p = (1/2, 1/2)` against the pure `q = (1, 0)`. -/
theorem known_classical_unsupported (α : ℝ) :
    geometricStateDivergence α (Fin 2)
        (Matrix.diagonal (fun i => ((![1/2, 1/2] : Fin 2 → ℝ) i : ℂ)))
        (Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ))) = ⊤ := by
  rw [geometricStateDivergence_diagonal α _ _ (by intro i; fin_cases i <;> norm_num)]
  have hs : ¬ (∀ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i = 0 → (![1/2, 1/2] : Fin 2 → ℝ) i = 0) := by
    intro h
    have := h 1 (by norm_num)
    norm_num at this
  simp only [eq_false hs, ↓reduceIte]

/-- Singular but supported commuting pair in dimension three: the pure
`p = (1, 0, 0)` against `q = (1/2, 1/2, 0)`, every order except 0 and 1: `log₂ 2 = 1`.
(At order 0 the same expression is 0, because `0 ^ 0 = 1`; Lean found this.) -/
theorem known_classical_singular (α : ℝ) (hα : α ≠ 1) (h0 : α ≠ 0) :
    geometricStateDivergence α (Fin 3)
        (Matrix.diagonal (fun i => ((![1, 0, 0] : Fin 3 → ℝ) i : ℂ)))
        (Matrix.diagonal (fun i => ((![1/2, 1/2, 0] : Fin 3 → ℝ) i : ℂ))) = (1 : EReal) := by
  rw [geometricStateDivergence_diagonal α _ _ (by intro i; fin_cases i <;> norm_num)]
  have hs : (∀ i : Fin 3, (![1/2, 1/2, 0] : Fin 3 → ℝ) i = 0 → (![1, 0, 0] : Fin 3 → ℝ) i = 0) := by
    intro i; fin_cases i <;> norm_num
  simp only [eq_true hs, ↓reduceIte]
  have hsum : (∑ i : Fin 3, (![1/2, 1/2, 0] : Fin 3 → ℝ) i *
      ((![1, 0, 0] : Fin 3 → ℝ) i / (![1/2, 1/2, 0] : Fin 3 → ℝ) i) ^ α) =
      (1 / 2) * (2 : ℝ) ^ α + (1 / 2) * (0 : ℝ) ^ α := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    norm_num
  rw [hsum]
  rw [Real.zero_rpow h0, mul_zero, add_zero]
  have h2 : (1 / 2 : ℝ) * 2 ^ α = 2 ^ (α - 1) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]; ring
  rw [h2, Real.logb_rpow (by norm_num) (by norm_num), div_self (sub_ne_zero.2 hα)]
  rfl

/-- Range inclusion as a factorisation. -/
theorem rangeIncluded_iff_exists_mul (ρ σ : Matrix n n ℂ) :
    RangeIncluded ρ σ ↔ ∃ Y : Matrix n n ℂ, ρ = σ * Y := by
  unfold RangeIncluded
  constructor
  · intro h
    have hcol : ∀ j, ∃ y : n → ℂ, σ.mulVec y = ρ.mulVec (Pi.single j 1) := by
      intro j
      have hmem : ρ.mulVec (Pi.single j 1) ∈ Set.range (fun v : n → ℂ => ρ.mulVec v) :=
        ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := h hmem
      exact ⟨y, hy⟩
    choose y hy using hcol
    refine ⟨Matrix.of (fun i j => y j i), ?_⟩
    ext i j
    have h2 := congrFun (hy j) i
    rw [Matrix.mulVec_single_one] at h2
    rw [Matrix.mul_apply]
    exact h2.symm
  · rintro ⟨Y, rfl⟩ x ⟨v, rfl⟩
    exact ⟨Y.mulVec v, by simp only [Matrix.mulVec_mulVec]⟩

/-- The support projector fixes every operator whose range lies in that of `σ`. -/
theorem supp_mul_of_rangeIncluded {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef)
    (h : RangeIncluded ρ σ) : σ * pinv σ * ρ = ρ := by
  obtain ⟨Y, rfl⟩ := (rangeIncluded_iff_exists_mul ρ σ).1 h
  rw [← Matrix.mul_assoc, penrose1 hσ]

theorem pinv_isHermitian (σ : Matrix n n ℂ) : (pinv σ).IsHermitian := by
  have hS := (supportInvSqrt_posSemidef σ).1
  unfold pinv
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hS.eq]

/-- For Hermitian `ρ` and PSD `σ`, range inclusion is kernel inclusion, the
usual statement of the support condition `supp ρ ⊆ supp σ`. -/
theorem rangeIncluded_iff_ker {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef) :
    RangeIncluded ρ σ ↔ ∀ v : n → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0 := by
  constructor
  · intro h v hv
    obtain ⟨Y, hY⟩ := (rangeIncluded_iff_exists_mul ρ σ).1 h
    have h1 : ρ = Y.conjTranspose * σ := by
      have := congrArg Matrix.conjTranspose hY
      rw [hρ.eq, Matrix.conjTranspose_mul, hσ.1.eq] at this
      exact this
    rw [h1, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · intro h
    have hker : ∀ w : n → ℂ, ρ.mulVec ((1 - pinv σ * σ).mulVec w) = 0 := by
      intro w
      apply h
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
        penrose1 hσ, sub_self, Matrix.zero_mulVec]
    have hz : ρ * (1 - pinv σ * σ) = 0 := by
      ext i j
      have h2 := congrFun (hker (Pi.single j 1)) i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
      exact h2
    have h3 : ρ = ρ * (pinv σ * σ) := by
      have := hz
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
      exact this
    have h4 : ρ = σ * (pinv σ * ρ) := by
      have := congrArg Matrix.conjTranspose h3
      rw [hρ.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hσ.1.eq,
        (pinv_isHermitian σ).eq, hρ.eq, Matrix.mul_assoc] at this
      exact this
    exact (rangeIncluded_iff_exists_mul ρ σ).2 ⟨_, h4⟩

/-- `S σ S` is the support projector `σ σ⁺`. -/
theorem sandwich_eq_supp {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    supportInvSqrt σ * σ * supportInvSqrt σ = σ * pinv σ := by
  rw [sandwich_self hσ, mul_pinv_eq_cfc hσ]

/-- Order two: the moment is `Tr[ρ σ⁺ ρ]` on supported pairs. -/
theorem geometricMoment_two {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef)
    (h : RangeIncluded ρ σ) :
    geometricMoment 2 ρ σ = (Matrix.trace (ρ * pinv σ * ρ)).re := by
  have hS := (supportInvSqrt_posSemidef σ).1
  have hX : (supportInvSqrt σ * ρ * supportInvSqrt σ).IsHermitian := by
    have := Matrix.isHermitian_mul_mul_conjTranspose (supportInvSqrt σ) hρ
    rwa [hS.eq] at this
  unfold geometricMoment
  rw [hermitianPower_two hX]
  have e1 : σ * (supportInvSqrt σ * ρ * supportInvSqrt σ *
      (supportInvSqrt σ * ρ * supportInvSqrt σ)) =
      (σ * supportInvSqrt σ * ρ * pinv σ * ρ) * supportInvSqrt σ := by
    unfold pinv
    simp only [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm]
  have e2 : supportInvSqrt σ * (σ * supportInvSqrt σ * ρ * pinv σ * ρ) =
      (supportInvSqrt σ * σ * supportInvSqrt σ) * ρ * pinv σ * ρ := by
    simp only [Matrix.mul_assoc]
  rw [e2, sandwich_eq_supp hσ, supp_mul_of_rangeIncluded hσ h]

/-- Order two with a positive definite reference: `Tr[ρ σ⁻¹ ρ]`, every Hermitian `ρ`. -/
theorem geometricMoment_two_posDef {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.PosDef) :
    geometricMoment 2 ρ σ = (Matrix.trace (ρ * σ⁻¹ * ρ)).re := by
  have hinv : pinv σ = σ⁻¹ := pinv_eq_inv hσ
  have hunit : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).1 hσ.isUnit
  have hR : RangeIncluded ρ σ :=
    (rangeIncluded_iff_exists_mul ρ σ).2 ⟨σ⁻¹ * ρ, by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv σ hunit, Matrix.one_mul]⟩
  rw [geometricMoment_two hρ hσ.posSemidef hR, hinv]

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
