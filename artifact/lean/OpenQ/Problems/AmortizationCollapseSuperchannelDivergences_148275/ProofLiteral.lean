import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown

/-!
Critic scratch (amortization problem, e001-i01). A literal transcription `CriticMain` of the working statement in DOSSIER.md that
uses no definition of the submitted module and no locked project definition:

* states: `Matrix.PosSemidef` and unit trace;
* spectral calculus: Mathlib's generic `cfc`; the support inverse square root is
  `cfc (fun x => if 0 < x then 1 / √x else 0)`;
* support condition: kernel inclusion `σ v = 0 → ρ v = 0`;
* channels: Physlib's `MatrixMap.IsCompletelyPositive` and `IsTracePreserving`;
* `id_r ⊗ N` and `N ⊗ id_e`: Physlib's `MatrixMap.kron` (the library tensor
  product of linear maps);
* flattening of `Fin a × Fin e`: Mathlib's `Matrix.reindexLinearEquiv`;
* suprema: indexed `⨆` in `EReal`, with `< ⊤` side conditions for the
  subtracted costs.

`main_iff : MainStatement ↔ CriticMain`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofLiteral

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification matrix_eq_sum_matrixUnits)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open scoped ComplexOrder

noncomputable section

/-! ### Literal definitions -/

section literal

variable {n : Type} [Fintype n] [DecidableEq n]

def IsState (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

def litMoment (α : ℝ) (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (σ * cfc (fun x : ℝ => x ^ α)
    (cfc (fun x : ℝ => if 0 < x then 1 / Real.sqrt x else 0) σ * ρ *
      cfc (fun x : ℝ => if 0 < x then 1 / Real.sqrt x else 0) σ))).re

open scoped Classical in
def litD (α : ℝ) (ρ σ : Matrix n n ℂ) : EReal :=
  if (∀ v : n → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) then
    ((Real.logb 2 (litMoment α ρ σ) / (α - 1) : ℝ) : EReal)
  else ⊤

end literal

def LibCPTP {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  N.IsCompletelyPositive ∧ N.IsTracePreserving

def litCh (α : ℝ) {a b : ℕ} (N M : MatrixMap (Fin a) (Fin b) ℂ) : EReal :=
  ⨆ (r : ℕ) (_ : 1 ≤ r) (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) (_ : IsState ρ),
    litD α (MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ) N ρ)
      (MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ) M ρ)

def litChA (α : ℝ) {a b : ℕ} (N M : MatrixMap (Fin a) (Fin b) ℂ) : EReal :=
  ⨆ (r : ℕ) (_ : 1 ≤ r) (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ)
    (σ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) (_ : IsState ρ) (_ : IsState σ)
    (_ : litD α ρ σ < ⊤),
    litD α (MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ) N ρ)
      (MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ) M σ) - litD α ρ σ

def litSc (α : ℝ) {a b c d : ℕ}
    (T₁ T₂ : MatrixMap (Fin a) (Fin b) ℂ → MatrixMap (Fin c) (Fin d) ℂ) : EReal :=
  ⨆ (N : MatrixMap (Fin a) (Fin b) ℂ) (_ : LibCPTP N), litCh α (T₁ N) (T₂ N)

def litScA (α : ℝ) {a b c d : ℕ}
    (T₁ T₂ : MatrixMap (Fin a) (Fin b) ℂ → MatrixMap (Fin c) (Fin d) ℂ) : EReal :=
  ⨆ (N : MatrixMap (Fin a) (Fin b) ℂ) (M : MatrixMap (Fin a) (Fin b) ℂ) (_ : LibCPTP N)
    (_ : LibCPTP M) (_ : litChA α N M < ⊤), litChA α (T₁ N) (T₂ M) - litChA α N M

/-- `F ∘ (N ⊗ id_E) ∘ Epre` with the memory of dimension `e`. -/
def litAct {a b c d : ℕ} (e : ℕ) (pre : MatrixMap (Fin c) (Fin (a * e)) ℂ)
    (post : MatrixMap (Fin (b * e)) (Fin d) ℂ) (N : MatrixMap (Fin a) (Fin b) ℂ) :
    MatrixMap (Fin c) (Fin d) ℂ :=
  post ∘ₗ (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv).toLinearMap ∘ₗ
    MatrixMap.kron N (LinearMap.id : MatrixMap (Fin e) (Fin e) ℂ) ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv.symm finProdFinEquiv.symm).toLinearMap ∘ₗ pre

/-- The working statement of DOSSIER.md, written with library operations only. -/
def CriticMain : Prop :=
  ∀ (a b c d : ℕ), 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d → ∀ α : ℝ, 1 < α → α ≤ 2 →
    ∀ (e₁ : ℕ) (pre₁ : MatrixMap (Fin c) (Fin (a * e₁)) ℂ)
      (post₁ : MatrixMap (Fin (b * e₁)) (Fin d) ℂ)
      (e₂ : ℕ) (pre₂ : MatrixMap (Fin c) (Fin (a * e₂)) ℂ)
      (post₂ : MatrixMap (Fin (b * e₂)) (Fin d) ℂ),
      1 ≤ e₁ → 1 ≤ e₂ → LibCPTP pre₁ → LibCPTP post₁ → LibCPTP pre₂ → LibCPTP post₂ →
        litScA α (litAct e₁ pre₁ post₁) (litAct e₂ pre₂ post₂) =
          litSc α (litAct e₁ pre₁ post₁) (litAct e₂ pre₂ post₂)

/-! ### Bridges -/

section bridges

variable {n : Type} [Fintype n] [DecidableEq n]

theorem scalar_fun_eq :
    supportInvSqrtScalar = fun x : ℝ => if 0 < x then 1 / Real.sqrt x else 0 := by
  funext x
  rw [supportInvSqrtScalar_eq]
  by_cases hx : 0 < x
  · simp [hx]
  · have h0 : Real.sqrt x = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hx)
    simp [hx, h0]

theorem moment_eq (α : ℝ) (ρ σ : Matrix n n ℂ) :
    geometricMoment α ρ σ = litMoment α ρ σ := by
  unfold geometricMoment litMoment hermitianPower supportInvSqrt
  rw [hsf_eq_cfc, hsf_eq_cfc, scalar_fun_eq]
  rfl

theorem D_eq (α : ℝ) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef) :
    geometricStateDivergence α n ρ σ = litD α ρ σ := by
  unfold geometricStateDivergence litD
  by_cases h : RangeIncluded ρ σ
  · have h' := (rangeIncluded_iff_ker hρ hσ).1 h
    simp only [eq_true h, eq_true h', ↓reduceIte, moment_eq]
    rfl
  · have h' : ¬ (∀ v : n → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :=
      fun h'' => h ((rangeIncluded_iff_ker hρ hσ).2 h'')
    simp only [eq_false h, eq_false h', ↓reduceIte]

theorem litD_ne_bot (α : ℝ) (ρ σ : Matrix n n ℂ) : litD α ρ σ ≠ ⊥ := by
  unfold litD
  split_ifs
  · exact EReal.coe_ne_bot _
  · simp

theorem litD_lt_top_iff (α : ℝ) (ρ σ : Matrix n n ℂ) :
    litD α ρ σ < ⊤ ↔ ∃ t : ℝ, litD α ρ σ = (t : EReal) := by
  constructor
  · intro h
    exact ⟨(litD α ρ σ).toReal, (EReal.coe_toReal h.ne (litD_ne_bot α ρ σ)).symm⟩
  · rintro ⟨t, ht⟩
    rw [ht]
    exact EReal.coe_lt_top t

theorem litD_self {τ : Matrix n n ℂ} (hτ : IsState τ) (α : ℝ) (hα : α ≠ 0) :
    litD α τ τ = 0 := by
  rw [← D_eq α hτ.1.1 hτ.1]
  exact geometricStateDivergence_self hτ α hα

end bridges

/-- The block-defined amplification is the library tensor product `id_k ⊗ Φ`. -/
theorem amplification_eq_kron {a b k : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    amplification k Φ X =
      MatrixMap.kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ) Φ X := by
  ext ⟨s, β⟩ ⟨t, γ⟩
  change Φ (fun i j => X (s, i) (t, j)) β γ = _
  rw [MatrixMap.kron_def]
  conv_lhs => rw [matrix_eq_sum_matrixUnits (fun i j => X (s, i) (t, j))]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.single_apply, ite_and, mul_comm]

theorem ordinaryCh_eq (α : ℝ) {a b : ℕ} (N M : Channel a b) :
    ordinaryChannelDivergence (geometricStateDivergence α) N M = litCh α N.val M.val := by
  unfold ordinaryChannelDivergence litCh
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨r, hr, ρ, hρ, rfl⟩
    have h1 := amplification_isDensityMatrix N hr ρ hρ
    have h2 := amplification_isDensityMatrix M hr ρ hρ
    rw [D_eq α h1.1.1 h2.1, amplification_eq_kron, amplification_eq_kron]
    exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)))
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun ρ => iSup_le fun hρ => ?_
    apply le_sSup
    refine ⟨r, hr, ρ, hρ, ?_⟩
    have h1 := amplification_isDensityMatrix N hr ρ hρ
    have h2 := amplification_isDensityMatrix M hr ρ hρ
    rw [D_eq α h1.1.1 h2.1, amplification_eq_kron, amplification_eq_kron]

theorem amortizedCh_eq (α : ℝ) {a b : ℕ} (N M : Channel a b) :
    amortizedChannelDivergence (geometricStateDivergence α) N M = litChA α N.val M.val := by
  unfold amortizedChannelDivergence litChA
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨r, hr, ρ, σ, hρ, hσ, t, ht, rfl⟩
    have h1 := amplification_isDensityMatrix N hr ρ hρ
    have h2 := amplification_isDensityMatrix M hr σ hσ
    rw [D_eq α hρ.1.1 hσ.1] at ht
    rw [D_eq α h1.1.1 h2.1, amplification_eq_kron, amplification_eq_kron, ← ht]
    have hlt : litD α ρ σ < ⊤ := by rw [ht]; exact EReal.coe_lt_top t
    exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le ρ (le_iSup_of_le σ
      (le_iSup_of_le hρ (le_iSup_of_le hσ (le_iSup_of_le hlt le_rfl))))))
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun ρ => iSup_le fun σ =>
      iSup_le fun hρ => iSup_le fun hσ => iSup_le fun hlt => ?_
    apply le_sSup
    obtain ⟨t, ht⟩ := (litD_lt_top_iff α ρ σ).1 hlt
    have h1 := amplification_isDensityMatrix N hr ρ hρ
    have h2 := amplification_isDensityMatrix M hr σ hσ
    refine ⟨r, hr, ρ, σ, hρ, hσ, t, ?_, ?_⟩
    · rw [D_eq α hρ.1.1 hσ.1]; exact ht
    · rw [D_eq α h1.1.1 h2.1, amplification_eq_kron, amplification_eq_kron, ht]

theorem flatten_eq (x e : ℕ) : Preparation.flatten x e =
    (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv).toLinearMap := by
  apply LinearMap.ext
  intro X
  rfl

theorem unflatten_eq (x e : ℕ) : Preparation.unflatten x e =
    (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv.symm finProdFinEquiv.symm).toLinearMap := by
  apply LinearMap.ext
  intro X
  rfl

/-- The registered action is the literal `F ∘ (N ⊗ id_E) ∘ Epre`. -/
theorem act_eq {a b c d : ℕ} (Θ : PhysicalSuperchannel a b c d)
    (N : MatrixMap (Fin a) (Fin b) ℂ) :
    Θ.act N = litAct Θ.memory Θ.pre Θ.post N := by
  unfold PhysicalSuperchannel.act litAct
  rw [General.insertSlot_eq_kron, flatten_eq, unflatten_eq]
  simp only [LinearMap.comp_assoc]

theorem ordinarySc_eq (α : ℝ) {a b c d : ℕ} (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) :
    ordinarySuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
      litSc α (litAct Θ₁.memory Θ₁.pre Θ₁.post) (litAct Θ₂.memory Θ₂.pre Θ₂.post) := by
  unfold ordinarySuperchannelDivergence litSc
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨N, rfl⟩
    rw [ordinaryCh_eq]
    have hN : LibCPTP N.val := (Preparation.libraryCPTP_iff _).2 N.property
    refine le_iSup_of_le N.val (le_iSup_of_le hN ?_)
    change litCh α (Θ₁.act N.val) (Θ₂.act N.val) ≤ _
    rw [act_eq, act_eq]
  · refine iSup_le fun N => iSup_le fun hN => ?_
    apply le_sSup
    refine ⟨⟨N, (Preparation.libraryCPTP_iff _).1 hN⟩, ?_⟩
    rw [ordinaryCh_eq]
    change _ = litCh α (Θ₁.act N) (Θ₂.act N)
    rw [act_eq, act_eq]

/-- A state on `Fin 1 × Fin a` for `a ≥ 1`. -/
theorem exists_state {a : ℕ} (ha : 1 ≤ a) :
    ∃ τ : Matrix (Fin 1 × Fin a) (Fin 1 × Fin a) ℂ, IsState τ := by
  refine ⟨Matrix.diagonal (Pi.single ((0 : Fin 1), (⟨0, ha⟩ : Fin a)) (1 : ℂ)), ?_, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i = ((0 : Fin 1), (⟨0, ha⟩ : Fin a))
    · subst hi; simp
    · simp [hi]
  · simp [Matrix.trace_diagonal]

theorem litChA_ne_bot (α : ℝ) (hα : α ≠ 0) {a b : ℕ} (ha : 1 ≤ a)
    (N M : MatrixMap (Fin a) (Fin b) ℂ) : litChA α N M ≠ ⊥ := by
  obtain ⟨τ, hτ⟩ := exists_state ha
  have hself := litD_self hτ α hα
  have hlt : litD α τ τ < ⊤ := by rw [hself]; exact EReal.zero_lt_top
  have hle : litD α (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 1) (Fin 1) ℂ) N τ)
      (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 1) (Fin 1) ℂ) M τ) - litD α τ τ ≤
      litChA α N M := by
    unfold litChA
    exact le_iSup_of_le 1 (le_iSup_of_le le_rfl (le_iSup_of_le τ (le_iSup_of_le τ
      (le_iSup_of_le hτ (le_iSup_of_le hτ (le_iSup_of_le hlt le_rfl))))))
  rw [hself, sub_zero] at hle
  intro hbot
  rw [hbot] at hle
  exact litD_ne_bot α _ _ (le_bot_iff.1 hle)

theorem amortizedSc_eq (α : ℝ) (hα : α ≠ 0) {a b c d : ℕ} (ha : 1 ≤ a)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) :
    amortizedSuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
      litScA α (litAct Θ₁.memory Θ₁.pre Θ₁.post) (litAct Θ₂.memory Θ₂.pre Θ₂.post) := by
  unfold amortizedSuperchannelDivergence litScA
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨N, M, t, ht, rfl⟩
    rw [amortizedCh_eq] at ht
    rw [amortizedCh_eq]
    have hN : LibCPTP N.val := (Preparation.libraryCPTP_iff _).2 N.property
    have hM : LibCPTP M.val := (Preparation.libraryCPTP_iff _).2 M.property
    have hlt : litChA α N.val M.val < ⊤ := by rw [ht]; exact EReal.coe_lt_top t
    refine le_iSup_of_le N.val (le_iSup_of_le M.val (le_iSup_of_le hN (le_iSup_of_le hM
      (le_iSup_of_le hlt ?_))))
    rw [← ht]
    change litChA α (Θ₁.act N.val) (Θ₂.act M.val) - _ ≤ _
    rw [act_eq, act_eq]
  · refine iSup_le fun N => iSup_le fun M => iSup_le fun hN => iSup_le fun hM =>
      iSup_le fun hlt => ?_
    apply le_sSup
    have hne := litChA_ne_bot α hα ha N M
    obtain ⟨t, ht⟩ : ∃ t : ℝ, litChA α N M = (t : EReal) :=
      ⟨(litChA α N M).toReal, (EReal.coe_toReal hlt.ne hne).symm⟩
    refine ⟨⟨N, (Preparation.libraryCPTP_iff _).1 hN⟩, ⟨M, (Preparation.libraryCPTP_iff _).1 hM⟩,
      t, ?_, ?_⟩
    · rw [amortizedCh_eq]; exact ht
    · rw [amortizedCh_eq]
      change _ = litChA α (Θ₁.act N) (Θ₂.act M) - _
      rw [act_eq, act_eq, ht]

/-- The candidate statement is equivalent to the critic's literal transcription. -/
theorem main_iff : MainStatement ↔ CriticMain := by
  constructor
  · intro h a b c d ha hb hc hd α h1 h2 e₁ pre₁ post₁ e₂ pre₂ post₂ he₁ he₂ hp₁ hq₁ hp₂ hq₂
    have key := h a b c d ha hb hc hd α h1 h2
      ⟨e₁, he₁, pre₁, post₁, (Preparation.libraryCPTP_iff _).1 hp₁,
        (Preparation.libraryCPTP_iff _).1 hq₁⟩
      ⟨e₂, he₂, pre₂, post₂, (Preparation.libraryCPTP_iff _).1 hp₂,
        (Preparation.libraryCPTP_iff _).1 hq₂⟩
    rw [amortizedSc_eq α (by linarith) ha, ordinarySc_eq] at key
    exact key
  · intro h a b c d ha hb hc hd α h1 h2 Θ₁ Θ₂
    rw [amortizedSc_eq α (by linarith) ha, ordinarySc_eq]
    exact h a b c d ha hb hc hd α h1 h2 Θ₁.memory Θ₁.pre Θ₁.post Θ₂.memory Θ₂.pre Θ₂.post
      Θ₁.memory_pos Θ₂.memory_pos ((Preparation.libraryCPTP_iff _).2 Θ₁.pre_cptp)
      ((Preparation.libraryCPTP_iff _).2 Θ₁.post_cptp)
      ((Preparation.libraryCPTP_iff _).2 Θ₂.pre_cptp)
      ((Preparation.libraryCPTP_iff _).2 Θ₂.post_cptp)

end

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofLiteral
