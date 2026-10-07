import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofLiteral

/-!
Critic scratch (amortization problem, e001-i01). End-to-end checks of the operational suprema of the candidate statement.

* `main_dim_one`: the instance `a = b = c = d = 1` of `MainStatement` holds, both
  sides being 0. It uses only `D(τ‖τ) = 0` on states, so it tests the `EReal`
  plumbing (non-empty value sets, real witnesses, subtraction).
* `self_normalization_geometric`: hypothesis (1) of the conditional lemma
  `ordinary_sc_le_amortized_sc` holds for the concrete geometric divergence.
* `ordinaryCh_le_amortizedCh_geometric`: `D_ch ≤ D_ch^A` for the geometric
  divergence, without any collapse hypothesis.
* `ordinary_sc_le_amortized_sc_weak`: the diagonal lower bound from the two
  weaker hypotheses `D_ch^A(N‖N) = 0` and `D_ch ≤ D_ch^A` at the output type,
  hence for the geometric divergence from `D_ch^A(N‖N) = 0` alone.
* `control_constant_divergence`: for the constant divergence `D ≡ 1` the
  conclusion of the conditional lemma fails in dimension one, so its hypotheses
  cannot all be dropped.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofTrivial

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofLiteral
open scoped ComplexOrder

noncomputable section

theorem amplification_id (r a : ℕ) (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    amplification r (LinearMap.id : ChannelMap a a) ρ = ρ := by
  ext ⟨s, β⟩ ⟨t, γ⟩
  rfl

/-- The only channel on a one-dimensional system is the identity. -/
theorem channel_one_eq_id (N : Channel 1 1) : N.val = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext i j
  fin_cases i
  fin_cases j
  have h := N.property.2 X
  simp only [Matrix.trace_fin_one] at h
  simpa using h

theorem exists_density {a : ℕ} (ha : 1 ≤ a) :
    ∃ τ : Matrix (Fin 1 × Fin a) (Fin 1 × Fin a) ℂ, OpenQ.IsDensityMatrix τ :=
  exists_state ha

section generic

variable (D : StateDivergence)

/-- Self-normalised state divergences give `D_ch(N‖N) = 0`. -/
theorem ordinaryCh_self {a b : ℕ} (ha : 1 ≤ a)
    (hD : ∀ (r : ℕ) (τ : Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ),
      OpenQ.IsDensityMatrix τ → D (Fin r × Fin b) τ τ = 0)
    (N : Channel a b) : ordinaryChannelDivergence D N N = 0 := by
  unfold ordinaryChannelDivergence
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨r, hr, ρ, hρ, rfl⟩
    rw [hD r _ (amplification_isDensityMatrix N hr ρ hρ)]
  · apply le_sSup
    obtain ⟨τ, hτ⟩ := exists_density ha
    exact ⟨1, Nat.one_pos, τ, hτ,
      (hD 1 _ (amplification_isDensityMatrix N Nat.one_pos τ hτ)).symm⟩

/-- `D_ch ≤ D_ch^A` for any state divergence that vanishes on equal states. -/
theorem ordinaryCh_le_amortizedCh {a b : ℕ}
    (hD : ∀ (r : ℕ) (τ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ),
      OpenQ.IsDensityMatrix τ → D (Fin r × Fin a) τ τ = 0)
    (N M : Channel a b) :
    ordinaryChannelDivergence D N M ≤ amortizedChannelDivergence D N M := by
  unfold ordinaryChannelDivergence amortizedChannelDivergence
  apply sSup_le
  rintro v ⟨r, hr, ρ, hρ, rfl⟩
  apply le_sSup
  refine ⟨r, hr, ρ, ρ, hρ, hρ, 0, ?_, ?_⟩
  · rw [hD r ρ hρ, EReal.coe_zero]
  · rw [EReal.coe_zero, sub_zero]

/-- The diagonal lower bound from weaker hypotheses than full channel collapse. -/
theorem ordinary_sc_le_amortized_sc_weak {a b c d : ℕ}
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (h1 : ∀ N : Channel a b, amortizedChannelDivergence D N N = 0)
    (h2 : ∀ P Q : Channel c d,
      ordinaryChannelDivergence D P Q ≤ amortizedChannelDivergence D P Q) :
    ordinarySuperchannelDivergence D Θ₁ Θ₂ ≤ amortizedSuperchannelDivergence D Θ₁ Θ₂ := by
  apply sSup_le
  rintro v ⟨N, rfl⟩
  refine le_trans (h2 _ _) ?_
  apply le_sSup
  refine ⟨N, N, 0, ?_, ?_⟩
  · rw [h1, EReal.coe_zero]
  · rw [EReal.coe_zero, sub_zero]

end generic

/-- Hypothesis (1) of the registered conditional lemma, for the geometric divergence. -/
theorem self_normalization_geometric (α : ℝ) (hα : α ≠ 0) {a b : ℕ} (ha : 1 ≤ a)
    (N : Channel a b) :
    ordinaryChannelDivergence (geometricStateDivergence α) N N = 0 :=
  ordinaryCh_self _ ha (fun _ _ hτ => geometricStateDivergence_self hτ α hα) N

theorem ordinaryCh_le_amortizedCh_geometric (α : ℝ) (hα : α ≠ 0) {a b : ℕ}
    (N M : Channel a b) :
    ordinaryChannelDivergence (geometricStateDivergence α) N M ≤
      amortizedChannelDivergence (geometricStateDivergence α) N M :=
  ordinaryCh_le_amortizedCh _ (fun _ _ hτ => geometricStateDivergence_self hτ α hα) N M

/-- For the geometric divergence the diagonal lower bound needs only `D_ch^A(N‖N) = 0`. -/
theorem geometric_lower_bound_of_dataProcessing (α : ℝ) (hα : α ≠ 0) {a b c d : ℕ}
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (h1 : ∀ N : Channel a b,
      amortizedChannelDivergence (geometricStateDivergence α) N N = 0) :
    ordinarySuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ ≤
      amortizedSuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ :=
  ordinary_sc_le_amortized_sc_weak _ Θ₁ Θ₂ h1
    (fun P Q => ordinaryCh_le_amortizedCh_geometric α hα P Q)

/-! ### Dimension one -/

def idChannel : Channel 1 1 :=
  ⟨LinearMap.id, (Preparation.libraryCPTP_iff _).1 (Preparation.LibraryCPTP.id (Fin 1))⟩

theorem channel_one_eq (N : Channel 1 1) : N = idChannel :=
  Subtype.ext (channel_one_eq_id N)

/-- A physical superchannel exists in dimension one (memory one, identity teeth). -/
def trivialSuperchannel : PhysicalSuperchannel 1 1 1 1 where
  memory := 1
  memory_pos := Nat.one_pos
  pre := (LinearMap.id : ChannelMap 1 1)
  post := (LinearMap.id : ChannelMap 1 1)
  pre_cptp := idChannel.property
  post_cptp := idChannel.property

theorem ordinaryCh_one (D : StateDivergence)
    (hD : ∀ (r : ℕ) (τ : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ),
      OpenQ.IsDensityMatrix τ → D (Fin r × Fin 1) τ τ = 0)
    (N M : Channel 1 1) : ordinaryChannelDivergence D N M = 0 := by
  rw [channel_one_eq N, channel_one_eq M]
  exact ordinaryCh_self D le_rfl hD idChannel

theorem amortizedCh_one (D : StateDivergence)
    (hD : ∀ (r : ℕ) (τ : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ),
      OpenQ.IsDensityMatrix τ → D (Fin r × Fin 1) τ τ = 0)
    (N M : Channel 1 1) : amortizedChannelDivergence D N M = 0 := by
  rw [channel_one_eq N, channel_one_eq M]
  unfold amortizedChannelDivergence
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨r, hr, ρ, σ, hρ, hσ, t, ht, rfl⟩
    have e1 : amplification r idChannel.val ρ = ρ := amplification_id r 1 ρ
    have e2 : amplification r idChannel.val σ = σ := amplification_id r 1 σ
    rw [e1, e2, ht, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  · apply le_sSup
    obtain ⟨τ, hτ⟩ := exists_density (le_refl 1)
    refine ⟨1, Nat.one_pos, τ, τ, hτ, hτ, 0, ?_, ?_⟩
    · rw [hD 1 τ hτ, EReal.coe_zero]
    · have e1 : amplification 1 idChannel.val τ = τ := amplification_id 1 1 τ
      rw [e1, hD 1 τ hτ, EReal.coe_zero, sub_zero]

/-- Both superchannel quantities vanish in dimension one, for every pair. -/
theorem sc_dim_one (D : StateDivergence)
    (hD : ∀ (r : ℕ) (τ : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ),
      OpenQ.IsDensityMatrix τ → D (Fin r × Fin 1) τ τ = 0)
    (Θ₁ Θ₂ : PhysicalSuperchannel 1 1 1 1) :
    amortizedSuperchannelDivergence D Θ₁ Θ₂ = 0 ∧
      ordinarySuperchannelDivergence D Θ₁ Θ₂ = 0 := by
  constructor
  · unfold amortizedSuperchannelDivergence
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨N, M, t, ht, rfl⟩
      rw [amortizedCh_one D hD] at ht
      rw [amortizedCh_one D hD, ← ht, sub_zero]
    · apply le_sSup
      refine ⟨idChannel, idChannel, 0, ?_, ?_⟩
      · rw [amortizedCh_one D hD, EReal.coe_zero]
      · rw [amortizedCh_one D hD, EReal.coe_zero, sub_zero]
  · unfold ordinarySuperchannelDivergence
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨N, rfl⟩
      rw [ordinaryCh_one D hD]
    · apply le_sSup
      exact ⟨idChannel, (ordinaryCh_one D hD _ _).symm⟩

/-- The instance `a = b = c = d = 1` of the candidate statement is true. -/
theorem main_dim_one (α : ℝ) (h1 : 1 < α) (_h2 : α ≤ 2)
    (Θ₁ Θ₂ : PhysicalSuperchannel 1 1 1 1) :
    amortizedSuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
      ordinarySuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ := by
  have hD : ∀ (r : ℕ) (τ : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ),
      OpenQ.IsDensityMatrix τ → geometricStateDivergence α (Fin r × Fin 1) τ τ = 0 :=
    fun _ _ hτ => geometricStateDivergence_self hτ α (by linarith)
  obtain ⟨hA, hO⟩ := sc_dim_one (geometricStateDivergence α) hD Θ₁ Θ₂
  rw [hA, hO]

/-- The quantifier over superchannels is not empty in dimension one. -/
theorem main_dim_one_nonvacuous (α : ℝ) (h1 : 1 < α) (_h2 : α ≤ 2) :
    amortizedSuperchannelDivergence (geometricStateDivergence α) trivialSuperchannel
        trivialSuperchannel = 0 ∧
      ordinarySuperchannelDivergence (geometricStateDivergence α) trivialSuperchannel
        trivialSuperchannel = 0 :=
  sc_dim_one (geometricStateDivergence α)
    (fun _ _ hτ => geometricStateDivergence_self hτ α (by linarith)) _ _

/-! ### Control: the constant divergence `D ≡ 1` -/

def constOne : StateDivergence := fun _ _ _ _ _ => 1

theorem control_constant_divergence :
    ¬ (ordinarySuperchannelDivergence constOne trivialSuperchannel trivialSuperchannel ≤
      amortizedSuperchannelDivergence constOne trivialSuperchannel trivialSuperchannel) := by
  have hO : ∀ N M : Channel 1 1, ordinaryChannelDivergence constOne N M = 1 := by
    intro N M
    unfold ordinaryChannelDivergence
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨r, hr, ρ, hρ, rfl⟩
      exact le_rfl
    · apply le_sSup
      obtain ⟨τ, hτ⟩ := exists_density (le_refl 1)
      exact ⟨1, Nat.one_pos, τ, hτ, rfl⟩
  have h11 : (1 : EReal) - 1 = 0 := by
    rw [← EReal.coe_one, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  have hA : ∀ N M : Channel 1 1, amortizedChannelDivergence constOne N M = 0 := by
    intro N M
    unfold amortizedChannelDivergence
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨r, hr, ρ, σ, hρ, hσ, t, ht, rfl⟩
      change (1 : EReal) = (t : EReal) at ht
      change (1 : EReal) - (t : EReal) ≤ 0
      rw [← ht, h11]
    · apply le_sSup
      obtain ⟨τ, hτ⟩ := exists_density (le_refl 1)
      refine ⟨1, Nat.one_pos, τ, τ, hτ, hτ, 1, rfl, ?_⟩
      change (0 : EReal) = (1 : EReal) - ((1 : ℝ) : EReal)
      rw [EReal.coe_one, h11]
  have hSO : ordinarySuperchannelDivergence constOne trivialSuperchannel trivialSuperchannel = 1 := by
    unfold ordinarySuperchannelDivergence
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨N, rfl⟩
      rw [hO]
    · apply le_sSup
      exact ⟨idChannel, (hO _ _).symm⟩
  have hSA : amortizedSuperchannelDivergence constOne trivialSuperchannel trivialSuperchannel = 0 := by
    unfold amortizedSuperchannelDivergence
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨N, M, t, ht, rfl⟩
      rw [hA] at ht
      rw [hA, ← ht, sub_zero]
    · apply le_sSup
      refine ⟨idChannel, idChannel, 0, ?_, ?_⟩
      · rw [hA, EReal.coe_zero]
      · rw [hA, EReal.coe_zero, sub_zero]
  rw [hSO, hSA]
  norm_num

end

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofTrivial
