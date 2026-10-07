import OpenQ.Foundations.Basic
import OpenQ.Problems.EqualWeightLowChoiRank_523ed7.ChannelCorrespondence
import OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.GeneralCircuit
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Operations

/-!
# Fixed-type geometric Rényi superchannel amortization

All matrices and maps are complex. The inserted channels always have type
`a → b`; only the state tests inside channel divergences have an external
reference. Finite subtracted costs are witnessed by real numbers. No truncation
of negative terms, and no subtraction of two infinities, occurs.

The generic operational extensions are applied to the concrete spectral state
divergence in `MainStatement`. Channel collapse is not a premise of that
statement. The comparison in `BasicBounds` keeps channel hypotheses explicit.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

open scoped BigOperators ComplexOrder Classical
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General
  (insertSlot insertSlot_isCPTP isCPTP_comp)

noncomputable section

abbrev Operator (n : Type) := Matrix n n ℂ
abbrev ChannelMap (a b : ℕ) := Operator (Fin a) →ₗ[ℂ] Operator (Fin b)

/-- Independently CPTP, rather than a positivity condition on a restricted
set of Choi matrices. Positive dimensions are imposed in `MainStatement`. -/
abbrev Channel (a b : ℕ) := {N : ChannelMap a b // IsCPTP N}

/-- A deterministic physical realization with an arbitrary positive finite
internal memory. The two members of a pair need not share a realization. -/
structure PhysicalSuperchannel (a b c d : ℕ) where
  memory : ℕ
  memory_pos : 0 < memory
  pre : ChannelMap c (a * memory)
  post : ChannelMap (b * memory) d
  pre_cptp : IsCPTP pre
  post_cptp : IsCPTP post

/-- Action on a complex-linear map, with slot-before-memory tensor order. -/
def PhysicalSuperchannel.act {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (N : ChannelMap a b) : ChannelMap c d :=
  Θ.post ∘ₗ insertSlot Θ.memory N ∘ₗ Θ.pre

/-- The realization extends complex linearly to the entire space of slot maps. -/
def PhysicalSuperchannel.actionLinear {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) : ChannelMap a b →ₗ[ℂ] ChannelMap c d where
  toFun := Θ.act
  map_add' N M := by
    ext X i j
    simp only [PhysicalSuperchannel.act, LinearMap.comp_apply,
      OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General.insertSlot_add,
      LinearMap.add_apply, map_add, Matrix.add_apply]
  map_smul' z N := by
    ext X i j
    simp only [PhysicalSuperchannel.act, LinearMap.comp_apply,
      OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General.insertSlot_smul,
      LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem PhysicalSuperchannel.act_isCPTP {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (N : ChannelMap a b) (hN : IsCPTP N) :
    IsCPTP (Θ.act N) := by
  exact isCPTP_comp (isCPTP_comp Θ.pre_cptp (insertSlot_isCPTP N hN)) Θ.post_cptp

/-- The operational action only ever receives fixed-type CPTP channels. -/
def PhysicalSuperchannel.onChannel {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (N : Channel a b) : Channel c d :=
  ⟨Θ.act N.val, Θ.act_isCPTP N.val N.property⟩

/-- A support test on the actual ranges of the complex matrix operators. -/
def RangeIncluded {n : Type} [Fintype n] (ρ σ : Operator n) : Prop :=
  Set.range (fun v : n → ℂ => ρ.mulVec v) ⊆
    Set.range (fun v : n → ℂ => σ.mulVec v)

/-- Hermitian spectral calculus, namely `U diag(f(λ_i)) Uᴴ`.
The total extension outside the Hermitian domain is unused on physical states. -/
def hermitianSpectralFunction {n : Type} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (X : Operator n) : Operator n :=
  if hX : X.IsHermitian then hX.cfc f else 0

theorem hermitianSpectralFunction_of_isHermitian {n : Type}
    [Fintype n] [DecidableEq n] (f : ℝ → ℝ) (X : Operator n)
    (hX : X.IsHermitian) : hermitianSpectralFunction f X = hX.cfc f := by
  simp only [hermitianSpectralFunction, dite_eq_left hX]

theorem hermitianSpectralFunction_isHermitian {n : Type}
    [Fintype n] [DecidableEq n] (f : ℝ → ℝ) (X : Operator n) :
    (hermitianSpectralFunction f X).IsHermitian := by
  by_cases hX : X.IsHermitian
  · rw [hermitianSpectralFunction_of_isHermitian f X hX, ← hX.cfc_eq]
    exact cfc_predicate f X
  · simpa only [hermitianSpectralFunction, dite_eq_right hX] using
      (Matrix.isHermitian_zero : (0 : Operator n).IsHermitian)

/-- Zero on a zero eigenvalue; reciprocal square root on a positive one. -/
def supportInvSqrtScalar (x : ℝ) : ℝ :=
  if x = 0 then 0 else (Real.sqrt x)⁻¹

@[simp] theorem supportInvSqrtScalar_zero : supportInvSqrtScalar 0 = 0 := by
  simp [supportInvSqrtScalar]

/-- The inverse square root on the support, extended by zero on the kernel.
This is a spectral operation, not the total matrix inverse. -/
def supportInvSqrt {n : Type} [Fintype n] [DecidableEq n]
    (σ : Operator n) : Operator n :=
  hermitianSpectralFunction supportInvSqrtScalar σ

/-- Real Hermitian spectral powers; on PSD matrices this is the usual power. -/
def hermitianPower {n : Type} [Fintype n] [DecidableEq n]
    (X : Operator n) (α : ℝ) : Operator n :=
  hermitianSpectralFunction (fun x => Real.rpow x α) X

/-- The sandwich used in the geometric moment is PSD, even for singular σ.
In particular the non-Hermitian fallback of its spectral power is unused. -/
theorem support_sandwich_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Operator n) (hρ : ρ.PosSemidef) :
    (supportInvSqrt σ * ρ * supportInvSqrt σ).PosSemidef := by
  have hS := hermitianSpectralFunction_isHermitian supportInvSqrtScalar σ
  simpa only [supportInvSqrt, hS.eq] using
    hρ.mul_mul_conjTranspose_same (hermitianSpectralFunction supportInvSqrtScalar σ)

def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- A matrix-family interface for operational extensions. Only density
matrices are tested by those extensions. -/
abbrev StateDivergence :=
  ∀ (n : Type) [Fintype n] [DecidableEq n], Operator n → Operator n → EReal

/-- The concrete geometric moment, with the denominator perspective orientation.
The trace is real for PSD state arguments, and `.re` reads that real scalar. -/
def geometricMoment {n : Type} [Fintype n] [DecidableEq n]
    (α : ℝ) (ρ σ : Operator n) : ℝ :=
  (Matrix.trace (σ * hermitianPower
    (supportInvSqrt σ * ρ * supportInvSqrt σ) α)).re

/-- Taking the real part in the definition does not change the trace scalar
on Hermitian denominators, and hence on every density-matrix pair. -/
theorem geometricMoment_trace_eq_real {n : Type} [Fintype n] [DecidableEq n]
    (α : ℝ) (ρ σ : Operator n) (hσ : σ.IsHermitian) :
    (geometricMoment α ρ σ : ℂ) = Matrix.trace (σ * hermitianPower
      (supportInvSqrt σ * ρ * supportInvSqrt σ) α) := by
  let P := hermitianPower (supportInvSqrt σ * ρ * supportInvSqrt σ) α
  have hP : P.IsHermitian := hermitianSpectralFunction_isHermitian _ _
  have htr : star (Matrix.trace (σ * P)) = Matrix.trace (σ * P) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hP.eq, hσ.eq, Matrix.trace_mul_comm]
  have him := congrArg Complex.im htr
  simp only [Complex.star_def, Complex.conj_im] at him
  have him0 : (Matrix.trace (σ * P)).im = 0 := by linarith
  apply Complex.ext
  · rfl
  · exact him0.symm

/-- Geometric Rényi state divergence. Its intended domain is normalized PSD
states and `1 < α ≤ 2`; unsupported pairs have value `+∞`. -/
def geometricStateDivergence (α : ℝ) : StateDivergence :=
  fun _ _ _ ρ σ =>
    if RangeIncluded ρ σ then
      ((log₂ (geometricMoment α ρ σ) / (α - 1) : ℝ) : EReal)
    else ⊤

theorem geometricStateDivergence_unsupported {n : Type}
    [Fintype n] [DecidableEq n] (α : ℝ) (ρ σ : Operator n)
    (h : ¬ RangeIncluded ρ σ) : geometricStateDivergence α n ρ σ = ⊤ := by
  simp only [geometricStateDivergence, ite_eq_right h]

/-- Complete trace preservation on the external-reference state space. -/
theorem amplification_trace {a b r : ℕ} (N : ChannelMap a b) (hN : IsCPTP N)
    (ρ : Operator (Fin r × Fin a)) :
    Matrix.trace (amplification r N ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun s _ => hN.2 (fun i j => ρ (s, i) (s, j)))

theorem amplification_isDensityMatrix {a b r : ℕ} (N : Channel a b)
    (hr : 0 < r) (ρ : Operator (Fin r × Fin a)) (hρ : OpenQ.IsDensityMatrix ρ) :
    OpenQ.IsDensityMatrix (amplification r N.val ρ) := by
  exact ⟨N.property.1 r hr ρ hρ.1, (amplification_trace N.val N.property ρ).trans hρ.2⟩

/-- Ordinary channel divergence, with every positive finite external reference. -/
def ordinaryChannelDivergence (D : StateDivergence) {a b : ℕ}
    (N M : Channel a b) : EReal :=
  sSup {v : EReal | ∃ (r : ℕ) (_hr : 0 < r)
    (ρ : Operator (Fin r × Fin a)), OpenQ.IsDensityMatrix ρ ∧
      v = D (Fin r × Fin b) (amplification r N.val ρ) (amplification r M.val ρ)}

/-- Channel amortization. An explicit real witness is the entire subtracted
state cost, excluding both infinite values without discarding negative terms. -/
def amortizedChannelDivergence (D : StateDivergence) {a b : ℕ}
    (N M : Channel a b) : EReal :=
  sSup {v : EReal | ∃ (r : ℕ) (_hr : 0 < r)
    (ρ σ : Operator (Fin r × Fin a)),
      OpenQ.IsDensityMatrix ρ ∧ OpenQ.IsDensityMatrix σ ∧
      ∃ t : ℝ, D (Fin r × Fin a) ρ σ = (t : EReal) ∧
        v = D (Fin r × Fin b) (amplification r N.val ρ)
          (amplification r M.val σ) - (t : EReal)}

/-- Ordinary fixed-type superchannel divergence. Only the physical action on
inserted CPTP maps occurs, and the memory is never an optimization variable. -/
def ordinarySuperchannelDivergence (D : StateDivergence) {a b c d : ℕ}
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : EReal :=
  sSup {v : EReal | ∃ N : Channel a b,
    v = ordinaryChannelDivergence D (Θ₁.onChannel N) (Θ₂.onChannel N)}

/-- Nested superchannel amortization, with finite input channel-amortized
cost. Inserted channels are still exactly `a → b`, with no inserted reference. -/
def amortizedSuperchannelDivergence (D : StateDivergence) {a b c d : ℕ}
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : EReal :=
  sSup {v : EReal | ∃ (N M : Channel a b) (t : ℝ),
    amortizedChannelDivergence D N M = (t : EReal) ∧
      v = amortizedChannelDivergence D (Θ₁.onChannel N) (Θ₂.onChannel M) - (t : EReal)}

/-- Realizations with identical CPTP-slot actions give the same ordinary value. -/
theorem ordinarySuperchannelDivergence_congr (D : StateDivergence) {a b c d : ℕ}
    (Θ₁ Θ₂ Ξ₁ Ξ₂ : PhysicalSuperchannel a b c d)
    (h₁ : ∀ (N : ChannelMap a b), IsCPTP N → Θ₁.act N = Ξ₁.act N)
    (h₂ : ∀ (N : ChannelMap a b), IsCPTP N → Θ₂.act N = Ξ₂.act N) :
    ordinarySuperchannelDivergence D Θ₁ Θ₂ = ordinarySuperchannelDivergence D Ξ₁ Ξ₂ := by
  have H₁ : Θ₁.onChannel = Ξ₁.onChannel :=
    funext (fun N => Subtype.ext (h₁ N.val N.property))
  have H₂ : Θ₂.onChannel = Ξ₂.onChannel :=
    funext (fun N => Subtype.ext (h₂ N.val N.property))
  simp only [ordinarySuperchannelDivergence, H₁, H₂]

/-- Realizations with identical CPTP-slot actions also give the same nested value. -/
theorem amortizedSuperchannelDivergence_congr (D : StateDivergence) {a b c d : ℕ}
    (Θ₁ Θ₂ Ξ₁ Ξ₂ : PhysicalSuperchannel a b c d)
    (h₁ : ∀ (N : ChannelMap a b), IsCPTP N → Θ₁.act N = Ξ₁.act N)
    (h₂ : ∀ (N : ChannelMap a b), IsCPTP N → Θ₂.act N = Ξ₂.act N) :
    amortizedSuperchannelDivergence D Θ₁ Θ₂ = amortizedSuperchannelDivergence D Ξ₁ Ξ₂ := by
  have H₁ : Θ₁.onChannel = Ξ₁.onChannel :=
    funext (fun N => Subtype.ext (h₁ N.val N.property))
  have H₂ : Θ₂.onChannel = Ξ₂.onChannel :=
    funext (fun N => Subtype.ext (h₂ N.val N.property))
  simp only [amortizedSuperchannelDivergence, H₁, H₂]

/-- The exact fixed-type geometric Rényi conjecture, including singular
supports and extended values, at the same real order in every term. -/
def MainStatement : Prop :=
  ∀ (a b c d : ℕ), 0 < a → 0 < b → 0 < c → 0 < d →
    ∀ (α : ℝ), 1 < α → α ≤ 2 →
      ∀ (Θ₁ Θ₂ : PhysicalSuperchannel a b c d),
        amortizedSuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂ =
          ordinarySuperchannelDivergence (geometricStateDivergence α) Θ₁ Θ₂

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
