/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticAlphaE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
Critic scratch (amortization problem, e002-i02). Side probe after the review, not part
of the research record.

Order-`α` perspective `G_α(X, Y) = Y^{1/2} (Y^{-1/2} X Y^{-1/2})^α Y^{1/2}` on the locked
definitions (support inverse square root, locked spectral power), for supported pairs with
singular `Y` allowed, and its transformer inequality for `1 < α < 2` from the order-two
case: by the integral representation of `x ^ α` the quadratic forms of `G_α(X, Y)` are
integrals of the quadratic forms of the order-two perspectives `X (X + tY)⁺ X`, whose
denominators always support `X`.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlpha

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation
  (exists_spectral hsf_kronecker)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannelValue
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel (nonneg_eq_ofReal)
open scoped ComplexOrder Kronecker Matrix

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### The square root on the support -/

/-- `Y^{1/2}` as `Y · Y^{+1/2}`. -/
def sqrtS (Y : Matrix n n ℂ) : Matrix n n ℂ := Y * supportInvSqrt Y

theorem S_comm {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    supportInvSqrt Y * Y = Y * supportInvSqrt Y := by
  have hid := cfc_id_eq hY.1
  calc supportInvSqrt Y * Y = cfc supportInvSqrtScalar Y * cfc (fun x : ℝ => x) Y := by
        rw [hid, supportInvSqrt_eq_cfc]
    _ = cfc (fun x : ℝ => supportInvSqrtScalar x * x) Y := by rw [cfc_mul2]
    _ = cfc (fun x : ℝ => x * supportInvSqrtScalar x) Y := by
        apply cfc_congr
        intro x _
        exact mul_comm _ _
    _ = cfc (fun x : ℝ => x) Y * cfc supportInvSqrtScalar Y := by rw [cfc_mul2]
    _ = Y * supportInvSqrt Y := by rw [hid, supportInvSqrt_eq_cfc]

theorem S_herm (Y : Matrix n n ℂ) : (supportInvSqrt Y).IsHermitian :=
  (supportInvSqrt_posSemidef Y).1

theorem sqrtS_herm {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : (sqrtS Y).IsHermitian := by
  rw [Matrix.IsHermitian, sqrtS, Matrix.conjTranspose_mul, (S_herm Y).eq, hY.1.eq, S_comm hY]

theorem sqrtS_sq {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : sqrtS Y * sqrtS Y = Y := by
  calc sqrtS Y * sqrtS Y = Y * supportInvSqrt Y * (supportInvSqrt Y * Y) := by
        rw [sqrtS, S_comm hY]
    _ = Y * pinv Y * Y := by unfold pinv; simp only [Matrix.mul_assoc]
    _ = Y := penrose1 hY

/-- The support projector `Y Y⁺`. -/
def suppP (Y : Matrix n n ℂ) : Matrix n n ℂ := Y * pinv Y

theorem suppP_herm {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : (suppP Y).IsHermitian :=
  penrose3 hY

theorem sqrtS_mul_S (Y : Matrix n n ℂ) : sqrtS Y * supportInvSqrt Y = suppP Y := by
  unfold sqrtS suppP pinv
  rw [Matrix.mul_assoc]

theorem S_mul_sqrtS {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    supportInvSqrt Y * sqrtS Y = suppP Y := by
  unfold sqrtS suppP
  rw [← Matrix.mul_assoc, sandwich_eq_supp hY]

theorem S_mul_suppP {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    supportInvSqrt Y * suppP Y = supportInvSqrt Y := by
  unfold suppP
  rw [mul_pinv_eq_cfc hY, supportInvSqrt_eq_cfc, cfc_mul2]
  apply cfc_congr
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]

theorem suppP_mul_S {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    suppP Y * supportInvSqrt Y = supportInvSqrt Y := by
  have h := congrArg Matrix.conjTranspose (S_mul_suppP hY)
  rwa [Matrix.conjTranspose_mul, (S_herm Y).eq, (suppP_herm hY).eq] at h

theorem suppP_mul_sqrtS {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : suppP Y * sqrtS Y = sqrtS Y := by
  unfold suppP sqrtS
  rw [← Matrix.mul_assoc, penrose1 hY]

theorem sqrtS_mul_suppP {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : sqrtS Y * suppP Y = sqrtS Y := by
  have h := congrArg Matrix.conjTranspose (suppP_mul_sqrtS hY)
  rwa [Matrix.conjTranspose_mul, (sqrtS_herm hY).eq, (suppP_herm hY).eq] at h

theorem suppP_mul_of_supp {X Y : Matrix n n ℂ} (hY : Y.PosSemidef) (hR : RangeIncluded X Y) :
    suppP Y * X = X := supp_mul_of_rangeIncluded hY hR

theorem mul_suppP_of_supp {X Y : Matrix n n ℂ} (hY : Y.PosSemidef) (hX : X.IsHermitian)
    (hR : RangeIncluded X Y) : X * suppP Y = X := by
  have h := congrArg Matrix.conjTranspose (suppP_mul_of_supp hY hR)
  rwa [Matrix.conjTranspose_mul, hX.eq, (suppP_herm hY).eq] at h

/-- The sandwich `A = S X S`. -/
def sand (X Y : Matrix n n ℂ) : Matrix n n ℂ := supportInvSqrt Y * X * supportInvSqrt Y

theorem sand_psd {X : Matrix n n ℂ} (Y : Matrix n n ℂ) (hX : X.PosSemidef) : (sand X Y).PosSemidef :=
  support_sandwich_posSemidef X Y hX

theorem sqrtS_sand_sqrtS {X Y : Matrix n n ℂ} (hY : Y.PosSemidef) (hX : X.IsHermitian)
    (hR : RangeIncluded X Y) : sqrtS Y * sand X Y * sqrtS Y = X := by
  calc sqrtS Y * sand X Y * sqrtS Y
      = (sqrtS Y * supportInvSqrt Y) * X * (supportInvSqrt Y * sqrtS Y) := by
        unfold sand; simp only [Matrix.mul_assoc]
    _ = X := by
        rw [sqrtS_mul_S, S_mul_sqrtS hY, suppP_mul_of_supp hY hR, mul_suppP_of_supp hY hX hR]

theorem suppP_mul_sand {X Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    suppP Y * sand X Y = sand X Y := by
  unfold sand
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, suppP_mul_S hY]

theorem sand_mul_suppP {X Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    sand X Y * suppP Y = sand X Y := by
  unfold sand
  rw [Matrix.mul_assoc, S_mul_suppP hY]

/-! ### The order-`α` perspective -/

/-- `G_α(X, Y) = Y^{1/2} (S X S)^α Y^{1/2}` with the locked spectral power. -/
def Gp (α : ℝ) (X Y : Matrix n n ℂ) : Matrix n n ℂ :=
  sqrtS Y * hermitianPower (sand X Y) α * sqrtS Y

theorem Gp_psd (α : ℝ) {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (Gp α X Y).PosSemidef := by
  have h := (ProofOrthogonal.hermitianPower_posSemidef (sand_psd Y hX) α).mul_mul_conjTranspose_same
    (sqrtS Y)
  rwa [(sqrtS_herm hY).eq] at h

/-- The locked moment is the trace of the perspective. -/
theorem moment_eq_trace (α : ℝ) (X : Matrix n n ℂ) {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    geometricMoment α X Y = (Matrix.trace (Gp α X Y)).re := by
  have h : Matrix.trace (sqrtS Y * hermitianPower (sand X Y) α * sqrtS Y) =
      Matrix.trace (Y * hermitianPower (sand X Y) α) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, sqrtS_sq hY]
  unfold geometricMoment Gp
  rw [h]
  rfl

/-- At order two the perspective is `X Y⁺ X` on supported pairs. -/
theorem Gp_two {X Y : Matrix n n ℂ} (hY : Y.PosSemidef) (hX : X.IsHermitian)
    (hR : RangeIncluded X Y) : Gp 2 X Y = X * pinv Y * X := by
  have hA : (sand X Y).IsHermitian := by
    have := Matrix.isHermitian_mul_mul_conjTranspose (supportInvSqrt Y) hX
    rwa [(S_herm Y).eq] at this
  unfold Gp
  rw [hermitianPower_two hA]
  calc sqrtS Y * (sand X Y * sand X Y) * sqrtS Y
      = (sqrtS Y * supportInvSqrt Y) * X * (supportInvSqrt Y * supportInvSqrt Y) * X *
          (supportInvSqrt Y * sqrtS Y) := by
        unfold sand; simp only [Matrix.mul_assoc]
    _ = X * pinv Y * X := by
        rw [sqrtS_mul_S, S_mul_sqrtS hY, suppP_mul_of_supp hY hR]
        unfold pinv
        rw [Matrix.mul_assoc, mul_suppP_of_supp hY hX hR]

/-! ### Order-two perspectives with denominator `X + t Y` -/

/-- `X` is always supported in `X + t Y`. -/
theorem rangeIncluded_add_smul {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) : RangeIncluded X (X + (t : ℂ) • Y) := by
  have hY' : ((t : ℂ) • Y).PosSemidef := hY.smul (Complex.zero_le_real.2 ht)
  rw [rangeIncluded_iff_ker hX.1 (hX.add hY')]
  intro v hv
  have h0 : star v ⬝ᵥ (X + (t : ℂ) • Y).mulVec v = 0 := by rw [hv, dotProduct_zero]
  rw [Matrix.add_mulVec, dotProduct_add] at h0
  have p1 := hX.dotProduct_mulVec_nonneg v
  have p2 := hY'.dotProduct_mulVec_nonneg v
  have h1 := (add_eq_zero_iff_of_nonneg p1 p2).1 h0
  exact hX.dotProduct_mulVec_zero_iff.1 h1.1

theorem shift_posDef {A : Matrix n n ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul (Complex.zero_lt_real.2 ht))

theorem shift_mul_inv {A : Matrix n n ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • (1 : Matrix n n ℂ)) * (A + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (shift_posDef hA ht).isUnit)

theorem shift_inv_mul {A : Matrix n n ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * (A + (t : ℂ) • (1 : Matrix n n ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (shift_posDef hA ht).isUnit)

/-- `X + t Y = Y^{1/2} (A + t) Y^{1/2}` on supported pairs. -/
theorem add_smul_eq {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hR : RangeIncluded X Y) (t : ℝ) :
    X + (t : ℂ) • Y = sqrtS Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ)) * sqrtS Y := by
  rw [Matrix.mul_add, Matrix.add_mul, sqrtS_sand_sqrtS hY hX.1 hR, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, sqrtS_sq hY]

/-- The support inverse of `X + t Y`. -/
theorem pinv_add_smul {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hR : RangeIncluded X Y) {t : ℝ} (ht : 0 < t) :
    pinv (X + (t : ℂ) • Y) =
      supportInvSqrt Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * supportInvSqrt Y := by
  have hA := sand_psd Y hX
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix n n ℂ, B = (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix n n ℂ, M = sand X Y + (t : ℂ) • (1 : Matrix n n ℂ) := ⟨_, rfl⟩
  rw [← hBdef]
  have hB1 : M * B = 1 := by rw [hMdef, hBdef]; exact shift_mul_inv hA ht
  have hB2 : B * M = 1 := by rw [hMdef, hBdef]; exact shift_inv_mul hA ht
  have hN : X + (t : ℂ) • Y = sqrtS Y * M * sqrtS Y := by rw [hMdef]; exact add_smul_eq hX hY hR t
  have hPM : suppP Y * M = M * suppP Y := by
    rw [hMdef, Matrix.mul_add, Matrix.add_mul, suppP_mul_sand hY, sand_mul_suppP hY,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hPB : suppP Y * B = B * suppP Y := by
    calc suppP Y * B = (B * M) * suppP Y * B := by rw [hB2, Matrix.one_mul]
      _ = B * (suppP Y * M) * B := by rw [hPM]; simp only [Matrix.mul_assoc]
      _ = B * suppP Y * (M * B) := by simp only [Matrix.mul_assoc]
      _ = B * suppP Y := by rw [hB1, Matrix.mul_one]
  have hNZ : (X + (t : ℂ) • Y) * (supportInvSqrt Y * B * supportInvSqrt Y) = suppP Y := by
    rw [hN]
    calc sqrtS Y * M * sqrtS Y * (supportInvSqrt Y * B * supportInvSqrt Y)
        = sqrtS Y * M * ((sqrtS Y * supportInvSqrt Y) * B) * supportInvSqrt Y := by
          simp only [Matrix.mul_assoc]
      _ = sqrtS Y * (M * B) * (suppP Y * supportInvSqrt Y) := by
          rw [sqrtS_mul_S, hPB]; simp only [Matrix.mul_assoc]
      _ = suppP Y := by rw [hB1, Matrix.mul_one, suppP_mul_S hY, sqrtS_mul_S]
  have hZN : (supportInvSqrt Y * B * supportInvSqrt Y) * (X + (t : ℂ) • Y) = suppP Y := by
    rw [hN]
    calc supportInvSqrt Y * B * supportInvSqrt Y * (sqrtS Y * M * sqrtS Y)
        = supportInvSqrt Y * (B * (supportInvSqrt Y * sqrtS Y)) * M * sqrtS Y := by
          simp only [Matrix.mul_assoc]
      _ = (supportInvSqrt Y * suppP Y) * (B * M) * sqrtS Y := by
          rw [S_mul_sqrtS hY, ← hPB]; simp only [Matrix.mul_assoc]
      _ = suppP Y := by rw [hB2, Matrix.mul_one, S_mul_suppP hY, S_mul_sqrtS hY]
  have hNpsd : (X + (t : ℂ) • Y).PosSemidef := hX.add (hY.smul (Complex.zero_le_real.2 ht.le))
  have b1 : (X + (t : ℂ) • Y) * (supportInvSqrt Y * B * supportInvSqrt Y) * (X + (t : ℂ) • Y) =
      X + (t : ℂ) • Y := by
    rw [hNZ, hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, suppP_mul_sqrtS hY]
  have b2 : (supportInvSqrt Y * B * supportInvSqrt Y) * (X + (t : ℂ) • Y) *
      (supportInvSqrt Y * B * supportInvSqrt Y) = supportInvSqrt Y * B * supportInvSqrt Y := by
    rw [hZN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, suppP_mul_S hY]
  have b3 : ((X + (t : ℂ) • Y) * (supportInvSqrt Y * B * supportInvSqrt Y)).IsHermitian := by
    rw [hNZ]; exact suppP_herm hY
  have b4 : ((supportInvSqrt Y * B * supportInvSqrt Y) * (X + (t : ℂ) • Y)).IsHermitian := by
    rw [hZN]; exact suppP_herm hY
  unfold pinv
  exact pinv_characterisation hNpsd _ b1 b2 b3 b4

/-- The order-two perspective with denominator `X + t Y` in terms of the sandwich. -/
theorem persp_add_smul {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hR : RangeIncluded X Y) {t : ℝ} (ht : 0 < t) :
    X * pinv (X + (t : ℂ) • Y) * X =
      sqrtS Y * (sand X Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * sand X Y) * sqrtS Y := by
  rw [pinv_add_smul hX hY hR ht]
  have hXR := sqrtS_sand_sqrtS hY hX.1 hR
  calc X * (supportInvSqrt Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * supportInvSqrt Y) * X
      = (sqrtS Y * sand X Y * sqrtS Y) *
          (supportInvSqrt Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * supportInvSqrt Y) *
          (sqrtS Y * sand X Y * sqrtS Y) := by rw [hXR]
    _ = sqrtS Y * (sand X Y * (sqrtS Y * supportInvSqrt Y)) *
          (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ *
          ((supportInvSqrt Y * sqrtS Y) * sand X Y) * sqrtS Y := by simp only [Matrix.mul_assoc]
    _ = sqrtS Y * (sand X Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * sand X Y) *
          sqrtS Y := by
        rw [sqrtS_mul_S, S_mul_sqrtS hY, sand_mul_suppP hY, suppP_mul_sand hY]
        simp only [Matrix.mul_assoc]

/-! ### Quadratic forms in the eigenbasis of the sandwich -/

theorem qform_diag (V : Matrix n n ℂ) (g : n → ℝ) (w : n → ℂ) :
    star w ⬝ᵥ (Vᴴ * Matrix.diagonal (fun i => (g i : ℂ)) * V).mulVec w =
      ((∑ i, g i * Complex.normSq ((V.mulVec w) i) : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem qform_conj {m : Type} [Fintype m] [DecidableEq m] (K : Matrix m n ℂ) (G : Matrix n n ℂ)
    (w : m → ℂ) :
    star w ⬝ᵥ (K * G * Kᴴ).mulVec w = star (Kᴴ.mulVec w) ⬝ᵥ G.mulVec (Kᴴ.mulVec w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

theorem conj_diag_mul (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1) (f g : n → ℂ) :
    (U * Matrix.diagonal f * Uᴴ) * (U * Matrix.diagonal g * Uᴴ) =
      U * Matrix.diagonal (fun i => f i * g i) * Uᴴ := by
  calc (U * Matrix.diagonal f * Uᴴ) * (U * Matrix.diagonal g * Uᴴ)
      = U * Matrix.diagonal f * (Uᴴ * U) * Matrix.diagonal g * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal f * Matrix.diagonal g) * Uᴴ := by
        rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => f i * g i) * Uᴴ := by rw [Matrix.diagonal_mul_diagonal]

/-- The inverse of the shifted sandwich in an eigenbasis. -/
theorem shift_inv_spectral {A U : Matrix n n ℂ} {d : n → ℝ} (hA : A.PosSemidef)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hAeq : A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) (hd0 : ∀ i, 0 ≤ d i)
    {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
      U * Matrix.diagonal (fun i => (((d i + t)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
  have hsh : A + (t : ℂ) • (1 : Matrix n n ℂ) =
      U * Matrix.diagonal (fun i => ((d i + t : ℝ) : ℂ)) * Uᴴ := by
    have e : Matrix.diagonal (fun i => ((d i + t : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (d i : ℂ)) + (t : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [e, Matrix.mul_add, Matrix.add_mul, ← hAeq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU2]
  apply Matrix.inv_eq_right_inv
  rw [hsh, conj_diag_mul U hU1]
  have e1 : (fun i => ((d i + t : ℝ) : ℂ) * (((d i + t)⁻¹ : ℝ) : ℂ)) = fun _ : n => (1 : ℂ) := by
    funext i
    have hne : (d i + t) ≠ 0 := by have := hd0 i; positivity
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one]
  rw [e1, Matrix.diagonal_one, Matrix.mul_one, hU2]

/-- Scalar integrand of Mathlib's representation of `x ^ α`, `1 < α < 2`, for `t > 0`. -/
theorem integrand_eq (α : ℝ) {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    Real.rpowIntegrand₁₂ α t x = t ^ (α - 2) * (x * (x + t)⁻¹ * x) := by
  have h1 : t ^ (α - 1) = t ^ (α - 2) * t := by
    have h := Real.rpow_add ht (α - 2) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hne : x + t ≠ 0 := by positivity
  have hne' : t + x ≠ 0 := by positivity
  unfold Real.rpowIntegrand₁₂
  rw [h1]
  field_simp
  ring

/-- The measure of Mathlib's integral representation of `x ^ α` for `1 < α < 2`. -/
def muA (α : ℝ) (hα : α ∈ Set.Ioo (1 : ℝ) 2) : MeasureTheory.Measure ℝ :=
  Classical.choose (Real.exists_measure_rpow_eq_integral_rpowIntegrand₁₂ hα)

theorem muA_spec {α : ℝ} (hα : α ∈ Set.Ioo (1 : ℝ) 2) {x : ℝ} (hx : 0 ≤ x) :
    MeasureTheory.IntegrableOn (fun t => Real.rpowIntegrand₁₂ α t x) (Set.Ioi 0) (muA α hα) ∧
      x ^ α = ∫ t in Set.Ioi 0, Real.rpowIntegrand₁₂ α t x ∂(muA α hα) :=
  Classical.choose_spec (Real.exists_measure_rpow_eq_integral_rpowIntegrand₁₂ hα) x hx

/-- Weighted quadratic form of the order-two perspective with denominator `X + t Y`. -/
def hfun (α : ℝ) (X Y : Matrix n n ℂ) (w : n → ℂ) (t : ℝ) : ℝ :=
  t ^ (α - 2) * (star w ⬝ᵥ (X * pinv (X + (t : ℂ) • Y) * X).mulVec w).re

/-- **Integral representation of the quadratic forms of `G_α`** for a supported pair,
`1 < α < 2`: integrals of quadratic forms of order-two perspectives. -/
theorem qform_integral {α : ℝ} (hα : α ∈ Set.Ioo (1 : ℝ) 2) {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hR : RangeIncluded X Y) (w : n → ℂ) :
    MeasureTheory.IntegrableOn (hfun α X Y w) (Set.Ioi 0) (muA α hα) ∧
      (star w ⬝ᵥ (Gp α X Y).mulVec w).re = ∫ t in Set.Ioi 0, hfun α X Y w t ∂(muA α hα) := by
  have hA := sand_psd Y hX
  obtain ⟨U, d, hU1, hU2, hAeq, hd⟩ := exists_spectral hA.1
  have hd0 : ∀ i, 0 ≤ d i := fun i => psd_spectrum_nonneg hA _ (hd i)
  have hRh := sqrtS_herm hY
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix n n ℂ, V = Uᴴ * sqrtS Y := ⟨_, rfl⟩
  have hVH : Vᴴ = sqrtS Y * U := by
    rw [hVdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh.eq]
  have hform : ∀ g : n → ℝ, sqrtS Y * (U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ) * sqrtS Y =
      Vᴴ * Matrix.diagonal (fun i => (g i : ℂ)) * V := by
    intro g
    rw [hVH, hVdef]
    simp only [Matrix.mul_assoc]
  obtain ⟨cc, hcdef⟩ : ∃ cc : n → ℝ, cc = fun i => Complex.normSq ((V.mulVec w) i) := ⟨_, rfl⟩
  have hc0 : ∀ i, 0 ≤ cc i := fun i => by rw [hcdef]; exact Complex.normSq_nonneg _
  -- the perspective
  have hpow : hermitianPower (sand X Y) α =
      U * Matrix.diagonal (fun i => ((d i ^ α : ℝ) : ℂ)) * Uᴴ := by
    have h := hsf_spectral_form (fun x => Real.rpow x α) U d hU1 hU2
    rw [← hAeq] at h
    exact h
  have key1 : (star w ⬝ᵥ (Gp α X Y).mulVec w).re = ∑ i, d i ^ α * cc i := by
    unfold Gp
    rw [hpow, hform, qform_diag, Complex.ofReal_re, hcdef]
  -- the order-two perspectives
  have key2 : ∀ t : ℝ, 0 < t → hfun α X Y w t =
      ∑ i, Real.rpowIntegrand₁₂ α t (d i) * cc i := by
    intro t ht
    have hABA : sand X Y * (sand X Y + (t : ℂ) • (1 : Matrix n n ℂ))⁻¹ * sand X Y =
        U * Matrix.diagonal (fun i => ((d i * (d i + t)⁻¹ * d i : ℝ) : ℂ)) * Uᴴ := by
      rw [shift_inv_spectral hA hU1 hU2 hAeq hd0 ht]
      conv_lhs => rw [hAeq]
      rw [conj_diag_mul U hU1, conj_diag_mul U hU1]
      congr 2
      funext i
      push_cast
      ring
    unfold hfun
    rw [persp_add_smul hX hY hR ht, hABA, hform, qform_diag, Complex.ofReal_re, hcdef,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integrand_eq α ht (hd0 i)]
    ring
  have hint : ∀ i ∈ (Finset.univ : Finset n),
      MeasureTheory.Integrable (fun t => Real.rpowIntegrand₁₂ α t (d i) * cc i)
        ((muA α hα).restrict (Set.Ioi 0)) :=
    fun i _ => ((muA_spec hα (hd0 i)).1).mul_const (cc i)
  have hEq : Set.EqOn (fun t => ∑ i, Real.rpowIntegrand₁₂ α t (d i) * cc i) (hfun α X Y w)
      (Set.Ioi 0) := fun t ht => (key2 t ht).symm
  refine ⟨?_, ?_⟩
  · exact MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.integrable_finsetSum _ hint) hEq
      measurableSet_Ioi
  · rw [key1, ← MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq,
      MeasureTheory.integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_mul_const, ← (muA_spec hα (hd0 i)).2]

/-! ### Transformer inequality at every order in `(1, 2]` -/

section transformer
variable {m : Type} [Fintype m] [DecidableEq m]

theorem conj_supported {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hR : RangeIncluded X Y) (K : Matrix m n ℂ) :
    RangeIncluded (K * X * Kᴴ) (K * Y * Kᴴ) :=
  (moment_le_of_dom ((dom_base hY hX.1 hR).conj K) (hY.mul_mul_conjTranspose_same K)).1

/-- Order `1 < α < 2`: from the order-two inequality under the integral. -/
theorem transformer_lt_two {α : ℝ} (hα : α ∈ Set.Ioo (1 : ℝ) 2) {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hR : RangeIncluded X Y) (K : Matrix m n ℂ) :
    (K * Gp α X Y * Kᴴ - Gp α (K * X * Kᴴ) (K * Y * Kᴴ)).PosSemidef := by
  have hX' : (K * X * Kᴴ).PosSemidef := hX.mul_mul_conjTranspose_same K
  have hY' : (K * Y * Kᴴ).PosSemidef := hY.mul_mul_conjTranspose_same K
  have hR' := conj_supported hX hY hR K
  have hG := Gp_psd α hX hY
  have hG' := Gp_psd α hX' hY'
  have hKG : (K * Gp α X Y * Kᴴ).PosSemidef := hG.mul_mul_conjTranspose_same K
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hKG.1.sub hG'.1) fun w => ?_
  obtain ⟨i1, e1⟩ := qform_integral hα hX hY hR (Kᴴ.mulVec w)
  obtain ⟨i2, e2⟩ := qform_integral hα hX' hY' hR' w
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), hfun α (K * X * Kᴴ) (K * Y * Kᴴ) w t ≤
      hfun α X Y (Kᴴ.mulVec w) t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hN : (X + (t : ℂ) • Y).PosSemidef := hX.add (hY.smul (Complex.zero_le_real.2 ht'.le))
    have h2 := transformer_le hN hX.1 (rangeIncluded_add_smul hX hY ht'.le) K
    have hKN : K * (X + (t : ℂ) • Y) * Kᴴ = K * X * Kᴴ + (t : ℂ) • (K * Y * Kᴴ) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hKN] at h2
    have h3 := h2.dotProduct_mulVec_nonneg w
    rw [Matrix.sub_mulVec, dotProduct_sub, qform_conj] at h3
    have h4 := (Complex.nonneg_iff.1 h3).1
    rw [Complex.sub_re] at h4
    unfold hfun
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg ht'.le _)
  have hle := MeasureTheory.setIntegral_mono_on i2 i1 measurableSet_Ioi hpt
  rw [← e1, ← e2] at hle
  rw [Matrix.sub_mulVec, dotProduct_sub, qform_conj]
  obtain ⟨ha, -⟩ := nonneg_eq_ofReal (hG.dotProduct_mulVec_nonneg (Kᴴ.mulVec w))
  obtain ⟨hb, -⟩ := nonneg_eq_ofReal (hG'.dotProduct_mulVec_nonneg w)
  rw [ha, hb, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.2 (by linarith)

/-- **Transformer inequality** for the locked perspective at every order `1 < α ≤ 2`,
supported pairs, singular denominators and rectangular `K` allowed. -/
theorem transformer_alpha {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hR : RangeIncluded X Y) (K : Matrix m n ℂ) :
    (K * Gp α X Y * Kᴴ - Gp α (K * X * Kᴴ) (K * Y * Kᴴ)).PosSemidef := by
  rcases lt_or_eq_of_le h2 with hlt | rfl
  · exact transformer_lt_two ⟨h1, hlt⟩ hX hY hR K
  · rw [Gp_two hY hX.1 hR, Gp_two (hY.mul_mul_conjTranspose_same K)
      (hX.mul_mul_conjTranspose_same K).1 (conj_supported hX hY hR K)]
    exact transformer_le hY hX.1 hR K

/-- Equality for a congruence with a two-sided inverse. -/
theorem Gp_conj_eq {α : ℝ} (h1 : 1 < α) (h2 : α ≤ 2) {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hR : RangeIncluded X Y)
    (K : Matrix m n ℂ) (K' : Matrix n m ℂ) (hK1 : K' * K = 1) (hK2 : K * K' = 1) :
    Gp α (K * X * Kᴴ) (K * Y * Kᴴ) = K * Gp α X Y * Kᴴ := by
  have hX' : (K * X * Kᴴ).PosSemidef := hX.mul_mul_conjTranspose_same K
  have hY' : (K * Y * Kᴴ).PosSemidef := hY.mul_mul_conjTranspose_same K
  have hR' := conj_supported hX hY hR K
  have t1 := transformer_alpha h1 h2 hX hY hR K
  have t2 := transformer_alpha h1 h2 hX' hY' hR' K'
  have hc1 : Kᴴ * K'ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hK1, Matrix.conjTranspose_one]
  have hc2 : K'ᴴ * Kᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hK2, Matrix.conjTranspose_one]
  have back : ∀ A : Matrix n n ℂ, K' * (K * A * Kᴴ) * K'ᴴ = A := by
    intro A
    calc K' * (K * A * Kᴴ) * K'ᴴ = (K' * K) * A * (Kᴴ * K'ᴴ) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hK1, hc1, Matrix.one_mul, Matrix.mul_one]
  rw [back X, back Y] at t2
  have t3 := t2.mul_mul_conjTranspose_same K
  have e : K * (K' * Gp α (K * X * Kᴴ) (K * Y * Kᴴ) * K'ᴴ - Gp α X Y) * Kᴴ =
      Gp α (K * X * Kᴴ) (K * Y * Kᴴ) - K * Gp α X Y * Kᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    calc K * (K' * Gp α (K * X * Kᴴ) (K * Y * Kᴴ) * K'ᴴ) * Kᴴ
        = (K * K') * Gp α (K * X * Kᴴ) (K * Y * Kᴴ) * (K'ᴴ * Kᴴ) := by simp only [Matrix.mul_assoc]
      _ = Gp α (K * X * Kᴴ) (K * Y * Kᴴ) := by rw [hK2, hc2, Matrix.one_mul, Matrix.mul_one]
  rw [e] at t3
  -- both differences are positive semidefinite, hence zero
  have htr : Matrix.trace (K * Gp α X Y * Kᴴ - Gp α (K * X * Kᴴ) (K * Y * Kᴴ)) = 0 := by
    have a1 := (nonneg_eq_ofReal t1.trace_nonneg)
    have a2 := (nonneg_eq_ofReal t3.trace_nonneg)
    have hneg : Matrix.trace (Gp α (K * X * Kᴴ) (K * Y * Kᴴ) - K * Gp α X Y * Kᴴ) =
        - Matrix.trace (K * Gp α X Y * Kᴴ - Gp α (K * X * Kᴴ) (K * Y * Kᴴ)) := by
      rw [Matrix.trace_sub, Matrix.trace_sub]; ring
    have hre : (Matrix.trace (K * Gp α X Y * Kᴴ - Gp α (K * X * Kᴴ) (K * Y * Kᴴ))).re = 0 := by
      have b2 := a2.2
      rw [hneg, Complex.neg_re] at b2
      linarith [a1.2]
    rw [a1.1, hre, Complex.ofReal_zero]
  exact (sub_eq_zero.1 ((t1.trace_eq_zero_iff).1 htr)).symm

end transformer

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofAlpha
