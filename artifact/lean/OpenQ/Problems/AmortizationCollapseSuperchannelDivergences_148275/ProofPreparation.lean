import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofChannelBound
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
import Mathlib.Analysis.Matrix.Order

/-!
# Portable proof: claim c3 on the locked definitions

* `hsf_kronecker`: the locked spectral function of a Kronecker product of
  Hermitian matrices, for a function that is multiplicative on the two spectra.
* `geometricMoment_kronecker`: `M_α(τ ⊗ ρ, τ ⊗ σ) = M_α(ρ, σ)` for positive
  semidefinite `τ` of trace one (possibly singular), positive semidefinite
  `ρ`, `σ`, every `α ≠ 0`.
* `prepSuper τ`: the memory-one physical superchannel that prepares `τ` and
  post-processes with the identity; `prepSuper_act`: its action on a slot map
  `K` is `z ↦ z • K τ`.
* `superchannel_bound` (claim c3): the locked ordinary superchannel divergence
  of the pair `(prepSuper ρ0, prepSuper σ0)` at order `3/2` is at most
  `2 log₂(87/50)`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General (insertSlot insertSlot_formula)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofChannelBound
open scoped ComplexOrder Kronecker

section spectral

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A unitary diagonalisation with real eigenvalues taken from the spectrum. -/
theorem exists_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ), U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose ∧
      ∀ i, d i ∈ spectrum ℝ A := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues, ?_, ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self _
  · exact Unitary.coe_mul_star_self _
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  · intro i
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i, rfl⟩

/-- Spectral function of a Kronecker product. -/
theorem hsf_kronecker (f : ℝ → ℝ) {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (hf : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B, f (x * y) = f x * f y) :
    hermitianSpectralFunction f (A ⊗ₖ B) =
      hermitianSpectralFunction f A ⊗ₖ hermitianSpectralFunction f B := by
  obtain ⟨U, a, hU1, hU2, hAeq, ha⟩ := exists_spectral hA
  obtain ⟨V, b, hV1, hV2, hBeq, hb⟩ := exists_spectral hB
  have hW1 : (U ⊗ₖ V).conjTranspose * (U ⊗ₖ V) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU1, hV1,
      Matrix.one_kronecker_one]
  have hW2 : (U ⊗ₖ V) * (U ⊗ₖ V).conjTranspose = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU2, hV2,
      Matrix.one_kronecker_one]
  have hAB : A ⊗ₖ B = (U ⊗ₖ V) * Matrix.diagonal (fun p : m × n => ((a p.1 * b p.2 : ℝ) : ℂ))
      * (U ⊗ₖ V).conjTranspose := by
    conv_lhs => rw [hAeq, hBeq]
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal]
    congr 2
    funext p
    push_cast
    rfl
  have hfA := hsf_spectral_form f U a hU1 hU2
  have hfB := hsf_spectral_form f V b hV1 hV2
  rw [← hAeq] at hfA
  rw [← hBeq] at hfB
  have hd : (fun p : m × n => ((f (a p.1 * b p.2) : ℝ) : ℂ))
      = (fun mn : m × n => ((f (a mn.1) : ℝ) : ℂ) * ((f (b mn.2) : ℝ) : ℂ)) := by
    funext p
    rw [hf _ (ha p.1) _ (hb p.2)]
    exact Complex.ofReal_mul _ _
  rw [hAB, hsf_spectral_form f (U ⊗ₖ V) (fun p : m × n => a p.1 * b p.2) hW1 hW2, hfA, hfB,
    Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal, hd]

/-- The support projector is fixed by every nonzero real power. -/
theorem hermitianPower_supp {τ : Matrix m m ℂ} (hτ : τ.PosSemidef) (α : ℝ) (hα : α ≠ 0) :
    hermitianPower (supportInvSqrt τ * τ * supportInvSqrt τ) α
      = supportInvSqrt τ * τ * supportInvSqrt τ := by
  rw [sandwich_self hτ, hermitianPower_eq_cfc]
  have hg : ContinuousOn (fun x : ℝ => x ^ α) ((fun x : ℝ => x * x⁻¹) '' spectrum ℝ τ) := by
    rw [← cfc_map_spectrum (fun x : ℝ => x * x⁻¹) τ hτ.1 (contOn _ _)]
    exact contOn _ _
  have hc := cfc_comp (fun x : ℝ => x ^ α) (fun x : ℝ => x * x⁻¹) τ hτ.1 hg (contOn _ _)
  rw [← hc]
  apply cfc_congr
  intro x _
  show (x * x⁻¹) ^ α = x * x⁻¹
  by_cases hx : x = 0
  · simp [hx, Real.zero_rpow hα]
  · simp [hx]

/-- `τ Π_τ = τ` for the support projector `Π_τ`. -/
theorem mul_supp {τ : Matrix m m ℂ} (hτ : τ.PosSemidef) :
    τ * (supportInvSqrt τ * τ * supportInvSqrt τ) = τ := by
  have hid := cfc_id_eq hτ.1
  rw [sandwich_self hτ]
  calc τ * cfc (fun x : ℝ => x * x⁻¹) τ
      = cfc (fun x : ℝ => x) τ * cfc (fun x : ℝ => x * x⁻¹) τ := by rw [hid]
    _ = cfc (fun x : ℝ => x * (x * x⁻¹)) τ := by rw [cfc_mul2]
    _ = cfc (fun x : ℝ => x) τ := by
        apply cfc_congr
        intro x _
        by_cases hx : x = 0
        · simp [hx]
        · simp [hx]
    _ = τ := hid

/-- Tensoring numerator and reference with the same trace-one positive
semidefinite matrix does not change the locked moment. -/
theorem geometricMoment_kronecker (α : ℝ) (hα : α ≠ 0) {τ : Matrix m m ℂ} {ρ σ : Matrix n n ℂ}
    (hτ : τ.PosSemidef) (htr : Matrix.trace τ = 1) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    geometricMoment α (τ ⊗ₖ ρ) (τ ⊗ₖ σ) = geometricMoment α ρ σ := by
  have hS : supportInvSqrt (τ ⊗ₖ σ) = supportInvSqrt τ ⊗ₖ supportInvSqrt σ := by
    unfold supportInvSqrt
    apply hsf_kronecker _ hτ.1 hσ.1
    intro x hx y _
    rw [supportInvSqrtScalar_eq, supportInvSqrtScalar_eq, supportInvSqrtScalar_eq,
      Real.sqrt_mul (psd_spectrum_nonneg hτ x hx), mul_inv]
  have hPi := support_sandwich_posSemidef τ τ hτ
  have hX := support_sandwich_posSemidef ρ σ hρ
  have hP : hermitianPower ((supportInvSqrt τ * τ * supportInvSqrt τ)
        ⊗ₖ (supportInvSqrt σ * ρ * supportInvSqrt σ)) α
      = (supportInvSqrt τ * τ * supportInvSqrt τ)
        ⊗ₖ hermitianPower (supportInvSqrt σ * ρ * supportInvSqrt σ) α := by
    have h := hsf_kronecker (fun x : ℝ => Real.rpow x α) hPi.1 hX.1 (by
      intro x hx y hy
      exact Real.mul_rpow (psd_spectrum_nonneg hPi x hx) (psd_spectrum_nonneg hX y hy))
    have h2 := hermitianPower_supp hτ α hα
    unfold hermitianPower at h2 ⊢
    rw [h, h2]
  unfold geometricMoment
  rw [hS, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hP, ← Matrix.mul_kronecker_mul,
    mul_supp hτ, Matrix.trace_kronecker, htr, one_mul]

theorem rangeIncluded_kronecker (τ : Matrix m m ℂ) {ρ σ : Matrix n n ℂ}
    (h : RangeIncluded ρ σ) : RangeIncluded (τ ⊗ₖ ρ) (τ ⊗ₖ σ) := by
  obtain ⟨Y, rfl⟩ := (rangeIncluded_iff_exists_mul ρ σ).1 h
  rw [rangeIncluded_iff_exists_mul]
  refine ⟨(1 : Matrix m m ℂ) ⊗ₖ Y, ?_⟩
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

end spectral

section preparation

/-- Preparation of `τ` from the one-dimensional input system. -/
noncomputable def prepMap (τ : Matrix (Fin 3) (Fin 3) ℂ) : ChannelMap 1 (3 * 1) where
  toFun Z := Z 0 0 • τ
  map_add' X Y := by rw [Matrix.add_apply, add_smul]
  map_smul' c X := by rw [Matrix.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul]

theorem prepMap_apply (τ : Matrix (Fin 3) (Fin 3) ℂ) (Z : Matrix (Fin 1) (Fin 1) ℂ) :
    prepMap τ Z = Z 0 0 • τ := rfl

theorem prepMap_cptp {τ : Matrix (Fin 3) (Fin 3) ℂ} (hτ : OpenQ.IsDensityMatrix τ) :
    IsCPTP (prepMap τ) := by
  constructor
  · intro k _ X hX
    have h : amplification k (prepMap τ) X
        = (X.submatrix (fun s : Fin k => (s, (0 : Fin 1))) (fun s : Fin k => (s, (0 : Fin 1))))
          ⊗ₖ τ := by
      ext ⟨s, i⟩ ⟨t, j⟩
      rfl
    rw [h]
    exact (hX.submatrix _).kronecker hτ.1
  · intro Z
    rw [prepMap_apply, Matrix.trace_smul, hτ.2, smul_eq_mul, mul_one, Matrix.trace_fin_one]

theorem id_cptp : IsCPTP (LinearMap.id : ChannelMap 2 2) :=
  (Preparation.libraryCPTP_iff _).1 (Preparation.LibraryCPTP.id (Fin 2))

/-- The memory-one physical superchannel that prepares `τ`, inserts the slot
channel and post-processes with the identity. -/
noncomputable def prepSuper (τ : Matrix (Fin 3) (Fin 3) ℂ) (hτ : OpenQ.IsDensityMatrix τ) :
    PhysicalSuperchannel 3 2 1 2 where
  memory := 1
  memory_pos := Nat.one_pos
  pre := prepMap τ
  post := (LinearMap.id : ChannelMap 2 2)
  pre_cptp := prepMap_cptp hτ
  post_cptp := id_cptp

/-- With memory dimension one, slot insertion is the slot map itself. -/
theorem insertSlot_one (K : ChannelMap 3 2) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    (insertSlot 1 K : ChannelMap (3 * 1) (2 * 1)) X = K X := by
  ext p q
  have hp : (finProdFinEquiv (p, (0 : Fin 1)) : Fin (2 * 1)) = p := by fin_cases p <;> rfl
  have hq : (finProdFinEquiv (q, (0 : Fin 1)) : Fin (2 * 1)) = q := by fin_cases q <;> rfl
  have hX : (fun i j : Fin 3 => X (finProdFinEquiv (i, (0 : Fin 1)))
      (finProdFinEquiv (j, (0 : Fin 1)))) = X := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h := insertSlot_formula K X (p, (0 : Fin 1)) (q, (0 : Fin 1))
  rw [hp, hq] at h
  rw [h]
  exact congrArg (fun Y => K Y p q) hX

/-- Action of the preparation superchannel: `Θ(K)(z) = z K(τ)`. -/
theorem prepSuper_act (τ : Matrix (Fin 3) (Fin 3) ℂ) (hτ : OpenQ.IsDensityMatrix τ)
    (K : ChannelMap 3 2) (Z : Matrix (Fin 1) (Fin 1) ℂ) :
    (prepSuper τ hτ).act K Z = Z 0 0 • K τ := by
  show (LinearMap.id : ChannelMap 2 2) (insertSlot 1 K (prepMap τ Z)) = Z 0 0 • K τ
  rw [LinearMap.id_apply, prepMap_apply, map_smul, insertSlot_one]

/-- The amplified output of the preparation superchannel is a product state. -/
theorem amplification_prepSuper (τ : Matrix (Fin 3) (Fin 3) ℂ) (hτ : OpenQ.IsDensityMatrix τ)
    (K : ChannelMap 3 2) (r : ℕ) (T : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ) :
    amplification r ((prepSuper τ hτ).act K) T
      = (T.submatrix (fun s : Fin r => (s, (0 : Fin 1))) (fun s : Fin r => (s, (0 : Fin 1))))
        ⊗ₖ K τ := by
  ext ⟨s, i⟩ ⟨t, j⟩
  have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) ℂ => Y i j)
    (prepSuper_act τ hτ K (Matrix.of fun a b => T (s, a) (t, b)))
  exact h

theorem reference_density {r : ℕ} {T : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ}
    (hT : OpenQ.IsDensityMatrix T) :
    (T.submatrix (fun s : Fin r => (s, (0 : Fin 1))) (fun s : Fin r => (s, (0 : Fin 1)))).PosSemidef ∧
      Matrix.trace (T.submatrix (fun s : Fin r => (s, (0 : Fin 1)))
        (fun s : Fin r => (s, (0 : Fin 1)))) = 1 := by
  refine ⟨hT.1.submatrix _, ?_⟩
  have h := hT.2
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_one] at h
  simpa [Matrix.trace] using h

theorem ρ0_density : OpenQ.IsDensityMatrix ρ0 := by
  constructor
  · unfold ρ0
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> simp
  · simp [ρ0, Matrix.trace, Fin.sum_univ_three]
    norm_num

theorem σ0_density : OpenQ.IsDensityMatrix σ0 := by
  constructor
  · unfold σ0
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> simp [Complex.nonneg_iff] <;> norm_num
  · simp [σ0, Matrix.trace, Fin.sum_univ_three]
    norm_num

/-- The two preparation superchannels of claim c3. -/
noncomputable def Θ₁ : PhysicalSuperchannel 3 2 1 2 := prepSuper ρ0 ρ0_density

noncomputable def Θ₂ : PhysicalSuperchannel 3 2 1 2 := prepSuper σ0 σ0_density

/-- For every inserted channel and every external reference state the state
divergence of the two outputs is the finite real number `2 log₂ M(K ρ0, K σ0)`. -/
theorem output_divergence (N : Channel 3 2) (r : ℕ) (T : Matrix (Fin r × Fin 1) (Fin r × Fin 1) ℂ)
    (hT : OpenQ.IsDensityMatrix T) :
    geometricStateDivergence (3 / 2) (Fin r × Fin 2)
        (amplification r (Θ₁.onChannel N).val T) (amplification r (Θ₂.onChannel N).val T)
      = ((log₂ (geometricMoment (3 / 2) (N.val ρ0) (N.val σ0)) / (3 / 2 - 1) : ℝ) : EReal) := by
  obtain ⟨hρ, hσ, hR, -⟩ := channel_bound N.val N.property
  obtain ⟨hTp, hTt⟩ := reference_density hT
  show geometricStateDivergence (3 / 2) (Fin r × Fin 2)
      (amplification r ((prepSuper ρ0 ρ0_density).act N.val) T)
      (amplification r ((prepSuper σ0 σ0_density).act N.val) T) = _
  rw [amplification_prepSuper, amplification_prepSuper]
  unfold geometricStateDivergence
  simp only [eq_true (rangeIncluded_kronecker _ hR), ↓reduceIte]
  rw [geometricMoment_kronecker (3 / 2) (by norm_num) hTp hTt hρ.1 hσ.1]

/-- Claim c3 on the locked definitions. -/
theorem superchannel_bound :
    ordinarySuperchannelDivergence (geometricStateDivergence (3 / 2)) Θ₁ Θ₂
      ≤ ((2 * log₂ (87 / 50) : ℝ) : EReal) := by
  unfold ordinarySuperchannelDivergence
  apply sSup_le
  rintro v ⟨N, rfl⟩
  unfold ordinaryChannelDivergence
  apply sSup_le
  rintro v ⟨r, _, T, hT, rfl⟩
  rw [output_divergence N r T hT]
  obtain ⟨hρ, hσ, hR, hM⟩ := channel_bound N.val N.property
  have h1 := OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative.one_le_geometricMoment hρ hσ hR (3 / 2) (by norm_num)
  have hlog : Real.log (geometricMoment (3 / 2) (N.val ρ0) (N.val σ0)) ≤ Real.log (87 / 50) :=
    Real.log_le_log (by linarith) hM
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : log₂ (geometricMoment (3 / 2) (N.val ρ0) (N.val σ0)) / (3 / 2 - 1)
      ≤ 2 * log₂ (87 / 50) := by
    unfold log₂
    have : Real.log (geometricMoment (3 / 2) (N.val ρ0) (N.val σ0)) / Real.log 2
        ≤ Real.log (87 / 50) / Real.log 2 := div_le_div_of_nonneg_right hlog h2.le
    have e : (3 / 2 - 1 : ℝ) = 1 / 2 := by norm_num
    rw [e, div_div, mul_one_div, div_le_iff₀ (by positivity)]
    calc Real.log (geometricMoment (3 / 2) (N.val ρ0) (N.val σ0))
        ≤ Real.log (87 / 50) := hlog
      _ = 2 * (Real.log (87 / 50) / Real.log 2) * (Real.log 2 / 2) := by field_simp
  exact_mod_cast hle

end preparation

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation
