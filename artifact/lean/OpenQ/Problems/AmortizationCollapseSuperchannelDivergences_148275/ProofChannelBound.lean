import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofMixedBound
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown

/-!
# Portable proof: claim c2 on the locked definitions

* `density_triple_bound`: for all qubit density matrices `κ₁, κ₂, κ₃`, the pair
  `ρ = (κ₁ + κ₂)/2`, `σ = κ₁/10 + 3κ₂/10 + 3κ₃/5` consists of density matrices,
  is supported (`RangeIncluded`), and has locked order-3/2 moment at most `87/50`.
* `channel_bound` (claim c2): for every `K : ChannelMap 3 2` with the locked
  `IsCPTP K`, the same holds for `(K ρ0, K σ0)` with `ρ0 = diag(1/2, 1/2, 0)`,
  `σ0 = diag(1/10, 3/10, 3/5)`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofChannelBound

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofQubitMoment OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofBloch OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPureBound
  OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofMixedBound
open scoped ComplexOrder

theorem blochMat_mρ (n1 n2 n3 : Fin 3 → ℝ) :
    blochMat (mρ n1 n2 n3) = (1 / 2 : ℂ) • blochMat n1 + (1 / 2 : ℂ) • blochMat n2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMat, mρ] <;> ring

theorem blochMat_mσ (n1 n2 n3 : Fin 3 → ℝ) :
    blochMat (mσ n1 n2 n3) =
      (1 / 10 : ℂ) • blochMat n1 + (3 / 10 : ℂ) • blochMat n2 + (3 / 5 : ℂ) • blochMat n3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMat, mσ] <;> ring

/-- A positive definite reference supports every operator. -/
theorem rangeIncluded_of_posDef {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    {σ : Matrix n n ℂ} (hσ : σ.PosDef) : RangeIncluded ρ σ := by
  rw [rangeIncluded_iff_exists_mul]
  refine ⟨σ⁻¹ * ρ, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det σ).1 hσ.isUnit),
    Matrix.one_mul]

/-- Claim c2 for arbitrary qubit density triples, with the support statement. -/
theorem density_triple_bound {κ1 κ2 κ3 : M2} (h1 : OpenQ.IsDensityMatrix κ1)
    (h2 : OpenQ.IsDensityMatrix κ2) (h3 : OpenQ.IsDensityMatrix κ3) :
    OpenQ.IsDensityMatrix ((1 / 2 : ℂ) • κ1 + (1 / 2 : ℂ) • κ2) ∧
      OpenQ.IsDensityMatrix ((1 / 10 : ℂ) • κ1 + (3 / 10 : ℂ) • κ2 + (3 / 5 : ℂ) • κ3) ∧
      RangeIncluded ((1 / 2 : ℂ) • κ1 + (1 / 2 : ℂ) • κ2)
        ((1 / 10 : ℂ) • κ1 + (3 / 10 : ℂ) • κ2 + (3 / 5 : ℂ) • κ3) ∧
      geometricMoment (3 / 2) ((1 / 2 : ℂ) • κ1 + (1 / 2 : ℂ) • κ2)
        ((1 / 10 : ℂ) • κ1 + (3 / 10 : ℂ) • κ2 + (3 / 5 : ℂ) • κ3) ≤ 87 / 50 := by
  obtain ⟨n1, b1, rfl⟩ := density_eq_blochMat h1
  obtain ⟨n2, b2, rfl⟩ := density_eq_blochMat h2
  obtain ⟨n3, b3, rfl⟩ := density_eq_blochMat h3
  rw [← blochMat_mρ n1 n2 n3, ← blochMat_mσ n1 n2 n3]
  have hm := ball_mρ (n3 := n3) b1 b2
  have hs := ball_mσ b1 b2 b3
  refine ⟨blochMat_density hm, blochMat_density hs, ?_, moment_le_bloch b1 b2 b3⟩
  rcases good_all b1 b2 b3 with ⟨hpd, -⟩ | heq
  · exact rangeIncluded_of_posDef _ (blochMat_posDef hpd)
  · rw [heq]
    exact subset_rfl

/-- A locked CPTP map sends positive semidefinite matrices to positive semidefinite ones. -/
theorem cptp_posSemidef {a b : ℕ} {K : ChannelMap a b} (hK : IsCPTP K)
    {X : Matrix (Fin a) (Fin a) ℂ} (hX : X.PosSemidef) : (K X).PosSemidef := by
  have h := hK.1 1 Nat.one_pos (X.submatrix Prod.snd Prod.snd) (hX.submatrix Prod.snd)
  have h2 := h.submatrix (fun i : Fin b => ((0 : Fin 1), i))
  exact h2

theorem cptp_density {a b : ℕ} {K : ChannelMap a b} (hK : IsCPTP K)
    {X : Matrix (Fin a) (Fin a) ℂ} (hX : OpenQ.IsDensityMatrix X) :
    OpenQ.IsDensityMatrix (K X) :=
  ⟨cptp_posSemidef hK hX.1, (hK.2 X).trans hX.2⟩

/-- The two prepared input states of the preparation pair. -/
noncomputable def ρ0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1 / 2, 1 / 2, 0]

noncomputable def σ0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1 / 10, 3 / 10, 3 / 5]

theorem single_density (x : Fin 3) :
    OpenQ.IsDensityMatrix (Matrix.single x x (1 : ℂ) : Matrix (Fin 3) (Fin 3) ℂ) := by
  constructor
  · have : (Matrix.single x x (1 : ℂ) : Matrix (Fin 3) (Fin 3) ℂ)
        = Matrix.diagonal (Pi.single x 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = x
        · subst hi; simp
        · simp [hi, Ne.symm hi]
      · simp [Matrix.single_apply, hij]
        intro h1 h2
        exact hij (h1.symm.trans h2)
    rw [this, Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases hi : i = x
    · subst hi; simp
    · simp [hi]
  · simp [Matrix.trace_single_eq_same]

theorem ρ0_eq : ρ0 = (1 / 2 : ℂ) • Matrix.single 0 0 (1 : ℂ) + (1 / 2 : ℂ) • Matrix.single 1 1 (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ρ0]

theorem σ0_eq : σ0 = (1 / 10 : ℂ) • Matrix.single 0 0 (1 : ℂ)
    + (3 / 10 : ℂ) • Matrix.single 1 1 (1 : ℂ) + (3 / 5 : ℂ) • Matrix.single 2 2 (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ0]

/-- Claim c2 on the locked definitions: every complex-linear CPTP map from
3-by-3 to 2-by-2 matrices. The output pair is a supported pair of density
matrices with order-3/2 moment at most `87/50`. -/
theorem channel_bound (K : ChannelMap 3 2) (hK : IsCPTP K) :
    OpenQ.IsDensityMatrix (K ρ0) ∧ OpenQ.IsDensityMatrix (K σ0) ∧
      RangeIncluded (K ρ0) (K σ0) ∧ geometricMoment (3 / 2) (K ρ0) (K σ0) ≤ 87 / 50 := by
  have h := density_triple_bound (cptp_density hK (single_density 0))
    (cptp_density hK (single_density 1)) (cptp_density hK (single_density 2))
  rw [ρ0_eq, σ0_eq]
  simp only [map_add, map_smul]
  exact h

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofChannelBound
