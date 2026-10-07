/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i01/CriticReindexE2I01.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown

/-!
Critic scratch (amortization problem, e002-i01). Not part of the research record.

Relabelling invariance of the locked geometric divergence: for a bijection
`e : m ≃ n` of index types and Hermitian `ρ`, `σ`,
`D̂_α(ρ.submatrix e e ‖ σ.submatrix e e) = D̂_α(ρ ‖ σ)`. This is the tool that
identifies a state on `Fin (x * r)` with the same state on `Fin x × Fin r`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The spectral function commutes with a relabelling of the basis. -/
theorem hsf_submatrix (f : ℝ → ℝ) (e : m ≃ n) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermitianSpectralFunction f (A.submatrix e e) =
      (hermitianSpectralFunction f A).submatrix e e := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix n n ℂ, U = (hA.eigenvectorUnitary : Matrix n n ℂ) :=
    ⟨_, rfl⟩
  have hU1 : U.conjTranspose * U = 1 := by
    rw [hUdef]; exact Unitary.coe_star_mul_self _
  have hU2 : U * U.conjTranspose = 1 := by
    rw [hUdef]; exact Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) *
      U.conjTranspose := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef]
    exact h
  have e2 : hermitianSpectralFunction f A =
      U * Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) * U.conjTranspose := by
    conv_lhs => rw [hspec]
    exact hsf_spectral_form f U hA.eigenvalues hU1 hU2
  have hW1 : (U.submatrix e e).conjTranspose * U.submatrix e e = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU1,
      Matrix.submatrix_one_equiv]
  have hW2 : U.submatrix e e * (U.submatrix e e).conjTranspose = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU2,
      Matrix.submatrix_one_equiv]
  have e1 : A.submatrix e e = U.submatrix e e *
      Matrix.diagonal (fun i => ((hA.eigenvalues (e i) : ℝ) : ℂ)) *
        (U.submatrix e e).conjTranspose := by
    conv_lhs => rw [hspec]
    rw [Matrix.conjTranspose_submatrix,
      show Matrix.diagonal (fun i => ((hA.eigenvalues (e i) : ℝ) : ℂ)) =
        (Matrix.diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ))).submatrix e e from
        (Matrix.submatrix_diagonal_equiv (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) e).symm,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [e1, hsf_spectral_form f (U.submatrix e e) (fun i => hA.eigenvalues (e i)) hW1 hW2, e2,
    Matrix.conjTranspose_submatrix,
    show Matrix.diagonal (fun i => ((f (hA.eigenvalues (e i)) : ℝ) : ℂ)) =
      (Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ))).submatrix e e from
      (Matrix.submatrix_diagonal_equiv (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) e).symm,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

omit [DecidableEq m] [DecidableEq n] in
theorem trace_submatrix (e : m ≃ n) (A : Matrix n n ℂ) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => A i i)

/-- The geometric moment is invariant under a relabelling of the basis. -/
theorem moment_submatrix (α : ℝ) (e : m ≃ n) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    geometricMoment α (ρ.submatrix e e) (σ.submatrix e e) = geometricMoment α ρ σ := by
  have hS : (supportInvSqrt σ).IsHermitian := hermitianSpectralFunction_isHermitian _ _
  have hsand : (supportInvSqrt σ * ρ * supportInvSqrt σ).IsHermitian := by
    have h := Matrix.isHermitian_mul_mul_conjTranspose (supportInvSqrt σ) hρ
    rwa [hS.eq] at h
  have h1 : supportInvSqrt (σ.submatrix e e) = (supportInvSqrt σ).submatrix e e :=
    hsf_submatrix _ e hσ
  unfold geometricMoment
  rw [h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have h2 : hermitianPower ((supportInvSqrt σ * ρ * supportInvSqrt σ).submatrix e e) α =
      (hermitianPower (supportInvSqrt σ * ρ * supportInvSqrt σ) α).submatrix e e :=
    hsf_submatrix _ e hsand
  rw [h2, Matrix.submatrix_mul_equiv, trace_submatrix]

/-- The support condition is invariant under a relabelling of the basis. -/
theorem rangeIncluded_submatrix (e : m ≃ n) (ρ σ : Matrix n n ℂ) :
    RangeIncluded (ρ.submatrix e e) (σ.submatrix e e) ↔ RangeIncluded ρ σ := by
  rw [rangeIncluded_iff_exists_mul, rangeIncluded_iff_exists_mul]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C.submatrix e.symm e.symm, ?_⟩
    have h := congrArg (fun M : Matrix m m ℂ => M.submatrix e.symm e.symm) hC
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h
    rw [h, ← Matrix.submatrix_mul_equiv (σ.submatrix e e) C e.symm e.symm e.symm]
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  · rintro ⟨C, hC⟩
    exact ⟨C.submatrix e e, by rw [hC, Matrix.submatrix_mul_equiv]⟩

/-- The locked geometric divergence is invariant under a relabelling of the basis. -/
theorem divergence_submatrix (α : ℝ) (e : m ≃ n) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    geometricStateDivergence α m (ρ.submatrix e e) (σ.submatrix e e) =
      geometricStateDivergence α n ρ σ := by
  unfold geometricStateDivergence
  by_cases h : RangeIncluded ρ σ
  · have h' := (rangeIncluded_submatrix e ρ σ).2 h
    simp only [eq_true h, eq_true h', ↓reduceIte, moment_submatrix α e hρ hσ]
  · have h' : ¬ RangeIncluded (ρ.submatrix e e) (σ.submatrix e e) :=
      fun hh => h ((rangeIncluded_submatrix e ρ σ).1 hh)
    simp only [eq_false h, eq_false h', ↓reduceIte]

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex
