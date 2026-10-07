import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.BasicBounds

/-!
Critic scratch (amortization problem, e001-i01). Independent characterisations of the spectral operations used by the candidate
`MainStatement`:

* `hsf_eq_cfc`: the project's `hermitianSpectralFunction` is Mathlib's generic
  continuous functional calculus `cfc` on every complex matrix.
* `hsf_spectral_form`: witness independence. For ANY unitary diagonalization
  `A = W diag(d) Wᴴ` with real `d`, the spectral function is `W diag(f ∘ d) Wᴴ`.
  Mathlib's chosen eigenbasis therefore plays no role.
* `hsf_diagonal`, `hsf_unitary_conj`: diagonal matrices and unitary covariance.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Every real function is continuous on the finite real spectrum of a matrix. -/
theorem contOn (f : ℝ → ℝ) (X : Matrix n n ℂ) : ContinuousOn f (spectrum ℝ X) := by
  rw [continuousOn_iff_continuous_domRestrict]; fun_prop

/-- The project's spectral function is Mathlib's generic functional calculus on
every matrix: both vanish off the Hermitian matrices. -/
theorem hsf_eq_cfc (f : ℝ → ℝ) (X : Matrix n n ℂ) :
    hermitianSpectralFunction f X = cfc f X := by
  by_cases hX : X.IsHermitian
  · rw [hermitianSpectralFunction_of_isHermitian f X hX, hX.cfc_eq]
  · have hX' : ¬ IsSelfAdjoint X := hX
    rw [cfc_apply_of_not_predicate X hX']
    simp only [hermitianSpectralFunction, dif_neg hX]

theorem diagonal_real_isHermitian (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- Witness independence of the spectral function. -/
theorem hsf_spectral_form (f : ℝ → ℝ) (W : Matrix n n ℂ) (d : n → ℝ)
    (hW : W.conjTranspose * W = 1) (hW' : W * W.conjTranspose = 1) :
    hermitianSpectralFunction f
        (W * Matrix.diagonal (fun i => (d i : ℂ)) * W.conjTranspose) =
      W * Matrix.diagonal (fun i => (f (d i) : ℂ)) * W.conjTranspose := by
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix n n ℂ,
      A = W * Matrix.diagonal (fun i => (d i : ℂ)) * W.conjTranspose := ⟨_, rfl⟩
  rw [← hAdef]
  have hA : A.IsHermitian := by
    rw [hAdef]
    exact Matrix.isHermitian_mul_mul_conjTranspose W (diagonal_real_isHermitian d)
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix n n ℂ, U = (hA.eigenvectorUnitary : Matrix n n ℂ) :=
    ⟨_, rfl⟩
  have hU1 : star U * U = 1 := by rw [hUdef]; exact Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := by rw [hUdef]; exact Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef]
    exact h
  have hcfc : hA.cfc f =
      U * Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) * star U := by
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, hUdef]
    rfl
  have hTint : Matrix.diagonal (fun i => (d i : ℂ)) * (W.conjTranspose * U) =
      (W.conjTranspose * U) * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) := by
    have h1 : W.conjTranspose * A * U =
        Matrix.diagonal (fun i => (d i : ℂ)) * (W.conjTranspose * U) := by
      rw [hAdef]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc W.conjTranspose W, hW, Matrix.one_mul]
    have h2 : W.conjTranspose * A * U =
        (W.conjTranspose * U) * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) := by
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [hU1, Matrix.mul_one]
    exact h1.symm.trans h2
  have hfT : Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * (W.conjTranspose * U) =
      (W.conjTranspose * U) *
        Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) := by
    ext i k
    have h := congrFun (congrFun hTint i) k
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h ⊢
    by_cases hT : (W.conjTranspose * U) i k = 0
    · rw [hT, mul_zero, zero_mul]
    · have hc : (d i : ℂ) = ((hA.eigenvalues k : ℝ) : ℂ) := by
        have h' : (d i : ℂ) * (W.conjTranspose * U) i k =
            ((hA.eigenvalues k : ℝ) : ℂ) * (W.conjTranspose * U) i k := by
          rw [h, mul_comm]
        exact mul_right_cancel₀ hT h'
      have hd : d i = hA.eigenvalues k := by exact_mod_cast hc
      rw [hd, mul_comm]
  have hTU : (W.conjTranspose * U) * star U = W.conjTranspose := by
    rw [Matrix.mul_assoc, hU2, Matrix.mul_one]
  have hWT : W * (W.conjTranspose * U) = U := by
    rw [← Matrix.mul_assoc, hW', Matrix.one_mul]
  rw [hermitianSpectralFunction_of_isHermitian f A hA, hcfc]
  calc U * Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) * star U
      = W * ((W.conjTranspose * U) *
          Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ))) * star U := by
        rw [← Matrix.mul_assoc W, hWT]
    _ = W * (Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * (W.conjTranspose * U)) *
          star U := by rw [hfT]
    _ = W * Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) *
          ((W.conjTranspose * U) * star U) := by simp only [Matrix.mul_assoc]
    _ = W * Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * W.conjTranspose := by rw [hTU]

/-- Spectral function of a real diagonal matrix. -/
theorem hsf_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    hermitianSpectralFunction f (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  have h := hsf_spectral_form f (1 : Matrix n n ℂ) d (by simp) (by simp)
  simpa using h

/-- Unitary covariance of the spectral function on Hermitian matrices. -/
theorem hsf_unitary_conj (f : ℝ → ℝ) (W A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hW : W.conjTranspose * W = 1) (hW' : W * W.conjTranspose = 1) :
    hermitianSpectralFunction f (W * A * W.conjTranspose) =
      W * hermitianSpectralFunction f A * W.conjTranspose := by
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
  have e1 : W * A * W.conjTranspose =
      (W * U) * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) *
        (W * U).conjTranspose := by
    conv_lhs => rw [hspec]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hWU1 : (W * U).conjTranspose * (W * U) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W.conjTranspose, hW,
      Matrix.one_mul, hU1]
  have hWU2 : (W * U) * (W * U).conjTranspose = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU2,
      Matrix.one_mul, hW']
  rw [e1, hsf_spectral_form f (W * U) hA.eigenvalues hWU1 hWU2]
  have e2 : hermitianSpectralFunction f A =
      U * Matrix.diagonal (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) * U.conjTranspose := by
    conv_lhs => rw [hspec]
    exact hsf_spectral_form f U hA.eigenvalues hU1 hU2
  rw [e2]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofSpectral
