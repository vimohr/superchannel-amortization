import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofBloch
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofScalar

/-!
# Portable proof: the bound for pure qubit triples

For unit Bloch vectors `n₁, n₂, n₃` the output pair of the preparation model is
`ρ = blochMat (mρ n₁ n₂ n₃)`, `σ = blochMat (mσ n₁ n₂ n₃)` with weights
`p = (1/2, 1/2, 0)` and `r = (1/10, 3/10, 3/5)`.

* `invariants`: with `a = (1 - n₁·n₂)/2`, `b = (1 - n₁·n₃)/2`, `c = (1 - n₂·n₃)/2`
  (these are `1 - |⟨ψ_x, ψ_y⟩|²`), `det σ = S`, `det ρ = a/4` and
  `tr(adj σ · ρ) = a/5 + 3b/10 + 3c/10`, in the form used by `G`.
* `triangle`: `(b + c - a)² ≤ 4bc` (Cauchy-Schwarz on Bloch differences).
* `pure_bound`: `G ≤ 87/50` when `σ` is positive definite.
* `coincident`: otherwise the three vectors coincide and `ρ = σ`.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPureBound

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofBloch OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofScalar

/-- Bloch vector of `ρ = (κ₁ + κ₂)/2`. The third argument is kept for symmetry. -/
noncomputable def mρ (n1 n2 _n3 : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => n1 i / 2 + n2 i / 2

/-- Bloch vector of `σ = κ₁/10 + 3κ₂/10 + 3κ₃/5`. -/
noncomputable def mσ (n1 n2 n3 : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => n1 i / 10 + 3 * n2 i / 10 + 3 * n3 i / 5

/-- `triangle_bound` with the invariants as free variables. -/
theorem triangle_bound' (a b c S N T P : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hH : (b + c - a) ^ 2 ≤ 4 * b * c) (hSdef : S = 3 * a / 100 + 3 * b / 50 + 9 * c / 50)
    (hS : 0 < S) (hN : N = a / 5 + 3 * b / 10 + 3 * c / 10) (hT : T = N / S)
    (hP : P = a / (4 * S)) :
    (T + Real.sqrt P - P) / Real.sqrt (T + 2 * Real.sqrt P) ≤ 87 / 50 := by
  subst hT hP hN hSdef
  exact triangle_bound a b c ha hb hc hH hS

section

variable {n1 n2 n3 : Fin 3 → ℝ}

theorem invariants (h1 : dot n1 n1 = 1) (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1) :
    1 - dot (mσ n1 n2 n3) (mσ n1 n2 n3)
        = 4 * (3 * ((1 - dot n1 n2) / 2) / 100 + 3 * ((1 - dot n1 n3) / 2) / 50
          + 9 * ((1 - dot n2 n3) / 2) / 50) ∧
      1 - dot (mρ n1 n2 n3) (mρ n1 n2 n3) = (1 - dot n1 n2) / 2 ∧
      1 - dot (mρ n1 n2 n3) (mσ n1 n2 n3)
        = 2 * (((1 - dot n1 n2) / 2) / 5 + 3 * ((1 - dot n1 n3) / 2) / 10
          + 3 * ((1 - dot n2 n3) / 2) / 10) := by
  simp only [dot, mρ, mσ] at *
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 / 100 : ℝ) * h1 + (-9 / 100 : ℝ) * h2 + (-36 / 100 : ℝ) * h3
  · linear_combination (-1 / 4 : ℝ) * h1 + (-1 / 4 : ℝ) * h2
  · linear_combination (-1 / 20 : ℝ) * h1 + (-3 / 20 : ℝ) * h2

/-- `(1 - nₓ·n_y)/2 = |nₓ - n_y|²/4` for unit vectors. -/
theorem half_one_sub_dot {u v : Fin 3 → ℝ} (hu : dot u u = 1) (hv : dot v v = 1) :
    (1 - dot u v) / 2 = ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2) / 4 := by
  simp only [dot] at *
  linear_combination (-1 / 4 : ℝ) * hu + (-1 / 4 : ℝ) * hv

/-- The triangle condition on the squared overlap distances of three pure qubit states. -/
theorem triangle (h1 : dot n1 n1 = 1) (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1) :
    ((1 - dot n1 n3) / 2 + (1 - dot n2 n3) / 2 - (1 - dot n1 n2) / 2) ^ 2
      ≤ 4 * ((1 - dot n1 n3) / 2) * ((1 - dot n2 n3) / 2) := by
  have hb := half_one_sub_dot h1 h3
  have hc := half_one_sub_dot h2 h3
  have hbca : (1 - dot n1 n3) / 2 + (1 - dot n2 n3) / 2 - (1 - dot n1 n2) / 2
      = ((n1 0 - n3 0) * (n2 0 - n3 0) + (n1 1 - n3 1) * (n2 1 - n3 1)
        + (n1 2 - n3 2) * (n2 2 - n3 2)) / 2 := by
    simp only [dot] at *
    linear_combination (-1 / 2 : ℝ) * h3
  rw [hbca, hb, hc]
  have key : 4 * (((n1 0 - n3 0) ^ 2 + (n1 1 - n3 1) ^ 2 + (n1 2 - n3 2) ^ 2) / 4)
        * (((n2 0 - n3 0) ^ 2 + (n2 1 - n3 1) ^ 2 + (n2 2 - n3 2) ^ 2) / 4)
      - (((n1 0 - n3 0) * (n2 0 - n3 0) + (n1 1 - n3 1) * (n2 1 - n3 1)
        + (n1 2 - n3 2) * (n2 2 - n3 2)) / 2) ^ 2
      = (((n1 0 - n3 0) * (n2 1 - n3 1) - (n1 1 - n3 1) * (n2 0 - n3 0)) ^ 2
        + ((n1 0 - n3 0) * (n2 2 - n3 2) - (n1 2 - n3 2) * (n2 0 - n3 0)) ^ 2
        + ((n1 1 - n3 1) * (n2 2 - n3 2) - (n1 2 - n3 2) * (n2 1 - n3 1)) ^ 2) / 4 := by
    ring
  have : 0 ≤ (((n1 0 - n3 0) * (n2 1 - n3 1) - (n1 1 - n3 1) * (n2 0 - n3 0)) ^ 2
        + ((n1 0 - n3 0) * (n2 2 - n3 2) - (n1 2 - n3 2) * (n2 0 - n3 0)) ^ 2
        + ((n1 1 - n3 1) * (n2 2 - n3 2) - (n1 2 - n3 2) * (n2 1 - n3 1)) ^ 2) / 4 := by
    positivity
  linarith

theorem half_one_sub_dot_nonneg {u v : Fin 3 → ℝ} (hu : dot u u = 1) (hv : dot v v = 1) :
    0 ≤ (1 - dot u v) / 2 := by
  rw [half_one_sub_dot hu hv]
  positivity

/-- Claim c2 for pure encodings with positive definite output reference, in the
closed form `G` of the locked moment. -/
theorem pure_bound (h1 : dot n1 n1 = 1) (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1)
    (hS : dot (mσ n1 n2 n3) (mσ n1 n2 n3) < 1) :
    G (mρ n1 n2 n3) (mσ n1 n2 n3) ≤ 87 / 50 := by
  obtain ⟨e1, e2, e3⟩ := invariants h1 h2 h3
  have ha := half_one_sub_dot_nonneg h1 h2
  have hb := half_one_sub_dot_nonneg h1 h3
  have hc := half_one_sub_dot_nonneg h2 h3
  have hH := triangle h1 h2 h3
  obtain ⟨a, hadef⟩ : ∃ a, a = (1 - dot n1 n2) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = (1 - dot n1 n3) / 2 := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = (1 - dot n2 n3) / 2 := ⟨_, rfl⟩
  rw [← hadef, ← hbdef, ← hcdef] at e1 e3 hH
  rw [← hadef] at e2 ha
  rw [← hbdef] at hb
  rw [← hcdef] at hc
  have hSpos : 0 < 3 * a / 100 + 3 * b / 50 + 9 * c / 50 := by linarith
  have hS0 : (3 * a / 100 + 3 * b / 50 + 9 * c / 50) ≠ 0 := hSpos.ne'
  unfold G
  rw [e1, e2, e3]
  exact triangle_bound' a b c (3 * a / 100 + 3 * b / 50 + 9 * c / 50)
    (a / 5 + 3 * b / 10 + 3 * c / 10) _ _ ha hb hc hH rfl hSpos rfl
    (by field_simp; ring) rfl

/-- If the output reference of a pure triple is singular, the three states
coincide, hence numerator and reference coincide. -/
theorem coincident (h1 : dot n1 n1 = 1) (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1)
    (hS : ¬ dot (mσ n1 n2 n3) (mσ n1 n2 n3) < 1) : mρ n1 n2 n3 = mσ n1 n2 n3 := by
  obtain ⟨e1, -, -⟩ := invariants h1 h2 h3
  have ha := half_one_sub_dot_nonneg h1 h2
  have hb := half_one_sub_dot_nonneg h1 h3
  have hc := half_one_sub_dot_nonneg h2 h3
  push Not at hS
  have ha0 : (1 - dot n1 n2) / 2 = 0 := by linarith
  have hb0 : (1 - dot n1 n3) / 2 = 0 := by linarith
  rw [half_one_sub_dot h1 h2] at ha0
  rw [half_one_sub_dot h1 h3] at hb0
  have eq_of_sq : ∀ x y z : ℝ, (x ^ 2 + y ^ 2 + z ^ 2) / 4 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    exact ⟨pow_eq_zero_iff (by norm_num) |>.1 hx, pow_eq_zero_iff (by norm_num) |>.1 hy,
      pow_eq_zero_iff (by norm_num) |>.1 hz⟩
  obtain ⟨x0, x1, x2⟩ := eq_of_sq _ _ _ ha0
  obtain ⟨y0, y1, y2⟩ := eq_of_sq _ _ _ hb0
  funext i
  fin_cases i
  · show n1 0 / 2 + n2 0 / 2 = n1 0 / 10 + 3 * n2 0 / 10 + 3 * n3 0 / 5
    linarith
  · show n1 1 / 2 + n2 1 / 2 = n1 1 / 10 + 3 * n2 1 / 10 + 3 * n3 1 / 5
    linarith
  · show n1 2 / 2 + n2 2 / 2 = n1 2 / 10 + 3 * n2 2 / 10 + 3 * n3 2 / 5
    linarith

end

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPureBound
