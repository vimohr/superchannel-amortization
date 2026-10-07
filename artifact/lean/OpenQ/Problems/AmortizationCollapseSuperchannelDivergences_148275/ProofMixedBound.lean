import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPureBound
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofConvex

/-!
# Portable proof: from pure triples to all qubit density triples

`moment_le_bloch`: for all Bloch vectors `n₁, n₂, n₃` in the closed unit ball,
the locked order-3/2 moment of `ρ = blochMat (mρ n₁ n₂ n₃)` against
`σ = blochMat (mσ n₁ n₂ n₃)` is at most `87/50`.

Route (the reduction of claim c1, without an integral representation):
* `G_convex`: two-point joint convexity of the closed form for positive definite
  references, from `OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofConvex.moment_convex_pd`.
* `G_mix_le`: a mixture of a positive definite pair with a pair `(τ, τ)` whose
  `τ` may be singular. The pair `(τ_ε, τ_ε)`, `τ_ε = (1-ε)τ + ε/2`, is positive
  definite with moment one; the bound passes to `ε = 0` because the mixture has
  a positive definite reference there, where the closed form is continuous.
  No continuity across a support change is used.
* `good_mix`: the predicate `Good c m s := (|s|² < 1 ∧ G m s ≤ c) ∨ m = s` is
  closed under two-point mixtures.
* `chord`: every vector of the ball is a mixture of two unit vectors.
* three applications, one per encoded state.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofMixedBound

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofQubitMoment OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofBloch OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPureBound OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofConvex
open scoped ComplexOrder Topology

theorem G_self {t : Fin 3 → ℝ} (ht : dot t t < 1) : G t t = 1 := by
  have h : (1 - dot t t) ≠ 0 := by linarith
  unfold G
  rw [mul_div_assoc, div_self h, Real.sqrt_one]
  norm_num

theorem blochMat_mix_real (θ : ℝ) (m m' : Fin 3 → ℝ) :
    blochMat ((1 - θ) • m + θ • m') = (1 - θ) • blochMat m + θ • blochMat m' := by
  rw [blochMat_mix, Complex.coe_smul, Complex.coe_smul]

/-- Convexity of the squared norm. -/
theorem dot_mix_le (u v : Fin 3 → ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    dot ((1 - θ) • u + θ • v) ((1 - θ) • u + θ • v) ≤ (1 - θ) * dot u u + θ * dot v v := by
  have key : (1 - θ) * dot u u + θ * dot v v - dot ((1 - θ) • u + θ • v) ((1 - θ) • u + θ • v)
      = θ * (1 - θ) * ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2) := by
    simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have : 0 ≤ θ * (1 - θ) * ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2) :=
    mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) (by positivity)
  linarith

/-- Two-point joint convexity of the closed form, positive definite references. -/
theorem G_convex {m1 s1 m2 s2 : Fin 3 → ℝ} (hm1 : dot m1 m1 ≤ 1) (hs1 : dot s1 s1 < 1)
    (hm2 : dot m2 m2 ≤ 1) (hs2 : dot s2 s2 < 1) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    G ((1 - θ) • m1 + θ • m2) ((1 - θ) • s1 + θ • s2) ≤ (1 - θ) * G m1 s1 + θ * G m2 s2 := by
  have hm : dot ((1 - θ) • m1 + θ • m2) ((1 - θ) • m1 + θ • m2) ≤ 1 := by
    have := dot_mix_le m1 m2 h0 h1
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hm2), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hm1)]
  have hs : dot ((1 - θ) • s1 + θ • s2) ((1 - θ) • s1 + θ • s2) < 1 := by
    have := dot_mix_le s1 s2 h0 h1
    rcases eq_or_lt_of_le h0 with hθ | hθ
    · rw [← hθ] at this ⊢
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      exact hs1
    · nlinarith [mul_pos hθ (sub_pos.2 hs2), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hs1.le)]
  have hconv := moment_convex_pd (blochMat_posSemidef hm1) (blochMat_posSemidef hm2)
    (blochMat_posDef hs1) (blochMat_posDef hs2) h0 h1
  rw [← blochMat_mix_real, ← blochMat_mix_real, moment_bloch hm hs, moment_bloch hm1 hs1,
    moment_bloch hm2 hs2] at hconv
  exact hconv

/-- Continuity of the closed form along a path, at a point where the reference
is positive definite. -/
theorem continuousAt_G_path {d1 d2 d3 : ℝ → ℝ} {x0 : ℝ} (h1 : ContinuousAt d1 x0)
    (h2 : ContinuousAt d2 x0) (h3 : ContinuousAt d3 x0) (hD : 1 - d2 x0 ≠ 0)
    (hden : Real.sqrt (2 * (1 - d1 x0) / (1 - d2 x0)
      + 2 * Real.sqrt ((1 - d3 x0) / (1 - d2 x0))) ≠ 0) :
    ContinuousAt (fun x => (2 * (1 - d1 x) / (1 - d2 x) + Real.sqrt ((1 - d3 x) / (1 - d2 x))
        - (1 - d3 x) / (1 - d2 x))
      / Real.sqrt (2 * (1 - d1 x) / (1 - d2 x) + 2 * Real.sqrt ((1 - d3 x) / (1 - d2 x)))) x0 := by
  have hD' : ContinuousAt (fun x => 1 - d2 x) x0 := continuousAt_const.sub h2
  have hT : ContinuousAt (fun x => 2 * (1 - d1 x) / (1 - d2 x)) x0 :=
    (continuousAt_const.mul (continuousAt_const.sub h1)).div hD' hD
  have hQ : ContinuousAt (fun x => (1 - d3 x) / (1 - d2 x)) x0 :=
    (continuousAt_const.sub h3).div hD' hD
  have hsQ : ContinuousAt (fun x => Real.sqrt ((1 - d3 x) / (1 - d2 x))) x0 := hQ.sqrt
  exact ((hT.add hsQ).sub hQ).div (hT.add (continuousAt_const.mul hsQ)).sqrt hden

/-- Mixture of a positive definite pair with a pair `(τ, τ)`, `τ` possibly singular. -/
theorem G_mix_le {c : ℝ} (hc : 1 ≤ c) {m1 s1 t : Fin 3 → ℝ} (hm1 : dot m1 m1 ≤ 1)
    (hs1 : dot s1 s1 < 1) (ht : dot t t ≤ 1) (hG : G m1 s1 ≤ c) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ < 1) :
    dot ((1 - θ) • s1 + θ • t) ((1 - θ) • s1 + θ • t) < 1 ∧
      G ((1 - θ) • m1 + θ • t) ((1 - θ) • s1 + θ • t) ≤ c := by
  have hθ : 0 < 1 - θ := sub_pos.2 h1
  -- the mixture has a positive definite reference for every τ in the ball
  have strict : ∀ t' : Fin 3 → ℝ, dot t' t' ≤ 1 →
      dot ((1 - θ) • s1 + θ • t') ((1 - θ) • s1 + θ • t') < 1 := by
    intro t' ht'
    have := dot_mix_le s1 t' h0 h1.le
    nlinarith [mul_pos hθ (sub_pos.2 hs1), mul_nonneg h0 (sub_nonneg.2 ht')]
  have ball : ∀ t' : Fin 3 → ℝ, dot t' t' ≤ 1 →
      dot ((1 - θ) • m1 + θ • t') ((1 - θ) • m1 + θ • t') ≤ 1 := by
    intro t' ht'
    have := dot_mix_le m1 t' h0 h1.le
    nlinarith [mul_nonneg hθ.le (sub_nonneg.2 hm1), mul_nonneg h0 (sub_nonneg.2 ht')]
  refine ⟨strict t ht, ?_⟩
  -- shrunk copies of τ
  have shrink : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → dot ((1 - ε) • t) ((1 - ε) • t) < 1 := by
    intro ε he0 he1
    have : dot ((1 - ε) • t) ((1 - ε) • t) = (1 - ε) ^ 2 * dot t t := by
      simp only [dot, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    have h2 : (1 - ε) ^ 2 < 1 := by nlinarith
    have h3 : 0 ≤ dot t t := by simp only [dot]; nlinarith [sq_nonneg (t 0), sq_nonneg (t 1), sq_nonneg (t 2)]
    nlinarith [sq_nonneg (1 - ε)]
  have bound : ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) 1 →
      G ((1 - θ) • m1 + θ • ((1 - ε) • t)) ((1 - θ) • s1 + θ • ((1 - ε) • t)) ≤ c := by
    intro ε hε
    have hsh := shrink ε hε.1 hε.2
    have := G_convex hm1 hs1 hsh.le hsh h0 h1.le
    rw [G_self hsh] at this
    nlinarith
  -- continuity at ε = 0
  have hcont : ContinuousAt (fun ε : ℝ =>
      G ((1 - θ) • m1 + θ • ((1 - ε) • t)) ((1 - θ) • s1 + θ • ((1 - ε) • t))) 0 := by
    have c1 : ContinuousAt (fun ε : ℝ => dot ((1 - θ) • m1 + θ • ((1 - ε) • t))
        ((1 - θ) • s1 + θ • ((1 - ε) • t))) 0 := by
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have c2 : ContinuousAt (fun ε : ℝ => dot ((1 - θ) • s1 + θ • ((1 - ε) • t))
        ((1 - θ) • s1 + θ • ((1 - ε) • t))) 0 := by
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have c3 : ContinuousAt (fun ε : ℝ => dot ((1 - θ) • m1 + θ • ((1 - ε) • t))
        ((1 - θ) • m1 + θ • ((1 - ε) • t))) 0 := by
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have ht0 : dot ((1 - (0 : ℝ)) • t) ((1 - (0 : ℝ)) • t) ≤ 1 := by simpa using ht
    have hs0 := strict _ ht0
    have hm0 := ball _ ht0
    have hD : 1 - dot ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))
        ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t)) ≠ 0 := by linarith
    have hms := dot_lt_one hm0 hs0
    have hden : Real.sqrt (2 * (1 - dot ((1 - θ) • m1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t)))
        / (1 - dot ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t)))
        + 2 * Real.sqrt ((1 - dot ((1 - θ) • m1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • m1 + θ • ((1 - (0 : ℝ)) • t)))
        / (1 - dot ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))))) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      have hpos : 0 < 2 * (1 - dot ((1 - θ) • m1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t)))
        / (1 - dot ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))) :=
        div_pos (by linarith) (by linarith)
      have := Real.sqrt_nonneg ((1 - dot ((1 - θ) • m1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • m1 + θ • ((1 - (0 : ℝ)) • t)))
        / (1 - dot ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))
          ((1 - θ) • s1 + θ • ((1 - (0 : ℝ)) • t))))
      linarith
    exact continuousAt_G_path c1 c2 c3 hD hden
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      G ((1 - θ) • m1 + θ • ((1 - ε) • t)) ((1 - θ) • s1 + θ • ((1 - ε) • t)) ≤ c :=
    Filter.eventually_of_mem (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) bound
  have hle := le_of_tendsto hlim hev
  simpa using hle

/-- Either the reference is positive definite and the closed form is bounded
by `c`, or numerator and reference coincide (moment one). -/
def Good (c : ℝ) (m s : Fin 3 → ℝ) : Prop := (dot s s < 1 ∧ G m s ≤ c) ∨ m = s

/-- `Good c` is closed under two-point mixtures of pairs in the ball. -/
theorem good_mix {c : ℝ} (hc : 1 ≤ c) {m1 s1 m2 s2 : Fin 3 → ℝ} (hm1 : dot m1 m1 ≤ 1)
    (hs1 : dot s1 s1 ≤ 1) (hm2 : dot m2 m2 ≤ 1) (hs2 : dot s2 s2 ≤ 1) (g1 : Good c m1 s1)
    (g2 : Good c m2 s2) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Good c ((1 - θ) • m1 + θ • m2) ((1 - θ) • s1 + θ • s2) := by
  rcases g1 with ⟨p1, b1⟩ | e1 <;> rcases g2 with ⟨p2, b2⟩ | e2
  · left
    have hconv := G_convex hm1 p1 hm2 p2 h0 h1
    refine ⟨?_, ?_⟩
    · have := dot_mix_le s1 s2 h0 h1
      rcases eq_or_lt_of_le h0 with hθ | hθ
      · rw [← hθ]
        simp only [sub_zero, one_smul, zero_smul, add_zero]
        exact p1
      · nlinarith [mul_pos hθ (sub_pos.2 p2), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 p1.le)]
    · nlinarith [mul_nonneg h0 (sub_nonneg.2 b2), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 b1)]
  · -- first pair positive definite, second pair (τ, τ)
    subst e2
    rcases eq_or_lt_of_le h1 with hθ | hθ
    · right
      rw [hθ]
      simp
    · left
      exact G_mix_le hc hm1 p1 hs2 b1 h0 hθ
  · -- first pair (τ, τ), second pair positive definite: swap the roles
    subst e1
    rcases eq_or_lt_of_le h0 with hθ | hθ
    · right
      rw [← hθ]
      simp
    · left
      have h := G_mix_le hc hm2 p2 hs1 b2 (θ := 1 - θ) (by linarith) (by linarith)
      have e : ∀ u v : Fin 3 → ℝ, (1 - (1 - θ)) • u + (1 - θ) • v = (1 - θ) • v + θ • u := by
        intro u v
        rw [sub_sub_cancel, add_comm]
      rw [e, e] at h
      exact h
  · right
    rw [e1, e2]

/-- Every point of the closed unit ball is a mixture of two points of the sphere. -/
theorem chord (n : Fin 3 → ℝ) (hn : dot n n ≤ 1) :
    ∃ (e e' : Fin 3 → ℝ) (θ : ℝ), dot e e = 1 ∧ dot e' e' = 1 ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      n = (1 - θ) • e + θ • e' := by
  by_cases h : dot n n = 0
  · have h' := h
    simp only [dot] at h'
    have z0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    have z1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    have z2 : n 2 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    refine ⟨![0, 0, 1], ![0, 0, -1], 1 / 2, by simp [dot], by simp [dot], by norm_num,
      by norm_num, ?_⟩
    funext i
    fin_cases i
    · simp [z0]
    · simp [z1]
    · simp [z2]; norm_num
  · have hpos : 0 < dot n n := by
      have : 0 ≤ dot n n := by
        simp only [dot]; nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
      exact lt_of_le_of_ne this (Ne.symm h)
    obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (dot n n) := ⟨_, rfl⟩
    have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = dot n n := by rw [hr]; exact Real.sq_sqrt hpos.le
    have hr1 : r ≤ 1 := by nlinarith
    have unit : ∀ s : ℝ, s ^ 2 = (r⁻¹) ^ 2 → dot (s • n) (s • n) = 1 := by
      intro s hs
      have : dot (s • n) (s • n) = s ^ 2 * dot n n := by
        simp only [dot, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this, hs, ← hr2]
      field_simp
    refine ⟨r⁻¹ • n, (-r⁻¹) • n, (1 - r) / 2, unit _ rfl, unit _ (by ring), by linarith,
      by linarith, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

section assembly

variable {n1 n2 n3 : Fin 3 → ℝ}

theorem ball_mρ (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 ≤ 1) :
    dot (mρ n1 n2 n3) (mρ n1 n2 n3) ≤ 1 := by
  have key : dot n1 n1 / 2 + dot n2 n2 / 2 - dot (mρ n1 n2 n3) (mρ n1 n2 n3)
      = ((n1 0 - n2 0) ^ 2 + (n1 1 - n2 1) ^ 2 + (n1 2 - n2 2) ^ 2) / 4 := by
    simp only [dot, mρ]
    ring
  have : 0 ≤ ((n1 0 - n2 0) ^ 2 + (n1 1 - n2 1) ^ 2 + (n1 2 - n2 2) ^ 2) / 4 := by positivity
  linarith

theorem ball_mσ (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 ≤ 1) (h3 : dot n3 n3 ≤ 1) :
    dot (mσ n1 n2 n3) (mσ n1 n2 n3) ≤ 1 := by
  have key : dot n1 n1 / 10 + 3 * dot n2 n2 / 10 + 3 * dot n3 n3 / 5
        - dot (mσ n1 n2 n3) (mσ n1 n2 n3)
      = 3 / 100 * ((n1 0 - n2 0) ^ 2 + (n1 1 - n2 1) ^ 2 + (n1 2 - n2 2) ^ 2)
        + 6 / 100 * ((n1 0 - n3 0) ^ 2 + (n1 1 - n3 1) ^ 2 + (n1 2 - n3 2) ^ 2)
        + 18 / 100 * ((n2 0 - n3 0) ^ 2 + (n2 1 - n3 1) ^ 2 + (n2 2 - n3 2) ^ 2) := by
    simp only [dot, mσ]
    ring
  have : 0 ≤ 3 / 100 * ((n1 0 - n2 0) ^ 2 + (n1 1 - n2 1) ^ 2 + (n1 2 - n2 2) ^ 2)
        + 6 / 100 * ((n1 0 - n3 0) ^ 2 + (n1 1 - n3 1) ^ 2 + (n1 2 - n3 2) ^ 2)
        + 18 / 100 * ((n2 0 - n3 0) ^ 2 + (n2 1 - n3 1) ^ 2 + (n2 2 - n3 2) ^ 2) := by
    positivity
  linarith

/-- Pure triples. -/
theorem good_pure (h1 : dot n1 n1 = 1) (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1) :
    Good (87 / 50) (mρ n1 n2 n3) (mσ n1 n2 n3) := by
  by_cases hS : dot (mσ n1 n2 n3) (mσ n1 n2 n3) < 1
  · exact Or.inl ⟨hS, pure_bound h1 h2 h3 hS⟩
  · exact Or.inr (coincident h1 h2 h3 hS)

theorem mρ_mix1 (θ : ℝ) (e e' : Fin 3 → ℝ) :
    mρ ((1 - θ) • e + θ • e') n2 n3 = (1 - θ) • mρ e n2 n3 + θ • mρ e' n2 n3 := by
  funext i
  simp only [mρ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mσ_mix1 (θ : ℝ) (e e' : Fin 3 → ℝ) :
    mσ ((1 - θ) • e + θ • e') n2 n3 = (1 - θ) • mσ e n2 n3 + θ • mσ e' n2 n3 := by
  funext i
  simp only [mσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mρ_mix2 (θ : ℝ) (e e' : Fin 3 → ℝ) :
    mρ n1 ((1 - θ) • e + θ • e') n3 = (1 - θ) • mρ n1 e n3 + θ • mρ n1 e' n3 := by
  funext i
  simp only [mρ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mσ_mix2 (θ : ℝ) (e e' : Fin 3 → ℝ) :
    mσ n1 ((1 - θ) • e + θ • e') n3 = (1 - θ) • mσ n1 e n3 + θ • mσ n1 e' n3 := by
  funext i
  simp only [mσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mρ_mix3 (θ : ℝ) (e e' : Fin 3 → ℝ) :
    mρ n1 n2 ((1 - θ) • e + θ • e') = (1 - θ) • mρ n1 n2 e + θ • mρ n1 n2 e' := by
  funext i
  simp only [mρ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mσ_mix3 (θ : ℝ) (e e' : Fin 3 → ℝ) :
    mσ n1 n2 ((1 - θ) • e + θ • e') = (1 - θ) • mσ n1 n2 e + θ • mσ n1 n2 e' := by
  funext i
  simp only [mσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- First state mixed, the other two pure. -/
theorem good_one (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1) :
    Good (87 / 50) (mρ n1 n2 n3) (mσ n1 n2 n3) := by
  obtain ⟨e, e', θ, he, he', h0, hθ1, rfl⟩ := chord n1 h1
  rw [mρ_mix1, mσ_mix1]
  exact good_mix (by norm_num) (ball_mρ he.le h2.le) (ball_mσ he.le h2.le h3.le)
    (ball_mρ he'.le h2.le) (ball_mσ he'.le h2.le h3.le) (good_pure he h2 h3)
    (good_pure he' h2 h3) h0 hθ1

/-- First two states mixed, the third pure. -/
theorem good_two (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 ≤ 1) (h3 : dot n3 n3 = 1) :
    Good (87 / 50) (mρ n1 n2 n3) (mσ n1 n2 n3) := by
  obtain ⟨e, e', θ, he, he', h0, hθ1, rfl⟩ := chord n2 h2
  rw [mρ_mix2, mσ_mix2]
  exact good_mix (by norm_num) (ball_mρ h1 he.le) (ball_mσ h1 he.le h3.le)
    (ball_mρ h1 he'.le) (ball_mσ h1 he'.le h3.le) (good_one h1 he h3)
    (good_one h1 he' h3) h0 hθ1

/-- All three states mixed. -/
theorem good_all (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 ≤ 1) (h3 : dot n3 n3 ≤ 1) :
    Good (87 / 50) (mρ n1 n2 n3) (mσ n1 n2 n3) := by
  obtain ⟨e, e', θ, he, he', h0, hθ1, rfl⟩ := chord n3 h3
  rw [mρ_mix3, mσ_mix3]
  exact good_mix (by norm_num) (ball_mρ h1 h2) (ball_mσ h1 h2 he.le)
    (ball_mρ h1 h2) (ball_mσ h1 h2 he'.le) (good_two h1 h2 he)
    (good_two h1 h2 he') h0 hθ1

/-- The reduction of claim c1 for an arbitrary bound `c ≥ 1`: if every pure
triple is `Good c`, so is every triple of the ball. -/
theorem good_all_of_pure {c : ℝ} (hc : 1 ≤ c)
    (hp : ∀ u1 u2 u3 : Fin 3 → ℝ, dot u1 u1 = 1 → dot u2 u2 = 1 → dot u3 u3 = 1 →
      Good c (mρ u1 u2 u3) (mσ u1 u2 u3))
    (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 ≤ 1) (h3 : dot n3 n3 ≤ 1) :
    Good c (mρ n1 n2 n3) (mσ n1 n2 n3) := by
  have one : ∀ u1 u2 u3 : Fin 3 → ℝ, dot u1 u1 ≤ 1 → dot u2 u2 = 1 → dot u3 u3 = 1 →
      Good c (mρ u1 u2 u3) (mσ u1 u2 u3) := by
    intro u1 u2 u3 k1 k2 k3
    obtain ⟨e, e', θ, he, he', h0, hθ1, rfl⟩ := chord u1 k1
    rw [mρ_mix1, mσ_mix1]
    exact good_mix hc (ball_mρ he.le k2.le) (ball_mσ he.le k2.le k3.le)
      (ball_mρ he'.le k2.le) (ball_mσ he'.le k2.le k3.le) (hp _ _ _ he k2 k3)
      (hp _ _ _ he' k2 k3) h0 hθ1
  have two : ∀ u1 u2 u3 : Fin 3 → ℝ, dot u1 u1 ≤ 1 → dot u2 u2 ≤ 1 → dot u3 u3 = 1 →
      Good c (mρ u1 u2 u3) (mσ u1 u2 u3) := by
    intro u1 u2 u3 k1 k2 k3
    obtain ⟨e, e', θ, he, he', h0, hθ1, rfl⟩ := chord u2 k2
    rw [mρ_mix2, mσ_mix2]
    exact good_mix hc (ball_mρ k1 he.le) (ball_mσ k1 he.le k3.le)
      (ball_mρ k1 he'.le) (ball_mσ k1 he'.le k3.le) (one _ _ _ k1 he k3)
      (one _ _ _ k1 he' k3) h0 hθ1
  obtain ⟨e, e', θ, he, he', h0, hθ1, rfl⟩ := chord n3 h3
  rw [mρ_mix3, mσ_mix3]
  exact good_mix hc (ball_mρ h1 h2) (ball_mσ h1 h2 he.le)
    (ball_mρ h1 h2) (ball_mσ h1 h2 he'.le) (two _ _ _ h1 h2 he)
    (two _ _ _ h1 h2 he') h0 hθ1

/-- The bound of claim c2 for every triple of qubit density matrices, in Bloch form,
on the locked moment. -/
theorem moment_le_bloch (h1 : dot n1 n1 ≤ 1) (h2 : dot n2 n2 ≤ 1) (h3 : dot n3 n3 ≤ 1) :
    geometricMoment (3 / 2) (blochMat (mρ n1 n2 n3)) (blochMat (mσ n1 n2 n3)) ≤ 87 / 50 := by
  have hm := ball_mρ (n3 := n3) h1 h2
  rcases good_all h1 h2 h3 with ⟨hs, hG⟩ | heq
  · rw [moment_bloch hm hs]
    exact hG
  · rw [heq, geometricMoment_self (blochMat_posSemidef (ball_mσ h1 h2 h3)) (3 / 2) (by norm_num),
      blochMat_trace]
    norm_num

end assembly

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofMixedBound
