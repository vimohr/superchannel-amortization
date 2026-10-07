import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Portable proof: the scalar part of claims c1 and c2

Real analysis only; no project definition is used.

* `J_pos`: the degree-six gap polynomial is at least `900000` on `[0, 2]`
  (Bernstein form on four intervals, each identity checked by `ring`).
* `F_le`: `(T + q - q²)/√(T + 2q) ≤ 87/50` whenever `0 ≤ q ≤ 2`,
  `0 < T + 2q` and `T ≤ U q`.
* `triangle_bound`: the bound for every nonnegative `a, b, c` with
  `(b + c - a)² ≤ 4bc` and `S > 0`, with `T`, `P` as in claim c1.
* `constraint_17`: the invariant inequality of claim c1.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofScalar

/-- The certified integer polynomial of the proof note, Eq. (20). -/
def J (q : ℝ) : ℝ :=
  7979950 - 8315351 * q - 9431541 * q ^ 2 + 7841845 * q ^ 3 + 5281750 * q ^ 4
    - 495000 * q ^ 5 - 253125 * q ^ 6

/-- The rational upper bound on the trace invariant, Eq. (19). -/
noncomputable def U (q : ℝ) : ℝ := 5 / 2 + 271 / 220 * q + 4 / 5 * q ^ 2 - 9 / 44 * q ^ 3

theorem gap_identity (q : ℝ) :
    (87 / 50 : ℝ) ^ 2 * (U q + 2 * q) - (U q + q - q ^ 2) ^ 2 = J q / 6050000 := by
  unfold U J
  ring

private theorem bern_nonneg {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (c0 c1 c2 c3 c4 c5 c6 : ℝ) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3)
    (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) :
    0 ≤ c0 * s ^ 6 + c1 * t * s ^ 5 + c2 * t ^ 2 * s ^ 4 + c3 * t ^ 3 * s ^ 3
      + c4 * t ^ 4 * s ^ 2 + c5 * t ^ 5 * s + c6 * t ^ 6 := by
  positivity

theorem J_ge (q : ℝ) (h0 : 0 ≤ q) (h2 : q ≤ 2) : 900000 ≤ J q := by
  have piece : ∀ (j : ℝ) (c0 c1 c2 c3 c4 c5 c6 : ℝ),
      0 ≤ c0 → 0 ≤ c1 → 0 ≤ c2 → 0 ≤ c3 → 0 ≤ c4 → 0 ≤ c5 → 0 ≤ c6 →
      j ≤ 2 * q → 2 * q ≤ j + 1 →
      J q - 900000 = c0 * (j + 1 - 2 * q) ^ 6 + c1 * (2 * q - j) * (j + 1 - 2 * q) ^ 5
        + c2 * (2 * q - j) ^ 2 * (j + 1 - 2 * q) ^ 4 + c3 * (2 * q - j) ^ 3 * (j + 1 - 2 * q) ^ 3
        + c4 * (2 * q - j) ^ 4 * (j + 1 - 2 * q) ^ 2 + c5 * (2 * q - j) ^ 5 * (j + 1 - 2 * q)
        + c6 * (2 * q - j) ^ 6 → 900000 ≤ J q := by
    intro j c0 c1 c2 c3 c4 c5 c6 k0 k1 k2 k3 k4 k5 k6 hl hr hid
    have := bern_nonneg (t := 2 * q - j) (s := j + 1 - 2 * q) (by linarith) (by linarith)
      c0 c1 c2 c3 c4 c5 c6 k0 k1 k2 k3 k4 k5 k6
    linarith
  rcases le_total (2 * q) 1 with h1 | h1
  · exact piece 0 7079950 (76644049 / 2) (332211949 / 4) (732567477 / 8) (214983939 / 4)
      (126761787 / 8) (118739547 / 64) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)
      (by unfold J; ring)
  rcases le_total (2 * q) 2 with h2' | h2'
  · exact piece 1 (118739547 / 64) (102695067 / 16) (105793221 / 16) (11495007 / 8)
      (4745779 / 4) 3510992 1708528 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)
      (by unfold J; ring)
  rcases le_total (2 * q) 3 with h3 | h3
  · exact piece 2 1708528 16991344 (274352819 / 4) (1127835857 / 8) (2490125681 / 16)
      (1406585617 / 16) (1276728595 / 64) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)
      (by unfold J; ring)
  · exact piece 3 (1276728595 / 64) (302950021 / 2) (1893799609 / 4) (6235526427 / 8)
      (2850815919 / 4) (686233503 / 2) 67925844 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)
      (by unfold J; ring)

theorem J_pos (q : ℝ) (h0 : 0 ≤ q) (h2 : q ≤ 2) : 0 < J q := by
  have := J_ge q h0 h2
  linarith

/-- `U q + 2 q ≥ 5/2` on `[0, 2]`. -/
theorem U_add_pos (q : ℝ) (h0 : 0 ≤ q) (h2 : q ≤ 2) : 5 / 2 ≤ U q + 2 * q := by
  unfold U
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h2), mul_nonneg h0 h0,
    mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h2)]

/-- The moment bound on the relaxed scalar domain. No derivative is used: with
`w = √(T + 2q)` the claim is `w² - q - q² ≤ (87/50) w` for `0 < w ≤ w_U`, and a
convex quadratic in `w` that is nonpositive at `0` and at `w_U` is nonpositive between. -/
theorem F_le (T q : ℝ) (hq0 : 0 ≤ q) (hq2 : q ≤ 2) (hT : 0 < T + 2 * q) (hTU : T ≤ U q) :
    (T + q - q ^ 2) / Real.sqrt (T + 2 * q) ≤ 87 / 50 := by
  set w := Real.sqrt (T + 2 * q) with hw
  set wU := Real.sqrt (U q + 2 * q) with hwU
  have hw0 : 0 < w := Real.sqrt_pos.2 hT
  have hUpos : 0 ≤ U q + 2 * q := by linarith [U_add_pos q hq0 hq2]
  have hwle : w ≤ wU := Real.sqrt_le_sqrt (by linarith)
  have hwsq : w ^ 2 = T + 2 * q := Real.sq_sqrt hT.le
  have hwUsq : wU ^ 2 = U q + 2 * q := Real.sq_sqrt hUpos
  have hwU0 : 0 < wU := lt_of_lt_of_le hw0 hwle
  -- endpoint: U + q - q² ≤ (87/50) wU, from the gap polynomial
  have hgap : (U q + q - q ^ 2) ^ 2 ≤ ((87 / 50 : ℝ) * wU) ^ 2 := by
    have h1 := gap_identity q
    have h2 := J_pos q hq0 hq2
    have h3 : 0 < J q / 6050000 := by positivity
    rw [mul_pow, hwUsq]
    linarith
  have hend : U q + q - q ^ 2 ≤ 87 / 50 * wU :=
    le_trans (le_abs_self _) (abs_le_of_sq_le_sq hgap (by positivity))
  -- wU² - q - q² ≤ (87/50) wU
  have hend' : wU ^ 2 - q - q ^ 2 ≤ 87 / 50 * wU := by rw [hwUsq]; linarith
  have hc : 0 ≤ q + q ^ 2 := by positivity
  have hmain : w ^ 2 - q - q ^ 2 ≤ 87 / 50 * w := by
    have h1 : 0 ≤ (wU - w) * w := mul_nonneg (sub_nonneg.2 hwle) hw0.le
    have h2 : 0 ≤ w * (87 / 50 * wU - (wU ^ 2 - q - q ^ 2)) :=
      mul_nonneg hw0.le (sub_nonneg.2 hend')
    have h3 : 0 ≤ (q + q ^ 2) * (wU - w) := mul_nonneg hc (sub_nonneg.2 hwle)
    have h4 : wU * (w ^ 2 - q - q ^ 2 - 87 / 50 * w) ≤ 0 := by nlinarith
    by_contra hcon
    push Not at hcon
    have : 0 < wU * (w ^ 2 - q - q ^ 2 - 87 / 50 * w) := mul_pos hwU0 (by linarith)
    linarith
  rw [div_le_iff₀ hw0]
  have : T + q - q ^ 2 = w ^ 2 - q - q ^ 2 := by rw [hwsq]; ring
  rw [this]
  exact hmain

/-- The invariant inequality of claim c1 (Eq. (17) of the note), from the
triangle condition `(b + c - a)² ≤ 4bc` on the squared distances. -/
theorem constraint_17 (a b c : ℝ)
    (hH : (b + c - a) ^ 2 ≤ 4 * b * c) (hS : 0 < 3 * a / 100 + 3 * b / 50 + 9 * c / 50) :
    100 * ((a / 5 + 3 * b / 10 + 3 * c / 10) / (3 * a / 100 + 3 * b / 50 + 9 * c / 50) - 5 / 2
        - 4 / 5 * (a / (4 * (3 * a / 100 + 3 * b / 50 + 9 * c / 50)))) ^ 2
      ≤ 15 * (a / (4 * (3 * a / 100 + 3 * b / 50 + 9 * c / 50)))
        * (10 - 3 * (a / (4 * (3 * a / 100 + 3 * b / 50 + 9 * c / 50)))) := by
  generalize hSdef : 3 * a / 100 + 3 * b / 50 + 9 * c / 50 = S at hS ⊢
  have hS0 : S ≠ 0 := hS.ne'
  have hpoly : 15 * (a / 4) * (10 * S - 3 * a / 4)
      - 100 * ((a / 5 + 3 * b / 10 + 3 * c / 10) - 5 * S / 2 - a / 5) ^ 2
      = 9 / 4 * (4 * b * c - (b + c - a) ^ 2) := by
    rw [← hSdef]
    ring
  have key : 15 * (a / (4 * S)) * (10 - 3 * (a / (4 * S)))
      - 100 * ((a / 5 + 3 * b / 10 + 3 * c / 10) / S - 5 / 2 - 4 / 5 * (a / (4 * S))) ^ 2
      = 9 / 4 * (4 * b * c - (b + c - a) ^ 2) / S ^ 2 := by
    rw [← hpoly]
    field_simp
  have : 0 ≤ 9 / 4 * (4 * b * c - (b + c - a) ^ 2) / S ^ 2 := by
    apply div_nonneg _ (by positivity)
    linarith
  linarith

/-- The scalar bound behind claim c2: all nonnegative squared distances with the
triangle condition and `S > 0`. -/
theorem triangle_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hH : (b + c - a) ^ 2 ≤ 4 * b * c) (hS : 0 < 3 * a / 100 + 3 * b / 50 + 9 * c / 50) :
    ((a / 5 + 3 * b / 10 + 3 * c / 10) / (3 * a / 100 + 3 * b / 50 + 9 * c / 50)
        + Real.sqrt (a / (4 * (3 * a / 100 + 3 * b / 50 + 9 * c / 50)))
        - a / (4 * (3 * a / 100 + 3 * b / 50 + 9 * c / 50)))
      / Real.sqrt ((a / 5 + 3 * b / 10 + 3 * c / 10) / (3 * a / 100 + 3 * b / 50 + 9 * c / 50)
        + 2 * Real.sqrt (a / (4 * (3 * a / 100 + 3 * b / 50 + 9 * c / 50)))) ≤ 87 / 50 := by
  have h17 := constraint_17 a b c hH hS
  set S := 3 * a / 100 + 3 * b / 50 + 9 * c / 50 with hSdef
  set T := (a / 5 + 3 * b / 10 + 3 * c / 10) / S with hTdef
  set P := a / (4 * S) with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hT0 : 0 ≤ T := by positivity
  set q := Real.sqrt P with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg P
  have hqsq : q ^ 2 = P := Real.sq_sqrt hP0
  -- P ≤ 10/3
  have hP3 : P ≤ 10 / 3 := by
    by_contra hcon
    push Not at hcon
    have : 15 * P * (10 - 3 * P) < 0 := by nlinarith
    nlinarith [sq_nonneg (T - 5 / 2 - 4 / 5 * P)]
  have hq2 : q ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  -- T > 0 because S > 0 forces a positive numerator
  have hTpos : 0 < T := by
    apply div_pos _ hS
    by_contra hcon
    push Not at hcon
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hc0 : c = 0 := by nlinarith
    rw [hSdef, ha0, hb0, hc0] at hS
    norm_num at hS
  -- T ≤ U q by the tangent of the square root at 11
  have hTU : T ≤ U q := by
    set d := T - 5 / 2 - 4 / 5 * P with hd
    have hz : 0 ≤ 150 - 45 * q ^ 2 := by rw [hqsq]; linarith
    have hd2 : d ^ 2 ≤ (q * ((150 - 45 * q ^ 2) + 121) / 220) ^ 2 := by
      have e1 : 100 * d ^ 2 ≤ q ^ 2 * (150 - 45 * q ^ 2) := by
        have : 15 * P * (10 - 3 * P) = q ^ 2 * (150 - 45 * q ^ 2) := by rw [hqsq]; ring
        linarith
      have e2 : (q * ((150 - 45 * q ^ 2) + 121) / 220) ^ 2
          - q ^ 2 * (150 - 45 * q ^ 2) / 100
          = q ^ 2 * ((150 - 45 * q ^ 2) - 121) ^ 2 / 48400 := by ring
      have e3 : 0 ≤ q ^ 2 * ((150 - 45 * q ^ 2) - 121) ^ 2 / 48400 := by positivity
      linarith
    have hr : 0 ≤ q * ((150 - 45 * q ^ 2) + 121) / 220 := by positivity
    have hd' : d ≤ q * ((150 - 45 * q ^ 2) + 121) / 220 :=
      le_trans (le_abs_self _) (abs_le_of_sq_le_sq hd2 hr)
    have : U q = 5 / 2 + 4 / 5 * P + q * ((150 - 45 * q ^ 2) + 121) / 220 := by
      unfold U; rw [← hqsq]; ring
    rw [this]
    linarith
  have := F_le T q hq0 hq2 (by linarith) hTU
  rw [hqsq] at this
  exact this

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofScalar
