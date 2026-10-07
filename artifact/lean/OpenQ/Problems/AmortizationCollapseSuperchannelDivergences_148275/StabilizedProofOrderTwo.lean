/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticMainE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofRealize

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Assembly of the reviewed headline claim on the locked definitions of
`StabilizedStatement` at order two.

* `regular_alpha2`: for every physical pair whose comb operators satisfy `J₁ ≪ J₂`
  (in particular for positive definite `J₂`), the nested-amortized and the ordinary
  quantity are the same real number `y`, the ordinary supremum restricted to the single
  inserted reference dimension `r = c a b` has the same value, and `2^y` is the least
  upper bound of the full-transpose pairing `Re Tr(W Γᵀ)` over feasible testers.
* `alpha2_collapse`: the order-two instance of the locked statement for every physical
  pair (both sides are `⊤` when `J₁` is not supported in `J₂`).
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofPreparation
  (exists_spectral)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
  (one_le_geometricMoment)
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofRealize
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-! ### A trace bound: the objective is bounded on feasible testers -/

theorem trace_mul_le {n : Type} [Fintype n] [DecidableEq n] {B P : Matrix n n ℂ}
    (hB : B.PosSemidef) (hP : P.PosSemidef) :
    (Matrix.trace (B * P)).re ≤ (Matrix.trace B).re * (Matrix.trace P).re := by
  obtain ⟨U, d, hU1, hU2, hPeq, hd⟩ := exists_spectral hP.1
  have hd0 : ∀ i, 0 ≤ d i := fun i => psd_spectrum_nonneg hP _ (hd i)
  have hC := hB.conjTranspose_mul_mul_same U
  have htr : Matrix.trace (B * P) =
      Matrix.trace (Uᴴ * B * U * Matrix.diagonal (fun i => (d i : ℂ))) := by
    conv_lhs => rw [hPeq]
    rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc]
  have htrB : Matrix.trace (Uᴴ * B * U) = Matrix.trace B := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
  have htrP : Matrix.trace P = ∑ i, (d i : ℂ) := by
    conv_lhs => rw [hPeq]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.trace_diagonal]
  have hci : ∀ i, 0 ≤ ((Uᴴ * B * U) i i).re :=
    fun i => (Complex.nonneg_iff.1 (hC.diag_nonneg (i := i))).1
  have e : ∀ i, ((Uᴴ * B * U) i i * (d i : ℂ)).re = ((Uᴴ * B * U) i i).re * d i := by
    intro i
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [htr, ← htrB, htrP]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum,
    Complex.ofReal_re, e]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun j => ((Uᴴ * B * U) i i).re * d j)
      (fun j _ => mul_nonneg (hci i) (hd0 j)) (Finset.mem_univ i)

variable {a b c d : ℕ}

theorem feasible_trace {Γ : Matrix (X3 c a b) (X3 c a b) ℂ} (h : Feasible c a b Γ) :
    Matrix.trace Γ = (a : ℂ) := by
  obtain ⟨-, τ, -, hτ, hm⟩ := h
  rw [← trace_ptr, hm, Matrix.trace_kronecker, hτ, Matrix.trace_one, Fintype.card_fin, one_mul]

/-- The objective is at most `a · Tr W` on feasible testers. -/
theorem pairing_le_bound {W : Matrix (X3 c a b) (X3 c a b) ℂ} (hW : W.PosSemidef)
    {Γ : Matrix (X3 c a b) (X3 c a b) ℂ} (h : Feasible c a b Γ) :
    pairing W Γ ≤ (Matrix.trace W).re * a := by
  rw [pairing_eq_trace]
  refine (trace_mul_le hW h.1.transpose).trans ?_
  rw [Matrix.trace_transpose, feasible_trace h]
  simp

/-! ### Positive definite feasible testers -/

/-- Feasible testers that are positive definite with positive definite marginal. -/
def FeasiblePD (c a b : ℕ) (Γ : Matrix (X3 c a b) (X3 c a b) ℂ) : Prop :=
  Γ.PosDef ∧ ∃ τ : Matrix (Fin c) (Fin c) ℂ, τ.PosDef ∧ τ.trace = 1 ∧
    OpenQ.partialTraceRight Γ = τ ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)

theorem FeasiblePD.feasible {Γ : Matrix (X3 c a b) (X3 c a b) ℂ} (h : FeasiblePD c a b Γ) :
    Feasible c a b Γ := by
  obtain ⟨h1, τ, h2, h3, h4⟩ := h
  exact ⟨h1.posSemidef, τ, h2.posSemidef, h3, h4⟩

theorem ptr_add {m n : Type} [Fintype n] (M M' : Matrix (m × n) (m × n) ℂ) :
    OpenQ.partialTraceRight (M + M') = OpenQ.partialTraceRight M + OpenQ.partialTraceRight M' := by
  ext i j
  simp only [OpenQ.partialTraceRight, Matrix.add_apply, Finset.sum_add_distrib]

/-- The maximally mixed tester `Γ_* = (1_C / c) ⊗ 1_A ⊗ (1_B / b)`. -/
def gammaStar (c a b : ℕ) : Matrix (X3 c a b) (X3 c a b) ℂ :=
  ((((c : ℝ) * b)⁻¹ : ℝ) : ℂ) • (1 : Matrix (X3 c a b) (X3 c a b) ℂ)

theorem ptr_one {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    OpenQ.partialTraceRight (1 : Matrix (m × n) (m × n) ℂ) =
      (Fintype.card n : ℂ) • (1 : Matrix m m ℂ) := by
  rw [← Matrix.one_kronecker_one, OpenQ.partialTraceRight_kronecker, Matrix.trace_one]

theorem gammaStar_feasiblePD (hb : 0 < b) (hc : 0 < c) : FeasiblePD c a b (gammaStar c a b) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (inv_pos.2 (mul_pos hc' hb'))),
    (((c : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin c) (Fin c) ℂ),
    Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (inv_pos.2 hc')), ?_, ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    field_simp
  · rw [gammaStar, ptr_smul, ptr_one, Fintype.card_fin, smul_smul, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
    congr 1
    push_cast
    field_simp

/-- A positive definite matrix is `K Kᴴ` for an invertible `K`, any finite index type. -/
theorem exists_factor' {n : Type} [Fintype n] [DecidableEq n] {η : Matrix n n ℂ}
    (hη : η.PosDef) : ∃ K K' : Matrix n n ℂ, K' * K = 1 ∧ K * K' = 1 ∧ K * Kᴴ = η := by
  have hS : (supportInvSqrt η).IsHermitian := (supportInvSqrt_posSemidef η).1
  have hunit : IsUnit η.det := (Matrix.isUnit_iff_isUnit_det η).1 hη.isUnit
  have h1 : supportInvSqrt η * η * supportInvSqrt η = 1 := by
    rw [sandwich_eq_supp hη.posSemidef]
    have : pinv η = η⁻¹ := pinv_eq_inv hη
    rw [this, Matrix.mul_nonsing_inv η hunit]
  have h2 : supportInvSqrt η * (η * supportInvSqrt η) = 1 := by
    rw [← Matrix.mul_assoc]; exact h1
  refine ⟨η * supportInvSqrt η, supportInvSqrt η, h2, mul_eq_one_comm.1 h2, ?_⟩
  rw [Matrix.conjTranspose_mul, hS.eq, hη.1.eq]
  calc η * supportInvSqrt η * (supportInvSqrt η * η) = η * pinv η * η := by
        unfold pinv; simp only [Matrix.mul_assoc]
    _ = η := penrose1 hη.posSemidef

/-- Realization data from a positive definite feasible tester. -/
theorem exists_data (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {r : ℕ} (eR : Fin r ≃ X3 c a b)
    {Γ : Matrix (X3 c a b) (X3 c a b) ℂ} (h : FeasiblePD c a b Γ) :
    ∃ D : Data a b c r, D.T * D.Tᴴ = Γ := by
  obtain ⟨hΓ, τ, hτ, hτtr, hm⟩ := h
  obtain ⟨T, T', hT1, hT2, hT⟩ := exists_factor' hΓ
  obtain ⟨ψ, ψ', hψ1, hψ2, hψ⟩ := exists_factor' hτ
  exact ⟨{ a₀ := ⟨0, ha⟩
           b₀ := ⟨0, hb⟩
           k₀ := finProdFinEquiv (⟨0, hb⟩, eR.symm ((⟨0, hc⟩, ⟨0, ha⟩), ⟨0, hb⟩))
           eR := eR
           T := T
           T' := T'
           ψ := ψ
           ψ' := ψ'
           hT1 := hT1
           hT2 := hT2
           hψ := hψ2
           hψ' := hψ1
           htr := by rw [hψ]; exact hτtr
           hmarg := by rw [hT, hψ]; exact hm }, hT⟩

/-! ### Realized values -/

/-- The pure test of a positive definite feasible tester under the locked ordinary
quantity: its divergence is `log₂ Re Tr(W Γᵀ)` when `J₁ ≪ J₂`, and `⊤` otherwise. -/
theorem realized (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    {r : ℕ} (eR : Fin r ≃ X3 c a b) {Γ : Matrix (X3 c a b) (X3 c a b) ℂ}
    (h : FeasiblePD c a b Γ) :
    ∃ (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))), OpenQ.IsDensityMatrix ρ ∧
      (RangeIncluded (combJ Θ₁) (combJ Θ₂) →
        geometricStateDivergence 2 (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
            (Θ₂.referenceAct r N.val ρ) = ((log₂ (pairing (Wop Θ₁ Θ₂) Γ) : ℝ) : EReal) ∧
          1 ≤ pairing (Wop Θ₁ Θ₂) Γ) ∧
      (¬ RangeIncluded (combJ Θ₁) (combJ Θ₂) →
        geometricStateDivergence 2 (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
            (Θ₂.referenceAct r N.val ρ) = ⊤) := by
  obtain ⟨D, hD⟩ := exists_data ha hb hc eR h
  refine ⟨D.chan, D.rho, D.rho_density, ?_, ?_⟩
  · intro hsupp
    obtain ⟨hR, hm⟩ := moment_conj_eq (combJ_psd Θ₂) (combJ_psd Θ₁).1 hsupp (D.KT d) (D.KT' d)
      D.KT'_mul_KT D.KT_mul_KT'
    rw [← D.output Θ₁, ← D.output Θ₂] at hR hm
    have hval : geometricMoment 2 (Θ₁.referenceAct r D.chan.val D.rho)
        (Θ₂.referenceAct r D.chan.val D.rho) = pairing (Wop Θ₁ Θ₂) Γ := by
      rw [hm, D.trace_conj, hD]
      rfl
    have hd1 : OpenQ.IsDensityMatrix (Θ₁.referenceAct r D.chan.val D.rho) :=
      ⟨by rw [D.output]; exact (combJ_psd Θ₁).mul_mul_conjTranspose_same _,
        ((Θ₁.referenceAct_isCPTP r _ D.chan.property).2 D.rho).trans D.rho_density.2⟩
    have hd2 : OpenQ.IsDensityMatrix (Θ₂.referenceAct r D.chan.val D.rho) :=
      ⟨by rw [D.output]; exact (combJ_psd Θ₂).mul_mul_conjTranspose_same _,
        ((Θ₂.referenceAct_isCPTP r _ D.chan.property).2 D.rho).trans D.rho_density.2⟩
    refine ⟨?_, ?_⟩
    · rw [div_two_of_supported hR, hval]
    · rw [← hval]
      exact one_le_geometricMoment hd1 hd2 hR 2 (by norm_num)
  · intro hns
    apply geometricStateDivergence_unsupported
    rw [D.output Θ₁, D.output Θ₂]
    exact not_rangeIncluded_conj _ _ D.KT'_mul_KT D.KT_mul_KT' hns

/-- Feasible full-rank regularization: a bound on positive definite feasible testers
extends to all feasible testers (only a linear objective is involved). -/
theorem pairing_le_of_PD (hb : 0 < b) (hc : 0 < c) {W : Matrix (X3 c a b) (X3 c a b) ℂ}
    (hW : W.PosSemidef) {q : ℝ} (hq : 0 < q)
    (hPD : ∀ Γ, FeasiblePD c a b Γ → pairing W Γ ≤ q) :
    ∀ Γ, Feasible c a b Γ → pairing W Γ ≤ q := by
  intro Γ hΓ
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = pairing W Γ := ⟨_, rfl⟩
  rw [← hAdef] at hlt
  have hApos : 0 < A := lt_trans hq hlt
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (A - q) / (2 * A) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact div_pos (by linarith) (by linarith)
  have hδ1 : δ < 1 := by
    rw [hδdef, div_lt_one (by linarith)]
    linarith
  have hδA : δ * A = (A - q) / 2 := by
    rw [hδdef]
    field_simp
  obtain ⟨hΓpsd, τ, hτ, hτtr, hm⟩ := hΓ
  obtain ⟨hSpd, τs, hτs, hτstr, hms⟩ := gammaStar_feasiblePD (a := a) hb hc
  have h1δ : (0 : ℝ) ≤ 1 - δ := by linarith
  have hfe : FeasiblePD c a b (((1 - δ : ℝ) : ℂ) • Γ + ((δ : ℝ) : ℂ) • gammaStar c a b) := by
    refine ⟨Matrix.PosDef.posSemidef_add (hΓpsd.smul (Complex.zero_le_real.2 h1δ))
        (hSpd.smul (Complex.zero_lt_real.2 hδ0)),
      ((1 - δ : ℝ) : ℂ) • τ + ((δ : ℝ) : ℂ) • τs,
      Matrix.PosDef.posSemidef_add (hτ.smul (Complex.zero_le_real.2 h1δ))
        (hτs.smul (Complex.zero_lt_real.2 hδ0)), ?_, ?_⟩
    · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hτtr, hτstr, smul_eq_mul,
        smul_eq_mul]
      push_cast
      ring
    · rw [ptr_add, ptr_smul, ptr_smul, hm, hms, Matrix.add_kronecker, Matrix.smul_kronecker,
        Matrix.smul_kronecker]
  have h2 := hPD _ hfe
  rw [pairing_add, pairing_smul, pairing_smul, ← hAdef] at h2
  have h3 : 0 ≤ pairing W (gammaStar c a b) := pairing_nonneg hW hSpd.posSemidef
  have h4 : 0 ≤ δ * pairing W (gammaStar c a b) := mul_nonneg hδ0.le h3
  have h5 : (1 - δ) * A = A - δ * A := by ring
  rw [h5, hδA] at h2
  linarith

/-! ### The headline theorem on the locked definitions -/

/-- The locked ordinary quantity restricted to one inserted reference dimension. -/
def ordinaryAt (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (r : ℕ) : EReal :=
  sSup {v : EReal | ∃ (N : Channel (a * r) (b * r)) (ρ : Operator (Fin (c * r))),
    OpenQ.IsDensityMatrix ρ ∧
    v = geometricStateDivergence 2 (Fin (d * r)) (Θ₁.referenceAct r N.val ρ)
      (Θ₂.referenceAct r N.val ρ)}

theorem ordinaryAt_le (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) {r : ℕ} (hr : 0 < r) :
    ordinaryAt Θ₁ Θ₂ r ≤
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ := by
  unfold ordinaryAt referenceStabilizedOrdinaryDivergence
  apply sSup_le_sSup
  rintro v ⟨N, ρ, hρ, rfl⟩
  exact ⟨r, hr, N, ρ, hρ, rfl⟩

/-- Identification of the single common reference `ℂ^(c a b)` with `C ⊗ A ⊗ B`. -/
def eStar (c a b : ℕ) : Fin (c * a * b) ≃ X3 c a b :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Fin b)))

/-- **Regular order-two comb theorem** on the locked definitions, for supported comb
operators `J₁ ≪ J₂` (singular `J₂` allowed). Both locked quantities equal one real
number `y`; the ordinary supremum at the single inserted reference dimension `c a b`
has the same value; and `2^y` is the least upper bound of the full-transpose pairing of
`W = Tr_D(J₁ J₂⁺ J₁)` with feasible testers. -/
theorem regular_alpha2 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) :
    ∃ y : ℝ,
      referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = (y : EReal) ∧
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = (y : EReal) ∧
      ordinaryAt Θ₁ Θ₂ (c * a * b) = (y : EReal) ∧
      IsLUB {x : ℝ | ∃ Γ, Feasible c a b Γ ∧ x = pairing (Wop Θ₁ Θ₂) Γ} ((2 : ℝ) ^ y) := by
  have hW := Wop_psd Θ₁ Θ₂ hsupp
  have hr : 0 < c * a * b := Nat.mul_pos (Nat.mul_pos hc ha) hb
  have hreal : ∀ Γ, FeasiblePD c a b Γ →
      ((log₂ (pairing (Wop Θ₁ Θ₂) Γ) : ℝ) : EReal) ≤ ordinaryAt Θ₁ Θ₂ (c * a * b) ∧
        1 ≤ pairing (Wop Θ₁ Θ₂) Γ := by
    intro Γ hΓ
    obtain ⟨N, ρ, hρ, h1, -⟩ := realized ha hb hc Θ₁ Θ₂ (eStar c a b) hΓ
    obtain ⟨h2, h3⟩ := h1 hsupp
    refine ⟨?_, h3⟩
    rw [← h2]
    exact le_sSup ⟨N, ρ, hρ, rfl⟩
  have hU'U := ordinaryAt_le Θ₁ Θ₂ hr
  have hUA := ordinary_le_amortized ha Θ₁ Θ₂
  have hbound := amortized_le hb ha Θ₁ Θ₂ hsupp (fun Γ hΓ => pairing_le_bound hW hΓ)
  have hstar := hreal _ (gammaStar_feasiblePD hb hc)
  have hU'top : ordinaryAt Θ₁ Θ₂ (c * a * b) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hU'U.trans (hUA.trans hbound))
  have hU'bot : ordinaryAt Θ₁ Θ₂ (c * a * b) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hstar.1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, ordinaryAt Θ₁ Θ₂ (c * a * b) = (y : EReal) :=
    ⟨_, (EReal.coe_toReal hU'top hU'bot).symm⟩
  have hPD : ∀ Γ, FeasiblePD c a b Γ → pairing (Wop Θ₁ Θ₂) Γ ≤ (2 : ℝ) ^ y := by
    intro Γ hΓ
    obtain ⟨h1, h2⟩ := hreal Γ hΓ
    rw [hy, EReal.coe_le_coe_iff, log₂_eq_logb] at h1
    exact (Real.logb_le_iff_le_rpow (by norm_num) (by linarith)).1 h1
  have hq : (0 : ℝ) < (2 : ℝ) ^ y := Real.rpow_pos_of_pos (by norm_num) y
  have hall := pairing_le_of_PD hb hc hW hq hPD
  have hAy : referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ ≤
      (y : EReal) := by
    have h := amortized_le hb ha Θ₁ Θ₂ hsupp hall
    rwa [log₂_eq_logb, Real.logb_rpow (by norm_num) (by norm_num)] at h
  have hUy : referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ =
      (y : EReal) := le_antisymm (hUA.trans hAy) (hy ▸ hU'U)
  have hAeq : referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ =
      (y : EReal) := le_antisymm hAy (hUy ▸ hUA)
  refine ⟨y, hAeq, hUy, hy, ?_, ?_⟩
  · rintro x ⟨Γ, hΓ, rfl⟩
    exact hall Γ hΓ
  · intro Q' hQ'
    have h1 : 1 ≤ Q' :=
      le_trans hstar.2 (hQ' ⟨_, (gammaStar_feasiblePD hb hc).feasible, rfl⟩)
    have h2 := amortized_le hb ha Θ₁ Θ₂ hsupp (fun Γ hΓ => hQ' ⟨Γ, hΓ, rfl⟩)
    rw [hAeq, EReal.coe_le_coe_iff, log₂_eq_logb] at h2
    exact (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).1 h2

/-- The reviewed case: positive definite denominator comb operator, with
`W = Tr_D(J₁ J₂⁻¹ J₁)`. -/
theorem regular_alpha2_posDef (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (hPD : (combJ Θ₂).PosDef) :
    ∃ y : ℝ,
      referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = (y : EReal) ∧
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = (y : EReal) ∧
      ordinaryAt Θ₁ Θ₂ (c * a * b) = (y : EReal) ∧
      IsLUB {x : ℝ | ∃ Γ, Feasible c a b Γ ∧ x = pairing
        (OpenQ.partialTraceRight (combJ Θ₁ * (combJ Θ₂)⁻¹ * combJ Θ₁)) Γ} ((2 : ℝ) ^ y) := by
  have hunit : IsUnit (combJ Θ₂).det := (Matrix.isUnit_iff_isUnit_det _).1 hPD.isUnit
  have hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂) :=
    (rangeIncluded_iff_exists_mul _ _).2 ⟨(combJ Θ₂)⁻¹ * combJ Θ₁, by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]⟩
  have h := regular_alpha2 ha hb hc Θ₁ Θ₂ hsupp
  rwa [Wop_posDef Θ₁ Θ₂ hPD] at h

/-- **Order-two collapse for every physical pair**: the instance `α = 2` of the locked
`ReferenceStabilizedMainStatement`. If `J₁` is not supported in `J₂` both sides are `⊤`. -/
theorem alpha2_collapse (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) :
    referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ =
      referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ := by
  by_cases hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)
  · obtain ⟨y, h1, h2, -, -⟩ := regular_alpha2 ha hb hc Θ₁ Θ₂ hsupp
    rw [h1, h2]
  · have hr : 0 < c * a * b := Nat.mul_pos (Nat.mul_pos hc ha) hb
    obtain ⟨N, ρ, hρ, -, h1⟩ := realized ha hb hc Θ₁ Θ₂ (eStar c a b)
      (gammaStar_feasiblePD hb hc)
    have hU : referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ = ⊤ := by
      apply top_le_iff.1
      rw [← h1 hsupp]
      exact le_sSup ⟨c * a * b, hr, N, ρ, hρ, rfl⟩
    have hA := ordinary_le_amortized ha Θ₁ Θ₂
    rw [hU] at hA ⊢
    exact top_le_iff.1 hA

/-- The same statement in the shape of the locked target, with `α` fixed to `2`. -/
theorem main_at_two : ∀ (a b c d : ℕ), 0 < a → 0 < b → 0 < c → 0 < d →
    ∀ (Θ₁ Θ₂ : PhysicalSuperchannel a b c d),
      referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ =
        referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ :=
  fun _ _ _ _ ha hb hc _ Θ₁ Θ₂ => alpha2_collapse ha hb hc Θ₁ Θ₂

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofOrderTwo
