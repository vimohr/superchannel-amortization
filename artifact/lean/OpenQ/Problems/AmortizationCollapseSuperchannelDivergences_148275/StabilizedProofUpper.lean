/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticUpperE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Upper bounds at order two on the locked quantities of `StabilizedStatement`:

* `amortized_le`: if the comb operators are supported (`J₁ ≪ J₂`) and every feasible
  tester has full-transpose pairing at most `Q` with `W = Tr_D(J₁ J₂⁺ J₁)`, then the
  nested-amortized quantity is at most `log₂ Q`. All inserted and external references,
  singular insertions and singular states are covered; only the finite entire input
  cost is used.
* `ordinary_le_amortized`: the ordinary quantity is at most the nested-amortized one
  (equal insertions have entire cost zero by data processing).
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofNonnegative
  (one_le_geometricMoment)
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel
open scoped ComplexOrder Kronecker Matrix

noncomputable section

variable {a b c d : ℕ}

/-- `W = Tr_D (J₁ J₂⁺ J₁)` on `C ⊗ A ⊗ B`, with the support inverse of the denominator
comb operator. For positive definite `J₂` it is `Tr_D (J₁ J₂⁻¹ J₁)`. -/
def Wop (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) : Matrix (X3 c a b) (X3 c a b) ℂ :=
  OpenQ.partialTraceRight (combJ Θ₁ * pinv (combJ Θ₂) * combJ Θ₁)

theorem Wop_posDef (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) (h : (combJ Θ₂).PosDef) :
    Wop Θ₁ Θ₂ = OpenQ.partialTraceRight (combJ Θ₁ * (combJ Θ₂)⁻¹ * combJ Θ₁) := by
  have : pinv (combJ Θ₂) = (combJ Θ₂)⁻¹ := pinv_eq_inv h
  rw [Wop, this]

theorem Wop_psd (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) : (Wop Θ₁ Θ₂).PosSemidef :=
  ptr_psd (dom_base (combJ_psd Θ₂) (combJ_psd Θ₁).1 hsupp).right

/-- **Global moment inequality** (18) of the reviewed note, on the locked definitions,
with the channel factor in the form of the note: any `q > 0` with
`Tr_{B R}(J_N J_M⁺ J_N) ≤ q · 1` (for instance its largest eigenvalue) and a supported
pair of joint Choi matrices. Every inserted reference `r`, every external reference `s`,
singular insertions and singular states are covered. -/
theorem moment_chain_q (hb : 0 < b) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) {Q : ℝ}
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (Wop Θ₁ Θ₂) Γ ≤ Q)
    {r : ℕ} (N M : Channel (a * r) (b * r))
    (hRNM : RangeIncluded (choi N.val) (choi M.val)) {q : ℝ} (hq : 0 < q)
    (hE : ((q : ℂ) • (1 : Matrix (Fin (a * r)) (Fin (a * r)) ℂ) -
      OpenQ.partialTraceRight (choi N.val * pinv (choi M.val) * choi N.val)).PosSemidef)
    {s : ℕ} {ρ σ : Operator (Fin s × Fin (c * r))}
    (hρ : OpenQ.IsDensityMatrix ρ) (hσ : OpenQ.IsDensityMatrix σ) (hR : RangeIncluded ρ σ) :
    RangeIncluded (amplification s (Θ₁.referenceAct r N.val) ρ)
        (amplification s (Θ₂.referenceAct r M.val) σ) ∧
      geometricMoment 2 (amplification s (Θ₁.referenceAct r N.val) ρ)
          (amplification s (Θ₂.referenceAct r M.val) σ) ≤
        q * geometricMoment 2 ρ σ * Q := by
  have d1 := dom_base (combJ_psd Θ₂) (combJ_psd Θ₁).1 hsupp
  have d2 := dom_base (choi_psd M.property) (choi_psd N.property).1 hRNM
  have d3 := dom_base hσ.1 hρ.1.1 hR
  have dd := contrS_dom d1 d2 d3
  rw [amp_refAct, amp_refAct]
  obtain ⟨hRout, hle⟩ := moment_le_of_dom dd dd.left
  refine ⟨hRout, hle.trans ?_⟩
  have hm1 : 1 ≤ geometricMoment 2 ρ σ := one_le_geometricMoment hρ hσ hR 2 (by norm_num)
  have hmH : Matrix.trace (ρ * pinv σ * ρ) = ((geometricMoment 2 ρ σ : ℝ) : ℂ) := by
    rw [geometricMoment_two hρ.1.1 hσ.1 hR]
    exact (nonneg_eq_ofReal d3.right.trace_nonneg).1
  exact chain_trace_bound hb d1.right d2.right d3.right hq (by linarith) hE hmH hQ

/-- The same inequality with the finite entire input cost `t` of the locked
channel-amortized divergence in place of `q`: `2^t` dominates `Tr_{B R}(J_N J_M⁺ J_N)`. -/
theorem moment_chain (hb : 0 < b) (ha : 0 < a) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) {Q : ℝ}
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (Wop Θ₁ Θ₂) Γ ≤ Q)
    {r : ℕ} (hr : 0 < r) (N M : Channel (a * r) (b * r)) {t : ℝ}
    (ht : amortizedChannelDivergence (geometricStateDivergence 2) N M = (t : EReal))
    {s : ℕ} {ρ σ : Operator (Fin s × Fin (c * r))}
    (hρ : OpenQ.IsDensityMatrix ρ) (hσ : OpenQ.IsDensityMatrix σ) (hR : RangeIncluded ρ σ) :
    RangeIncluded (amplification s (Θ₁.referenceAct r N.val) ρ)
        (amplification s (Θ₂.referenceAct r M.val) σ) ∧
      geometricMoment 2 (amplification s (Θ₁.referenceAct r N.val) ρ)
          (amplification s (Θ₂.referenceAct r M.val) σ) ≤
        (2 : ℝ) ^ t * geometricMoment 2 ρ σ * Q := by
  obtain ⟨hRNM, hE⟩ := cost_bound (Nat.mul_pos ha hr) N M ht
  exact moment_chain_q hb Θ₁ Θ₂ hsupp hQ N M hRNM (Real.rpow_pos_of_pos (by norm_num) t) hE
    hρ hσ hR

/-- **Upper bound for the nested-amortized quantity** at order two. -/
theorem amortized_le (hb : 0 < b) (ha : 0 < a) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (hsupp : RangeIncluded (combJ Θ₁) (combJ Θ₂)) {Q : ℝ}
    (hQ : ∀ Γ, Feasible c a b Γ → pairing (Wop Θ₁ Θ₂) Γ ≤ Q) :
    referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ ≤
      ((log₂ Q : ℝ) : EReal) := by
  unfold referenceStabilizedAmortizedDivergence
  apply sSup_le
  rintro v ⟨r, hr, N, M, t, ht, rfl⟩
  have key : amortizedChannelDivergence (geometricStateDivergence 2)
      (Θ₁.referenceOnChannel r N) (Θ₂.referenceOnChannel r M) ≤ ((log₂ Q + t : ℝ) : EReal) := by
    unfold amortizedChannelDivergence
    apply sSup_le
    rintro w ⟨s, hs, ρ, σ, hρ, hσ, u, hu, rfl⟩
    obtain ⟨hR, rfl⟩ := div_two_real hu
    obtain ⟨hRout, hle⟩ := moment_chain hb ha Θ₁ Θ₂ hsupp hQ hr N M ht hρ hσ hR
    have hd1 := amplification_isDensityMatrix (Θ₁.referenceOnChannel r N) hs ρ hρ
    have hd2 := amplification_isDensityMatrix (Θ₂.referenceOnChannel r M) hs σ hσ
    have hRout' : RangeIncluded (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ) := hRout
    have hout1 := one_le_geometricMoment hd1 hd2 hRout' 2 (by norm_num)
    have hm1 : 1 ≤ geometricMoment 2 ρ σ := one_le_geometricMoment hρ hσ hR 2 (by norm_num)
    have hq : (0 : ℝ) < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
    have hle' : geometricMoment 2 (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ) ≤
        (2 : ℝ) ^ t * geometricMoment 2 ρ σ * Q := hle
    have hQpos : 0 < Q := by
      by_contra hneg
      rw [not_lt] at hneg
      have : (2 : ℝ) ^ t * geometricMoment 2 ρ σ * Q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hq.le (by linarith)) hneg
      linarith
    rw [div_two_of_supported hRout', ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h1 : log₂ (geometricMoment 2 (amplification s (Θ₁.referenceOnChannel r N).val ρ)
        (amplification s (Θ₂.referenceOnChannel r M).val σ)) ≤
        log₂ ((2 : ℝ) ^ t * geometricMoment 2 ρ σ * Q) := by
      rw [log₂_eq_logb, log₂_eq_logb]
      exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hle'
    have h2 : log₂ ((2 : ℝ) ^ t * geometricMoment 2 ρ σ * Q) =
        t + log₂ (geometricMoment 2 ρ σ) + log₂ Q := by
      rw [log₂_eq_logb, log₂_eq_logb, log₂_eq_logb,
        Real.logb_mul (mul_pos hq (by linarith)).ne' hQpos.ne',
        Real.logb_mul hq.ne' (by linarith : geometricMoment 2 ρ σ ≠ 0),
        Real.logb_rpow (by norm_num) (by norm_num)]
    linarith
  calc amortizedChannelDivergence (geometricStateDivergence 2)
        (Θ₁.referenceOnChannel r N) (Θ₂.referenceOnChannel r M) - (t : EReal)
      ≤ ((log₂ Q + t : ℝ) : EReal) - (t : EReal) := EReal.sub_le_sub key le_rfl
    _ = ((log₂ Q : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        congr 1
        ring

/-- The ordinary quantity is at most the nested-amortized one at order two, for every
physical pair (no support assumption). -/
theorem ordinary_le_amortized (ha : 0 < a) (Θ₁ Θ₂ : PhysicalSuperchannel a b c d) :
    referenceStabilizedOrdinaryDivergence (geometricStateDivergence 2) Θ₁ Θ₂ ≤
      referenceStabilizedAmortizedDivergence (geometricStateDivergence 2) Θ₁ Θ₂ := by
  unfold referenceStabilizedOrdinaryDivergence
  apply sSup_le
  rintro v ⟨r, hr, N, ρ, hρ, rfl⟩
  have hin := amortized_self (Nat.mul_pos ha hr) N
  refine le_trans ?_ (le_sSup ⟨r, hr, N, N, 0, by rw [hin, EReal.coe_zero], rfl⟩)
  rw [EReal.coe_zero, sub_zero]
  -- the test with a one-dimensional external reference and equal states
  let e : Fin 1 × Fin (c * r) ≃ Fin (c * r) := Equiv.uniqueProd (Fin (c * r)) (Fin 1)
  let e' : Fin 1 × Fin (d * r) ≃ Fin (d * r) := Equiv.uniqueProd (Fin (d * r)) (Fin 1)
  have hρ' : OpenQ.IsDensityMatrix (ρ.submatrix e e) :=
    ⟨hρ.1.submatrix e, (OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex.trace_submatrix e ρ).trans hρ.2⟩
  have hamp : ∀ Ψ : ChannelMap (c * r) (d * r),
      amplification 1 Ψ (ρ.submatrix e e) = (Ψ ρ).submatrix e' e' := by
    intro Ψ
    ext ⟨s₀, β⟩ ⟨s₁, γ⟩
    rfl
  have h1 := amplification_isDensityMatrix (Θ₁.referenceOnChannel r N) Nat.one_pos _ hρ'
  have h2 := amplification_isDensityMatrix (Θ₂.referenceOnChannel r N) Nat.one_pos _ hρ'
  have hP1 : (Θ₁.referenceAct r N.val ρ).PosSemidef := by
    have := h1.1
    rw [show (Θ₁.referenceOnChannel r N).val = Θ₁.referenceAct r N.val from rfl, hamp] at this
    exact (Matrix.posSemidef_submatrix_equiv e').1 this
  have hP2 : (Θ₂.referenceAct r N.val ρ).PosSemidef := by
    have := h2.1
    rw [show (Θ₂.referenceOnChannel r N).val = Θ₂.referenceAct r N.val from rfl, hamp] at this
    exact (Matrix.posSemidef_submatrix_equiv e').1 this
  unfold amortizedChannelDivergence
  apply le_sSup
  refine ⟨1, Nat.one_pos, ρ.submatrix e e, ρ.submatrix e e, hρ', hρ', 0, ?_, ?_⟩
  · rw [geometricStateDivergence_self hρ' 2 (by norm_num), EReal.coe_zero]
  · rw [EReal.coe_zero, sub_zero]
    rw [show (Θ₁.referenceOnChannel r N).val = Θ₁.referenceAct r N.val from rfl,
      show (Θ₂.referenceOnChannel r N).val = Θ₂.referenceAct r N.val from rfl, hamp, hamp]
    exact (OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofReindex.divergence_submatrix 2 e' hP1.1 hP2.1).symm

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
