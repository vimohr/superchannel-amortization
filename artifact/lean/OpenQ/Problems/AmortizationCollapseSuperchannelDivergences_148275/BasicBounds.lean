import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.Statement

/-!
# A conditional diagonal lower bound

Channel self-normalization and channel collapse are explicit hypotheses, not
axioms or verified geometric Rényi results. The complete-lattice argument
includes an infinite ordinary supremum and requires no maximizing channel.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

noncomputable section

/-- Structural lower bound from the diagonal inserted pair `N = M`.
No upper bound or superchannel collapse assumption occurs among the premises. -/
theorem ordinary_sc_le_amortized_sc {a b c d : ℕ} (D : StateDivergence)
    (Θ₁ Θ₂ : PhysicalSuperchannel a b c d)
    (self_normalization : ∀ N : Channel a b, ordinaryChannelDivergence D N N = 0)
    (input_channel_collapse : ∀ N M : Channel a b,
      amortizedChannelDivergence D N M = ordinaryChannelDivergence D N M)
    (output_channel_collapse : ∀ P Q : Channel c d,
      amortizedChannelDivergence D P Q = ordinaryChannelDivergence D P Q) :
    ordinarySuperchannelDivergence D Θ₁ Θ₂ ≤ amortizedSuperchannelDivergence D Θ₁ Θ₂ := by
  apply sSup_le
  rintro v ⟨N, rfl⟩
  apply le_sSup
  refine ⟨N, N, 0, ?_, ?_⟩
  · rw [input_channel_collapse, self_normalization, EReal.coe_zero]
  · rw [output_channel_collapse, EReal.coe_zero, sub_zero]

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
