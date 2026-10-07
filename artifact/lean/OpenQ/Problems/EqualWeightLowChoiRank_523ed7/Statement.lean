import OpenQ.Foundations.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Equal-weight low-Choi-rank decompositions

The Choi convention is unnormalized and input-first: the first index is in
`Fin a` and the second in `Fin b`. The marginal over the output is `I_a`.
All ranks are matrix ranks over `ℂ`.

These are independent matrix formulations of the strong Ruskai-Audenaert
conjecture. See Kumar and Wolf, arXiv:2607.23066v1, Section 2, Conjecture 1.
`MainStatement` is an unproved proposition, not an existence theorem.
-/

namespace OpenQ.Problems.EqualWeightLowChoiRank_523ed7

open scoped BigOperators ComplexOrder

/-- Complex matrices on the input-output tensor product, in input-first order. -/
abbrev ChoiMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

/-- Positivity and the output partial trace of an unnormalized channel Choi matrix. -/
def IsChannelChoi {a b : ℕ} (J : ChoiMatrix a b) : Prop :=
  J.PosSemidef ∧ OpenQ.partialTraceRight J = (1 : Matrix (Fin a) (Fin a) ℂ)

/-- Exactly `b` channel Choi matrices, each of complex rank at most `a`,
with equal weights. Repeated matrices are permitted. -/
def HasUniformDecomposition {a b : ℕ} (J : ChoiMatrix a b) : Prop :=
  ∃ K : Fin b → ChoiMatrix a b,
    (∀ r, (K r).PosSemidef ∧
      OpenQ.partialTraceRight (K r) = (1 : Matrix (Fin a) (Fin a) ℂ) ∧
      (K r).rank ≤ a) ∧
    J = (b : ℂ)⁻¹ • ∑ r, K r

/-- Exactly `b` positive parts, each with marginal `I_a / b` and complex rank
at most `a`. This predicate is defined independently of uniform decomposition. -/
def HasEquipartition {a b : ℕ} (J : ChoiMatrix a b) : Prop :=
  ∃ P : Fin b → ChoiMatrix a b,
    (∀ r, (P r).PosSemidef ∧
      OpenQ.partialTraceRight (P r) = (b : ℂ)⁻¹ • (1 : Matrix (Fin a) (Fin a) ℂ) ∧
      (P r).rank ≤ a) ∧
    J = ∑ r, P r

/-- The universal matrix conjecture, including singular Choi matrices.
Both dimensions are positive natural numbers; there are exactly `b` terms. -/
def MainStatement : Prop :=
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ J : ChoiMatrix a b, IsChannelChoi J → HasUniformDecomposition J

end OpenQ.Problems.EqualWeightLowChoiRank_523ed7
