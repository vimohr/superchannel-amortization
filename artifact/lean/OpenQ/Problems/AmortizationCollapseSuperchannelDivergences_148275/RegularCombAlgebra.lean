import OpenQ.Foundations.Basic
import Mathlib.Analysis.Matrix.Order

/-!
Algebraic cores of the regular order-two comb proof. These declarations do not
formalize the spectral pseudoinverse, physical circuit, or final collapse.
The full argument, with those hypotheses, is in work/e002_i02/proof.md.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

open Matrix
open scoped ComplexOrder Kronecker

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- The residual in the order-two transformer argument is a positive
congruence whenever the complementary projector is positive. -/
theorem regularComb_transformer_residual (L : Matrix m n ℂ)
    (H P : Matrix n n ℂ) (hH : H.IsHermitian)
    (hP : (1 - P).PosSemidef) :
    (L * H * H * Lᴴ - L * H * P * H * Lᴴ).PosSemidef := by
  have heq : L * H * H * Lᴴ - L * H * P * H * Lᴴ =
      (L * H) * (1 - P) * (L * H)ᴴ := by
    simp only [conjTranspose_mul, hH.eq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  rw [heq]
  exact hP.mul_mul_conjTranspose_same (L * H)

/-- The full transpose, rather than a partial transpose, represents
the unconjugated entry pairing in the physical link contraction. -/
theorem regularComb_fullTranspose_pairing (W Γ : Matrix n n ℂ) :
    trace (W * Γᵀ) = ∑ i, ∑ j, W i j * Γ i j := by
  simp only [trace, diag_apply, mul_apply, transpose_apply]

/-- Adding a positive tensor filler preserves positivity and dominates
the original contracted tester. -/
theorem regularComb_completion_positive (Γ : Matrix (m × n) (m × n) ℂ)
    (Δ : Matrix m m ℂ) (β : Matrix n n ℂ)
    (hΓ : Γ.PosSemidef) (hΔ : Δ.PosSemidef) (hβ : β.PosSemidef) :
    (Γ + Δ ⊗ₖ β).PosSemidef ∧
      (Γ + Δ ⊗ₖ β - Γ).PosSemidef := by
  constructor
  · exact hΓ.add (hΔ.kronecker hβ)
  · simpa only [add_sub_cancel_left] using hΔ.kronecker hβ

/-- A tensor filler whose last factor has trace one completes the marginal
exactly. In the comb proof β is I_B/b. -/
theorem regularComb_completion_marginal
    (Γ : Matrix (m × n) (m × n) ℂ) (T : Matrix m m ℂ)
    (β : Matrix n n ℂ) (hβ : trace β = 1) :
    OpenQ.partialTraceRight
        (Γ + (T - OpenQ.partialTraceRight Γ) ⊗ₖ β) = T := by
  have hadd (X Y : Matrix (m × n) (m × n) ℂ) :
      OpenQ.partialTraceRight (X + Y) =
        OpenQ.partialTraceRight X + OpenQ.partialTraceRight Y := by
    ext i j
    simp only [OpenQ.partialTraceRight, Matrix.add_apply, Finset.sum_add_distrib]
  rw [hadd, OpenQ.partialTraceRight_kronecker, hβ, one_smul]
  exact add_sub_cancel _ _

end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
