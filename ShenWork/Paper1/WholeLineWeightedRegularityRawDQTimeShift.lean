import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Restart-time changes of variables for raw-DQ Volterra estimates

These identities translate an interval beginning at an absolute restart time
to an interval beginning at zero.  They require no integrability hypotheses:
`intervalIntegral.integral_comp_add_right` is an identity for the interval
integral itself.
-/

/-- Translate an interval integral on `[a, a + q]` to restart-time
coordinates on `[0, q]`. -/
theorem intervalIntegral_restart_eq
    (a q : ℝ) (f : ℝ → ℝ) :
    (∫ s in a..a + q, f s) = ∫ τ in (0 : ℝ)..q, f (a + τ) := by
  have h := intervalIntegral.integral_comp_add_right
    (f := f) (a := (0 : ℝ)) (b := q) a
  simpa [add_comm] using h.symm

/-- Restart-time change of variables for the constant-plus-inverse-square-root
Volterra kernel. -/
theorem intervalIntegral_restart_invSqrtKernel_eq
    (a q C0 C1 : ℝ) (x : ℝ → ℝ) :
    (∫ s in a..a + q,
        (C0 + C1 * (a + q - s) ^ (-1 / 2 : ℝ)) * x s) =
      ∫ τ in (0 : ℝ)..q,
        (C0 + C1 * (q - τ) ^ (-1 / 2 : ℝ)) * x (a + τ) := by
  rw [intervalIntegral_restart_eq]
  refine intervalIntegral.integral_congr (fun τ _ ↦ ?_)
  congr 3
  ring

/-- Restart-time change of variables for a nonsingular affine reaction
majorant. -/
theorem intervalIntegral_restart_affineKernel_eq
    (a q C D : ℝ) (x : ℝ → ℝ) :
    (∫ s in a..a + q, C * x s + D) =
      ∫ τ in (0 : ℝ)..q, C * x (a + τ) + D := by
  exact intervalIntegral_restart_eq a q (fun s ↦ C * x s + D)

end ShenWork.Paper1

#print axioms ShenWork.Paper1.intervalIntegral_restart_eq
#print axioms ShenWork.Paper1.intervalIntegral_restart_invSqrtKernel_eq
#print axioms ShenWork.Paper1.intervalIntegral_restart_affineKernel_eq
