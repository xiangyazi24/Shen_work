/-
  ShenWork/PDE/IntervalFullKernelGradientTiling.lean

  **Toward the full-kernel gradient L∞→L∞ estimate (ROUND-17 route).**

  The full Neumann semigroup gradient bound
  `|deriv (intervalFullSemigroupOperator t f) x| ≤ (1/√π) t^(−1/2) ‖f‖∞`
  requires the real-space method-of-images tiling — there is no spectral
  shortcut (spectral gives non-integrable `1/t`).  This file builds the tiling
  in small, independently-verified steps.

  Step 1 (this commit): the heat-gradient L¹ norm in `t^(−1/2)` form (the power
  the Duhamel envelope needs), restating the existing closed form
  `∫_ℝ |∂ₓ heat(t,·)| = 2/√(4πt)`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.HeatKernelGradientEstimates

open MeasureTheory
open scoped Topology

namespace ShenWork

open ShenWork.IntervalDomain

/-- **Heat-gradient `L¹` norm in `t^(−1/2)` form.**  `∫_ℝ |∂ₓ heat(t,·)|` equals
`heatGradientLinftyLinftyConstant · t^(−1/2)` (`= (1/√π) t^(−1/2)`), the
envelope-integrable power.  Restates `heatKernel_deriv_abs_integral` (`= 2/√(4πt)`). -/
theorem heatKernel_deriv_abs_integral_sqrt_form {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, |deriv (fun z : ℝ => heatKernel t z) x|
      = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * t ^ (-(1 / 2) : ℝ) := by
  rw [heatKernel_deriv_abs_integral ht]
  unfold ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  -- `√(4πt) = 2 · √π · √t`.
  have hsqrt : Real.sqrt (4 * Real.pi * t) = 2 * (Real.sqrt Real.pi * Real.sqrt t) := by
    rw [show (4 * Real.pi * t : ℝ) = (2 : ℝ) ^ 2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul hpi]
  -- `t^(−1/2) = (√t)⁻¹`.
  have hrpow : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  rw [hsqrt, hrpow]
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hst : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  field_simp

end ShenWork
