import ShenWork.Defs

/-!
# The sharp constant for the linear quadratic form

This file minimizes the scalar symbol
`(s + α) * (s + 1) / s` over positive modes `s`.  The resulting constant
`(1 + √α)²` is sharp only for the linearized/quadratic statement; no nonlinear
stability threshold is claimed here.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Every positive mode lies above the sharp constant `(1 + √α)²`.

This is a scalar linear/quadratic-form inequality, not a nonlinear stability
statement. -/
theorem sharp_constant_le_mode_ratio
    (α : ℝ) (hα : 0 < α) {s : ℝ} (hs : 0 < s) :
    (1 + Real.sqrt α) ^ 2 ≤ (s + α) * (s + 1) / s := by
  have hsq : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα.le
  rw [le_div_iff₀ hs]
  nlinarith [sq_nonneg (s - Real.sqrt α)]

/-- The positive mode `s = √α` attains the sharp linear/quadratic constant.

This equality concerns only the linearized quadratic form and makes no claim
about a nonlinear stability threshold. -/
theorem sharp_constant_eq_mode_ratio_at_sqrt
    (α : ℝ) (hα : 0 < α) :
    (1 + Real.sqrt α) ^ 2 =
      (Real.sqrt α + α) * (Real.sqrt α + 1) / Real.sqrt α := by
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hsq : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα.le
  rw [eq_div_iff (ne_of_gt hsqrt)]
  nlinarith

section AxiomAudit

#print axioms sharp_constant_le_mode_ratio
#print axioms sharp_constant_eq_mode_ratio_at_sqrt

end AxiomAudit

end ShenWork.Paper1
