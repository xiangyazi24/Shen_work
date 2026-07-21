import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The Green kernel has unit mass

The resolver oscillation bound (`resolver_oscillation_bound`) carries the kernel
unit-mass `∫ K = 1` as a hypothesis.  For the Green kernel of `-v_zz + v = u`,
`K(s) = ½ e^{-|s|}`, this file discharges it:

`∫_ℝ ½ e^{-|s|} ds = ½ (∫_{Iic 0} e^{s} + ∫_{Ioi 0} e^{-s}) = ½ (1 + 1) = 1`,

using `integral_exp_Iic_zero` and `integral_exp_neg_Ioi_zero`.  (The shifted mass
`∫_y ½ e^{-|z-y|} dy = 1` follows by translation/reflection invariance of Lebesgue
measure — the remaining glue for the general `hmass`.)
-/

open MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- `exp (-|·|)` is integrable on `ℝ` (each half is a standard exponential tail). -/
theorem integrable_exp_neg_abs : Integrable (fun s : ℝ => Real.exp (-|s|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
  constructor
  · -- on `Iic 0`, `exp (-|s|) = exp s`
    apply (integrableOn_exp_Iic 0).congr_fun (fun s hs => ?_) measurableSet_Iic
    rw [abs_of_nonpos hs, neg_neg]
  · -- on `Ioi 0`, `exp (-|s|) = exp (-s)`
    apply (integrableOn_exp_neg_Ioi 0).congr_fun (fun s hs => ?_) measurableSet_Ioi
    rw [abs_of_pos hs]

/-- **Unit mass of the Green kernel.**  `∫_ℝ ½ e^{-|s|} ds = 1`. -/
theorem greenKernel_integral_eq_one :
    ∫ s : ℝ, (1 / 2 : ℝ) * Real.exp (-|s|) = 1 := by
  have hInt : Integrable (fun s : ℝ => Real.exp (-|s|)) := integrable_exp_neg_abs
  -- split at 0
  have hsplit : (∫ s : ℝ, Real.exp (-|s|))
      = (∫ s in Iic (0:ℝ), Real.exp (-|s|)) + ∫ s in Ioi (0:ℝ), Real.exp (-|s|) := by
    rw [← integral_add_compl measurableSet_Iic hInt, compl_Iic]
  have hIic : (∫ s in Iic (0:ℝ), Real.exp (-|s|)) = 1 := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := Real.exp)
      (fun s hs => by rw [abs_of_nonpos hs, neg_neg])]
    exact integral_exp_Iic_zero
  have hIoi : (∫ s in Ioi (0:ℝ), Real.exp (-|s|)) = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => Real.exp (-s))
      (fun s hs => by rw [abs_of_pos hs])]
    exact integral_exp_neg_Ioi_zero
  rw [integral_const_mul, hsplit, hIic, hIoi]
  norm_num

section AxiomAudit

#print axioms greenKernel_integral_eq_one

end AxiomAudit

end ShenWork.Paper1
