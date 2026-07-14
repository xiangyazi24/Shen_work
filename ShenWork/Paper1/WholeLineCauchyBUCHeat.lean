import ShenWork.Paper1.WholeLineCauchyBUCConvolution

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time Gaussian operators on `BUC(ℝ)`
-/

def wholeLineModifiedHeatKernel (t z : ℝ) : ℝ :=
  Real.exp (-t) * heatKernel t z

def wholeLineModifiedHeatGradientKernel (t z : ℝ) : ℝ :=
  Real.exp (-t) * deriv (fun w : ℝ => heatKernel t w) z

theorem wholeLineModifiedHeatKernel_continuous
    {t : ℝ} (ht : 0 < t) :
    Continuous (wholeLineModifiedHeatKernel t) := by
  unfold wholeLineModifiedHeatKernel heatKernel
  fun_prop

theorem wholeLineModifiedHeatGradientKernel_continuous
    {t : ℝ} (ht : 0 < t) :
    Continuous (wholeLineModifiedHeatGradientKernel t) := by
  have heq : wholeLineModifiedHeatGradientKernel t = fun z : ℝ =>
      Real.exp (-t) * (-(z / (2 * t)) * heatKernel t z) := by
    funext z
    rw [wholeLineModifiedHeatGradientKernel, deriv_heatKernel ht z]
  rw [heq]
  unfold heatKernel
  fun_prop

theorem wholeLineModifiedHeatKernel_integrable
    {t : ℝ} (ht : 0 < t) :
    Integrable (wholeLineModifiedHeatKernel t) := by
  exact (heatKernel_integrable ht).const_mul (Real.exp (-t))

theorem wholeLineModifiedHeatGradientKernel_integrable
    {t : ℝ} (ht : 0 < t) :
    Integrable (wholeLineModifiedHeatGradientKernel t) := by
  exact (heatKernel_deriv_integrable ht).const_mul (Real.exp (-t))

theorem wholeLineModifiedHeatKernel_integral_abs
    {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ, |wholeLineModifiedHeatKernel t z|) = Real.exp (-t) := by
  simp only [wholeLineModifiedHeatKernel, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  rw [integral_const_mul, heatKernel_integral_abs_eq_one ht, mul_one]

theorem wholeLineModifiedHeatGradientKernel_integral_abs
    {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ, |wholeLineModifiedHeatGradientKernel t z|) =
      Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t)) := by
  exact modifiedHeatKernel_deriv_abs_integral ht

theorem kernelConvVal_wholeLineModifiedHeatKernel_eq
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) (x : ℝ) :
    kernelConvVal (wholeLineModifiedHeatKernel t) u.1 x =
      wholeLineCauchyHeatOp t (u.1 : ℝ → ℝ) x := by
  unfold kernelConvVal wholeLineModifiedHeatKernel wholeLineCauchyHeatOp
    modifiedSemigroup
  rw [show (fun y : ℝ =>
      Real.exp (-t) * heatKernel t (x - y) * u.1 y) =
      fun y : ℝ => Real.exp (-t) *
        (heatKernel t (x - y) * u.1 y) by
    funext y
    ring]
  rw [integral_const_mul]
  rfl

theorem kernelConvVal_wholeLineModifiedHeatGradientKernel_eq
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) (x : ℝ) :
    kernelConvVal (wholeLineModifiedHeatGradientKernel t) u.1 x =
      wholeLineCauchyHeatGradOp t (u.1 : ℝ → ℝ) x := by
  unfold kernelConvVal wholeLineModifiedHeatGradientKernel
    wholeLineCauchyHeatGradOp
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change Real.exp (-t) * deriv (fun w : ℝ => heatKernel t w) (x - y) * u.1 y =
      Real.exp (-t) * (deriv (fun z : ℝ => heatKernel t (z - y)) x * u.1 y)
    rw [deriv_heatKernel_translated_left_global]
    ring

/-- Positive-time modified heat flow as a BUC element. -/
def wholeLineCauchyHeatBUC
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) : WholeLineBUC :=
  kernelConvBUC (wholeLineModifiedHeatKernel_continuous ht)
    (wholeLineModifiedHeatKernel_integrable ht) u

/-- Positive-time Gaussian gradient operator as a BUC element. -/
def wholeLineCauchyHeatGradientBUC
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) : WholeLineBUC :=
  kernelConvBUC (wholeLineModifiedHeatGradientKernel_continuous ht)
    (wholeLineModifiedHeatGradientKernel_integrable ht) u

@[simp] theorem wholeLineCauchyHeatBUC_apply
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineCauchyHeatBUC t ht u).1 x =
      wholeLineCauchyHeatOp t (u.1 : ℝ → ℝ) x := by
  exact kernelConvVal_wholeLineModifiedHeatKernel_eq ht u x

@[simp] theorem wholeLineCauchyHeatGradientBUC_apply
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineCauchyHeatGradientBUC t ht u).1 x =
      wholeLineCauchyHeatGradOp t (u.1 : ℝ → ℝ) x := by
  exact kernelConvVal_wholeLineModifiedHeatGradientKernel_eq ht u x

theorem wholeLineCauchyHeatBUC_dist_le
    {t : ℝ} (ht : 0 < t) (u w : WholeLineBUC) :
    dist (wholeLineCauchyHeatBUC t ht u)
        (wholeLineCauchyHeatBUC t ht w) ≤
      Real.exp (-t) * dist u w := by
  simpa [wholeLineCauchyHeatBUC,
    wholeLineModifiedHeatKernel_integral_abs ht] using
    kernelConvBUC_dist_le (wholeLineModifiedHeatKernel_continuous ht)
      (wholeLineModifiedHeatKernel_integrable ht) u w

theorem wholeLineCauchyHeatGradientBUC_dist_le
    {t : ℝ} (ht : 0 < t) (u w : WholeLineBUC) :
    dist (wholeLineCauchyHeatGradientBUC t ht u)
        (wholeLineCauchyHeatGradientBUC t ht w) ≤
      (Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t))) * dist u w := by
  simpa [wholeLineCauchyHeatGradientBUC,
    wholeLineModifiedHeatGradientKernel_integral_abs ht] using
    kernelConvBUC_dist_le (wholeLineModifiedHeatGradientKernel_continuous ht)
      (wholeLineModifiedHeatGradientKernel_integrable ht) u w

section WholeLineCauchyBUCHeatAxiomAudit

#print axioms wholeLineCauchyHeatBUC_apply
#print axioms wholeLineCauchyHeatGradientBUC_apply
#print axioms wholeLineCauchyHeatBUC_dist_le
#print axioms wholeLineCauchyHeatGradientBUC_dist_le

end WholeLineCauchyBUCHeatAxiomAudit

end ShenWork.Paper1
