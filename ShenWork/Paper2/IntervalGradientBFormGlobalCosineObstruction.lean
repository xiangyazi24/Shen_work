/-
  Obstruction for the current gradient-to-B-form bridge.

  `IntervalGradientBFormGlobalCosine` exposes a hypothesis `hgradB` equating the
  gradient Neumann Duhamel leg with the B-kernel Duhamel leg.  At the Neumann
  endpoints the gradient side is forced to vanish.  This file records the
  resulting endpoint-vanishing consequence for the B-kernel side, making the
  obstruction explicit instead of spending more work on the false bridge.
-/
import ShenWork.Paper2.IntervalGradientBFormGlobalCosine
import ShenWork.PDE.IntervalFullSemigroupNeumann

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalGradientBFormGlobalCosine

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

/-- The current `hgradB` target forces the B-kernel Duhamel leg to vanish at both
Neumann endpoints.  This is an obstruction diagnostic: the gradient semigroup
leg has zero spatial derivative at `x = 0, 1`, while the B-kernel leg is not
expected to vanish there for a general source. -/
theorem hgradB_forces_B_kernel_endpoint_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hgradB : ∀ t, 0 < t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x)
        =
      ∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (D.u s)) x)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (D.u s)) 0) = 0 ∧
    (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (D.u s)) 1) = 0 := by
  constructor
  · rw [← hgradB t ht htT 0 (by constructor <;> norm_num)]
    calc
      (∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) 0)
          = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro s _hs
            exact ShenWork.intervalFullSemigroupOperator_deriv_at_zero_eq_zero
              (t - s) (chemFluxLifted p (D.u s))
      _ = 0 := by simp
  · rw [← hgradB t ht htT 1 (by constructor <;> norm_num)]
    calc
      (∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) 1)
          = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro s _hs
            exact ShenWork.intervalFullSemigroupOperator_deriv_at_one_eq_zero
              (t - s) (chemFluxLifted p (D.u s))
      _ = 0 := by simp

#print axioms hgradB_forces_B_kernel_endpoint_zero

end ShenWork.IntervalGradientBFormGlobalCosine
