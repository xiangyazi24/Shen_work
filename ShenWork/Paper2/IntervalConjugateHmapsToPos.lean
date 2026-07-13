import ShenWork.Paper2.IntervalConjugatePicardInfThreshold
import ShenWork.Paper2.IntervalConjugateDuhamelMap

/-!
# `hmapsTo_pos` floor lemma generalized to an arbitrary ball trajectory

`intervalConjugateDuhamelMap_ge_half_floor` is stated for the Picard iterates;
the `ConjugateMildExistenceCore.hmapsTo_pos` field needs the same lower bound for
an ARBITRARY ball element `w`.  This file abstracts the per-`w` chemotaxis-flux
and logistic analytic inputs as explicit hypotheses (discharged by the ball-level
flux integrability/bound lemmas), mirroring the proven iterate-level argument.
-/

namespace ShenWork.Paper2

open scoped BigOperators
open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalConjugatePicard

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}

/-- Algebraic half-floor bound when the homogeneous semigroup lower bound is
supplied explicitly.  This is the threshold-uniform form: unlike
`intervalConjugateDuhamelMap_ge_half_floor_of_ball`, it does not inspect a
chosen floor witness attached to the datum. -/
theorem intervalConjugateDuhamelMap_ge_half_floor_of_semigroup_lower
    {floor CQ CL : ℝ} (hCQ : 0 ≤ CQ) (hCL : 0 ≤ CL)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
        + T * CL ≤ floor / 2)
    {w : ℝ → intervalDomainPoint → ℝ}
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint)
    (hS : floor ≤
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1)
    (hB_abs :
      |∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (w s)) x.1|
        ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
    (hR_abs :
      |∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1| ≤ T * CL) :
    floor / 2 ≤ intervalConjugateDuhamelMap p u₀ w t x := by
  set S : ℝ := intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  set B : ℝ := ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1
  set R : ℝ := ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1
  have hchem_lower :
      -(|p.χ₀| *
          (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ))
        ≤ (-p.χ₀) * B := by
    have hchem_abs : |(-p.χ₀) * B| ≤
        |p.χ₀| *
          (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ) := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left hB_abs (abs_nonneg p.χ₀)
    exact (abs_le.mp hchem_abs).1
  have hR_lower : -(T * CL) ≤ R := (abs_le.mp hR_abs).1
  change floor / 2 ≤ S + (-p.χ₀) * B + R
  linarith

/-- Per-`w` one-step half-floor lower bound for the conjugate Duhamel map. -/
theorem intervalConjugateDuhamelMap_ge_half_floor_of_ball
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {CQ CL : ℝ} (hCQ : 0 ≤ CQ) (hCL : 0 ≤ CL)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
        + T * CL ≤ paperPositiveFloor hu₀ / 2)
    {w : ℝ → intervalDomainPoint → ℝ}
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint)
    (hB_abs :
      |∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (w s)) x.1|
        ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
    (hR_abs :
      |∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1| ≤ T * CL) :
    paperPositiveFloor hu₀ / 2 ≤
      intervalConjugateDuhamelMap p u₀ w t x := by
  have hS : paperPositiveFloor hu₀ ≤
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 := by
    exact intervalFullSemigroupOperator_ge_paperPositiveFloor hu₀ ht x.1
  exact intervalConjugateDuhamelMap_ge_half_floor_of_semigroup_lower
    hCQ hCL hsmall ht x hS hB_abs hR_abs


end ShenWork.Paper2
