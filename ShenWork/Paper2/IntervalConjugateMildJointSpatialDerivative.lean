/-
  Interior space-time continuity of the faithful mild spatial derivative.

  Joint continuity of the values and the uniform positive-time Holder modulus
  of the spatial derivative are converted to joint derivative continuity by
  the generic parametric mean-value bridge.
-/
import ShenWork.Paper2.IntervalConjugateMildJointValue
import ShenWork.Paper2.IntervalConjugateMildPositiveTimeC1
import ShenWork.Paper2.IntervalParametricSpatialDerivativeContinuity

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)

/-- The ordinary spatial derivative of the lifted faithful mild solution is
jointly continuous at every strict-positive-time interior spatial point. -/
theorem conjugateMild_jointSpatialDeriv_interior
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦ deriv (intervalDomainLift (D.u t)) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Ioo (0 : ℝ) 1) := by
  apply parametricSpatialDeriv_jointContinuousOn_Ioo_space_of_positiveStripHolder
    (theta := (1 : ℝ) / 4) (by norm_num)
  · exact conjugateMild_jointValue_u D hu0_bound hu0_meas
  · intro t ht x hx
    exact (conjugateMild_intervalDomainLift_hasDerivAt_interior
      D hu0_bound hu0_meas
        (θ := (1 : ℝ) / 4) (by norm_num) (by norm_num)
        ht.1 ht.2.le hx).differentiableAt.differentiableWithinAt
  · intro tau htau
    obtain ⟨H, hH, hholder⟩ :=
      conjugateMild_intervalDomainLift_deriv_positiveTime_holder_uniform
        D hu0_bound hu0_meas
          (τ := tau) (eta := (1 : ℝ) / 4)
          htau (by norm_num) (by norm_num)
    refine ⟨H, hH, ?_⟩
    intro t ht x hx y hy
    exact hholder t ht.1 ht.2 x hx y hy

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMild_jointSpatialDeriv_interior
