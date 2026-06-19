import ShenWork.PDE.IntervalCoupledRegularityBanked
import ShenWork.Paper2.IntervalRegularityFrontierWiring

open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring

/-- The already banked regularity frontier is exactly the post-T6 residual
package for the coupled resolver, after unfolding the two resolver aliases. -/
theorem coupledDuhamelClassicalResidualAfterT6_of_frontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (F : GradientMildClassicalRegularityFrontierData p D) :
    CoupledDuhamelClassicalResidualAfterT6 p D.T D.u where
  v_interiorC2 := by
    intro t ht
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.vSpatialInterior t ht
  timeC1 := by
    intro x t ht
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.timeSlices x t ht
  jointTimeDeriv := by
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.jointTimeDerivInterior
  v_neumannLimits := by
    intro t ht
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.vNeumannLimits t ht
  v_closedC2 := by
    intro t ht
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.vClosedSpatial t ht
  closedJointTimeDeriv := by
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.jointTimeDerivClosed
  jointValue := by
    simpa [coupledChemicalConcentration, mildChemicalConcentration]
      using F.jointSolutionClosed

/-- Discharge `CoupledDuhamelClassicalResidualAfterT6` for a gradient mild fixed
point from the banked u-time, resolver-time, restart/O1 spatial, and resolver
positivity atoms.  This theorem is independent of the T6 slice-agreement bridge. -/
theorem coupledDuhamelClassicalResidualAfterT6_of_banked_resolver_O1_T6
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (Hv : HasResolverDirectSpectralData D.T
      (mildChemicalConcentration p D.u) p)
    (Hrestart : HasRestartCosineRepresentations D.T D.u)
    (Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p D.u t x) :
    CoupledDuhamelClassicalResidualAfterT6 p D.T D.u :=
  coupledDuhamelClassicalResidualAfterT6_of_frontier p D
    (gradientMildClassicalRegularityFrontierData_of_spectral
      p D Hu Hv Hrestart Hvpos)

#print axioms coupledDuhamelClassicalResidualAfterT6_of_frontier
#print axioms coupledDuhamelClassicalResidualAfterT6_of_banked_resolver_O1_T6

end ShenWork.IntervalCoupledRegularityBootstrap
