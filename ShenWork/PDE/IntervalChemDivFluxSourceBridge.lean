import ShenWork.PDE.IntervalChemDivAEMeasurable
import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.Paper2.IntervalGradientDuhamelMap

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Classical-solution specialization of the chemotactic flux/source bridge.

This is only a wrapper around the physical product/quotient/rpow chain rule
`solution_chemotaxisFlux_hasDerivAt`, plus the resolver-gradient identity
`solution_lift_v_deriv_eq_resolverGrad` on an interior neighborhood.  It does
not use the restart/time-neighborhood spectral package. -/
theorem coupledChemDivSourceLift_hasDerivAt_chemFluxLifted_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (chemFluxLifted p (u s)) (coupledChemDivSourceLift p u s y) y := by
  let yy : intervalDomainPoint := ⟨y, Ioo_subset_Icc_self hy⟩
  have hphys :
      HasDerivAt
        (fun z : ℝ =>
          intervalDomainLift (u s) z *
            deriv (intervalDomainLift (coupledChemicalConcentration p u s)) z /
              (1 + intervalDomainLift (coupledChemicalConcentration p u s) z) ^ p.β)
        (intervalDomainChemotaxisDiv p (u s)
          (coupledChemicalConcentration p u s) yy) y :=
    ShenWork.solution_chemotaxisFlux_hasDerivAt
      (p := p) (T := T) (u := u) (v := coupledChemicalConcentration p u)
      hsol (τ := s) hs (y := yy) hy
  have hflux_eq :
      chemFluxLifted p (u s) =ᶠ[𝓝 y]
        (fun z : ℝ =>
          intervalDomainLift (u s) z *
            deriv (intervalDomainLift (coupledChemicalConcentration p u s)) z /
              (1 + intervalDomainLift (coupledChemicalConcentration p u s) z) ^ p.β) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz
    have hgrad :
        deriv (intervalDomainLift (coupledChemicalConcentration p u s)) z =
          ShenWork.Paper2.resolverGradReal p (u s) z :=
      ShenWork.Paper2.solution_lift_v_deriv_eq_resolverGrad
        (p := p) (T := T) (u := u)
        (v := coupledChemicalConcentration p u) hsol hs hz
    have hgrad' :
        deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (u s))) z =
          ShenWork.Paper2.resolverGradReal p (u s) z := by
      simpa [coupledChemicalConcentration] using hgrad
    unfold chemFluxLifted coupledChemicalConcentration
    rw [hgrad']
  have hsource :
      coupledChemDivSourceLift p u s y =
        intervalDomainChemotaxisDiv p (u s)
          (coupledChemicalConcentration p u s) yy := by
    simp [coupledChemDivSourceLift, intervalDomainLift, yy, Ioo_subset_Icc_self hy]
  rw [hsource]
  exact hphys.congr_of_eventuallyEq hflux_eq

#print axioms coupledChemDivSourceLift_hasDerivAt_chemFluxLifted_of_classical

end ShenWork.IntervalCoupledRegularityBootstrap