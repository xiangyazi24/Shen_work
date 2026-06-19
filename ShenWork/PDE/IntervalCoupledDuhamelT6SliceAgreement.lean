import ShenWork.PDE.IntervalChemDivFluxChain
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity
import ShenWork.PDE.IntervalFullSemigroupNeumann
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalGradientDuhamelMap

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- The Picard gradient-form chemotaxis flux vanishes at the left endpoint.
This is the endpoint cancellation requested for the `Q` factor: the endpoint
resolver gradient is zero. -/
theorem chemFluxLifted_endpoint_zero
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    chemFluxLifted p w 0 = 0 := by
  unfold chemFluxLifted
  rw [ShenWork.Paper2.resolverGradReal_zero]
  simp

/-- The Picard gradient-form chemotaxis flux vanishes at the right endpoint. -/
theorem chemFluxLifted_endpoint_one
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    chemFluxLifted p w 1 = 0 := by
  unfold chemFluxLifted
  rw [ShenWork.Paper2.resolverGradReal_one]
  simp

/-- The coupled chem-div inner flux also vanishes at the left endpoint.  In the
current source-form file this flux is expressed with
`deriv (intervalDomainLift (coupledChemicalConcentration ...))`, whose endpoint
derivative is zero for the zero-extension lift. -/
theorem coupledChemDivFluxLift_endpoint_zero
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) :
    coupledChemDivFluxLift p u s 0 = 0 := by
  simp [coupledChemDivFluxLift,
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_zero]

/-- The coupled chem-div inner flux vanishes at the right endpoint. -/
theorem coupledChemDivFluxLift_endpoint_one
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) :
    coupledChemDivFluxLift p u s 1 = 0 := by
  simp [coupledChemDivFluxLift,
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_one]

/-- Any pointwise bridge from a full-Neumann gradient term to a full-Neumann
source profile forces the source profile to vanish at the left endpoint.  This
is a definition-level check on the proposed `∂ₓS_N Q = S_N(∂ₓQ)` route. -/
theorem neumannGradient_sourceBridge_forces_leftEndpoint_zero
    (t : ℝ) (flux source : ℝ → ℝ)
    (hbridge : deriv (fun z => intervalFullSemigroupOperator t flux z) 0 =
      intervalFullSemigroupOperator t source 0) :
    intervalFullSemigroupOperator t source 0 = 0 := by
  rw [← hbridge]
  exact ShenWork.intervalFullSemigroupOperator_deriv_at_zero_eq_zero t flux

/-- Right-endpoint version of
`neumannGradient_sourceBridge_forces_leftEndpoint_zero`. -/
theorem neumannGradient_sourceBridge_forces_rightEndpoint_zero
    (t : ℝ) (flux source : ℝ → ℝ)
    (hbridge : deriv (fun z => intervalFullSemigroupOperator t flux z) 1 =
      intervalFullSemigroupOperator t source 1) :
    intervalFullSemigroupOperator t source 1 = 0 := by
  rw [← hbridge]
  exact ShenWork.intervalFullSemigroupOperator_deriv_at_one_eq_zero t flux

#print axioms chemFluxLifted_endpoint_zero
#print axioms chemFluxLifted_endpoint_one
#print axioms coupledChemDivFluxLift_endpoint_zero
#print axioms coupledChemDivFluxLift_endpoint_one
#print axioms neumannGradient_sourceBridge_forces_leftEndpoint_zero
#print axioms neumannGradient_sourceBridge_forces_rightEndpoint_zero

end ShenWork.IntervalCoupledRegularityBootstrap

