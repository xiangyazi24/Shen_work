import ShenWork.Paper2.IntervalGeneralChiFrontier
import ShenWork.PDE.IntervalChemDivTimeDerivative

/-!
# General-chi mild source `hsrc`: exact residual wrapper

This file intentionally adds only a new constructor.  The existing library already
has the chem-div source producer
`coupledChemDivSource_timeC1_of_fields` and the split constructor
`coupledChemicalSource_duhamelSourceTimeC1`; this theorem exposes exactly the
remaining inputs needed for the `GradientMildSolutionData` fixed point.

No `sorry`, `admit`, custom axiom, or slice-agreement wiring.
-/

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Coupled chemical source `DuhamelSourceTimeC1` for a gradient mild fixed point,
modulo the precise source-regularity residuals.

Residuals:
* `hlog`: global time-`C¹`/ℓ¹ package for the logistic coefficients;
* `hchem`: the committed chem-div coefficient field package, including the
  uniform derivative bound `hMdot`;
* `hcoeffSplit`: the coefficient-level split of the coupled source into
  `-χ₀ * chemDiv + logistic`.
-/
noncomputable def coupledChemicalSourceCoeffs_duhamelSourceTimeC1_of_gradientMild
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p D.u))
    (hchem : CoupledChemDivTimeC1Fields p D.u)
    (hcoeffSplit : coupledChemicalSourceCoeffs p D.u =
      fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p D.u s n)
        + coupledLogisticSourceCoeffs p D.u s n) :
    DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p D.u) := by
  exact coupledChemicalSource_duhamelSourceTimeC1 hlog
    (coupledChemDivSource_timeC1_of_fields hchem) hcoeffSplit

#print axioms coupledChemicalSourceCoeffs_duhamelSourceTimeC1_of_gradientMild

end ShenWork.IntervalCoupledRegularityBootstrap
