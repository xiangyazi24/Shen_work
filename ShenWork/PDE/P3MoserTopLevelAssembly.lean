import ShenWork.PDE.P3MoserRealInduction
import ShenWork.PDE.P3MoserRealInductionClosure
import ShenWork.PDE.P3MoserSubintervalInput
import ShenWork.PDE.P3MoserUniformization
import ShenWork.PDE.P3MoserShortTimeBounded
import ShenWork.PDE.P3MoserContinuityExtension

/-!
# Top-level assembly: Moser chain conditional theorem

Wires tasks 25–34 into a single conditional theorem reducing
`IsPaper2BoundedBefore` to exactly two irreducible residuals:

1. `SubintervalAssemblyResidual` — the Moser iteration output on subintervals
2. `PointwiseUniformizationResidual` — per-t → uniform bound conversion

All other intermediate residuals (short-time, extension, bootstrap input,
Lp bridge, real-induction closure) are discharged unconditionally for
`intervalDomain`.
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation
open ShenWork.IntervalDomainExistence.P3MoserRealInduction
open ShenWork.IntervalDomainExistence.P3MoserRealInductionClosure
open ShenWork.IntervalDomainExistence.P3MoserShortTimeBounded
open ShenWork.IntervalDomainExistence.P3MoserContinuityExtension
open ShenWork.IntervalDomainExistence.P3MoserSubintervalInput
open ShenWork.IntervalDomainExistence.P3MoserUniformization
open ShenWork.Paper2

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserTopLevelAssembly

/-- **Top-level Moser chain assembly for `intervalDomain`.**

Given two irreducible residuals:
1. `SubintervalAssemblyResidual` — the Moser iteration produces a uniform
   bound on each closed subinterval `[0, τ]` from bootstrap data
2. `PointwiseUniformizationResidual` — the conversion from per-time-slice
   bounds to a single uniform bound on `(0, T)`

every classical solution on the unit interval is bounded before `T`.

All intermediate pieces (short-time A, continuation wiring B, extension C,
supremum closure D, Lp bridge, bootstrap input) are proved unconditionally
for `intervalDomain` by tasks 29–34. -/
theorem intervalDomain_isPaper2BoundedBefore_of_assembly_and_uniformization
    {p : CM2Params}
    (hAssembly : SubintervalAssemblyResidual intervalDomain p)
    (hUniform : PointwiseUniformizationResidual intervalDomain p)
    {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hshort : ShortTimeBoundedBeforeResidual intervalDomain p :=
    intervalDomain_shortTimeBoundedBeforeResidual p
  have hextend : ExtensionByContinuityResidual intervalDomain p :=
    intervalDomain_extensionByContinuityResidual p
  have hLp : SubintervalLpPowerBoundResidual p :=
    subintervalLpPowerBoundResidual_of_pointwiseUniformizationResidual hUniform
  have hInputs : SubintervalMoserInputResidual p :=
    intervalDomain_subintervalMoserInputResidual hLp
  have hClosure : FirstCrossingPointwiseUniformClosureResidual intervalDomain p :=
    intervalDomain_FirstCrossingPointwiseUniformClosureResidual hUniform
  have hD : FirstCrossingSupremumClosureResidual intervalDomain p :=
    intervalDomain_FirstCrossingSupremumClosureResidual hInputs hClosure
  exact boundedBefore_of_classical_and_assembly hshort hAssembly hextend hD hsol

#print axioms intervalDomain_isPaper2BoundedBefore_of_assembly_and_uniformization

end ShenWork.IntervalDomainExistence.P3MoserTopLevelAssembly

end
