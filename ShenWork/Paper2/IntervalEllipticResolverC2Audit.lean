import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalChemDivFluxFactorFAC
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity
import ShenWork.Paper2.IntervalResolverWeakBounds

/-!
# Audit: elliptic C2 route for the interval Neumann resolver

This module records whether the committed elliptic resolver API supplies the
`ContDiffAt R 2` facts needed by the FAC package without the spectral
lambda-square coefficient route.

## Findings

The FAC consumer is
`CoupledChemDivFluxFactorJointC2Inputs.exists_local_slab`.  Its resolver fields
are joint `ContDiffAt R 2` facts for

* `(t, x) |-> lift (coupledChemicalConcentration p u t) x`, and
* `(t, x) |-> deriv (lift (coupledChemicalConcentration p u t)) x`.

The current FAC wrapper obtains these via
`ResolverHasSpectralAgreementC2Coeff` and
`resolverSpectralJointC2At_of_restartSmoothCutoff`.

The committed elliptic resolver regularity does not contain a Schauder-style
bounded/Holder-source theorem.  The available spatial C2 theorem is
`IntervalResolverSpatialC2.resolverR_contDiff_two`, and its hypothesis is
`SourceCoeffQuadraticDecay p u`.  That is exactly the coefficient-decay route:
the source coefficients must satisfy `|a_k| <= C / (k*pi)^2`, not merely be
bounded, continuous, or Holder.

The weak bounded/continuous-source APIs in `IntervalResolverWeakBounds` prove
source coefficient `l2`, absolute convergence of the value and gradient series,
sup bounds, and continuity.  `IntervalResolverDirectTimeRegularity` proves direct
time differentiability and joint continuity of the time derivative from
`DuhamelSourceTimeC1`.  None of those statements gives the FAC's joint
`ContDiffAt R 2` value and gradient fields.

Verdict: route (b).  No clean re-wiring is available from committed lemmas.  The
missing bridge is a genuine elliptic regularity theorem for the concrete
Neumann resolver, e.g. Holder source implies the lifted resolver is spatial
`C2,alpha`, plus a time-parametric version strong enough to yield the two FAC
joint `ContDiffAt R 2` fields.  The one-dimensional problem is analytically
tractable, but it is not already committed in this tree.
-/

namespace ShenWork
namespace Paper2

def ellipticResolverC2AuditQuestion : String :=
  "Does intervalNeumannResolverR already map a bounded/Holder source to C2?"

theorem ellipticResolverC2AuditSkeleton : True := by
  trivial

#print axioms ellipticResolverC2AuditSkeleton

#check ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorFACInputs
#check ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs
#check ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
#check ShenWork.IntervalResolverSpatialC2.resolverR_contDiff_two
#check ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
#check ShenWork.IntervalResolverWeakBounds.resolver_cosineSeries_summable_of_sourceL2
#check ShenWork.IntervalResolverWeakBounds.resolver_sineSeries_summable_of_sourceL2
#check ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_jointSolutionClosed
#check ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_jointTimeDerivClosed

end Paper2
end ShenWork
