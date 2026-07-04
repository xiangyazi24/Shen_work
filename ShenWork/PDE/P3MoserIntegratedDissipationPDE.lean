import ShenWork.PDE.P3MoserRegularityProducer

/-!
# Frontier #3: integrated Moser dissipation from the PDE energy interface

This file is the thin PDE-facing assembly layer for
`IntegratedMoserDissipationDropBefore`.

The strict-time `LpBootstrapEnergyInequality` is already produced from the
classical PDE, the cross-diffusion bootstrap, and the abstract bootstrap
hypothesis.  The integrated closure then needs the window FTC, relative Moser
interpolation, closed-time regularity, and the coefficient gap that leaves
coefficient `2` after absorption.

The current public predicate existentially forgets the final constant `C(p)`.
This file therefore does not claim a polynomial-growth bound for `C(p)`; such a
bound needs a strengthened quantitative predicate carrying the interpolation
constant growth.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDE

/-- Integrated Moser dissipation from the global PDE energy route, conditional
on the two residuals that the existing Moser stack keeps explicit:

* `hdata`: closed-time power-energy regularity plus gradient time
  integrability;
* `hgap`: the coefficient gap `2 < p*A` needed to absorb the higher-power term
  with final gradient coefficient `2`.

The PDE part itself is supplied by
`intervalDomain_LpBootstrapEnergyInequality_of_regularity`, which consumes
`hsol`, `hcross`, and `hboot`. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hgap :
      ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 := by
  have hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
      hdata hsol
  have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical
      (p0 := p0) hsol
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  exact
    intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
      (params := params) (T := T) (rho := rho) (p0 := p0) (u := u)
      hboot henergy hftc hreg hnonneg hrel hgap

/-- Same assembly, with the regularity and coefficient-gap residuals supplied
as `Fact` instances.  This keeps the visible argument list aligned with the
frontier-#3 PDE inputs while preserving the residual assumptions in the theorem
context. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_fact
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    [hdata : Fact (IntervalDomainIntegratedMoserClassicalRegularityData u T p0)]
    [hgap : Fact
      (∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A)]
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
  intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE
    hsol hcross hboot hftc hrel hdata.out hgap.out

#print axioms intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE
#print axioms intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_fact

end ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDE

end
