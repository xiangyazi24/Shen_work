# Q2490 shen2: common route constructor audit

Repo target: `xiangyazi24/Shen_work`.

Question: after adding the generic `IntervalDomainMassLpSmoothingIntegratedStepResiduals` package and making Paper3's local integrated-step route pass through `to_integratedStepResiduals`, should the next small commit factor a common constructor

```lean
intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
```

shared by the old `IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals` and the new `IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals`?

## Recommendation

Yes, but only in the narrow route-level sense.

The next small commit is worth doing if it is exactly the following refactor:

1. Add one PDE-level constructor in `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` that consumes:
   - `0 < p.a`,
   - `0 ≤ p.χ₀`,
   - `IntervalDomainBoundednessHyp p`,
   - the existing `l2SeedRegularity` field,
   - an already-supplied `Corollary_2_1 intervalDomain p`, and
   - an already-supplied `Proposition_2_5 intervalDomain p`.
2. Make both existing `to_routeResiduals` definitions call this constructor.
3. Do not touch the analytic producer surface.
4. Do not introduce any new theorem producing an integrated step.
5. Do not derive `MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore` from `Corollary_2_1`.

This is a good cleanup because the duplicated part is not analytic. It is the route-level reconstruction of `driftBoundFromMass` from L2 absorption, bootstrap, `Corollary_2_1`, and `Proposition_2_5`. The old pointwise-Moser route and the new integrated-step route now differ only in how they produce those two theorem-level inputs.

## Source-shape facts from the current files

In `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`, the old package already has theorem wrappers:

```lean
IntervalDomainMassLpSmoothingMoserLadderResiduals.corollary21
IntervalDomainMassLpSmoothingMoserLadderResiduals.proposition25
```

where the route-level theorems are obtained from the old actual atoms:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

The new integrated-step package mirrors this shape with:

```lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
```

using:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Both `to_routeResiduals` definitions currently contain the same long `driftBoundFromMass` proof: build spatial/uniform/half-energy L2 ingredients, obtain `LpPowerBoundedBefore intervalDomain 2 T u`, seed the bootstrap, apply `intervalDomainBoundedBefore_of_corollary21_and_proposition25`, convert bounded-before to pointwise bounded-before, then call `IntervalDomainChemotacticDriftBound_of_LinfBound`.

In `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`, the Paper3-local integrated-step residual already has the right adapter boundary:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_integratedStepResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
```

and local `to_routeResiduals` is already just:

```lean
(h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

Therefore the common constructor belongs in `IntervalDomainMoserLadderAtoms.lean`; Paper3 should get the cleanup for free through the generic package. A Paper3 rewrite is not needed for this factoring commit.

## Benefits

### 1. It makes the route boundary explicit

The constructor name states the true route:

```lean
Corollary_2_1 + Proposition_2_5 + L2 seed route
  ⟶ IntervalDomainMassLpSmoothingRouteResiduals
```

That is the common layer. It is independent of whether `Corollary_2_1` and `Proposition_2_5` came from old nonnegative-B pointwise Moser atoms or from the new integrated first-crossing step atoms.

### 2. It removes duplicated brittle proof script

The duplicated proof is not logically hard, but it is long and touches many names:

```lean
intervalDomainL2SpatialAbsorptionEstimate_of_classical
intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution
IntervalDomainL2AbsorbingDifferentialInequality
IntervalDomainL2AbsorbingIntegratedInequality
intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
intervalDomainBoundedBefore_of_corollary21_and_proposition25
pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
supNormControlsPointwiseBefore_of_classicalSolution
IntervalDomainChemotacticDriftBound_of_LinfBound
```

Keeping two copies means future harmless changes to the L2 seed route or drift interface must be synchronized twice.

### 3. It does not add analytic content

The new constructor should not prove either `Corollary_2_1` or `Proposition_2_5`. It only consumes them. Thus it does not claim:

```lean
IntegratedMoserFirstCrossingStep
MoserDissipationDropBeforeNonnegB
RelativeMoserInterpolationBefore
```

from anything weaker.

### 4. It protects the new integrated-step route from accidentally becoming a pointwise route

After the factor, the integrated-step package says:

```lean
integratedStep ⟶ corollary21/proposition25 ⟶ common route constructor
```

not:

```lean
integratedStep ⟶ old pointwise Moser atoms ⟶ old route
```

That is exactly the desired honest separation.

## Risks and how to avoid them

### Risk 1: too much generalization

Do not abstract over the domain, the mass route, or arbitrary theorem names. Keep the constructor interval-domain-specific and route-specific. A fully generic constructor would create typeclass/inference churn without helping the current proof graph.

### Risk 2: placing the constructor inside the wrong namespace

Do not put it inside `namespace IntervalDomainMassLpSmoothingMoserLadderResiduals`. The integrated-step package should call it without importing or opening the old residual namespace semantically.

Recommended placement:

```lean
namespace ShenWork.IntervalDomainExistence

-- after `structure IntervalDomainMassLpSmoothingMoserLadderResiduals`
-- before `namespace IntervalDomainMassLpSmoothingMoserLadderResiduals`

def intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25 ...

namespace IntervalDomainMassLpSmoothingMoserLadderResiduals
...
```

This location is visible to both residual namespaces.

### Risk 3: accidentally changing Paper3 APIs

Do not rename or remove Paper3-facing names. In particular, keep:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_integratedStepResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
```

The current Paper3 shape is already correct.

### Risk 4: attempting a false converse

Do not add any theorem of the form:

```lean
Corollary_2_1 intervalDomain p -> ... -> IntegratedMoserFirstCrossingStep ...
Corollary_2_1 intervalDomain p -> MoserDissipationDropBeforeNonnegB ...
Corollary_2_1 intervalDomain p -> RelativeMoserInterpolationBefore ...
```

That would violate the requested constraints and is not supported by the source shape.

## Minimal compile-oriented patch

Only `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` needs to change.

The imports are already suitable in the current file:

```lean
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainVSliceBounds

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.MinPersistenceAtoms
open Filter
```

### Add this constructor after `structure IntervalDomainMassLpSmoothingMoserLadderResiduals` and before `namespace IntervalDomainMassLpSmoothingMoserLadderResiduals`

```lean
/-- Common route-level constructor for the mass/Lp/smoothing residual package.

This is the shared part of the old pointwise-Moser route and the integrated-step
route: once the L² seed route, Corollary 2.1, and Proposition 2.5 are available,
the chemotactic drift field follows from the reconstructed `L∞` bound.  The
constructor deliberately does not produce either theorem-level input and does
not mention the analytic atoms used to obtain them. -/
def intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
    {p : CM2Params}
    (ha : 0 < p.a)
    (hχ0 : 0 ≤ p.χ₀)
    (hboundedness : IntervalDomainBoundednessHyp p)
    (hl2Seed :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          IntervalDomainL2SeedRegularityFrontier T u)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p) :
    IntervalDomainMassLpSmoothingRouteResiduals p where
  a_pos := ha
  chi_nonneg := hχ0
  boundednessHyp := hboundedness
  driftBoundFromMass := by
    intro u₀ hu₀ T hT u v hsol htrace hmass
    have hspatial :
        IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass :=
      intervalDomainL2SpatialAbsorptionEstimate_of_classical
        hboundedness hsol hmass
    have huniform :
        IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
        hsol
    have hhalf :
        IntervalDomainL2HalfEnergyDifferentialInequality p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution hsol
    have habsorbing :
        IntervalDomainL2AbsorbingDifferentialInequalityResult p T u :=
      IntervalDomainL2AbsorbingDifferentialInequality
        hboundedness.1 hsol hmass hspatial huniform
    have hregularity : IntervalDomainL2SeedRegularityFrontier T u :=
      hl2Seed u₀ hu₀ T hT u v hsol htrace
    have hintegrated :
        IntervalDomainL2AbsorbingIntegratedInequalityResult p T u :=
      IntervalDomainL2AbsorbingIntegratedInequality
        hboundedness.2.1 hsol habsorbing hregularity
    have hL2 :
        LpPowerBoundedBefore intervalDomain 2 T u :=
      intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
        hsol hintegrated hregularity
    have hbootstrap :
        ∃ rho > 0,
          CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
            ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
              LpPowerBoundedBefore intervalDomain p0 T u :=
      intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
        hboundedness hu₀ hT hsol htrace hhalf hL2
    have hbounded :
        IsPaper2BoundedBefore intervalDomain T u :=
      intervalDomainBoundedBefore_of_corollary21_and_proposition25
        hCor21 hProp25 hu₀ hT hsol htrace hbootstrap
    have hpoint : PointwiseBoundedBefore T u :=
      pointwiseBoundedBefore_of_boundedBefore_and_supNormControls hbounded
        (supNormControlsPointwiseBefore_of_classicalSolution hsol)
    exact IntervalDomainChemotacticDriftBound_of_LinfBound hsol hpoint
  l2SeedRegularity := hl2Seed
  allLpBoundFromBootstrap := hCor21
  endpointBoundFromLp := hProp25
```

### Replace the old pointwise-Moser `to_routeResiduals` body with this

```lean
/-- Build the old residual package.  The old drift field is reconstructed from
L² seed regularity plus the route-level `Corollary_2_1` and `Proposition_2_5`
inputs produced by the actual nonnegative-`B` Moser atoms. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
    (p := p) h.a_pos h.chi_nonneg h.boundednessHyp h.l2SeedRegularity
    h.corollary21 h.proposition25
```

### Replace the integrated-step `to_routeResiduals` body with this

```lean
/-- Build the old mass/Lp/smoothing residual package from the integrated-step
route.  The only integrated-step-specific work is producing Corollary 2.1 and
Proposition 2.5; the route-level drift reconstruction is shared. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
    (p := p) h.a_pos h.chi_nonneg h.boundednessHyp h.l2SeedRegularity
    h.corollary21 h.proposition25
```

The rest of the file can stay unchanged:

```lean
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound
```

and

```lean
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound
```

should still compile as before.

## Optional axiom-print additions

The existing file already prints axioms for the integrated-step route. If desired, add one print for the common constructor:

```lean
#print axioms intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
```

This is optional. It can help verify that the common constructor itself introduced no new axioms beyond the already-used route dependencies, but it is not needed for the refactor.

## What not to change

Do not change `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` for this factoring unless you only update comments. Its current integrated-step route is already the right wrapper shape:

```lean
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

After the PDE-level generic `to_routeResiduals` is factored, this Paper3 wrapper automatically consumes the common constructor.

## Bottom line

This is worth the churn if kept to one constructor plus two short rewrites. It is not worth doing as a broader abstraction pass.

The safe next commit should be a pure refactor in `IntervalDomainMoserLadderAtoms.lean`:

```text
Corollary_2_1 + Proposition_2_5 + L2 seed route
  -> common route constructor
  -> old pointwise-Moser to_routeResiduals
  -> integrated-step to_routeResiduals
```

No new analytic claims are needed, and the hard constraints are preserved.
