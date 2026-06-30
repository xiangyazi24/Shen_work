# Q2484 shen1 — audit and corrected generic integrated-step Moser route

Repo: `xiangyazi24/Shen_work`

Target files:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

## Source audit summary

The current source already has the relevant split:

* `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` is in namespace
  `ShenWork.IntervalDomainExistence` and already imports `ShenWork.PDE.P3MoserActualWiring`.
* That file already defines the generic non-integrated package
  `IntervalDomainMassLpSmoothingMoserLadderResiduals`, with methods
  `corollary21`, `proposition25`, `to_routeResiduals`, and `aprioriBound`.
* `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` currently has the Paper3-local integrated-step package
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals`, whose `to_routeResiduals` repeats the long L2/mass/smoothing route body inline.
* `P3MoserActualWiring` already provides the two route-level consumers needed for the integrated-step package:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Those consumers produce `Corollary_2_1 intervalDomain p` and `Proposition_2_5 intervalDomain p` from a supplied `IntegratedMoserFirstCrossingStep` atom plus the quantitative endpoint.  The generic package should use them directly.  It should **not** produce `IntegratedMoserFirstCrossingStep`, and it should **not** derive `MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore` from `Corollary_2_1`.

## Compile-risk checklist and corrections

1. **Namespace placement.**  Add the generic integrated-step package inside

```lean
namespace ShenWork.IntervalDomainExistence
```

in `IntervalDomainMoserLadderAtoms.lean`, alongside `IntervalDomainMassLpSmoothingMoserLadderResiduals`.  Do not put it in `ShenWork.Paper3`, and do not put it under `P3MoserActualWiring`.

2. **Name resolution for `IntegratedMoserFirstCrossingStep`.**  `IntervalDomainMoserLadderAtoms.lean` currently opens `P3MoserActualWiring`, but not `P3MoserIntegratedClosure`.  Either add

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

near the existing opens, or use the qualified name

```lean
P3MoserIntegratedClosure.IntegratedMoserFirstCrossingStep
```

in the new structure field.  I recommend the qualified name to avoid changing global open behavior.

3. **Imports.**  No new import is needed in `IntervalDomainMoserLadderAtoms.lean`: it already imports `ShenWork.PDE.P3MoserActualWiring`, and that file imports `P3MoserIntegratedClosure`.  Do **not** import `Paper3.IntervalDomainActualLinearStatementAssembly` or any Paper3 file into the PDE file.

4. **Do not convert through `IntervalDomainMassLpSmoothingMoserLadderResiduals`.**  That existing structure requires `moserDissipation` and `relativeMoserInterpolation`.  An integrated-step package does not have these fields and should not synthesize them.  The integrated-step package should go directly to `IntervalDomainMassLpSmoothingRouteResiduals` using route-level `Corollary_2_1` and `Proposition_2_5`.

5. **Can `to_routeResiduals` code be copied?**  Yes, but copy it from `IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals`, not from the Paper3-local integrated-step version.  The generic copy should use an abstract `l2SeedRegularity` field.  Better still, factor the common long body into a route-level constructor that takes `Corollary_2_1` and `Proposition_2_5` as arguments; then the old and new routes can share the same body.

6. **Closed-energy conversion remains Paper3-local.**  `ClosedEnergyIdentityTraceData` is currently in namespace `P3MoserLemmaDischarge`.  The generic PDE package should not mention it.  Keep the conversion

```lean
P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
```

inside the Paper3-local `to_integratedStepResiduals` adapter.

7. **Paper3 local `to_routeResiduals`.**  Yes: it should become a short alias through `to_integratedStepResiduals`.  That removes duplicate L2/mass/smoothing code from Paper3 and makes future route corrections generic.

## Patch 1: add the generic integrated-step route in `IntervalDomainMoserLadderAtoms.lean`

Insert this after the existing namespace block

```lean
end IntervalDomainMassLpSmoothingMoserLadderResiduals
```

and before

```lean
end ShenWork.IntervalDomainExistence
```

```lean
/-- Common constructor for mass/Lp/smoothing route residuals once the route-level
Corollary 2.1 and Proposition 2.5 consumers have been supplied.

This is the common body of the old Moser-ladder route and the integrated-step
route.  It does not know how either `Corollary_2_1` or `Proposition_2_5` was
proved, and it does not manufacture dissipation or relative-Moser atoms. -/
def intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
    {p : CM2Params}
    (ha : 0 < p.a)
    (hchi : 0 ≤ p.χ₀)
    (hboundedness : IntervalDomainBoundednessHyp p)
    (hl2SeedRegularity :
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
  chi_nonneg := hchi
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
      hl2SeedRegularity u₀ hu₀ T hT u v hsol htrace
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
  l2SeedRegularity := hl2SeedRegularity
  allLpBoundFromBootstrap := hCor21
  endpointBoundFromLp := hProp25

/-- Generic mass/Lp/smoothing residuals whose Moser component is supplied as an
integrated first-crossing step atom.

This package consumes an already-proved integrated step.  It does not prove such
a step, and it does not derive physical-`B` dissipation or relative interpolation
from route-level outputs. -/
structure IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals
    (p : CM2Params) : Prop where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  integratedStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        P3MoserIntegratedClosure.IntegratedMoserFirstCrossingStep
          intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals

/-- Route-level Corollary 2.1 from the integrated first-crossing step atom. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    h.integratedStep

/-- Route-level Proposition 2.5 from the integrated first-crossing step atom and
quantitative endpoint. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    h.integratedStep h.quantitativeEndpoint

/-- Build the old mass/Lp/smoothing route residual surface from the integrated
step package. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
    h.a_pos h.chi_nonneg h.boundednessHyp h.l2SeedRegularity
    h.corollary21 h.proposition25

/-- A-priori bound from the integrated-step mass/Lp/smoothing residuals. -/
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound

#print axioms intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
#print axioms IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals.corollary21
#print axioms IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals.proposition25
#print axioms IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals.aprioriBound

end IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals
```

### Optional low-risk refactor

After adding the common constructor, the existing
`IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals` can be shortened later to:

```lean
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  intervalDomainMassLpSmoothingRouteResiduals_of_corollary21_and_proposition25
    h.a_pos h.chi_nonneg h.boundednessHyp h.l2SeedRegularity
    h.corollary21 h.proposition25
```

This refactor is not required for Q2484.  It is safer to add the integrated-step route first and leave the existing route untouched unless you want to reduce duplication in the same commit.

## Patch 2: make the Paper3-local integrated route an alias

In `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`, replace the current long body of

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
```

with an adapter through the new generic package.  Keep this inside the existing namespace

```lean
namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

```lean
/-- Convert the Paper3 actual-linear closed-energy integrated-step package to the
generic integrated-step residual surface.

The closed-energy-to-L²-seed conversion intentionally remains Paper3-local. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingMoserIntegratedStepResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  integratedStep := h.integratedStep
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Build the old route residual surface via the generic integrated-step package. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_integratedStepResiduals ha hχ0).to_routeResiduals

#print axioms IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_integratedStepResiduals
#print axioms IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
```

No downstream theorem statement needs to change.  For example, the existing line

```lean
massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0
```

in `IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts.to_aprioriActualLinearSmallFacts` should keep compiling, because the local `to_routeResiduals` signature is unchanged.

## Things not to add

Do not add any theorem of the following form in this genericization:

```lean
theorem ... : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := ...
```

The integrated step remains an analytic atom supplied by the residual package.

Do not add a conversion

```lean
Corollary_2_1 intervalDomain p →
  MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
```

or

```lean
Corollary_2_1 intervalDomain p →
  RelativeMoserInterpolationBefore intervalDomain u T rho p0
```

Those would invert a route-level conclusion into analytic inputs and would be mathematically backwards.

Do not make the generic integrated-step residual extend or convert to
`IntervalDomainMassLpSmoothingMoserLadderResiduals`; that would require exactly the forbidden dissipation/interpolation fields.  The correct target is directly
`IntervalDomainMassLpSmoothingRouteResiduals`.
