# Q2479 shen2: genericizing the Paper3-local integrated-step route

Repo target: `xiangyazi24/Shen_work`, after commit `5b83ceab`.

This is the **genericization** plan only. It is not a Paper2 statement-wrapper audit.

## Goal

Move the reusable residual package out of `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` and into:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Then make Paper3 consume that generic package while keeping the existing Paper3-facing API names stable.

The generic package should fill:

```lean
IntervalDomainMassLpSmoothingRouteResiduals p
```

directly by producing route-level:

```lean
Corollary_2_1 intervalDomain p
Proposition_2_5 intervalDomain p
```

from a supplied:

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

plus the existing quantitative endpoint/root tower.  It must **not** derive old pointwise atoms and must **not** produce the integrated step.

## File 1: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`

### Import/open changes

Current imports already include:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

At `5b83ceab`, `P3MoserActualWiring` imports `P3MoserIntegratedClosure`, but add the direct import for clarity:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

Recommended import block:

```lean
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainVSliceBounds
```

Add this open near the existing `P3MoserActualWiring` open:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This avoids fully qualifying `IntegratedMoserFirstCrossingStep`.

### Placement

Insert the new generic package immediately after:

```lean
end IntervalDomainMassLpSmoothingMoserLadderResiduals
```

and before:

```lean
end ShenWork.IntervalDomainExistence
```

This keeps the reusable pointwise-Moser and integrated-step mass/Lp/smoothing packages adjacent.

### Generic names

Use these exact generic names:

```lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound
```

Do not use Paper3/actual-linear-small names in the PDE-level file.

### Compile-oriented code

```lean
/-- Lower-level inputs that replace the old pointwise Moser-ladder route fields
by a supplied integrated first-crossing step.

This package is route-level: it consumes `IntegratedMoserFirstCrossingStep`
directly via `P3MoserActualWiring` and does not derive old pointwise Moser atoms
such as `MoserDissipationDropBeforeNonnegB` or
`RelativeMoserInterpolationBefore`. -/
structure IntervalDomainMassLpSmoothingIntegratedStepResiduals
    (p : CM2Params) where
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
      IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
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

namespace IntervalDomainMassLpSmoothingIntegratedStepResiduals

/-- Corollary 2.1 from the supplied integrated first-crossing step. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    h.integratedStep

/-- Proposition 2.5 from the supplied integrated first-crossing step and the
quantitative Moser endpoint/root tower. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    h.integratedStep h.quantitativeEndpoint

/-- Build the old mass/Lp/smoothing residual package from the integrated-step
route.

The drift field is reconstructed from the `L∞` bound obtained by the L² seed,
Corollary 2.1, and Proposition 2.5, exactly as in
`IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals`. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  driftBoundFromMass := by
    intro u₀ hu₀ T hT u v hsol htrace hmass
    have hCor21 : Corollary_2_1 intervalDomain p := h.corollary21
    have hProp25 : Proposition_2_5 intervalDomain p := h.proposition25
    have hspatial :
        IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass :=
      intervalDomainL2SpatialAbsorptionEstimate_of_classical
        h.boundednessHyp hsol hmass
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
        h.boundednessHyp.1 hsol hmass hspatial huniform
    have hregularity : IntervalDomainL2SeedRegularityFrontier T u :=
      h.l2SeedRegularity u₀ hu₀ T hT u v hsol htrace
    have hintegrated :
        IntervalDomainL2AbsorbingIntegratedInequalityResult p T u :=
      IntervalDomainL2AbsorbingIntegratedInequality
        h.boundednessHyp.2.1 hsol habsorbing hregularity
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
        h.boundednessHyp hu₀ hT hsol htrace hhalf hL2
    have hbounded :
        IsPaper2BoundedBefore intervalDomain T u :=
      intervalDomainBoundedBefore_of_corollary21_and_proposition25
        hCor21 hProp25 hu₀ hT hsol htrace hbootstrap
    have hpoint : PointwiseBoundedBefore T u :=
      pointwiseBoundedBefore_of_boundedBefore_and_supNormControls hbounded
        (supNormControlsPointwiseBefore_of_classicalSolution hsol)
    exact IntervalDomainChemotacticDriftBound_of_LinfBound hsol hpoint
  l2SeedRegularity := h.l2SeedRegularity
  allLpBoundFromBootstrap := h.corollary21
  endpointBoundFromLp := h.proposition25

/-- A-priori bound from the integrated-step residual package. -/
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound

end IntervalDomainMassLpSmoothingIntegratedStepResiduals
```

## File 2: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

### Import/open changes

This file already imports:

```lean
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
```

Add a direct import if the generic package is not already visible transitively:

```lean
import ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

This should not create a cycle: `IntervalDomainMoserLadderAtoms` is PDE/Paper2-level and does not import Paper3 actual-linear statement assembly.

Existing opens are sufficient:

```lean
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

## Paper3 local definitions: keep vs replace

### Keep public Paper3 names

Keep these names stable:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts.to_aprioriActualLinearSmallFacts
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepFrontierData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepFrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
```

These are Paper3-facing API names and should remain as wrappers/adapters.

### Add a local adapter to the generic package

Inside:

```lean
namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

add:

```lean
/-- Convert the Paper3 actual-linear-small integrated-step residual surface to
the reusable integrated-step mass/Lp/smoothing residual package. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
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
```

Then replace the long local implementation of `to_routeResiduals` with:

```lean
/-- Build the generic mass/Lp/smoothing route residuals from the Paper3
actual-linear-small integrated-step residual surface. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

### Should local structures become aliases?

No.  Keep the Paper3 local residual structure, sectorial facts, and frontend structures.

Reason: the local residual package is Paper3-specific because it carries `closedEnergyTrace` and converts it to `l2SeedRegularity` using:

```lean
P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
```

The generic PDE package should stay generic and only require `l2SeedRegularity` directly, matching the existing reusable `IntervalDomainMassLpSmoothingMoserLadderResiduals` design.

### Should sectorial facts change?

No public name change is needed.  Existing code like:

```lean
massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0
```

can remain unchanged because `to_routeResiduals` now delegates to the generic package.

## Calls to ActualWiring consumers

Only the new generic package should call:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Paper3 local code should call:

```lean
(h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

rather than duplicating the route proof or directly calling the consumers.

## Honesty pitfalls

Do not construct or infer:

```lean
MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
RelativeMoserInterpolationBefore intervalDomain u T rho p0
```

from `Corollary_2_1`, `Proposition_2_5`, or the integrated-step route.  The generic package should not have fields or conclusions with those old atom types.

Do not add any theorem that produces:

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

The integrated step remains a supplied field.

Do not import Paper3 into `IntervalDomainMoserLadderAtoms.lean`.

## Build commands

Run target files first:

```bash
lake env lean ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
lake env lean ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

Then module builds:

```bash
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

Finally:

```bash
lake build ShenWork
```

## `#print axioms` targets

Reusable package:

```lean
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound
```

Paper3 adapter:

```lean
#print axioms ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_integratedStepResiduals
#print axioms ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
#print axioms ShenWork.Paper3.IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts.to_aprioriActualLinearSmallFacts
#print axioms ShenWork.Paper3.intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
#print axioms ShenWork.Paper3.intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
```

Expected profile: no `sorryAx`, no new custom axiom, and no theorem producing `IntegratedMoserFirstCrossingStep`.

## Minimal commit scope

One commit is enough:

1. add `IntervalDomainMassLpSmoothingIntegratedStepResiduals` and namespace methods to `PDE/IntervalDomainMoserLadderAtoms.lean`;
2. add `to_integratedStepResiduals` in the Paper3 local residual namespace;
3. replace the long Paper3-local `to_routeResiduals` proof body with:

```lean
(h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

Do not rename the higher Paper3 frontend names in this commit.
