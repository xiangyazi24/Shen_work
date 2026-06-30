# Q2479 shen2: genericizing the Paper3-local integrated-step route

Repo target: `xiangyazi24/Shen_work`, after commit `5b83ceab`.

This is the **genericization** plan only.  It is not a Paper2 statement-wrapper audit.

## Goal

Move the reusable part of the Paper3-local direct integrated-step route into:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Then make:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

consume the generic package.  The patch must preserve the current honest design:

* consume a supplied `IntegratedMoserFirstCrossingStep`;
* consume the existing quantitative endpoint/root-tower field;
* produce `Corollary_2_1`, `Proposition_2_5`, and then `IntervalDomainMassLpSmoothingRouteResiduals` directly;
* do **not** derive `MoserDissipationDropBeforeNonnegB`;
* do **not** derive `RelativeMoserInterpolationBefore`;
* do **not** produce `IntegratedMoserFirstCrossingStep`.

## File 1: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`

### Import/open changes

Current imports already include:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

At `5b83ceab`, `P3MoserActualWiring` imports `P3MoserIntegratedClosure`, but add a direct import for robustness and readability:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

Recommended import header:

```lean
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainVSliceBounds
```

Current opens include:

```lean
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.MinPersistenceAtoms
open Filter
```

Add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

so `IntegratedMoserFirstCrossingStep` is available unqualified.

### Placement

Insert the generic integrated-step package immediately after the existing block:

```lean
namespace IntervalDomainMassLpSmoothingMoserLadderResiduals
...
end IntervalDomainMassLpSmoothingMoserLadderResiduals
```

and before:

```lean
end ShenWork.IntervalDomainExistence
```

This keeps all reusable mass/Lp/smoothing residual packages in the same PDE-level file.

### Generic names

Use generic names, not Paper3-local actual-linear names:

```lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound
```

These parallel the existing reusable package:

```lean
IntervalDomainMassLpSmoothingMoserLadderResiduals
```

### Code skeleton

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

It likely reaches `IntervalDomainMoserLadderAtoms` transitively through Paper3 imports, but add a direct import if Lean cannot see the new generic package:

```lean
import ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

This should not create a cycle because `IntervalDomainMoserLadderAtoms` is PDE/Paper2-level and does not import this Paper3 file.

Current opens already include:

```lean
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

No new open is required for the generic package if `open ShenWork.IntervalDomainExistence` remains.

## Paper3 local definitions: what to keep vs replace

### Keep public Paper3 names

Keep these Paper3-facing names stable:

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

Reason: these are Paper3-specific API names that encode actual-linear-small hypotheses and are likely referenced downstream.

### Replace only the implementation of the local route residual conversion

Add a local adapter:

```lean
namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals

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

Then replace the long local `to_routeResiduals` body by:

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

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

### Should local residual structure become an alias?

For this commit, **do not replace the local Paper3 residual structure by an alias**.  Keep it as-is.

Reason: the local structure has a Paper3-specific `closedEnergyTrace` field and parameter conversion `hχ0 : 0 < p.χ₀`, while the generic package expects `l2SeedRegularity` and `chi_nonneg`.  Making the local structure an alias would either lose the closed-energy convenience or force more imports/fields into the generic PDE file.  The minimal compile-safe refactor is a local adapter, not a type alias.

### Should sectorial facts become aliases?

No.  Keep:

```lean
IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
```

and its public method:

```lean
to_aprioriActualLinearSmallFacts
```

unchanged in name.  Its implementation can remain:

```lean
massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0
```

because the local `to_routeResiduals` now delegates to the generic package.

If you want a clearer intermediate helper, you can add one, but it is optional:

```lean
def to_integratedStepRouteResiduals
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.massLpSmoothing.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

This optional helper is not needed for minimal scope.

## Calls to ActualWiring consumers

Only the generic package should call these directly:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Specifically:

```lean
theorem corollary21 ... :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    h.integratedStep
```

and:

```lean
theorem proposition25 ... :=
  intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    h.integratedStep h.quantitativeEndpoint
```

After this refactor, the Paper3 local `to_routeResiduals` should no longer call those consumers directly; it should call:

```lean
(h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

## Pitfalls

1. **Do not derive old atoms.**  The generic package should never try to construct:

```lean
MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
RelativeMoserInterpolationBefore intervalDomain u T rho p0
```

from `Corollary_2_1` or `Proposition_2_5`.  The route is deliberately integrated-step based.

2. **Do not produce the integrated step.**  The field remains:

```lean
integratedStep : ... → IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

No theorem in this patch should have conclusion `IntegratedMoserFirstCrossingStep ...` unless it is just projecting an existing field.

3. **Do not move closed-energy trace data into the generic PDE package in this commit.**  The generic package should use `l2SeedRegularity`, matching the existing reusable `IntervalDomainMassLpSmoothingMoserLadderResiduals`.  Paper3 can keep converting `closedEnergyTrace` to `l2SeedRegularity` locally using:

```lean
P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
```

4. **Do not rename Paper3 public frontiers.**  Keep the local Paper3 actual-linear-small frontend names stable.  The patch is an internal factoring of the reusable residual route, not a public Paper3 API rename.

5. **Avoid import cycles.**  `IntervalDomainMoserLadderAtoms.lean` may import `P3MoserIntegratedClosure`, but `P3MoserIntegratedClosure` must not import `IntervalDomainMoserLadderAtoms`.  Do not import any Paper3 files into `IntervalDomainMoserLadderAtoms.lean`.

## Build commands

Run the target files first:

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

Expected profile: same as existing route wrappers; no `sorryAx`, no new custom axiom, and no theorem producing `IntegratedMoserFirstCrossingStep`.  The step remains a supplied field.

## Minimal commit scope

One commit is fine:

1. add `IntervalDomainMassLpSmoothingIntegratedStepResiduals` and namespace methods to `PDE/IntervalDomainMoserLadderAtoms.lean`;
2. add `to_integratedStepResiduals` to the Paper3 local residual namespace;
3. replace the local long `to_routeResiduals` proof body with:

```lean
(h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

Do not also refactor/rename the higher Paper3 frontend names in this commit.
