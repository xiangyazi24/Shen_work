# Q2471 shen2: genericizing the Paper3-local integrated-step route

Repo target: `xiangyazi24/Shen_work`, base local commit before pending Paper2 wrapper: `5b83ceab`.

## Source-grounded orientation

At `5b83ceab`, `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` already contains the reusable non-integrated Moser-ladder residual package:

```lean
IntervalDomainMassLpSmoothingMoserLadderResiduals
IntervalDomainMassLpSmoothingMoserLadderResiduals.corollary21
IntervalDomainMassLpSmoothingMoserLadderResiduals.proposition25
IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingMoserLadderResiduals.aprioriBound
```

This package carries `a_pos`, `chi_nonneg`, `boundednessHyp`, `l2SeedRegularity`, old pointwise Moser atoms, and the quantitative endpoint.  Its `to_routeResiduals` proof reconstructs `IntervalDomainMassLpSmoothingRouteResiduals` by first obtaining `Corollary_2_1` and `Proposition_2_5`, then using the L² seed route to get boundedness and hence the chemotactic drift bound.

At `5b83ceab`, `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` has a Paper3-local integrated-step route:

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

The local residual proof uses the landed consumers:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

and deliberately fills `IntervalDomainMassLpSmoothingRouteResiduals` directly.  It must not derive old pointwise atoms such as:

```lean
MoserDissipationDropBeforeNonnegB
RelativeMoserInterpolationBefore
```

from `Corollary_2_1`.

## Recommended commit shape

Make this a two-file refactor commit:

1. Add a reusable integrated-step residual package to:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

2. Change the Paper3 local integrated-step route in:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

to consume that reusable package.

Do not change the analytic frontier.  Do not produce `IntegratedMoserFirstCrossingStep`.  Do not convert integrated-step data into old Moser atoms.

## File 1: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`

### Import/open changes

Current imports at `5b83ceab` are:

```lean
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.Paper2.IntervalDomainVSliceBounds
```

`P3MoserActualWiring` already imports `P3MoserIntegratedClosure` at `5b83ceab`, so the integrated-step type is transitively available.  For clarity and cycle robustness, I recommend adding a direct import:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

near `P3MoserActualWiring`.  There should be no import cycle: `P3MoserIntegratedClosure` imports the lower Moser closure/dissipation files and does not import `IntervalDomainMoserLadderAtoms`.

Current opens include:

```lean
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
```

Add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

so `IntegratedMoserFirstCrossingStep` can be written unqualified.

### Placement

Place the new package immediately after the existing namespace block:

```lean
end IntervalDomainMassLpSmoothingMoserLadderResiduals
```

and before the final:

```lean
end ShenWork.IntervalDomainExistence
```

This keeps it next to the existing reusable Moser-ladder residuals and avoids mixing it into Paper3-specific actual-linear structures.

### Suggested names

Use generic names, not Paper3/actual-linear names:

```lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound
```

These parallel the existing:

```lean
IntervalDomainMassLpSmoothingMoserLadderResiduals
```

but the new package carries a supplied integrated step instead of old pointwise Moser atoms.

### Compile-oriented code

```lean
/-- Lower-level inputs that replace the old pointwise Moser-ladder route fields
by a supplied integrated first-crossing step.

This package is intentionally route-level: it consumes
`IntegratedMoserFirstCrossingStep` directly via `P3MoserActualWiring` and does
not derive old pointwise Moser atoms such as
`MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore`. -/
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

### If you want a closed-energy convenience adapter in this generic file

The Paper3-local integrated route currently combines closed-energy trace data with integrated step data.  If you want to move that part too, add a second generic structure, but this is optional and increases blast radius because it requires importing or exposing `P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData`.

For the smallest genericization, do **not** move the closed-energy adapter.  Keep it Paper3-local and construct `l2SeedRegularity` before calling the generic residual package.

## File 2: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

### Import/open changes

This file already imports:

```lean
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
```

It also imports `ShenWork.Paper3.IntervalDomainMoserLadderHeadline`, which may already import `IntervalDomainMoserLadderAtoms`, but for clarity add a direct import if needed:

```lean
import ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

This should not create a cycle: `IntervalDomainMoserLadderAtoms` is PDE/Paper2-level and does not import Paper3 actual-linear statement assembly.

Current opens already include:

```lean
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

These are enough to see the generic residual package and integrated-step type.

### Adapt the Paper3-local residual package

Keep the local Paper3-specific name for compatibility:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

but make its conversion target the new reusable package first.

Add a new conversion:

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

Then replace the body of the existing local `to_routeResiduals` by a one-liner:

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

This keeps the Paper3 local public API stable while removing the duplicated long route proof from Paper3.

### Adapt sectorial facts

The existing Paper3 local facts conversion can remain unchanged if it calls `to_routeResiduals`:

```lean
massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0
```

No RHS change is needed after rewriting `to_routeResiduals` as above.

If you prefer exposing the reusable package one level higher, add an optional helper:

```lean
def IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts.to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing :=
    (h.massLpSmoothing.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

But this is not necessary; the current `to_aprioriActualLinearSmallFacts` can keep its name and one-line implementation.

## Pitfalls

1. **Do not derive old Moser atoms.**  The generic package should call only:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

It should not mention:

```lean
MoserDissipationDropBeforeNonnegB
RelativeMoserInterpolationBefore
```

except in nearby older packages.

2. **Do not move Paper3 parameter hypotheses into the generic package.**  The reusable residual takes `a_pos : 0 < p.a` and `chi_nonneg : 0 ≤ p.χ₀` directly.  The Paper3 actual-linear adapter converts `hχ0 : 0 < p.χ₀` by `le_of_lt hχ0`.

3. **Avoid importing Paper3 into `IntervalDomainMoserLadderAtoms`.**  The generic file should stay PDE/Paper2-level.  If you move closed-energy trace conversion into the generic file, make sure the source of `ClosedEnergyIdentityTraceData` is not Paper3-specific.  The safest small commit leaves closed-energy conversion in Paper3.

4. **Keep public Paper3 names stable.**  Downstream code may already use names such as:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData
```

Do not rename them in this commit.  Only change their internals to pass through the generic residual package.

5. **Use direct imports for clarity if Lean resolution becomes fragile.**  In `IntervalDomainMoserLadderAtoms.lean`, add both:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

and:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This avoids relying on transitive imports.

## Minimal build commands

Run these first:

```bash
lake env lean ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
lake env lean ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

Then:

```bash
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
lake build ShenWork
```

## Suggested `#print axioms` targets

For the reusable package:

```lean
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
#print axioms ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound
```

For the Paper3 adapter:

```lean
#print axioms ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_integratedStepResiduals
#print axioms ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
#print axioms ShenWork.Paper3.IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts.to_aprioriActualLinearSmallFacts
#print axioms ShenWork.Paper3.intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
#print axioms ShenWork.Paper3.intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
```

Expected profile: same as the existing route wrappers.  There should be no `sorryAx`, no new custom axiom, and no theorem that produces `IntegratedMoserFirstCrossingStep`.  The step remains an explicit field.

## Recommended commit scope

One small commit:

1. Add `IntervalDomainMassLpSmoothingIntegratedStepResiduals` and namespace methods to `PDE/IntervalDomainMoserLadderAtoms.lean`.
2. Add `to_integratedStepResiduals` in `Paper3/IntervalDomainActualLinearStatementAssembly.lean`.
3. Replace the long local `to_routeResiduals` proof body with:

```lean
(h.to_integratedStepResiduals ha hχ0).to_routeResiduals
```

Do not refactor the higher Paper3 frontend names in the same commit unless the changes are only one-line RHS updates forced by the conversion.
