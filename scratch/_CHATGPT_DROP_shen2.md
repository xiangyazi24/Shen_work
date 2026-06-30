# Q2465 shen2: Paper2 integrated-step statement wrapper audit

Repo target: `xiangyazi24/Shen_work`, after commit `5b83ceab`.

## Source facts checked

The landed `ShenWork/PDE/P3MoserActualWiring.lean` consumers are exactly:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

with signatures:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    {params : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params
```

and

```lean
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    {params : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Proposition_2_5 intervalDomain params
```

`IntervalDomainStatementAssembly.lean` already imports:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

and at `5b83ceab`, `P3MoserActualWiring` imports:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

So no direct new import is strictly necessary in `IntervalDomainStatementAssembly.lean`.  For readability and robustness, either add a direct import

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

near `P3MoserActualWiring`, or rely on the transitive import.  There is no cycle risk if adding the direct import, because `P3MoserIntegratedClosure` is below `P3MoserActualWiring` and does not import statement assembly.

## Open caveat

To use `IntegratedMoserFirstCrossingStep` unqualified in the new structure, add near the existing open block:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Current block:

```lean
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
```

Recommended block:

```lean
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Alternatively, keep no new `open` and write the type fully qualified:

```lean
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserFirstCrossingStep
```

The open line is cleaner and consistent with downstream uses of imported names.

## Exact placement

Minimal-diff placement: insert one contiguous block after the raw-drop terminal-endpoint mass-gradient Corollary 2.1 Fact wrapper and before the comment:

```lean
/-- Section-2 target wrapper from the thinner branch data, with Proposition
2.4 supplied by the interval-domain mass proof and Proposition 2.5 supplied by
the current theorem-level route. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
```

This is the transition point after all current Prop. 2.5 / Corollary 2.1 actual-atom wrappers and before the section-2 thin bootstrap wrappers.  It avoids threading the new route into multiple earlier clusters while preserving the file’s organization.

The existing thin wrapper to reuse is:

```lean
intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
```

It takes a `Proposition_2_5 intervalDomain p`, so the integrated-step thin wrapper should simply feed it

```lean
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData p hStep
```

## Minimal compile-safe code

```lean
/-- Integrated-step frontier for interval-domain Proposition 2.5 and Corollary 2.1.

This route consumes a supplied `IntegratedMoserFirstCrossingStep`.  It does not
produce that step from integrated dissipation/regularity; that remains the hard
analytic frontier. -/
structure IntervalDomainPaper2Prop25IntegratedStepFrontierData
    (p : CM2Params) : Prop where
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
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

/-- Integrated-step frontier produces interval-domain Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    hData.integratedStep
    hData.quantitativeEndpoint

/-- Instance-facing integrated-step Proposition 2.5 wrapper. -/
theorem intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25IntegratedStepFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
    p hData.out

/-- Integrated-step frontier produces interval-domain Corollary 2.1. -/
theorem intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    hData.integratedStep

/-- Instance-facing integrated-step Corollary 2.1 wrapper. -/
theorem intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25IntegratedStepFrontierData p)] :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
    p hData.out

/-- Integrated-step frontier produces both Tier-1 Moser outputs. -/
theorem
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData p hData,
    intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData p hData⟩

/-- Section-2 targets from thin frontiers and the integrated-step Proposition
2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hStep : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    p hThin
    (intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
      p hStep)

/-- Instance-facing section-2 wrapper from thin frontiers and the integrated-step
Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierDataFact
    (p : CM2Params)
    [hThin : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)]
    [hStep : Fact (IntervalDomainPaper2Prop25IntegratedStepFrontierData p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
    p hThin.out hStep.out
```

## Why Fact wrappers are included

Nearby patterns include Fact wrappers for:

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierDataFact
intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierDataFact
intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierDataFact
```

So including Fact wrappers for the individual Proposition/Corollary and thin-bootstrap target is consistent.  I would **not** add a Fact wrapper for the pair theorem, because the nearby pair theorem for actual atoms has no Fact wrapper.

## Naming notes

Recommended new names:

```lean
IntervalDomainPaper2Prop25IntegratedStepFrontierData
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierDataFact
intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierDataFact
intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierDataFact
```

These match existing naming style:

```lean
IntervalDomainPaper2Prop25ActualAtomFrontierData
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData
```

## Checks

Run:

```bash
lake env lean ShenWork/Paper2/IntervalDomainStatementAssembly.lean
lake build ShenWork.Paper2.IntervalDomainStatementAssembly
```

Suggested `#print axioms` targets:

```lean
#print axioms ShenWork.Paper2.intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
#print axioms ShenWork.Paper2.intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
#print axioms ShenWork.Paper2.intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
#print axioms ShenWork.Paper2.intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
```

Expected profile: same as nearby statement wrappers; no `sorryAx` and no new analytic axioms.  The hard analytic atom remains the supplied `IntegratedMoserFirstCrossingStep` field.
