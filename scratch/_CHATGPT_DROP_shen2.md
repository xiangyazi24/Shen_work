# Q2465 shen2: Paper2 integrated-step statement wrapper audit

Repo target: `xiangyazi24/Shen_work`, after commit `5b83ceab`.

Redispatch note: this overwrites the scratch drop for the repeated Q2465 request with the same compile-oriented guidance, grounded in the landed consumer names.

## Source facts checked

The landed `ShenWork/PDE/P3MoserActualWiring.lean` consumers are exactly:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Their relevant arguments are:

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

At `5b83ceab`, `P3MoserActualWiring` imports:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

So no new import is strictly required in `IntervalDomainStatementAssembly.lean`.  Adding a direct import is still harmless and clearer:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

place it next to `P3MoserActualWiring` if Lean does not resolve `IntegratedMoserFirstCrossingStep` transitively.

## Open caveat

To use `IntegratedMoserFirstCrossingStep` unqualified, add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

near the existing open block:

```lean
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Without that open, use the fully qualified type:

```lean
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserFirstCrossingStep
```

## Exact placement

Insert the new block after the existing raw-drop terminal-endpoint mass-gradient Corollary 2.1 Fact wrapper:

```lean
intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierDataFact
```

and before:

```lean
/-- Section-2 target wrapper from the thinner branch data, with Proposition
2.4 supplied by the interval-domain mass proof and Proposition 2.5 supplied by
the current theorem-level route. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
```

That placement matches the existing file organization: all Proposition 2.5 / Corollary 2.1 route wrappers first, then the section-2 thin bootstrap wrappers.

The existing theorem to reuse for the thin wrapper is:

```lean
intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
```

It already takes a produced `Proposition_2_5 intervalDomain p`, so the integrated-step thin wrapper should call it with:

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

## Fact wrappers

Nearby pattern uses Fact wrappers for single-output wrappers such as:

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierDataFact
intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierDataFact
intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierDataFact
```

So include Fact wrappers for:

```lean
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierDataFact
intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierDataFact
intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierDataFact
```

Do not add a Fact wrapper for the pair theorem; the nearby actual-atom pair theorem does not have one.

## Naming notes

Recommended names:

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

These match nearby naming style:

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
