# Q2462 shen2: follow-up ranking after integrated-step consumers and Paper3 direct route

Repo target: `xiangyazi24/Shen_work`.

Context assumed from the local verified patch:

1. `ShenWork/PDE/P3MoserIntegratedClosure.lean` has fixed-interval integrated-Moser time-integral bridge lemmas.
2. `ShenWork/PDE/P3MoserActualWiring.lean` has consumers from a supplied `IntegratedMoserFirstCrossingStep` to `Corollary_2_1` and `Proposition_2_5`.
3. Paper3 actual-linear-small has a direct integrated-step route filling `IntervalDomainMassLpSmoothingRouteResiduals` without deriving the old pointwise Moser atoms.

## Ranking

### 1. (C) Add Paper2 statement wrappers around integrated-step consumers — best immediate next commit

**Honest progress:** high routing progress, low analytic risk.  This exposes the integrated-step route at the Paper2 statement layer without claiming to produce the step.

**Blast radius:** low.  It should touch only:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

possibly only adding an import/open if the new namespace is not already visible through `P3MoserActualWiring`.

**Why first:** the current patch already added the real lower-level consumers.  The next best follow-up is to make that route available to the same Paper2 assembly layer that currently has actual-atom, raw-drop, mass-gradient, and terminal-endpoint wrappers.  It is a naming/API stabilization commit, not a new proof frontier.

### 2. (B) Genericize the Paper3-local `IntegratedStepResiduals` into `IntervalDomainMoserLadderAtoms`

**Honest progress:** medium-high.  It removes an ad hoc Paper3-local route and makes the integrated-step residual package reusable by Paper2/Paper3/Paper3 headline files.

**Blast radius:** medium.  It likely touches:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

and possibly the Paper3 file that currently introduced the local `IntegratedStepResiduals`.

**Why second:** this is valuable, but it is a refactor/commonization of a route that already works locally.  It is best done after (C), once the integrated-step consumer names and statement-layer route names are fixed.

### 3. (A) Implement the pre-crossing interval skeleton

**Honest progress:** medium and mathematically direct toward the hard first-crossing proof.  It gives fixed-interval/averaged estimates, not a pointwise step.

**Blast radius:** low-to-medium if kept isolated in:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

**Why not first:** it is closer to the eventual analytic proof, but it does not feed existing theorem wrappers immediately.  It also invites more design churn around regularity/integrability fields.  Do it after the route exposure/refactor work unless the immediate goal is analytic proof development rather than API stabilization.

### 4. (D) Produce `IntegratedMoserFirstCrossingStep`

**Honest progress:** highest if successful, but this is the real analytic theorem.

**Blast radius:** high.  It needs continuity/lower-average/existence-of-crossing machinery and careful constant management.

**Why last:** do not attempt this as the next small commit.  The current fixed-interval lemmas and pre-crossing skeleton should be in place first.  The final theorem should be attacked only after the local averaged contradiction ingredients are separated and compiled.

## Minimal next commit scope: option C

### File

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

### Import caveat

This file already imports:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

If the newly landed `P3MoserActualWiring` imports `P3MoserIntegratedClosure`, no new import is needed.  If Lean cannot see `IntegratedMoserFirstCrossingStep`, add:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

near the existing `P3MoserActualWiring` import.  This should not create a cycle: `P3MoserIntegratedClosure` imports `P3MoserDissipationShape`, while the statement assembly is downstream of both.

Add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

near the existing `open` block if the field type is otherwise too verbose.

### Proposed names

Use these exact statement-layer names unless the landed ActualWiring consumer names already force a small RHS rename:

```lean
IntervalDomainPaper2Prop25IntegratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
```

Add Fact wrappers only if the file style around the nearby actual-atom routes needs them immediately; otherwise keep the first commit small.

### Code skeleton

Assuming the new ActualWiring consumers are named:

```lean
intervalDomain_allLpBoundFromBootstrap_of_integratedStep
intervalDomain_endpointBoundFromLp_of_integratedStep
```

then the Paper2 statement wrappers should look like this:

```lean
/-- Integrated-step frontier for interval-domain Proposition 2.5 / Corollary 2.1.

This is strictly weaker than producing the step.  It only exposes the route once
`IntegratedMoserFirstCrossingStep` is supplied by some later analytic argument. -/
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

/-- Integrated-step route to interval-domain Corollary 2.1. -/
theorem intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_integratedStep
    hData.integratedStep

/-- Integrated-step route to interval-domain Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_integratedStep
    hData.integratedStep hData.quantitativeEndpoint

/-- Integrated-step route to both Tier-1 Moser outputs. -/
theorem
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData p hData,
    intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData p hData⟩

/-- Section-2 targets from thin frontiers and an integrated-step Proposition 2.5 route. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hStep : IntervalDomainPaper2Prop25IntegratedStepFrontierData p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    p hThin
    (intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
      p hStep)
```

If the actual landed consumer names are instead longer, for example:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step
intervalDomain_endpointBoundFromLp_of_actual_integrated_step
```

then only the RHS names need adjustment; keep the statement-layer names above.

### Fact wrappers if desired

If you want exact parity with nearby wrappers, add:

```lean
theorem intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25IntegratedStepFrontierData p)] :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData p hData.out

theorem intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25IntegratedStepFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData p hData.out

theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierDataFact
    (p : CM2Params)
    [hThin : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)]
    [hStep : Fact (IntervalDomainPaper2Prop25IntegratedStepFrontierData p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
    p hThin.out hStep.out
```

### Checks

```bash
lake env lean ShenWork/Paper2/IntervalDomainStatementAssembly.lean
lake build ShenWork.Paper2.IntervalDomainStatementAssembly
```

Suggested `#print axioms` targets:

```lean
#print axioms ShenWork.Paper2.intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
#print axioms ShenWork.Paper2.intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
#print axioms ShenWork.Paper2.intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
```

Expected profile: same as nearby statement wrappers; no `sorryAx`, no new analytic axioms.

## Option B follow-up after C: common integrated-step ladder residuals

Once the statement-layer route names are stable, genericize the Paper3-local integrated residuals into:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

### Import caveat

This file currently imports `ShenWork.PDE.P3MoserActualWiring`.  If `P3MoserActualWiring` already imports `P3MoserIntegratedClosure`, the type may already be visible through the import chain.  Prefer adding the direct import anyway for clarity:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

No cycle should result if `P3MoserIntegratedClosure` remains below `P3MoserActualWiring` and does not import ladder atoms.

Add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

### Proposed names

```lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
```

### Shape

The common residual should mirror the existing `IntervalDomainMassLpSmoothingMoserLadderResiduals`, but replace pointwise Moser atoms by a supplied step:

```lean
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
```

Then copy the existing `.to_routeResiduals` proof from `IntervalDomainMassLpSmoothingMoserLadderResiduals`, replacing:

```lean
h.corollary21
h.proposition25
```

by the integrated-step versions.

Do not in the same commit delete the Paper3-local route unless the replacement is a tiny one-line change.  Safer two-step sequence:

1. add common residuals + build;
2. switch Paper3 local route to use common residuals + build.

## Option A later: pre-crossing interval skeleton

This remains a good analytic-direction follow-up, but it should be isolated in:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Candidate names from the prior audit remain appropriate:

```lean
IntegratedMoserPrecrossingIntervalData
IntegratedMoserPrecrossingIntervalData.maxOne_timeIntegral_le
integratedMoser_gradient_timeIntegral_le_of_precrossing_interval
integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
integratedMoser_higherPower_timeAverage_le_of_precrossing_interval
```

Keep outputs as time-integral or averaged bounds only.  Do not output `LpPowerBoundedBefore`.

## Option D later: produce `IntegratedMoserFirstCrossingStep`

This is the hard theorem and should wait until A’s pre-crossing/averaged-bound scaffolding is compiled and tested.  It must use `IntegratedMoserFirstCrossingRegularity` to turn averaged control into pointwise control by an actual first-crossing/continuity contradiction.

Do not write a theorem of this shape until the continuity/lower-average lemma is explicit:

```lean
theorem integratedMoserFirstCrossingStep_of_integrated_dissipation_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hT : 0 < T)
    (hrho : 0 < rho)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0
```

## Final recommendation

Next commit: **C only**.

Keep it to `IntervalDomainStatementAssembly.lean`, add `IntervalDomainPaper2Prop25IntegratedStepFrontierData` plus Proposition 2.5 / Corollary 2.1 / thin-section wrappers.  This gives an externally usable Paper2 integrated-step route with minimal blast radius and no new analytic claim.

Then do **B** as a refactor/commonization commit.  After those API routes are stable, return to **A** and finally **D**.
