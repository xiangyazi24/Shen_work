# Q2647 shen2: audit of integrated-Moser regularity producer path

Repo target: `xiangyazi24/Shen_work`, default branch `main`.

Scope: producer progress toward unconditional Paper2/Paper3 Moser headline routes **without editing**:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

Audited modules:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
ShenWork/PDE/P3MoserRegularityProducer.lean
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

## Bottom line

`IntegratedMoserFirstCrossingRegularity` is **partly but not fully wireable** from the existing classical-solution infrastructure.

What is already wired:

* `initialPowerBound` is purely algebraic via `intervalDomain_initialPowerBound`.
* energy nonnegativity is wired from `IsPaper2ClassicalSolution` via `intervalDomain_integratedMoserEnergyNonnegativity_of_classical`.
* `powerTimeIntegrable` is wired from **closed-time** energy continuity via `intervalDomain_powerTimeIntegrable_of_energyContinuous`.
* interior energy continuity on `(0,T)` is already proved from `IsPaper2ClassicalSolution` by `intervalDomain_energyContinuousOn_Ioo`.
* all fixed-window restriction plumbing from the regularity package into precrossing/window data is already present in `P3MoserIntegratedClosure`.

What is **not** yet wired from `IsPaper2ClassicalSolution` alone:

* `energyContinuous` on the closed set `Set.Icc 0 T`; the current theorem gives only `Set.Ioo 0 T`.
* `gradientTimeIntegrable` on `Set.uIcc 0 T`; no current declaration proves this from classical regularity.

So the honest next producer task is to add a small endpoint/gradient regularity producer layer, not to touch the high-excursion or threshold-plan files.

## Exact declarations to grep

### In `ShenWork/PDE/P3MoserEnergyContinuity.lean`

```text
intervalDomain_solution_jointContinuousOn
intervalDomain_power_jointContinuousOn
intervalDomain_power_bounded_on_slab
intervalDomain_energyContinuousOn_Ioo
```

Important status:

```lean
intervalDomain_energyContinuousOn_Ioo :
  IsPaper2ClassicalSolution intervalDomain params T u v →
  ContinuousOn
    (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
    (Ioo (0 : ℝ) T)
```

This is real progress, but it does **not** provide the `Set.Icc 0 T` continuity required by `IntegratedMoserFirstCrossingRegularity.energyContinuous`.

Also grep in `ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean`:

```text
intervalDomainPowerEnergy
intervalDomainPowerDeriv
intervalDomainPowerEnergy_hasDerivAt
intervalDomain_lp_timeLeibniz
```

Those are the engine behind the current interior continuity theorem.

### In `ShenWork/PDE/P3MoserRegularityProducer.lean`

```text
IntervalDomainIntegratedMoserRegularityFrontierData
IntervalDomainIntegratedMoserRegularityFrontierDataLite
intervalDomain_energyContinuous_of_regularityFrontierData
intervalDomain_initialPowerBound
intervalDomain_powerTimeIntegrable_of_energyContinuous
intervalDomain_powerTimeIntegrable_of_regularityFrontierData
intervalDomain_gradientTimeIntegrable_of_regularityFrontierData
intervalDomain_regularFrontierData_of_lite
intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierDataFact
intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
intervalDomain_regularity_and_nonnegativity_of_classical
intervalDomain_regularity_and_nonnegativity_of_lite_classical
intervalDomain_lowerAverageEpsilonData_of_classical
intervalDomain_lowerAverageEpsilonData_of_lite_classical
intervalDomain_firstCrossingStep_of_classical_and_frontiers
intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
```

The key existing reduced interface is:

```lean
structure IntervalDomainIntegratedMoserRegularityFrontierDataLite
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

This already omits the redundant `powerTimeIntegrable` field. Once `energyContinuous` and `gradientTimeIntegrable` are available, the file already expands them into full `IntegratedMoserFirstCrossingRegularity`.

### In `ShenWork/PDE/P3MoserIntegratedClosure.lean`

```text
IntegratedMoserFirstCrossingRegularity
integratedMoserEnergy
integratedMoserGradientEnergy
intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
Icc_subset_uIcc_zero_T_of_endpoint_memberships
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
intervalIntegrable_max_one_of_intervalIntegrable
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
IntegratedMoserEnergyNonnegativity
intervalDomain_integral_nonneg
intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
intervalDomain_integratedMoserEnergyNonnegativity_of_pointwise_nonneg
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
currentEnergy_Icc_bound_of_LpPowerBoundedBefore
integratedMoserPrecrossingIntervalData_of_regular_window
integratedMoser_windowUpperBoundData_of_precrossing
IntegratedMoserFirstCrossingLowerAverageEpsilonData
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
integratedMoserFirstCrossingStep_of_windowFrontier
integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
```

Important: the closure layer has already separated wiring from analytics. Once `IntegratedMoserFirstCrossingRegularity`, `IntegratedMoserEnergyNonnegativity`, dissipation, relative interpolation, and either lower/upper gap data or threshold-plan data are supplied, the step is a consumer theorem.

### In `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`

```text
IntervalDomainMassLpSmoothingIntegratedStepResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingWindowFrontierResiduals
IntervalDomainMassLpSmoothingWindowFrontierResiduals.to_integratedStepResiduals
IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals
IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.to_windowFrontierResiduals
IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.to_integratedStepResiduals
```

The integrated-step residual route is already available. A producer for regularity does not need to edit this file. Once the `integratedStep` field can be produced from classical solution plus honest PDE frontiers, this file can consume it through existing structures.

### In `ShenWork/PDE/P3MoserThresholdPlanProducer.lean` — grep only, do not edit

Even though this file should not be edited for this task, grep these declarations to understand the shortest existing consumer path:

```text
integratedMoserFirstCrossingStep_of_abstract_data
intervalDomain_gradient_integral_nonneg
intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

The interval-domain theorem already gives:

```lean
IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 →
IntegratedMoserEnergyNonnegativity intervalDomain u T p0 →
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 →
RelativeMoserInterpolationBefore intervalDomain u T rho p0 →
0 < rho →
0 ≤ p0 →
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

This means producer progress on `IntegratedMoserFirstCrossingRegularity` directly helps the unconditional route, without touching the high-excursion or threshold-plan files.

## Field-by-field status of `IntegratedMoserFirstCrossingRegularity`

Current target:

```lean
structure IntegratedMoserFirstCrossingRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  initialPowerBound :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        D.integral (fun x => (u 0 x) ^ p) ≤ C0
  powerTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

### `initialPowerBound` — already wiring

Current declaration:

```lean
intervalDomain_initialPowerBound
```

This is purely algebraic: take `max integral 0`.

### `powerTimeIntegrable` — already wiring once closed-time continuity exists

Current declaration:

```lean
intervalDomain_powerTimeIntegrable_of_energyContinuous
```

This derives `IntegrableOn ... (Set.uIcc 0 T)` from `ContinuousOn ... (Set.Icc 0 T)` and `0 ≤ T`.

### `energyContinuous` — partially wired

Current declaration:

```lean
intervalDomain_energyContinuousOn_Ioo
```

This gives only the interior open interval. It is not enough for the current regularity structure, which demands `Set.Icc 0 T`.

This is not merely a missing theorem name. The current `IsPaper2ClassicalSolution` API does not, by itself, relate the value `u 0` to the interior limit. The value `u 0` is unconstrained unless an `InitialTrace` or a closed-time solution interface is supplied. Similarly, the right endpoint `T` is not covered by the current joint-continuity theorem, which is on `(0,T) × [0,1]`.

So a producer from `IsPaper2ClassicalSolution` alone to closed-time energy continuity would be suspicious. A producer from `IsPaper2ClassicalSolution` plus endpoint-continuity data is honest.

### `gradientTimeIntegrable` — genuine analytic frontier

No current declaration proves:

```lean
∀ p, p0 ≤ p →
  IntegrableOn
    (fun t => intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (Set.uIcc (0 : ℝ) T) volume
```

from `IsPaper2ClassicalSolution`.

Interior classical regularity may help prove local-in-time integrability on compact subintervals `Icc a b ⊂ Ioo 0 T`, but the current full regularity field asks for `uIcc 0 T`. Controlling behavior near `0` and `T` is extra analytic information unless the API is weakened to only require interior windows.

## Minimal producer interface to attack next

The next source task should be in:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
ShenWork/PDE/P3MoserRegularityProducer.lean
```

Do **not** edit:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

### Step 1: endpoint-continuity glue in `P3MoserEnergyContinuity.lean`

Add a small endpoint data structure and a theorem that upgrades the existing `Ioo` theorem to `Icc`.

Code-shaped snippet:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Endpoint continuity data needed to upgrade the already-proved interior
energy continuity to the closed interval `[0,T]`.

This is honest: `IsPaper2ClassicalSolution` currently controls interior times,
while the closed regularity field also asks about the values at `0` and `T`. -/
structure IntervalDomainPowerEnergyEndpointContinuity
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) 0
  atRight :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) T

/-
Target theorem to prove next, using `intervalDomain_energyContinuousOn_Ioo` for
interior points and the two endpoint fields above for the boundary points:

theorem intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0) :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
-/

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
```

Implementation detail: the proof should split a point `t ∈ Set.Icc 0 T` into `t = 0`, `0 < t ∧ t < T`, or `t = T`. For the interior branch, use `intervalDomain_energyContinuousOn_Ioo hsol` and the fact that `Set.Ioo 0 T` is a neighborhood of an interior point. The exact Mathlib lemma names likely to test are:

```lean
#check ContinuousOn.continuousWithinAt
#check IsOpen.mem_nhds
#check continuousAt_iff_continuousWithinAt_univ
```

A robust proof can avoid fancy API by showing continuity within `Set.Icc 0 T` locally agrees with continuity within `Set.Ioo 0 T` at interior points.

### Step 2: classical-facing lite regularity producer in `P3MoserRegularityProducer.lean`

Once the closed energy continuity theorem exists, add a producer that uses it plus the already-existing gradient frontier.

Code-shaped snippet:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Minimal classical-solution-facing data still needed to produce the reduced
integrated-Moser regularity frontier.

The endpoint energy field is separated because current classical regularity is
interior in time.  The gradient time-integrability field is a genuine analytic
frontier. -/
structure IntervalDomainIntegratedMoserClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy :
    P3MoserEnergyContinuity.IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-
Target theorem:

theorem intervalDomain_regulariyLite_of_classicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0) :
    IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0 :=
  { energyContinuous :=
      P3MoserEnergyContinuity.intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
        hsol hdata.endpointEnergy
    gradientTimeIntegrable := hdata.gradientTimeIntegrable }
-/

/-- Once the lite data are produced, the existing producer immediately gives the
full `IntegratedMoserFirstCrossingRegularity`. -/
-- Target theorem:
-- theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData ...

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

The final theorem body can call the existing:

```lean
intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
```

so the only new proof work is the endpoint continuity glue.

### Step 3: optional direct consumer wrapper toward first crossing

This wrapper is useful but should be added only after Step 2 compiles. It does not edit threshold/high producer files; it consumes existing declarations.

```lean
/-- Producer-facing shortcut: classical solution plus endpoint/gradient regularity
and the honest PDE frontiers feed the existing first-crossing consumer. -/
-- theorem intervalDomain_firstCrossingStep_of_classicalRegularityData_and_frontiers
--     {params : CM2Params} {T rho p0 : ℝ}
--     {u v : ℝ → intervalDomain.Point → ℝ}
--     (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
--     (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
--     (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
--     (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
--     (hrho : 0 < rho)
--     (hp0_nonneg : 0 ≤ p0)
--     ... : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

There are two consumer choices:

1. Existing regularity producer route:
   ```lean
   intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
   ```
   This still asks for lower-average and epsilon-gap frontiers.

2. Existing threshold-plan route in `P3MoserThresholdPlanProducer.lean`:
   ```lean
   intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
   ```
   This asks for regularity, energy nonnegativity, dissipation, relative interpolation, `0 < rho`, and `0 ≤ p0`; interval-domain gradient integral nonnegativity is already discharged there.

Because the user asked not to edit threshold/high producer files, the safest next commit should stop at the regularity producer. A later wrapper can import and consume the threshold theorem if desired.

## Genuine analytic gaps vs wiring

### Wiring / already proved

```lean
intervalDomain_initialPowerBound
intervalDomain_powerTimeIntegrable_of_energyContinuous
intervalDomain_regularFrontierData_of_lite
intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
currentEnergy_Icc_bound_of_LpPowerBoundedBefore
integratedMoserPrecrossingIntervalData_of_regular_window
integratedMoser_windowUpperBoundData_of_precrossing
```

These are route plumbing. They should not be reproved.

### Partly wired but endpoint gap remains

```lean
intervalDomain_energyContinuousOn_Ioo
```

This is strong interior producer progress. The missing piece is upgrading to:

```lean
ContinuousOn ... (Set.Icc (0 : ℝ) T)
```

That upgrade needs endpoint continuity assumptions or a stronger closed-time classical-solution interface.

### Genuine analytic frontiers

```lean
gradientTimeIntegrable
IntegratedMoserDissipationDropBefore
RelativeMoserInterpolationBefore
```

These are not currently produced from `IsPaper2ClassicalSolution`. The threshold route also needs `0 < rho` and `0 ≤ p0`, but those are usually available from the bootstrap hypothesis or scalar assumptions.

For the high-excursion/window route, the genuine extra frontiers remain:

```lean
IntegratedMoserHighExcursionLowerAverageWindowFrontier
IntegratedMoserWindowUpperDataGapFrontier
IntegratedMoserWindowUpperGapEpsilonFrontier
```

Those should remain with Zinan-owned producer files if they concern high-excursion/threshold construction.

### Not true / do not claim

Do not claim:

```lean
IsPaper2ClassicalSolution intervalDomain params T u v →
IntegratedMoserFirstCrossingRegularity intervalDomain u T p0
```

with no extra assumptions. The endpoint values and gradient time-integrability are not available from the current API.

Do not claim:

```lean
intervalDomain_energyContinuousOn_Ioo → intervalDomain_energyContinuousOn_Icc
```

without endpoint continuity. The value `u 0` is not constrained by `IsPaper2ClassicalSolution` alone.

Do not claim gradient time-integrability from local interior classical regularity without handling possible endpoint behavior. Local-in-time continuity on compact interior slabs does not by itself give `IntegrableOn ... (Set.uIcc 0 T)`.

## Recommended next Lean task

The best next producer task is:

```text
File 1: ShenWork/PDE/P3MoserEnergyContinuity.lean
  Add endpoint-continuity data and the Ioo+endpoint -> Icc energy continuity theorem.

File 2: ShenWork/PDE/P3MoserRegularityProducer.lean
  Add IntervalDomainIntegratedMoserClassicalRegularityData and a producer to
  IntervalDomainIntegratedMoserRegularityFrontierDataLite / IntegratedMoserFirstCrossingRegularity.
```

Suggested names:

```text
IntervalDomainPowerEnergyEndpointContinuity
intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
IntervalDomainIntegratedMoserClassicalRegularityData
intervalDomain_regularityLite_of_classicalRegularityData
intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
intervalDomain_regularity_and_nonnegativity_of_classicalRegularityData
```

This reduces the regularity producer burden to the two honest frontiers that are actually missing:

```lean
endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
gradientTimeIntegrable : ∀ p, p0 ≤ p → IntegrableOn gradientEnergy (Set.uIcc 0 T) volume
```

Everything else in `IntegratedMoserFirstCrossingRegularity` is already wired.

## How this helps the headline routes

After this producer exists, an interval-domain Moser step can be supplied to existing route records without touching high/threshold files:

```text
classical solution
+ endpoint energy continuity
+ gradient time integrability
+ energy nonnegativity from classical solution
+ dissipation frontier
+ relative interpolation frontier
+ threshold/high-excursion consumer already in existing files
  ⟶ IntegratedMoserFirstCrossingStep
  ⟶ IntervalDomainMassLpSmoothingIntegratedStepResiduals.integratedStep
  ⟶ Corollary_2_1 / Proposition_2_5
  ⟶ Paper2/Paper3 Moser headline routes
```

The immediate producer progress is therefore to close the regularity package, not to refactor the Moser route or invent a new first-crossing theorem.
