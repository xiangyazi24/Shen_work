# Q2665 shen2: gradient-time-integrability residual audit

Repo target: `xiangyazi24/Shen_work`, Lean 4.

Question: can the remaining field

```lean
gradientTimeIntegrable :
  ∀ p, p0 ≤ p →
    IntegrableOn
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      (Set.uIcc (0 : ℝ) T) volume
```

be proved from `IsPaper2ClassicalSolution` plus already-present Moser energy/dissipation hypotheses, without adding axioms and without editing:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

## Short answer

No existing repository theorem currently proves this field from `IsPaper2ClassicalSolution` plus the existing Moser energy/dissipation interfaces.

There are useful nearby theorems, but they fall into three categories:

1. **Pointwise-in-space / pointwise-in-time regularity**, e.g. Moser-gradient algebraic identities.
2. **Pointwise differential/energy inequalities**, e.g. `LpBootstrapEnergyInequality` and `IntegratedMoserDissipationDropBefore`.
3. **Consumers that already require the missing `IntegrableOn` field**, e.g. `IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc` and the threshold-plan route.

None of these gives the measure-theoretic conclusion `IntegrableOn gradientEnergy (Set.uIcc 0 T) volume`.

The minimal honest next reduction is to expose a **closed-time gradient-energy continuity** producer interface and prove a small theorem:

```lean
ContinuousOn gradientEnergy (Set.Icc 0 T)
  → IntegrableOn gradientEnergy (Set.uIcc 0 T) volume
```

This belongs in `ShenWork/PDE/P3MoserRegularityProducer.lean`, not in high-excursion or threshold-plan files.

## Exact repository declarations to inspect

### `ShenWork/PDE/P3MoserRegularityProducer.lean`

Current relevant names:

```text
IntervalDomainIntegratedMoserRegularityFrontierData
IntervalDomainIntegratedMoserRegularityFrontierDataLite
IntervalDomainIntegratedMoserClassicalRegularityData
intervalDomain_gradientTimeIntegrable_of_regularityFrontierData
intervalDomain_regularFrontierData_of_lite
intervalDomain_regularityLite_of_classicalRegularityData
intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
```

The new classical-facing bundle is correctly shaped: it leaves `gradientTimeIntegrable` as a field rather than claiming it follows from `IsPaper2ClassicalSolution`.

### `ShenWork/PDE/P3MoserIntegratedClosure.lean`

Relevant names:

```text
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
intervalDomain_gradient_integral_nonneg
integratedMoserPrecrossingIntervalData_of_regular_window
integratedMoser_windowUpperBoundData_of_precrossing
```

Important distinction:

```lean
intervalDomain_gradient_integral_nonneg
```

only gives:

```lean
0 ≤ ∫ s in a..b, integratedMoserGradientEnergy intervalDomain u q s
```

It is not an `IntegrableOn` theorem. Meanwhile:

```lean
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
```

is a consumer of the regularity package, so it cannot produce the package.

### `ShenWork/PDE/P3MoserDissipationShape.lean`

Relevant names:

```text
IntegratedMoserDissipationDropBefore
integratedMoserDissipationDropBefore_of_integrated_energy
moser_step_of_energy_nonnegB_relative_interpolation
```

`IntegratedMoserDissipationDropBefore` contains inequalities involving interval integrals of the gradient energy:

```lean
D.integral (fun x => (u t2 x) ^ p) -
    D.integral (fun x => (u t1 x) ^ p) +
  2 * ∫ s in t1..t2,
    D.integral (fun x =>
      (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
  C * p * ∫ s in t1..t2,
    max 1 (D.integral (fun x => (u s x) ^ p))
```

This is a fixed-window inequality. It does not assert that the time profile is `IntegrableOn`. In Lean, an inequality about the value of `∫` is not an integrability certificate for the integrand.

The old nonnegative-`B` pointwise route:

```lean
moser_step_of_energy_nonnegB_relative_interpolation
```

can extract a pointwise bound for the gradient term when supplied with `LpBootstrapEnergyInequality`, nonnegative-`B` dissipation, relative interpolation, and an `LpPowerBoundedBefore` input. But it still does not prove `IntegrableOn` for the gradient-energy profile. To turn such a pointwise bound into `IntegrableOn`, one would still need measurability/a.e. measurability of the gradient-energy time profile plus integrability of the dominating higher-power profile.

### `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean`

Relevant names:

```text
intervalDomain_u_rpow_intervalIntegrable_of_regularity
intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
intervalDomainLpMoserGradientControl_of_regularity
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

These are important but do not close the residual.

`intervalDomain_moser_gradient_integral_eq_weighted_of_regularity` is a pointwise-in-time identity:

```lean
intervalDomain.integral
    (fun x =>
      (intervalDomain.gradNorm
        (fun y : intervalDomain.Point => (u t y) ^ (pExp / 2)) x) ^ 2) =
  (pExp / 2) ^ 2 *
    intervalDomainLpWeightedGradientDissipation pExp u t
```

It can identify the integrand at a fixed time, but it does not supply time integrability on `Set.uIcc 0 T`.

`intervalDomain_LpBootstrapEnergyInequality_of_regularity` produces the pointwise `LpBootstrapEnergyInequality` from classical regularity, cross-diffusion bootstrap, and the abstract bootstrap hypothesis. It does not produce an integrated-in-time regularity package.

### `ShenWork/PDE/P3MoserThresholdPlanProducer.lean` — inspect only, do not edit

Relevant names:

```text
integratedMoserFirstCrossingStep_of_abstract_data
intervalDomain_gradient_integral_nonneg
intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

This file confirms the gap: the main theorem consumes

```lean
hreg : IntegratedMoserFirstCrossingRegularity D u T p0
```

and then uses `hreg.gradientTimeIntegrable` later. It separately proves gradient-integral nonnegativity for intervalDomain. So the threshold-plan route is not a producer of the missing field; it is downstream of it.

## Why existing Moser energy/dissipation does not suffice

A tempting route is:

```text
LpBootstrapEnergyInequality
+ MoserDissipationDropBeforeNonnegB
+ RelativeMoserInterpolationBefore
+ LpPowerBoundedBefore
→ pointwise bound on gradient energy
→ IntegrableOn gradient energy
```

The first arrow exists in a limited form via `moser_step_of_energy_nonnegB_relative_interpolation`, but the second arrow is not currently available. It would need at least:

```lean
AEStronglyMeasurable
  (fun t => integratedMoserGradientEnergy intervalDomain u p t)
  (volume.restrict (Set.uIcc (0 : ℝ) T))
```

plus an integrable dominating function. The current pointwise energy and dissipation predicates do not carry that measurability/continuity information.

The integrated route has a similar limitation. `IntegratedMoserDissipationDropBefore` bounds interval integrals of the gradient profile, but it does not assert `IntervalIntegrable` or `IntegrableOn` of that profile. Since `∫` is total in Lean, a finite-looking inequality involving `∫` is not a proof that the integrand is integrable.

So there is no compile-safe theorem of the form:

```lean
IsPaper2ClassicalSolution intervalDomain params T u v →
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 →
...
  IntegrableOn gradientEnergy (Set.uIcc 0 T) volume
```

using only existing repository facts.

## Recommended next theorem

Add the following reducer in:

```text
ShenWork/PDE/P3MoserRegularityProducer.lean
```

Place it in the `/-! ### Gradient time integrability -/` section, immediately before or after:

```lean
intervalDomain_gradientTimeIntegrable_of_regularityFrontierData
```

This is the minimal honest reduction: it replaces the raw `IntegrableOn` residual by a more geometric closed-time continuity residual.

```lean
import ShenWork.PDE.P3MoserRegularityProducer

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

/-- Closed-time continuity of the Moser gradient energy implies the
`gradientTimeIntegrable` field needed by `IntegratedMoserFirstCrossingRegularity`.

This is a pure compact-interval integrability reducer.  It does not claim that
classical solutions already provide the closed-time continuity. -/
theorem intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.Icc (0 : ℝ) T)) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hIcc :
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.Icc (0 : ℝ) T) volume :=
    (hgrad p hp).integrableOn_Icc
  simpa [Set.uIcc_of_le hT] using hIcc

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

This proof is likely to compile because it is exactly the same pattern already used by:

```lean
intervalDomain_powerTimeIntegrable_of_energyContinuous
```

in the same file.

## Minimal residual package to expose

If you want a package rather than just a theorem, add this in the same file near `IntervalDomainIntegratedMoserClassicalRegularityData`:

```lean
/-- Classical-facing regularity data with the gradient residual stated as
closed-time continuity rather than raw time integrability. -/
structure IntervalDomainIntegratedMoserClassicalGradientContinuityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientEnergyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.Icc (0 : ℝ) T)

/-- Convert the closed-gradient-continuity package to the existing classical
regularity-data package. -/
theorem intervalDomain_classicalRegularityData_of_gradientEnergyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hdata :
      IntervalDomainIntegratedMoserClassicalGradientContinuityData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy := hdata.endpointEnergy
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
      hT hdata.gradientEnergyContinuous
```

Then the existing theorem

```lean
intervalDomain_regularityLite_of_classicalRegularityData
```

can consume the converted data unchanged.

## Why this is better than an “integrated energy inequality implies integrability” theorem right now

A theorem named something like:

```lean
gradientTimeIntegrable_of_integratedMoserDissipation
```

would be misleading with the current definitions. The integrated dissipation interface contains real interval integrals but not the `IntervalIntegrable`/`IntegrableOn` hypotheses that Lean needs to certify those integrals as integrability facts. It also does not provide the a.e. measurability of the gradient-energy time profile.

A genuinely honest energy-inequality-to-integrability package would have to include at least one of the following:

```lean
-- Option A: direct closed-time continuity of gradient energy
∀ p, p0 ≤ p → ContinuousOn gradientEnergy (Set.Icc 0 T)

-- Option B: measurable dominated bound
∀ p, p0 ≤ p →
  AEStronglyMeasurable gradientEnergy
    (volume.restrict (Set.uIcc (0 : ℝ) T)) ∧
  ∃ H, IntegrableOn H (Set.uIcc (0 : ℝ) T) volume ∧
    ∀ᵐ t ∂volume.restrict (Set.uIcc (0 : ℝ) T),
      ‖gradientEnergy t‖ ≤ H t
```

Option A is much smaller and repository-local because the existing `ContinuousOn.integrableOn_Icc` pattern already compiles in this file.

## What not to do

Do not use these as producers of the missing field:

```lean
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
intervalDomain_gradient_integral_nonneg
integratedMoserFirstCrossingStep_of_abstract_data
intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

They are either downstream consumers or nonnegativity statements.

Do not claim `IntegratedMoserDissipationDropBefore` implies `IntegrableOn` without adding measurability or continuity of the gradient-energy profile.

Do not edit:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

The clean next edit is a small producer reducer in `P3MoserRegularityProducer.lean`.
