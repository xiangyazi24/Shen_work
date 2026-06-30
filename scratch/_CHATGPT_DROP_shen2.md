# Q2652 shen2: audit of the classical-facing Moser regularity bundle

Repo target: `xiangyazi24/Shen_work`, default branch `main`.

Scope: Paper3/Paper2 integrated-Moser regularity producer audit. Do **not** edit:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

User context says Codex just added a bundle like:

```lean
structure IntervalDomainIntegratedMoserClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

I could not see that exact structure name in the tracked `main` file exposed by the connector, but the surrounding declarations are visible. This audit treats the added structure as local/pending and checks whether its two fields are already derivable from tracked APIs.

## Verdict

Both fields are honest residuals. I found no existing theorem that should simply be wired to derive either field from only:

```lean
IsPaper2ClassicalSolution intervalDomain params T u v
```

The closest current theorem is interior only:

```lean
ShenWork/PDE/P3MoserEnergyContinuity.lean
  intervalDomain_energyContinuousOn_Ioo
```

It gives:

```lean
ContinuousOn
  (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
  (Set.Ioo (0 : ℝ) T)
```

not continuity on `Set.Icc 0 T`. The current `IsPaper2ClassicalSolution` regularity/PDE/positivity hypotheses are all interior-time facing (`0 < t`, `t < T`). They do not constrain `u 0` or `u T` enough to force closed-endpoint energy continuity.

For the gradient field, the closest current theorem is:

```lean
ShenWork/PDE/P3MoserIntegratedClosure.lean
  intervalDomain_gradient_integral_nonneg
```

but that is only nonnegativity of interval integrals of the gradient energy. It is not `IntegrableOn ... (Set.uIcc 0 T) volume`.

## Grep targets

Inspect these before attempting any rewrite.

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
  intervalDomain_solution_jointContinuousOn
  intervalDomain_power_jointContinuousOn
  intervalDomain_power_bounded_on_slab
  intervalDomain_energyContinuousOn_Ioo
```

```text
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
  intervalDomainPowerEnergy
  intervalDomainPowerDeriv
  intervalDomainPowerEnergy_hasDerivAt
  intervalDomain_lp_timeLeibniz
```

```text
ShenWork/PDE/P3MoserRegularityProducer.lean
  IntervalDomainIntegratedMoserRegularityFrontierData
  IntervalDomainIntegratedMoserRegularityFrontierDataLite
  intervalDomain_initialPowerBound
  intervalDomain_powerTimeIntegrable_of_energyContinuous
  intervalDomain_regularFrontierData_of_lite
  intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
  intervalDomain_regularity_and_nonnegativity_of_lite_classical
  intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
```

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
  IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
  IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
  intervalDomain_gradient_integral_nonneg
  integratedMoserPrecrossingIntervalData_of_regular_window
  integratedMoser_windowUpperBoundData_of_precrossing
```

```text
ShenWork/PDE/P3MoserLemmas.lean
  ClosedEnergyIdentityTraceData.energyContinuous
  closedEnergyTrace_to_l2SeedRegularityFrontier
  relativeMoserInterpolationBefore_of_massGradient
```

`ClosedEnergyIdentityTraceData.energyContinuous` is useful but only for the L² seed energy under a separate closed energy identity. It does not discharge all-exponent Moser power-energy endpoint continuity.

## Why the residuals are honest

`endpointEnergy` is honest because `intervalDomain_energyContinuousOn_Ioo` proves only interior continuity. An abstract solution satisfying `IsPaper2ClassicalSolution ... T u v` can have endpoint slices not controlled by the interior regularity statement, so closed-time `Icc` continuity cannot be inferred without extra endpoint data or a longer/global solution route.

`gradientTimeIntegrable` is honest because all tracked gradient-energy declarations either consume the regularity package, prove nonnegativity, or use the gradient energy in interpolation estimates. None prove integrability of

```lean
fun t => intervalDomain.integral (fun x =>
  (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)
```

on `Set.uIcc 0 T` from classical regularity alone. Interior regularity can support local compact-subinterval arguments, but the full field includes possible endpoint behavior.

## Recommended next theorem

The smallest useful producer reduction is to discharge the **right endpoint** part of `endpointEnergy` from a global classical solution. This keeps the left endpoint as an explicit residual and uses the existing interior theorem on the longer horizon `T + 1`.

Target file:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
```

Code-shaped target:

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

/-- Produce endpoint power-energy continuity from a left-endpoint residual and a
global classical solution.  The right endpoint `T` is an interior time for the
longer horizon `T + 1`, so it follows from `intervalDomain_energyContinuousOn_Ioo`. -/
theorem intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero :
      ∀ p, p0 ≤ p →
        ContinuousWithinAt
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T) 0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0 := by
  refine ⟨hzero, ?_⟩
  intro p hp
  have hTplus : 0 < T + 1 := by linarith
  have hsolLong :
      IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus
  have hIoo :
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Ioo (0 : ℝ) (T + 1)) :=
    intervalDomain_energyContinuousOn_Ioo (p := p) hsolLong
  have hTmem : T ∈ Set.Ioo (0 : ℝ) (T + 1) := by
    exact ⟨hT, by linarith⟩
  have hcontAt :
      ContinuousAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) T :=
    hIoo.continuousAt (isOpen_Ioo.mem_nhds hTmem)
  exact hcontAt.continuousWithinAt

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
```

If only method syntax fails, test these names:

```lean
#check ContinuousOn.continuousAt
#check isOpen_Ioo.mem_nhds
#check ContinuousAt.continuousWithinAt
#check IsPaper2GlobalClassicalSolution.classical
```

This theorem is a real reduction: after it lands, `endpointEnergy` for global-solution routes only needs a left-endpoint continuity residual.

## What not to do

Do not replace `endpointEnergy` with `intervalDomain_energyContinuousOn_Ioo`; that loses both endpoints.

Do not cite `intervalDomain_gradient_integral_nonneg` as a proof of `gradientTimeIntegrable`; nonnegativity is not integrability.

Do not use `IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc` as a producer; it consumes the target package.

Do not claim `ClosedEnergyIdentityTraceData.energyContinuous` proves the all-exponent Moser energy continuity; it is L² seed-specific and requires its own closed identity data.
