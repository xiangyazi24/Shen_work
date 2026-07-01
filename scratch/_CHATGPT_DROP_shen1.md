# Q2966 (shen1) — P3MoserRegularityProducer threshold-plan refactor audit

Repo: `xiangyazi24/Shen_work`  
Audited ref: current main `d9a5fb318daa3226f7ab9a622de1bb8bddbcf67c`  
File: `ShenWork/PDE/P3MoserRegularityProducer.lean`  
Scope: source audit only; no project source edits.

## Answer

Yes. It is sound to refactor

```lean
intervalDomain_firstCrossingStep_raw_of_globalClassicalTraceAnchored_upperDataGapFrontiers
```

so that it calls the direct threshold-plan producer and removes the two high-excursion / upper-data-gap hypotheses

```lean
hlower : ... IntegratedMoserHighExcursionLowerAverageWindowFrontier ...
hupperDataGap : ... IntegratedMoserWindowUpperDataGapFrontier ...
```

from the theorem signature.

The current proof builds the anchored representative

```lean
let uA := intervalDomainWithInitialSlice u₀ u
```

then packages `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` solely in order to call

```lean
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

But `P3MoserRegularityProducer.lean` already imports

```lean
import ShenWork.PDE.P3MoserThresholdPlanProducer
```

and opens

```lean
open ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer
```

The imported file provides exactly the interval-domain wrapper:

```lean
intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

with inputs

```lean
hreg hnonneg hdiss hrel hrho hp0_nonneg
```

For the anchored representative `uA`, the target theorem already has or can construct all of these:

* `hreg` from
  ```lean
  intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
    hglobal hT htrace hdatum hgrad
  ```
* `hnonneg` from
  ```lean
  intervalDomain_integratedMoserEnergyNonnegativity_of_classical
    (p0 := p0) hsolA
  ```
* `hdiss` by `simpa [uA] using hdiss`.
* `hrel` by `simpa [uA] using hrel`.
* `hrho` and `hp0_nonneg` directly.

Then the existing positive-time congruence theorem

```lean
intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
```

transfers the anchored step back to raw `u`.

## Ordering / import / name-resolution notes

No import obstruction: `ShenWork.PDE.P3MoserThresholdPlanProducer` is already imported at the top of `P3MoserRegularityProducer.lean`.

No ordering obstruction if the proof calls the imported theorem directly. The local convenience theorem

```lean
intervalDomain_firstCrossingStep_of_lite_classical_integratedData
```

appears later in the same file, so this target theorem should **not** call that local wrapper unless the file is reordered. Calling the imported

```lean
P3MoserThresholdPlanProducer.intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

avoids the ordering issue.

Name resolution should work unqualified because the namespace is opened, but the fully qualified call below is safer and minimal.

The theorem name `..._upperDataGapFrontiers` becomes stale after the refactor. Keeping the name is the smallest API patch; renaming it would be cleaner but is not required for soundness. Connector code search for the exact theorem name only showed the defining file, so there is no visible separate caller to update, but I would still check locally with `grep` before landing.

## Exact minimal Lean patch

Replace the theorem signature and proof body with the following. The rest of the file can stay as-is.

```lean
/-- Produce a raw first-crossing step by running the direct threshold-plan route
on the re-anchored representative, then transferring the positive-time step back
to the raw trajectory.

All closed-time Moser inputs in this theorem are stated for
`intervalDomainWithInitialSlice u₀ u`; only the final first-crossing step is
exported back to raw `u`.  The old lower-average / upper-data-gap frontiers are
no longer needed here because the threshold-plan producer consumes regularity,
energy nonnegativity, dissipation, and relative interpolation directly. -/
theorem
    intervalDomain_firstCrossingStep_raw_of_globalClassicalTraceAnchored_upperDataGapFrontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hgrad : IntervalDomainRawMoserGradientTimeIntegrability u T p0)
    (hdiss :
      IntegratedMoserDissipationDropBefore intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0)
    (hrel :
      RelativeMoserInterpolationBefore intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  let uA : ℝ → intervalDomain.Point → ℝ :=
    intervalDomainWithInitialSlice u₀ u
  have hglobalA :
      IsPaper2GlobalClassicalSolution intervalDomain params uA v := by
    simpa [uA] using
      (intervalDomain_globalClassical_withInitialSlice
        (u₀ := u₀) (u := u) (v := v) hglobal)
  have hsolA : IsPaper2ClassicalSolution intervalDomain params T uA v :=
    hglobalA.classical hT
  have hregA :
      IntegratedMoserFirstCrossingRegularity intervalDomain uA T p0 := by
    simpa [uA] using
      intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
        hglobal hT htrace hdatum hgrad
  have hstepA : IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0 :=
    ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer
      .intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
      hregA
      (intervalDomain_integratedMoserEnergyNonnegativity_of_classical
        (p0 := p0) hsolA)
      (by simpa [uA] using hdiss)
      (by simpa [uA] using hrel)
      hrho hp0_nonneg
  exact intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
    (u₀ := u₀) (u := u) (T := T) (rho := rho) (p0 := p0)
    (by simpa [uA] using hstepA)
```

## Why the old high-excursion route is not necessary here

The high-excursion lower-average and upper-data-gap route is still available in the same file through helpers such as

```lean
intervalDomain_lowerAverageUpperDataGapData_of_classical
intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
```

but it is no longer necessary for this anchored raw global-classical theorem. The threshold-plan producer bypasses the explicit `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` package and derives `IntegratedMoserFirstCrossingStep` from the abstract regularity/nonnegativity/dissipation/interpolation data directly.

So the proposed refactor is a real residual reduction: it deletes two unnecessary hypotheses from this theorem without adding any new analytic input.
