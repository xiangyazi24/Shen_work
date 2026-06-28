# Q1784 (cron2): eventually proof pattern

GitHub-connector only. I did not read the local `/tmp/q_cron3_eventually.txt` file and did not run Lean locally. Repository search did not find the literal file name. The strongest matching target is the `eventually` obligation in `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, especially the `level0_chemDiv_timeDerivData` / positive-window source-data proof.

## Bottom line

There are two correct patterns.

If the property is true for every point, close the filter goal with:

```lean
exact Filter.Eventually.of_forall (fun r => by
  -- prove P r
)
```

If the proof needs positive time, do **not** use `Eventually.of_forall` directly. Instead restrict to a small ball around the positive center `s`:

```lean
apply Filter.eventually_of_mem
  (Metric.ball_mem_nhds s (lt_min one_pos (half_pos hs_pos)))
intro r hr
have hr_pos : s / 2 < r := by
  have hdist := Metric.mem_ball.mp hr
  rw [Real.dist_eq] at hdist
  have hlt := lt_of_lt_of_le hdist (min_le_right 1 (s / 2))
  linarith [(abs_lt.mp hlt).1]
have hr_pos' : 0 < r := by linarith
-- now prove P r using positive-time infrastructure
```

This is exactly the right shape for `level0_chemDiv_timeDerivData`, because the surrounding proof has `s ∈ Icc c T` and `hc : 0 < c`, so

```lean
have hs_pos : 0 < s := lt_of_lt_of_le hc hs.1
```

Then `δ = min 1 (s / 2)` keeps every `r ∈ Metric.ball s δ` in positive time.

## For an `IntervalIntegrable`-nearby goal

For a goal shaped like

```lean
∀ᶠ r in 𝓝 s,
  IntervalIntegrable
    (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
    MeasureTheory.volume (0 : ℝ) 1
```

use the positive-ball pattern above, then prove the fixed positive-time slice:

```lean
apply Filter.eventually_of_mem
  (Metric.ball_mem_nhds s (lt_min one_pos (half_pos hs_pos)))
intro r hr
have hr_pos : s / 2 < r := by
  have hdist := Metric.mem_ball.mp hr
  rw [Real.dist_eq] at hdist
  have hlt := lt_of_lt_of_le hdist (min_le_right 1 (s / 2))
  linarith [(abs_lt.mp hlt).1]
have hr_pos' : 0 < r := by linarith
-- prove IntervalIntegrable at this fixed r
```

## For a pure continuity-nearby goal

If you already have a fixed-slice theorem with no positivity precondition, for example

```lean
hcont_slice : ∀ r,
  ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
    (Set.Icc (0 : ℝ) 1)
```

then the filter wrapper is one line:

```lean
exact Filter.Eventually.of_forall (fun r => hcont_slice r)
```

If the fixed-slice theorem needs `0 < r`, combine the two patterns:

```lean
apply Filter.eventually_of_mem
  (Metric.ball_mem_nhds s (lt_min one_pos (half_pos hs_pos)))
intro r hr
have hr_pos : s / 2 < r := by
  have hdist := Metric.mem_ball.mp hr
  rw [Real.dist_eq] at hdist
  have hlt := lt_of_lt_of_le hdist (min_le_right 1 (s / 2))
  linarith [(abs_lt.mp hlt).1]
have hr_pos' : 0 < r := by linarith
exact hcont_slice_pos r hr_pos'
```

## Minimal check block

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

#check Filter.Eventually.of_forall
#check Filter.eventually_of_mem
#check Metric.ball_mem_nhds
#check Metric.mem_ball
```

## Warning

`Filter.Eventually.of_forall` only removes the filter wrapper. It does not prove the fixed-slice analytic fact. In this file, the real work is still the positive-time slice proof: smooth heat profile, resolver regularity, chemDiv source regularity, or interval integrability. If the proof needs `0 < r`, use the ball-restriction pattern so the positive-time infrastructure is available.
