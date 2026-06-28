# Q1706 (cron2): cron3 approach prompt

GitHub-connector only. I did not read the local `/tmp/q_cron3_approach.txt` file and did not run Lean locally. Repository search for the literal filename found no target. The strongest repository match for “approach” is the initial-approach/initial-trace thread around:

```text
ShenWork/Paper2/IntervalPicardIterateInitialApproach.lean
ShenWork/Paper2/IntervalBFormInitialTrace.lean
```

## Bottom line

The initial-approach route is already landed. Do **not** rebuild it by proving a global `ContinuousOn` statement at `t = 0`; that is the wrong shape for several semigroup conventions. Use the one-sided initial approach theorems already in the repository.

For the χ₀ = 0 Picard iterate side, use:

```lean
ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
ShenWork.IntervalPicardIterateInitialApproach.gradientDuhamelMap_initialApproach_of_ball
ShenWork.IntervalPicardIterateInitialApproach.picardIter_initialApproach
```

For the B-form/conjugate fixed-point side, use:

```lean
ShenWork.Paper2.BFormInitialTrace.intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
```

The proof architecture is:

1. homogeneous heat leg: `S(t)u₀ → u₀` uniformly as `t → 0+`;
2. Duhamel correction: bounded by `A * sqrt t + B * t`, hence small for small `t`;
3. fixed-point transfer: rewrite by `hmild` and apply the map-level approach.

## Minimal check block

```lean
import ShenWork.Paper2.IntervalPicardIterateInitialApproach
import ShenWork.Paper2.IntervalBFormInitialTrace

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)

#check ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
#check ShenWork.IntervalPicardIterateInitialApproach.gradientDuhamelMap_initialApproach_of_ball
#check ShenWork.IntervalPicardIterateInitialApproach.picardIter_initialApproach
#check ShenWork.Paper2.BFormInitialTrace.intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
#check ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
```

## How to consume it

For a Picard iterate goal of the form

```lean
∀ ε, 0 < ε → ∃ δ > 0, ∀ s, 0 < s → s < δ →
  ∀ y : intervalDomainPoint, |picardIter p u₀ n s y - u₀ y| < ε
```

use:

```lean
exact ShenWork.IntervalPicardIterateInitialApproach.picardIter_initialApproach
  p hχ0 hu₀_cont hTpos hM hball n
```

For the conjugate fixed-point initial trace, use:

```lean
exact ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
  p hu₀_cont DB
```

For a pointwise map-approach intermediate goal, use:

```lean
exact ShenWork.Paper2.BFormInitialTrace.intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
  p hu₀_cont DB
```

## Why this is the right route

`semigroup_initialApproach` proves the homogeneous leg by clipping the continuous datum to a continuous real-line function and applying the interval semigroup uniform convergence theorem.

`gradientDuhamelMap_initialApproach_of_ball` handles the χ₀ = 0 Picard map: the chemotaxis correction vanishes, and the logistic Duhamel term is bounded by `t * C_L`.

`intervalConjugateDuhamelMap_initialApproach_of_conjugate_data` handles the B-form map: the chemotaxis/conjugate correction is bounded by a `sqrt t` term and the logistic correction by a `t` term. The final `conjugatePicardLimit_initialTrace_of_conjugate_data` rewrites the fixed point by `hmild` and closes the `InitialTrace` field.

## Warning

Do not replace these with a closed-slab `ContinuousOn` claim including `t = 0` unless the map is definitionally compatible at `0`. Several files intentionally avoid a global `∀ τ : ℝ` or closed-slab-at-zero statement because the semigroup-side convention can jump at `τ = 0`. The safe statement is the one-sided initial trace: `0 < t` and `t < δ`.
