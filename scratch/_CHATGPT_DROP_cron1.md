# Q815 / cron1: heat level-0 lift vs cosine-series representative

Repo inspected: `xiangyazi24/Shen_work`
Source refs inspected:
- `chatgpt-scratch` for `IntervalPicardIterateRepresentation.lean` and scratch write target.
- `main` for the current `IntervalConjugateLevel0BFormSourceOn.lean` and `IntervalHeatSemigroupHighRegularity.lean` state.  Note: fetching `IntervalConjugateLevel0BFormSourceOn.lean` on `chatgpt-scratch` returned 404, so the Level0 usage below is from `main`.
Branch written: `chatgpt-scratch`

## Verdict

Yes, the agreement lemma you want already exists.  The name is:

```lean
ShenWork.IntervalPicardIterateRepresentation.hagree_zero
```

It gives exactly the level-0 heat-slice cosine-series agreement on `[0,1]`, packaged as `Set.EqOn`:

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
```

and

```lean
iterateReprCoeff p u₀ 0 σ k
  = Real.exp (-σ * unitIntervalCosineEigenvalue k)
      * cosineCoeffs (intervalDomainLift u₀) k
```

by the definition of `iterateReprCoeff`.

So for your RHS using `heatCoeff u₀ k`, use the existing abbrev

```lean
abbrev heatCoeff (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ :=
  cosineCoeffs (intervalDomainLift u₀)
```

from `IntervalPicardLevel0SourceTimeC1On.lean`, and `simpa [iterateReprCoeff, heatCoeff]` should align the RHS.

## Answer to the three search questions

### 1. Agreement lemma on `Icc 0 1`?

Yes: `hagree_zero`.  Strictly, it is stated for `picardIter p u₀ 0 σ`, not for `conjugatePicardIter p u₀ 0 σ`, but the level-0 branches are definitionally the same heat semigroup slice:

```lean
picardIter p u₀ 0
  = fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1

conjugatePicardIter p u₀ 0
  = fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

The current Level0 file already relies on this: it uses `hagree_zero` to prove an agreement whose LHS is written with `conjugatePicardIter p u₀ 0 s`.

### 2. `hagree_zero` or similar?

Yes.  `hagree_zero` is the relevant lemma.  I did not find a better/directly named lemma matching `intervalDomainLift.*cosineSeries.*agree`; the repo convention here is the `hagree_*` family from `IntervalPicardIterateRepresentation.lean`.

Also nearby:

```lean
hbsum_zero
hagree_succ
```

but for the level-0 heat slice, `hagree_zero` is the one to use.

### 3. Does the Level0 file already use `hagree_zero`?

Yes.  In `IntervalConjugateLevel0BFormSourceOn.lean`, the current file uses:

```lean
have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 s) x = U_cos x := by
  intro x hx
  exact ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hs_pos _hu₀_cont _hu₀_bound hx
```

and later:

```lean
have hagree_w : Set.EqOn (intervalDomainLift w)
    (fun x => ∑' k, (Real.exp (-s * unitIntervalCosineEigenvalue k) *
      heatCoeff u₀ k) * cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
  ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hs_pos _hu₀_cont _hu₀_bound
```

So the exact bridge from conjugate level-0 lift to heat cosine series is already being used in that file.

## Wiring `heatSemigroup_jointContDiffAt_two`

The new joint regularity theorem is here:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

Its target is the cosine-series representative:

```lean
ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
  ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
    cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀)
```

The Level0 file currently opens only:

```lean
open ShenWork.Paper2.HeatSemigroupHighRegularity (heatSemigroup_contDiff_four)
```

so either add/open the joint namespace:

```lean
open ShenWork.Paper2.HeatSemigroupJointRegularity
  (heatSemigroup_jointContDiffAt_two)
```

or call the theorem fully qualified.

## Suggested bridge shape

For an interior spatial basepoint `hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1`, define:

```lean
let U_lift : ℝ × ℝ → ℝ := fun q =>
  intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2

let U_series : ℝ × ℝ → ℝ := fun q =>
  ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
    cosineMode k q.2
```

Then:

```lean
have hU_series_C2 : ContDiffAt ℝ 2 U_series (s₀, x₀) := by
  -- with hs₀ : c < s₀, hc : 0 < c
  simpa [U_series, ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff] using
    ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
      (u₀ := u₀) (M₀ := M₀) _hu₀_bound hc hs₀
```

Build the event-level agreement from `hagree_zero`:

```lean
have hU_lift_eq_series : U_lift =ᶠ[𝓝 (s₀, x₀)] U_series := by
  -- Need two neighborhood facts:
  --   (a) q.1 > 0 near s₀, since 0 < c < s₀;
  --   (b) q.2 ∈ Icc 0 1 near x₀, since x₀ ∈ Ioo 0 1.
  filter_upwards [/* time-neighborhood q.1 > 0 */,
                  /* space-neighborhood q.2 ∈ Icc 0 1 */] with q hq_time hq_x
  have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hq_time _hu₀_cont _hu₀_bound hq_x
  -- `h` is for `picardIter`; unfold/simpa level-0 definitions to rewrite
  -- `conjugatePicardIter` to the same heat slice.
  simpa [U_lift, U_series,
    ShenWork.IntervalConjugatePicard.conjugatePicardIter,
    ShenWork.IntervalMildPicard.picardIter,
    ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff,
    ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff] using h
```

Finally transfer:

```lean
exact hU_series_C2.congr_of_eventuallyEq hU_lift_eq_series
```

The orientation above matches the pattern already used in
`heatSemigroup_jointContDiffAt_two`: `h.congr_of_eventuallyEq hEq` transfers from the current smooth representative to the left side of `hEq`.

## Important endpoint caveat

This `ContDiffAt` transfer is an **interior** bridge.  `hagree_zero` is `EqOn Icc`, but an ordinary neighborhood of `(s₀, 0)` or `(s₀, 1)` contains spatial points outside `[0,1]`; there the zero-extension `intervalDomainLift` is generally `0`, while the cosine-series representative is the even/periodic heat representative.  So for plain `ContDiffAt` you want `x₀ ∈ Ioo 0 1`.

At endpoints, use a within-set statement (`ContDiffWithinAt`/`ContDiffOn`) or switch to the globally even cosine representative rather than the zero-extension.
