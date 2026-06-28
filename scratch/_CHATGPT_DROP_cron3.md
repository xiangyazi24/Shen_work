# Q1568 (cron3): does `IntervalHeatResolverJointC2.lean` call the changed `heatResolverJointContDiffAt_two` API?

## Short answer

Yes, `ShenWork/Paper2/IntervalHeatResolverJointC2.lean` imports

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
```

at the top of the file.

But no, `IntervalHeatResolverJointC2.lean` does **not** call the changed theorem

```lean
heatResolverJointContDiffAt_two
```

from `IntervalHeatSemigroupHighRegularity.lean` / namespace
`ShenWork.Paper2.HeatResolverJointRegularity`.

So the build of `IntervalHeatResolverJointC2.lean` will see the changed API because of the import, but it should not be affected by the added `hu₀_pos` argument **unless** the imported file itself fails to compile.  There is no downstream missing-argument call to `heatResolverJointContDiffAt_two` inside `IntervalHeatResolverJointC2.lean`.

## Exact check

I checked commit

```text
ac0dc64368c84b83c6ff4cf8b83530adbf6148a9
```

### 1. Import is present

`ShenWork/Paper2/IntervalHeatResolverJointC2.lean` has:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries
```

So yes, building `ShenWork.Paper2.IntervalHeatResolverJointC2` requires elaborating/importing `IntervalHeatSemigroupHighRegularity.lean` first.

### 2. Exact grep for `heatResolverJointContDiffAt_two`

Repository search for the exact identifier:

```text
heatResolverJointContDiffAt_two
```

returned only:

```text
UNDERSTANDING.md
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

It did **not** return:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

So `IntervalHeatResolverJointC2.lean` does not reference the exact changed identifier.

### 3. The theorem in HighRegularity has the new `hu₀_pos` argument

In `IntervalHeatSemigroupHighRegularity.lean`, the changed theorem is:

```lean
theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
```

The new argument is passed into:

```lean
obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
  (p := p) hu₀_bound hu₀_cont hu₀_pos
```

So the API change is real in `HighRegularity`.

### 4. `IntervalHeatResolverJointC2.lean` defines a different theorem name

`IntervalHeatResolverJointC2.lean` defines:

```lean
theorem heatResolver_jointContDiffAt_two
```

with an underscore after `heatResolver`, not

```lean
heatResolverJointContDiffAt_two
```

The local theorem is a direct cutoff-series theorem and currently has the signature:

```lean
theorem heatResolver_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 ... := by
```

Its proof calls:

```lean
have hCutoff := (cutoffResolverSeries_contDiff_two (p := p)
  hu₀_bound hu₀_cont hfloor hc).contDiffAt (x := (s₀, x₀))
```

It does **not** call the imported `heatResolverJointContDiffAt_two`.

The nearby diagnostic print is also for the local underscore theorem:

```lean
#print axioms heatResolver_jointContDiffAt_two
```

not for `heatResolverJointContDiffAt_two`.

## Dependency implication

The dependency shape is:

```text
IntervalHeatResolverJointC2.lean
  imports IntervalHeatSemigroupHighRegularity.lean
```

but inside `IntervalHeatResolverJointC2.lean`:

```text
no call to HeatResolverJointRegularity.heatResolverJointContDiffAt_two
```

Therefore:

1. If `IntervalHeatSemigroupHighRegularity.lean` itself compiles after commit `ac0dc64`, then the added `hu₀_pos` parameter should not break `IntervalHeatResolverJointC2.lean`.
2. If the build fails while importing `IntervalHeatSemigroupHighRegularity.lean`, then the problem is upstream inside `HighRegularity` or one of its importers/callers, not a missing `hu₀_pos` argument in `IntervalHeatResolverJointC2.lean`.
3. If Codex reports a missing argument for `heatResolverJointContDiffAt_two`, grep the whole repo for callers outside `IntervalHeatResolverJointC2.lean`; the exact search already indicates the call is not in this file.

## Practical conclusion

For this specific build target:

```text
ShenWork.Paper2.IntervalHeatResolverJointC2
```

the `hu₀_pos` addition to

```lean
heatResolverJointContDiffAt_two
```

should be harmless as a downstream API change, because the target file imports the defining module but does not call the changed theorem.
