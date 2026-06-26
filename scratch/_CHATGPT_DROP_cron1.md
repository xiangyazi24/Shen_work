# Q859 / cron1: can heat `FlooredSourceTimeData` be built by `τ > 0` vs `τ ≤ 0`?

Repo inspected: `xiangyazi24/Shen_work`

Source ref inspected: `main`

Branch written: `chatgpt-scratch`

## Verdict

Not as stated.

The case split works for two open regions:

```lean
τ > 0
τ < 0
```

but it does **not** solve the global `FlooredSourceTimeData` obligation because the structure quantifies over **all** `τ : ℝ`, including `τ = 0`.

At `τ = 0`, every metric ball `Metric.ball 0 δ` contains positive and negative times.  The heat-kernel convention gives zero for nonpositive time, while for positive time the heat semigroup is the genuine smoothing of `u₀`.  So the time profile is a hard zero-extension through `t = 0`, not a smooth extension.  The `d0` / `d1` fields require local `HasDerivAt` data for every `s ∈ Metric.ball τ δ`; at `τ = 0`, that includes `s = 0`, where the hard zero-extension is generally not differentiable unless the positive-time right germ is also zero.

So the split should be:

```lean
τ > 0     -- choose δ < τ/2, all times positive
τ < 0     -- choose δ < -τ/2, all times negative, zero branch
τ = 0     -- obstruction; not trivial
```

The `τ = 0` branch is the problem.

## Why the structure blocks this

`FlooredSourceTimeData` has global local-in-time fields:

```lean
d0 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
  (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc 0 1)) ∧
  (∀ x ∈ Ioo 0 1, ∀ s ∈ Metric.ball τ δ,
    HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
  ContinuousOn (Function.uncurry s₁) (Icc (τ - δ) (τ + δ) ×ˢ Icc 0 1)
```

and similarly for `d1`.  Because this is `∀ τ`, the proof must pass through `τ = 0`.

The later fields are also global in `t`:

```lean
sliceC2      : ∀ i ≤ 2, ∀ t, ContDiffOn ℝ 2 ... (Icc 0 1)
sliceNeumann : ∀ i ≤ 2, ∀ t, ...
zerothBound  : ∀ i ≤ 2, ∃ D, ∀ t, |cosineCoeffs ... 0| ≤ D
laplBound    : ∀ i ≤ 2, ∃ M, ∀ t k, 1 ≤ k → |cosineCoeffs ... k| ≤ M / (kπ)^2
```

For a heat semigroup from rough bounded initial data, the uniform `laplBound` over **all** `t > 0` is also suspect near `t = 0`; positive-time smoothing gives `C∞` for each fixed `t > 0`, but the spatial `C²` constants typically blow up as `t ↓ 0`.  On a fixed positive window `[c,T]`, this is fine; globally from `0` it is not.

## The zero convention is real, but it does not make `τ = 0` smooth

The repo has the zero-time convention for the kernel:

```lean
theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatKernel t x = 0
```

and the interval full kernel uses that convention in the nonpositive-time branch.  This makes the `τ < 0` branch trivial if the whole local ball stays negative.  It does **not** imply differentiability through `τ = 0`.

The same issue is already visible elsewhere in the repo: `level0_chemDiv_timeDerivData` has a `τ ≤ 0` branch comment saying the branch is never reached in practice because downstream uses `c > 0`, and that the heat semigroup jumps near `0` under the zero convention.

## What is reachable by case split

For `τ > 0`:

```lean
choose δ := min 1 (τ / 2)
```

Then `s ∈ Metric.ball τ δ` implies `0 < s`, so the positive-time heat semigroup regularity applies.  This is the correct branch for the actual `[c,T]` use.

For `τ < 0`:

```lean
choose δ := min 1 ((-τ) / 2)
```

Then `s ∈ Metric.ball τ δ` implies `s < 0`, so the zero branch applies.  The source slice and its time derivatives can be taken as zero.

For `τ = 0`:

no positive `δ` avoids positive times.  Unless the theorem is weakened/localized, or the trajectory is replaced by a smooth-in-time extension, this branch remains blocked.

## Recommended fix

Do not try to prove global `FlooredSourceTimeData` for the hard-zero-extended heat semigroup unless the data are specially trivial.

Use one of these instead:

### Option A: make a windowed structure

Define a positive-window analogue, e.g.

```lean
FlooredSourceTimeDataOn p u s₁ s₂ c T
```

where all local `τ` obligations are only for `τ ∈ Icc c T` with `0 < c`, and all uniform bounds are only over `t ∈ Icc c T`.  Then the `τ > 0` branch is the only branch needed.

This matches the actual level-0 consumer, which works on `[c,T]`.

### Option B: build a smooth positive-time extension

Replace the hard-zero extension by a smooth extension in time that agrees with the heat semigroup on `[c,T]` and is smooth/floored on all of `ℝ`.  This is more work.  A naive zero cutoff may reintroduce `rpow`/floor trouble at the cutoff interface unless the function is arranged carefully.

### Option C: bypass `FlooredSourceTimeData` for level 0

For the heat semigroup, prove the resolver/source coefficient `ContDiffAt` and summable majorants directly on the positive window, as in the direct-resolver route.  This avoids the global `∀ τ` surface entirely.

## Bottom line

The proposed `τ > 0` / `τ ≤ 0` split is **not sufficient**.  It hides the actual hard case `τ = 0` inside `τ ≤ 0`.

A correct proof can split into `τ > 0`, `τ < 0`, and `τ = 0`; the first two are plausible, but the third is generally false for the hard-zero-extended heat semigroup.  For the heat level-0 use, the right move is to work on a positive window `[c,T]` or use a smooth extension/cutoff, not a global `FlooredSourceTimeData` over all real times.
