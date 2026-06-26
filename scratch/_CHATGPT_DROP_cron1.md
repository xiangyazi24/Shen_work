# Q884 / cron1: `IterateSourceTimeData.floor` usage audit

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Main file inspected:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

Related downstream file inspected:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

## Question

`IterateSourceTimeData.floor` currently asks for global-in-time interior positivity:

```lean
floor : ∀ t : ℝ, ∀ x ∈ Ioo (0:ℝ) 1, 0 < intervalDomainLift (u t) x
```

For the heat semigroup convention in this repo, this is false for the raw heat iterate `u t = S(t) u₀`, because `S(0)u₀ = 0` and `S(t)u₀ = 0` for `t < 0`.

The concrete question was whether this all-time floor is genuinely needed, or whether downstream proofs only use it at positive times.

## Exact grep result

For:

```bash
grep -n "\.floor" ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

The only actual `.floor` uses are:

```lean
160:    exact hasDerivAt_srcSlice (H.floor s x hx) (hdiff x hx s hs)
166:    exact hasDerivAt_srcSlice1 (H.floor s x hx) h1 h2
```

There is also the field declaration:

```lean
114:  floor : ∀ t : ℝ, ∀ x ∈ Ioo (0:ℝ) 1, 0 < intervalDomainLift (u t) x
```

## Where it is used

The uses occur only inside:

```lean
theorem flooredSourceTimeData_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u)
```

Specifically:

```lean
  d0 τ := by
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.time1 τ
    refine ⟨δ, hδ, hcont, ?_, hcd⟩
    intro x hx s hs
    exact hasDerivAt_srcSlice (H.floor s x hx) (hdiff x hx s hs)
```

and:

```lean
  d1 τ := by
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.time2 τ
    refine ⟨δ, hδ, hcont, ?_, hcd⟩
    intro x hx s hs
    obtain ⟨h1, h2⟩ := hdiff x hx s hs
    exact hasDerivAt_srcSlice1 (H.floor s x hx) h1 h2
```

So `.floor` is not used directly by the final coupled resolver theorem except through the intermediate `FlooredSourceTimeData` produced by `flooredSourceTimeData_of_iterate`.

## Verdict

`IterateSourceTimeData.floor` is currently genuinely global in time.

It is not merely a positive-time downstream hypothesis. The local derivative fields `time1` and `time2` are themselves quantified over every `τ : ℝ`, and the constructor for `FlooredSourceTimeData` uses `H.floor s x hx` for every local time `s ∈ Metric.ball τ δ` around that arbitrary `τ`.

Thus, for the current definitions, a raw heat semigroup iterate with the convention

```lean
S(0)u₀ = 0
S(t)u₀ = 0  -- for t < 0
```

cannot satisfy `IterateSourceTimeData.floor` as written.

## Why this matters downstream

The target downstream structure is also global in time. `FlooredSourceTimeData` has:

```lean
d0 : ∀ τ : ℝ, ...
d1 : ∀ τ : ℝ, ...
```

and `physicalSourceTimeC2_of_floored` produces:

```lean
PhysicalSourceTimeC2 p u (builtEs H)
```

with:

```lean
src_contDiff k := srcTimeCoeff_contDiff H k
src_bound i k t hi := srcTimeCoeff_bound H i k t hi
```

where `srcTimeCoeff_contDiff` is global `ContDiff ℝ 2` in the real time variable. So the current pipeline has a global-time shape all the way from `IterateSourceTimeData` through `FlooredSourceTimeData` into `PhysicalSourceTimeC2`.

## Recommended repair options

The cleanest repair is not to try to prove the current `floor` for the raw heat semigroup. It is false at `t ≤ 0`.

Instead, one of these interface changes is needed:

### Option A: positive-window data structure

Create a positive-window analogue of the data structure, with time hypotheses restricted to a slab/window such as `Ioi 0`, `Icc c T` with `0 < c`, or local neighborhoods inside positive time.

This matches the mathematical truth: heat smoothing and strong positivity are available only for `t > 0` for the current semigroup convention.

### Option B: extend the iterate artificially for `t ≤ 0`

Define a modified time extension `u_ext` that is positive for all real `t`, e.g. constant equal to a positive slice for `t ≤ 0`, and agrees with the heat iterate on the positive window where the PDE argument is used.

This may be awkward because derivative/regularity fields must then be proved across the splice unless a smooth cutoff/extension is used.

### Option C: weaken `floor` to match `time1/time2` neighborhoods

Replace the standalone all-time field by local floor hypotheses inside `time1` and `time2`, for example requiring positivity only for the same `s ∈ Metric.ball τ δ` used by the derivative chain. But unless `τ` itself is restricted to positive time, this still fails for arbitrary negative `τ` under the raw heat semigroup convention.

So this option only helps if paired with a positive-time restriction.

## Bottom line

The answer to the implementation question is:

No, as written, `IterateSourceTimeData` cannot be instantiated directly for the raw heat semigroup `S(t)u₀` if `S(0)u₀ = 0` and `S(t)u₀ = 0` for `t < 0`.

The `.floor` field is used only in the `flooredSourceTimeData_of_iterate` bridge, but that bridge constructs globally quantified `d0/d1` fields. Therefore the all-time floor is currently a real requirement of the interface, not just an unused or positive-time-only assumption.
