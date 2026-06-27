# Q1518 (cron1) -- `FlooredSourceTimeData` time domain and bound issue

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only repository inspection. I did not run Lean locally and did not edit any Lean source file. I inspected the target branch `chatgpt-scratch`, because that is the branch requested for the git-drop.

Relevant files inspected:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

## Short answer

On the requested branch `chatgpt-scratch`, `FlooredSourceTimeData` does **not** merely require uniform bounds for all `t > 0`. It requires a stronger, all-real-time domain:

* `d0 : ∀ τ : ℝ, ...`
* `d1 : ∀ τ : ℝ, ...`
* `sliceC2 : ... ∀ t : ℝ, ...`
* `sliceNeumann : ... ∀ t : ℝ, ...`
* `zerothBound : ... ∀ t : ℝ, ...`
* `laplBound : ... ∀ (t : ℝ) (k : ℕ), ...`

So the current target-branch structure is **global on all of `ℝ`**, not positive-time-only, and definitely not windowed-away-from-zero.

`flooredSourceTimeData_of_iterate` does **not** handle the `t → 0+` blow-up by using windowed bounds. It simply assumes all-real-time bounds in the input `IterateSourceTimeData` and forwards them unchanged into `FlooredSourceTimeData`.

Thus the present `chatgpt-scratch` version resolves the issue only by pushing the hard/impossible uniform-bound obligation upstream into `IterateSourceTimeData`; it does not solve it locally.

## Exact `FlooredSourceTimeData` signatures on `chatgpt-scratch`

In `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean`, the structure is:

```lean
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  /-- `∂ₜ srcSlice = s₁` pointwise in `x ∈ (0,1)`, locally in `t`. -/
  d0 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
    ContinuousOn (Function.uncurry s₁) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)

  /-- `∂ₜ s₁ = s₂` pointwise in `x ∈ (0,1)`, locally in `t`. -/
  d1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (s₁ s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => s₁ r x) (s₂ s x) s) ∧
    ContinuousOn (Function.uncurry s₂) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)

  /-- Each time-derivative slice is space-`C²` on `[0,1]` (under the floor). -/
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)

  /-- Neumann endpoint data of each time-derivative slice (for IBP decay). -/
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 1 = 0

  /-- Uniform-in-`t` zeroth-mode and Laplacian envelopes per time order. -/
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D

  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

There is no `0 < τ` hypothesis in `d0`/`d1`, and no `0 < t` hypothesis in `sliceC2`, `sliceNeumann`, `zerothBound`, or `laplBound` on this branch.

## Exact `IterateSourceTimeData` signatures

In `ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean`, the input structure is also all-real-time:

```lean
structure IterateSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (du d2u : ℝ → ℝ → ℝ)
    : Prop where
  floor : ∀ t : ℝ, ∀ x ∈ Ioo (0:ℝ) 1, 0 < intervalDomainLift (u t) x

  time1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x) (du s x) s) ∧
    ContinuousOn (Function.uncurry (srcSlice1 p u du))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)

  time2 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice1 p u du s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x) (du s x) s ∧
      HasDerivAt (fun r => du r x) (d2u s x) s) ∧
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)

  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2
      ((sliceFam (srcSlice p u) (srcSlice1 p u du) (srcSlice2 p u du d2u) i) t)
      (Icc (0:ℝ) 1)

  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 1 = 0

  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 0| ≤ D

  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

So even the iterate-side data is not windowed or positive-time-only. It asks for global envelopes before `flooredSourceTimeData_of_iterate` is called.

## What `flooredSourceTimeData_of_iterate` actually does

The producer is just a field-forwarding bridge plus the pointwise chain/product-rule wrappers:

```lean
theorem flooredSourceTimeData_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u) where
  d0 τ := by
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.time1 τ
    refine ⟨δ, hδ, hcont, ?_, hcd⟩
    intro x hx s hs
    exact hasDerivAt_srcSlice (H.floor s x hx) (hdiff x hx s hs)
  d1 τ := by
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.time2 τ
    refine ⟨δ, hδ, hcont, ?_, hcd⟩
    intro x hx s hs
    obtain ⟨h1, h2⟩ := hdiff x hx s hs
    exact hasDerivAt_srcSlice1 (H.floor s x hx) h1 h2
  sliceC2 := H.sliceC2
  sliceNeumann := H.sliceNeumann
  zerothBound := H.zerothBound
  laplBound := H.laplBound
```

Therefore:

* There is **no window parameter** like `ε`, `τ₀`, `a`, `T`, or `0 < c` in the bound fields.
* There is **no localized statement** like `∀ t ∈ Icc a T`.
* There is **no positive-time guard** like `0 < t`.
* There is **no proof inside this producer** that bounds the heat-derived `λ_k`/`λ_k²` weighted coefficients near `t = 0+`.

The constructor handles the problem only by requiring `H.zerothBound` and `H.laplBound` to have already solved it globally.

## Downstream confirms the all-time interpretation

`IntervalPhysicalSourceTimeC2Concrete.lean` also uses the fields globally.

The source coefficient regularity theorem is global:

```lean
theorem srcTimeCoeff_contDiff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k) := by
```

The source bound theorem quantifies over arbitrary `t : ℝ`:

```lean
theorem srcTimeCoeff_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) (t : ℝ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k := by
```

And `physicalSourceTimeC2_of_floored` forwards this as:

```lean
src_contDiff k := srcTimeCoeff_contDiff H k
src_bound i k t hi := srcTimeCoeff_bound H i k t hi
```

So downstream currently expects global `PhysicalSourceTimeC2` data on all time, not merely positive-time-local data.

## Mathematical diagnosis

For heat smoothing from rough/merely bounded cosine coefficients, the coefficients of time derivatives contain factors like

```text
λ_k * exp(-t λ_k) * a_k
λ_k^2 * exp(-t λ_k) * a_k
```

For each fixed `t > 0`, the exponential wins and the sums are fine. On a window `[a, T]` with `a > 0`, they are uniformly controlled by majorants such as `λ_k^m exp(-a λ_k)`. But as `a → 0+`, the constants blow up unless the initial data already has corresponding spatial regularity/weighted coefficient bounds.

Thus a uniform-in-`t > 0` bound for `i = 1, 2` is generally false for the heat-semoothing-only route. The `chatgpt-scratch` structure is even stronger than that: it asks for uniform-in-`t : ℝ` bounds.

Defining `du` or `d2u` to be `0` for `t ≤ 0` would not fix the obstruction, because the blow-up is from the right limit `t → 0+`.

## Practical consequence for the proof plan

The current `chatgpt-scratch` version cannot honestly discharge the heat-smoothing base-iterate source time data for `i = 1, 2` from mere positive-time smoothing plus bounded initial cosine coefficients. The obstruction is not in `flooredSourceTimeData_of_iterate`; it is in the shape of the structures it connects:

```text
IterateSourceTimeData.zerothBound/laplBound
      ↓ forwarded unchanged
FlooredSourceTimeData.zerothBound/laplBound
      ↓ used to build all-time builtEs
PhysicalSourceTimeC2.src_bound
```

The bridge is correct as a bridge, but the assumptions are too strong for the intended heat-smoothing proof.

## Suggested repair direction

There are two coherent ways forward.

### Option A: change the data to positive-time/windowed data

Use local positive-time windows. The bound fields should depend on a positive lower time cutoff, e.g. one of these shapes:

```lean
-- window lower-bound style
zerothBoundWindow : ∀ i : ℕ, i ≤ 2 → ∀ a T : ℝ, 0 < a → a ≤ T →
  ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc a T,
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D

laplBoundWindow : ∀ i : ℕ, i ≤ 2 → ∀ a T : ℝ, 0 < a → a ≤ T →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a T, ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤
      M / ((k : ℝ) * Real.pi) ^ 2
```

or, equivalently, a local-at-`τ > 0` version with `δ ≤ τ/2`, so every local slab stays away from zero.

But this is not just a local edit: downstream `PhysicalSourceTimeC2` currently wants a global `src_bound i k t hi`, so the physical structure or theorem consuming it must also become local/windowed/positive-time.

### Option B: keep global bounds but strengthen hypotheses drastically

If the goal is to keep the current global `PhysicalSourceTimeC2` shape, then the initial data/iterate hypotheses must include enough regularity to make the `λ_k`, `λ_k²` weighted time-derivative source coefficients uniformly bounded up to `t = 0`. That is a much stronger assumption than heat smoothing for arbitrary continuous/bounded-coefficient data.

For the current intended heat-smoothing route, Option A is the natural fix.

## Final answer

`flooredSourceTimeData_of_iterate` does **not** use windowed bounds. It simply forwards the all-time `IterateSourceTimeData.zerothBound` and `IterateSourceTimeData.laplBound` fields into `FlooredSourceTimeData`.

On `chatgpt-scratch`, `FlooredSourceTimeData` does **not** require `∀ t > 0`; it requires `∀ t : ℝ`. The same is true for the iterate-side input data and the downstream `src_bound` theorem.

So the suspected `t → 0+` blow-up is a real structural obstruction in this branch, unless the plan is to add stronger initial regularity assumptions. The honest heat-smoothing approach needs a positive-time/windowed version of these data structures and corresponding downstream consumers.
