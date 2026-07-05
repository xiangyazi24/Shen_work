ANSWER Q3436 8bd2dfef

# Q3436: Task73 H¹ lap endpoint API audit

## Verdict

The proposed API layer is sound and honest.

A zero-right field

```lean
lap_cont0 : ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici (0 : ℝ)) 0
```

is strong enough to prove

```lean
H1LapComponentEndpointContinuousBefore u T
```

when combined with the existing strict-window continuity

```lean
∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
  ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
```

The endpoint case `b = 0` is handled entirely by the zero-right field, since `Set.Icc 0 0 ⊆ Set.Ici 0`. The positive interior points of `[0,b]` are handled by restricting to a strict positive-time subwindow whose left endpoint is below the point, e.g. `[x/2, b]`.

This does **not** fake the H² theorem: the new zero-right record is exactly the missing H²/laplacian trace input. No existing theorem in the inspected files produces it from `H1InitialEndpointData`, `H1UxxL1ContBefore`, or strict representative continuity.

## Current code shape

`IntervalChiNegH1LapComponentContinuity.lean` already has the endpoint record:

```lean
structure H1LapComponentEndpointContinuousBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  lap_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b)
```

It also has the strict positive-time producers:

```lean
lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
```

and the existing endpoint/strict combiner:

```lean
lapL2sq_continuousOn_before_of_endpoint_and_strict
```

`IntervalChiNegH1Bridge.lean` already uses this seam mechanically. In the requested region it has:

```lean
H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
H1IdentityRHSComponentsContinuousBefore_of_lapEndpoint_and_lapStrict
H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lap_zero
H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lapEndpoint
H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lap_zero
H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lapEndpoint
```

`UNDERSTANDING.md` correctly records the frontier: current infrastructure gives H¹ endpoint energy data, positive-time `u_xx` L¹ continuity, and strict positive-time representative continuity/equality, but no zero-start theorem for `lapL2sq`; the next producer should be either zero-right continuity of `lapL2sq` or a zero-slab representative for `liftDeriv2`.

## Recommended additions in `IntervalChiNegH1LapComponentContinuity.lean`

### 1. Atomic zero-right frontier record

Add this near `H1LapComponentEndpointContinuousBefore`:

```lean
/-- Atomic zero-right lap-component continuity frontier.  This is H²/laplacian
trace data, not H¹ endpoint energy data. -/
structure H1LapComponentZeroRightContinuous
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  lap_cont0 : ContinuousWithinAt
    (fun τ => lapL2sq u τ) (Set.Ici (0 : ℝ)) 0
```

This is non-duplicative: the existing endpoint record packages all zero-start windows `[0,b]`; the proposed record is the smaller atomic local input at `0`.

### 2. Produce endpoint-window record from zero-right + strict

I would name the theorem:

```lean
theorem H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (hstrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)) :
    H1LapComponentEndpointContinuousBefore u T
```

`0 < T` is not logically needed for this theorem: the field receives `b < T` as an input, and if there are no such `b` the statement is vacuous. It is harmless to add `(hT : 0 < T)` for route aesthetics, but the cleaner theorem omits it.

### Proof sketch at Lean tactic granularity

```lean
  refine ⟨?_⟩
  intro b hb0 hbT
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    -- goal: ContinuousWithinAt f (Icc 0 b) 0
    -- from h0.lap_cont0 : ContinuousWithinAt f (Ici 0) 0
    exact h0.lap_cont0.mono_left
      (nhdsWithin_mono 0 (by
        intro y hy
        exact hy.1))
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    -- strict window [x/2, b]
    have hxhalf_pos : 0 < x / 2 := half_pos hxpos
    have hxhalf_le_x : x / 2 ≤ x := by linarith
    have hxhalf_le_b : x / 2 ≤ b := le_trans hxhalf_le_x hx.2
    have hstrict_x := hstrict (a := x / 2) (b := b)
      hxhalf_pos hxhalf_le_b hbT
    have hx_in_strict : x ∈ Set.Icc (x / 2) b := ⟨hxhalf_le_x, hx.2⟩
    have hcx : ContinuousWithinAt (fun τ => lapL2sq u τ)
      (Set.Icc (x / 2) b) x := hstrict_x x hx_in_strict
    -- Transfer from [x/2,b] to [0,b] because these sets agree near x.
    -- Use local equality or filter inequality.
```

For the last transfer, the cleanest route is local equality of within-filters:

```lean
    have hsets : Set.Icc (0 : ℝ) b =ᶠ[𝓝 x] Set.Icc (x / 2) b := by
      filter_upwards [Set.Ioi_mem_nhds hxhalf_pos?] with y hy
      -- better actual bound is `x / 2 < y`, obtained from
      -- `Ioi_mem_nhds (show x / 2 < x by linarith)`.
      constructor
      · intro hy0b
        exact ⟨le_of_lt hy, hy0b.2⟩
      · intro hyhb
        exact ⟨le_trans (by linarith [hxhalf_pos.le]) hyhb.1, hyhb.2⟩
```

The exact local neighborhood line should be:

```lean
      filter_upwards [Set.Ioi_mem_nhds (show x / 2 < x by linarith)] with y hy
```

Then either rewrite the within-filter or use the filter inequality induced by that eventual equality:

```lean
    -- likely API names, depending on local Mathlib:
    --   hsets.nhdsWithin_eq
    --   Filter.EventuallyEq.nhdsWithin_eq
    --   nhdsWithin_congr hsets
    --   hcx.mono_left <filter inequality>
```

The most robust final step is likely:

```lean
    rw [← hsets.nhdsWithin_eq] at hcx
    exact hcx
```

or the equivalent `simpa [hsets.nhdsWithin_eq] using hcx`, depending on the name generated by the local Mathlib version. If the `.nhdsWithin_eq` projection is not available, use `nhdsWithin_congr` / `Filter.EventuallyEq.nhdsWithin_eq` explicitly.

### Endpoint `b = 0`

No special top-level case split on `b = 0` is needed. If `b = 0`, then any `x ∈ Set.Icc 0 b` is `x = 0`, so the `hx0` branch handles the singleton. If the proof does split on `x`, the `x > 0` branch is impossible because `x ≤ b = 0` and `0 ≤ x`.

## Special wrappers in the lap file

These are worthwhile because they are local to lap continuity and avoid duplicating Bridge logic.

### Wrapper using `H1LiftDeriv2JointContinuousBefore`

```lean
/-- Endpoint lap-continuity from zero-right lap trace plus strict `liftDeriv2`
joint continuity. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroRight_and_liftDeriv2_jointContinuousBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (huxx : H1LiftDeriv2JointContinuousBefore u T) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
    h0 (lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore huxx)
```

### Wrapper using the strict-slab representative route

```lean
/-- Endpoint lap-continuity from zero-right lap trace plus a strict positive-time
continuous representative of `liftDeriv2`. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strictSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
    h0
    (lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
      hF hEqInterior)
```

These names are long but consistent with the existing file.

## Should Bridge get a wrapper too?

Not required.

`IntervalChiNegH1Bridge.lean` already has the mechanical wrappers from `H1LapComponentEndpointContinuousBefore` to `H1IdentityRHSComponentsContinuousBefore`, including both `lapEndpoint_and_lapStrict` and the strict-source variants. Once the lap file can produce `H1LapComponentEndpointContinuousBefore` from `H1LapComponentZeroRightContinuous`, callers can compose:

```lean
H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict ...
H1IdentityRHSComponentsContinuousBefore_of_lapEndpoint_and_lapStrict ...
```

A Bridge wrapper that takes `H1LapComponentZeroRightContinuous` directly would be purely ergonomic and would duplicate the composition. If added, it should be one thin theorem only, but I would keep Task73 in `IntervalChiNegH1LapComponentContinuity.lean` unless local use shows the direct Bridge API is repeatedly needed.

## Do not claim current hypotheses produce the zero-right frontier

I found no theorem in the inspected regions producing zero-right lap continuity from current data. The current facts remain exactly as Q3434 summarized:

* `H1InitialEndpointData` controls `H1energy`, not `lapL2sq`.
* `H1UxxL1ContBefore` is positive-time and L¹, not zero-time squared-lap continuity.
* `H1LiftDeriv2JointContinuousBefore` and strict representative theorems are strict positive-time only.
* Bridge wrappers consume `hLap0` / `H1LapComponentEndpointContinuousBefore`; they do not prove it.

Therefore `H1LapComponentZeroRightContinuous` is the right smaller honest frontier, and the theorem converting it plus strict-window continuity into `H1LapComponentEndpointContinuousBefore` is the correct API layer.
