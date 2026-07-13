ANSWER Q3434 ccfcdd62

# Q3434: H¹ zero-start lap-continuity route audit

## Verdict

`H1LapComponentEndpointContinuousBefore u T` is **not producible from the currently committed infrastructure** at main commit `85bff765def14b15d7c0786880a433d4ea2438fd`.

It remains a genuine extra H²/laplacian trace frontier. The committed code now exposes the seam and provides strict-positive-time bridge wrappers, but it does not prove right-continuity at time zero of

```lean
fun τ => lapL2sq u τ
```

nor does it provide zero-time joint continuity/equality of `liftDeriv2` or a zero-time continuous representative.

## Exact source facts

### 1. The endpoint frontier is explicitly a separate record

In `ShenWork/Paper2/IntervalChiNegH1LapComponentContinuity.lean`:

```lean
structure H1LapComponentEndpointContinuousBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  lap_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b)
```

The file comment also says the strict-window file intentionally stays on strict time windows and claims no continuity at `t = 0`.

### 2. The landed strict lap theorems do not include zero-start windows

The generic integral theorem can be used on any `[a,b]` **if** the representative data on that actual slab are supplied:

```lean
theorem lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
```

But the committed family wrapper is strict-positive-time only:

```lean
theorem lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
```

Likewise, the older joint-continuity route is strict:

```lean
theorem lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h : H1LiftDeriv2JointContinuousBefore u T) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
```

So the landed theorem can cover `[0,b]` only if someone supplies `hFcont` and `hEqInterior` on `Set.Icc 0 b ×ˢ ...`. No current committed producer supplies those zero-start hypotheses.

### 3. Bridge wrappers require the endpoint input; they do not create it

In `ShenWork/Paper2/IntervalChiNegH1Bridge.lean`, the full component record still requires all `0 ≤ a` windows:

```lean
structure H1IdentityRHSComponentsContinuousBefore ... where
  lap_cont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
  ...
```

Task69 added strict and endpoint-upgrade wrappers, but each still takes the endpoint lap continuity as an explicit input. For example:

```lean
theorem H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
    (hLap0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b))
    (hLapStrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    ... :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX
```

and the record-style version:

```lean
theorem H1IdentityRHSComponentsContinuousBefore_of_lapEndpoint_and_lapStrict
    (hLap0 : H1LapComponentEndpointContinuousBefore u T)
    (hLapStrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    ... :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX
```

The representative/joint-continuity bridge wrappers have the same shape: they combine strict lap data with an explicit `hLap0` / `H1LapComponentEndpointContinuousBefore`; they do not prove `hLap0`.

### 4. `H1InitialEndpointData` is H¹ energy data, not lap data

In `ShenWork/Paper2/IntervalChiNegH1InitialContinuity.lean`:

```lean
def H1InitialTraceEnergyTendsto
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  Tendsto (H1energy u) (𝓝[Set.Ioc (0 : ℝ) T] (0 : ℝ))
    (𝓝 (H1InitialEnergy u₀))

structure H1InitialEndpointData
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  tendsto : H1InitialTraceEnergyTendsto u₀ u T
  compatible : H1InitialEnergyCompatibleAtZero u₀ u
```

This is convergence/compatibility for

```lean
H1energy u τ = (1 / 2) * ∫ x in 0..1, (deriv (intervalDomainLift (u τ)) x)^2
```

not for

```lean
lapL2sq u τ = ∫ x in 0..1, (deriv (fun y => deriv (intervalDomainLift (u τ)) y) x)^2
```

The endpoint-data theorems only produce `ContinuousWithinAt (H1energy u) (Set.Ici 0) 0` and `ContinuousOn (H1energy u) (Set.Icc a b)`; they do not mention `lapL2sq`.

### 5. `H1UxxL1ContBefore` is positive-time and L¹, not endpoint squared-lap continuity

`H1UxxL1ContBefore` is a positive-time local continuity statement:

```lean
def H1UxxL1ContBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∀ τ, 0 < τ → τ < T → ∀ ε > 0, ∃ δ > 0,
    ∀ s, |s - τ| < δ → s ∈ Set.Ioo (0 : ℝ) T →
      ∫ x in (0 : ℝ)..1,
        ‖deriv (fun y : ℝ => deriv (intervalDomainLift (u s)) y) x -
          deriv (fun y : ℝ => deriv (intervalDomainLift (u τ)) y) x‖ ≤ ε
```

It has no `τ = 0` case and controls an L¹ difference of `u_xx`, not the squared L² integral `lapL2sq`. In `IntervalChiNegH1ScalarRegularityProducer.lean`, it is used to prove continuity of `H1energy`, not continuity of `lapL2sq`.

### 6. Classical/representative transfer lemmas are strict-positive-time

`IntervalChiNegH1LiftDeriv2Transfer.lean` confirms the same boundary. For example:

```lean
theorem liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
    ... (ha : 0 < a) ... :
    ContinuousOn ... (Set.Icc a b ×ˢ Set.Icc 0 1)
```

```lean
theorem logisticReaction_continuousOn_strictSlab_of_classicalSolution
    ... (ha : 0 < a) ... :
    ContinuousOn ... (Set.Icc a b ×ˢ Set.Icc 0 1)
```

```lean
theorem liftDeriv2_eq_liftDeriv2PhysicalRHS_strictSlab_interior_of_classicalSolution
    ... (ha : 0 < a) ... :
    Set.EqOn ... (Set.Icc a b ×ˢ Set.Ioo 0 1)
```

The theorem names and hypotheses are important: the current classical route never supplies `liftDeriv2` representative continuity/equality on `Set.Icc 0 b ×ˢ ...`.

## Why there is no hidden derivation

A hypothetical derivation would need one of the following at time zero:

1. right-continuity of `lapL2sq u` at zero;
2. joint continuity of `liftDeriv2 u` on `[0,b] × [0,1]`;
3. a continuous representative `F` on `[0,b] × [0,1]` plus interior-spatial equality to `liftDeriv2` on `[0,b] × (0,1)`;
4. an H²/lap trace theorem tying positive-time `u_xx` to the stored zero slice.

The committed APIs provide none of these. They provide H¹ energy endpoint data, positive-time `u_xx` L¹ continuity, and positive-time representative continuity/equality. None implies squared-lap endpoint continuity by type or by analysis.

## Minimal honest additional hypothesis/theorem

The minimal already-exposed frontier is exactly:

```lean
H1LapComponentEndpointContinuousBefore u T
```

If a more atomic producer is desired, introduce only a right-continuity-at-zero hypothesis and combine it with the existing strict theorem:

```lean
/-- Atomic endpoint input: right-continuity at zero of the squared-laplacian
component.  This is H²/lap trace data, not H¹ endpoint data. -/
def H1LapComponentContinuousAtZero
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici (0 : ℝ)) 0
```

Then the honest producer theorem would be:

```lean
theorem H1LapComponentEndpointContinuousBefore_of_continuousAtZero_and_strict
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici (0 : ℝ)) 0)
    (hstrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)) :
    H1LapComponentEndpointContinuousBefore u T
```

Proof idea: for each `[0,b]`, use `h0` at the point `0`; for any point `x ∈ [0,b]` with `x > 0`, choose a strict positive-time subwindow around `x` and apply `hstrict`. This is the exact analogue of the H¹-energy continuity proof pattern, but with a lap-specific zero-continuity input.

An alternative H² representative-style frontier would also be honest:

```lean
theorem H1LapComponentEndpointContinuousBefore_of_zeroSlab_rep
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LapComponentEndpointContinuousBefore u T
```

This would be a direct application of the landed generic theorem `lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous` with `a = 0`, but the hypotheses are precisely the missing H²/lap trace data.

## Recommendation

Keep `H1LapComponentEndpointContinuousBefore u T` as an explicit route frontier. Do not try to derive it from `H1InitialEndpointData`, `IsPaper2ClassicalSolution`, or `H1UxxL1ContBefore`.

The cleanest next analytic seam is either:

* a direct proof of `H1LapComponentEndpointContinuousBefore u T` from a genuine H² initial/lap trace theorem; or
* a smaller endpoint theorem `ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici 0) 0`, then wire it with existing strict-positive-time lap continuity.

The current bridge code is already correctly shaped: it asks for `hLap0` explicitly and uses strict-positive-time infrastructure only where the type signatures justify it.
