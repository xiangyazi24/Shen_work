# Task 29: Discharge Residual A — ShortTimeBoundedBeforeResidual

## Goal

Create `ShenWork/PDE/P3MoserShortTimeBounded.lean` that proves
`ShortTimeBoundedBeforeResidual` for `intervalDomain`.

## Background

Residual A is defined in `P3MoserFirstCrossingContinuation.lean`:

```lean
def ShortTimeBoundedBeforeResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ∃ τ, 0 < τ ∧ BoundedBeforeOnSubinterval D u τ T

def BoundedBeforeOnSubinterval
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (τ T : ℝ) : Prop :=
  τ ≤ T ∧ ∀ t, 0 < t → t < τ → ∃ M, ∀ x, |u t x| ≤ M
```

## What this means

For `intervalDomain`, the point type is `intervalDomainPoint = Subtype (Icc 0 1)`.
A classical solution has `IsPaper2ClassicalSolution intervalDomain p T u v`, which gives:
- `0 < T`
- `intervalDomainClassicalRegularity T u v` (spatial C², time C¹, joint continuity)
- Positivity: `∀ t x, 0 < t → t < T → 0 < u t x`

We need: `∃ τ > 0, ∀ t ∈ (0, τ), ∃ M, ∀ x : intervalDomainPoint, |u t x| ≤ M`

Note: the M here can depend on t (it's `∃ M` inside the `∀ t`).

## Proof strategy

For each fixed t ∈ (0, T), the classical solution u(t, ·) : intervalDomainPoint → ℝ
needs to be shown bounded. Since `intervalDomainPoint` is `Icc 0 1` (a compact
subset of ℝ), if u(t, ·) is continuous, it's bounded.

**Does the classical regularity give continuity of u(t, ·)?**

`intervalDomainClassicalRegularity` gives:
1. `ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Ioo 0 1)` for t ∈ (0, T)
2. Time differentiability for all x : intervalDomainPoint
3. Joint space-time continuity of the time-derivative

The spatial C² regularity is on the OPEN interval (0,1). We also have Neumann BC
(`normalDeriv (u t) x = 0` at boundary points). For a C² function on (0,1) with
Neumann BC at {0, 1}, the function extends continuously to [0, 1].

**Simplest approach**: Instead of proving continuity of u(t,·) on the closed interval
(which requires connecting the lift's C² to the point function), observe:

For ANY function f : intervalDomainPoint → ℝ where intervalDomainPoint is a finite
type... wait, is it? No, it's `Icc 0 1` which is infinite.

**Better approach**: The positivity field gives `0 < u t x` for all t ∈ (0,T), x.
So u(t,x) > 0 everywhere. But this doesn't give an upper bound.

**Practical approach**: Since intervalDomainPoint = Icc 0 1 is compact (it's a closed
bounded subset of ℝ with the subspace topology), and the classical regularity gives
spatial C² on the interior, the function is bounded IF it extends continuously to the
boundary.

The cleanest way to handle this: introduce a NAMED predicate
`ClassicalSolutionBoundedAtFixedTime` as a residual that captures exactly this:
"at each fixed interior time t, u(t,·) is bounded on the compact domain". Then
prove `ShortTimeBoundedBeforeResidual` conditional on this predicate.

**Alternatively**: Prove it unconditionally using the following argument:
- The lift `intervalDomainLift (u t)` is C² on (0,1) and is 0 outside [0,1]
- Therefore on (0,1) it's continuous, hence bounded on any [ε, 1-ε]
- The Neumann BC gives `deriv = 0` at the boundary (in the sense of one-sided limits)
- Combined with C² on the interior, the function has finite limits at 0 and 1
- Therefore the original function u(t,·) is bounded on [0,1]

This is a real analysis argument. If it's too complex in Lean, leave it as a named
residual.

## Files to read first

1. `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — residual definitions
2. `ShenWork/PDE/IntervalDomain.lean` lines 2746-2760 — `intervalDomainPoint`, `intervalDomainSupNorm`
3. `ShenWork/PDE/IntervalDomain.lean` lines 2768-2860 — `intervalDomainClassicalRegularity`
4. `ShenWork/Paper2/Statements.lean` lines 70-130 — `IsPaper2ClassicalSolution`

## Approach

Try to prove this directly. If the real analysis argument about continuity on the
closed domain is too hard in Lean, then:

1. Define a named residual predicate `ClassicalPointwiseBoundedAtTime` for the
   missing piece (continuity → boundedness on compact domain)
2. Prove `ShortTimeBoundedBeforeResidual` conditional on this predicate
3. Make this AXIOM-CLEAN — use the residual predicate as a named hypothesis, not sorry

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserShortTimeBounded.lean
```
