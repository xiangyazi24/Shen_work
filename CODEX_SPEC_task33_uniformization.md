# Task 33: Discharge PointwiseUniformizationResidual (+ SubintervalLpPowerBoundResidual)

## Goal

Create `ShenWork/PDE/P3MoserUniformization.lean` that proves
`PointwiseUniformizationResidual` (from T32) and `SubintervalLpPowerBoundResidual`
(from T31) for `intervalDomain`.

Both residuals reduce to the same core analytic fact: **a continuous function
on a compact set is bounded**.

## Background

### PointwiseUniformizationResidual (T32)
```lean
def PointwiseUniformizationResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      BoundedBeforeOnSubinterval D u T T →
        ∃ M, ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M
```

Given: classical solution + per-t pointwise bounds on (0,T).
Prove: ∃ UNIFORM M.

### SubintervalLpPowerBoundResidual (T31)
```lean
def SubintervalLpPowerBoundResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 < τ →
          ∀ p0 > 0, LpPowerBoundedBefore intervalDomain p0 τ u
```

Given: classical solution + bounded-before on [0,τ) + τ > 0.
Prove: ∀ p0 > 0, uniform Lp bound on (0,τ).

## Core proof strategy

### For PointwiseUniformizationResidual:

The classical solution provides joint space-time continuity of u on (0,T) × D.
For intervalDomain, D.Point = Subtype [0,1] which is compact.

Given `BoundedBeforeOnSubinterval D u T T`:
- ∀ t ∈ (0,T), ∃ M_t, ∀ x, |u t x| ≤ M_t

But we already have this from the classical solution's regularity: each time
slice is continuous on [0,1] (compact) hence bounded.

The KEY observation: the function `t ↦ sSup {|u t x| : x}` is continuous
in time (from joint space-time continuity). On any compact [ε, T-ε], it
is bounded. For ε → 0, we use the short-time bound (from T29) that already
gives a bound near t=0.

ACTUAL PROOF (simpler, works in Lean):

Pick ε = T/2. Two intervals:
1. On (0, T/2]: use the short-time bound (from ShortTimeBoundedBeforeResidual
   applied to the classical solution). T29 gives: ∃ τ₀ > 0 and M₀ such that
   |u t x| ≤ M₀ for t ∈ (0, τ₀). Now we need to cover (τ₀, T/2].
   
Actually, the cleanest approach that avoids re-deriving short-time:

We have `BoundedBeforeOnSubinterval D u T T` which gives: for each t ∈ (0,T),
there exists M_t such that |u t x| ≤ M_t for all x.

For intervalDomain specifically: u t is continuous on [0,1] (from
`intervalDomainClassicalRegularity`). The function (t, x) ↦ u t x is
jointly continuous on (0,T) × [0,1].

For ANY compact K ⊆ (0,T), the function (t,x) ↦ |u t x| is continuous
on K × [0,1] (compact), hence bounded by some M_K.

Take K_n = [1/n, T - 1/n] for large enough n. Each gives M_n.
Then (0,T) = ⋃ K_n, and on each K_n the bound is M_n.

BUT this doesn't give a SINGLE uniform M! (M_n might grow as n → ∞.)

The per-t bounds M_t from `BoundedBeforeOnSubinterval` DO exist for all t.
What we need to show is that the function t ↦ M_t can be chosen uniformly.

**SIMPLEST LEAN APPROACH:**

The classical solution gives u : ℝ → D.Point → ℝ with joint continuity
on (0,T) × [0,1]. The `BoundedBeforeOnSubinterval D u T T` says exactly
that each slice is bounded (from the definition). What we need to prove:

Claim: If f : (0,T) → [0,1] → ℝ is jointly continuous AND for each t,
the function f(t, ·) is bounded (i.e., ∃ M_t, ∀ x, |f(t,x)| ≤ M_t),
then f is bounded on (ε, T-ε) × [0,1] for each ε > 0.

This follows from: continuous function on compact set is bounded. But
(0,T) is NOT compact!

**CORRECT APPROACH: Use the full classical solution structure.**

`IsPaper2ClassicalSolution` provides:
- `hsol.positivity`: 0 < T
- `hsol.regularity`: the classical regularity package

The regularity package for intervalDomain includes:
- Joint space-time continuity of u (and v) on (0,T) × [0,1]
- Spatial C² on (0,T) × [0,1]
- Time C¹ on (0,T) × [0,1]

Crucially, the regularity is on the OPEN interval (0,T) for time. The
function u is NOT assumed continuous at t=0.

So for any compact [a,b] ⊂ (0,T), u restricted to [a,b] × [0,1] is
continuous hence bounded. This gives a bound on [a,b] × [0,1].

From `BoundedBeforeOnSubinterval D u T T`, we know each t ∈ (0,T)
has a finite bound M_t. But M_t might blow up as t → 0⁺ or t → T⁻.

**For t → T⁻:** The continuity of u on (0,T) × [0,1] means u is
bounded on [ε, T-ε] × [0,1] for any ε > 0. So the only concern is
near t = 0 and t = T. But the `BoundedBeforeOnSubinterval` only
requires bounds for t ∈ (0,T), not at t=0 or t=T.

**Hmm, this seems hard in general.** Let me think again...

Actually, `BoundedBeforeOnSubinterval D u T T` just says:
- T ≤ T (trivially true)
- ∀ t, 0 < t → t < T → ∃ M, ∀ x, |u t x| ≤ M

This is WEAKER than a uniform bound. The per-t M depends on t.

BUT: for intervalDomain, u t is continuous on [0,1] (compact),
so `∃ M, ∀ x, |u t x| ≤ M` is automatic. The CONTENT of
BoundedBeforeOnSubinterval is trivially true for any function
with continuous spatial slices!

Wait — is that right? Let me check the definition of `BoundedBeforeOnSubinterval`.

Read `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` to check the exact definition.

If BoundedBeforeOnSubinterval just means each time slice is bounded (which it
is for any continuous function on compact [0,1]), then:

- `BoundedBeforeOnSubinterval D u T T` is TRIVIALLY TRUE for classical solutions
- The uniformization `∃ M, ∀ t ∈ (0,T), ∀ x, |u t x| ≤ M` is a genuinely
  new claim that requires an argument about u not blowing up as t → 0 or t → T.

The standard PDE argument: the Moser iteration already shows u stays bounded
(that's what the whole assembly produces). So the uniformization is... circular?

No! The point is:
- The REAL INDUCTION showed: given short-time bounded + right-extension, we get
  `BoundedBeforeOnSubinterval D u T T`
- The right-extension step produces δ-extensions with EXPLICIT bounds from the
  assembly
- Each extension step has its own bound
- The number of steps is finite (T is finite, each step has δ ≥ some minimum)
- So the uniform bound is: max of all step-bounds

BUT THIS STRUCTURAL ARGUMENT IS NOT CAPTURED by the residual decomposition.
The residual just says "given per-t bounds, produce uniform M" — it lost the
information about HOW the per-t bounds were obtained (via finitely many steps).

**RESOLUTION: Prove directly using the classical solution's continuity.**

For ANY compact K ⊂ (0,T), u restricted to K × [0,1] is bounded (continuous
on compact). The issue is (0,T) is open. We need u bounded on ALL of (0,T).

Since classical solutions have finite-time existence on [0,T] and the assembly
produces bounds, the solution DOES have a uniform bound. But proving this from
the abstract `BoundedBeforeOnSubinterval` alone may not be possible.

**PRAGMATIC APPROACH: Leave both as named residuals and note they converge to
the same underlying fact. The downstream assembly already produces the uniform
bound M — the BoundedBefore = ∃ M, ∀ t < T, supNorm(u t) ≤ M — so when
we close the full loop, these residuals get discharged.**

Actually wait — let me re-read `IsPaper2BoundedBefore`:
```
∃ M, ∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ M
```

This IS the uniform bound. And the whole point of the assembly is to PRODUCE
this. So `PointwiseUniformizationResidual` is asking to convert per-t bounds
to a uniform bound — which is what the assembly does!

The cleanest resolution: the uniformization residual IS the gap between
"per-t bounded" (trivial for continuous slices) and "uniformly bounded"
(what the assembly provides). The real induction already showed τ* = T.
What remains is that each Moser iteration step gives a SPECIFIC bound, and
there are finitely many steps, so the max is finite.

This is STRUCTURAL — it needs to track the bounds through the finitely many
extension steps. The cleanest Lean proof would work by well-founded induction
on the gap T - τ, showing that after ≤ k steps (each reducing the gap by
at least a fixed fraction), we have a uniform bound.

**FOR CODEX: Try the simplest approach first.** If `intervalDomainClassicalRegularity`
gives joint continuity on a CLOSED domain like [0,T] × [0,1], then the bound
is immediate (continuous on compact = bounded). Check what the regularity
package provides. If it's only on the open (0,T), then:

Use `isClosed_Icc.isCompact.exists_bound_of_continuousOn` on any [ε, T-ε] × [0,1],
get M_ε. For ε → 0⁺, use the short-time bound (ShortTimeBoundedBeforeResidual gives
M₀ on [0, τ₀)). Then M = max(M₀, M_{T/2}) covers all of (0,T).

Wait, this DOES work! Here's the 2-piece argument:

1. ShortTimeBoundedBeforeResidual gives: ∃ τ₀ > 0, ∃ M₀, ∀ t ∈ (0,τ₀), ∀ x, |u t x| ≤ M₀
   (Actually, it gives BoundedBeforeOnSubinterval which is per-t, not uniform.
    But from T29, the short-time bound IS uniform — check.)
2. On [τ₀/2, T - τ₀/2] × [0,1] (compact, contained in (0,T) × [0,1]), u is
   continuous hence bounded by some M₁.
3. M = max(M₀, M₁) works for all of (0,T).

But step 1 depends on whether the short-time bound is UNIFORM. Let me check T29.

T29's `intervalDomain_shortTimeBoundedBeforeResidual` produces `ShortTimeBoundedBeforeResidual`,
which in T25 is defined as:
```
∃ τ₀ > 0, BoundedBeforeOnSubinterval D u τ₀ T
```
And `BoundedBeforeOnSubinterval` gives per-t bounds, not uniform.

BUT T29 proves this using compactness of [0,1]: for each t near 0, |u t x| ≤ C_t.
The bound C_t = sSup {|u t x| : x ∈ [0,1]} is finite but depends on t.

So step 1 gives NON-UNIFORM bounds near 0. To make them uniform, we need
u continuous on [0, τ₀] × [0,1]... which requires continuity at t=0.

Does the classical solution extend to t=0? Check `IsPaper2ClassicalSolution.regularity`.

If regularity is on (0,T) × [0,1] only (not including t=0), then:
- On (0, τ₀) × [0,1], u is continuous but NOT on the closure [0, τ₀] × [0,1]
- So compactness argument on [ε, τ₀] × [0,1] gives M_ε, but this might blow up as ε → 0

This is genuinely hard. The standard PDE approach would use the initial data regularity
+ heat kernel estimates to control u near t=0. But this is beyond what our formalization
captures.

**PRAGMATIC VERDICT: The uniformization residual is GENUINELY ANALYTIC — it requires
either initial-data control or the full assembly's explicit bound tracking. It cannot
be discharged by a generic compact-continuous argument alone. Keep it as a named residual.**

## Revised goal

Since the uniformization is genuinely non-trivial, the task is:

1. Read T31's `SubintervalLpPowerBoundResidual` and T32's `PointwiseUniformizationResidual`
2. Try the compact-continuous approach: if `IsPaper2ClassicalSolution` provides continuity
   on a CLOSED time interval (including t=0 or at least including initial data control),
   use it to close both residuals.
3. If the classical solution's regularity is only on the OPEN interval (0,T), then:
   - Show that the two residuals are equivalent (or one implies the other)
   - Leave them as named residuals with a clear comment about what's needed
   - Write a bridge theorem showing their relationship

## Files to read first

1. `ShenWork/PDE/P3MoserRealInductionClosure.lean` — PointwiseUniformizationResidual definition
2. `ShenWork/PDE/P3MoserSubintervalInput.lean` — SubintervalLpPowerBoundResidual definition
3. `ShenWork/Paper2/Statements.lean` lines 60-100 — IsPaper2ClassicalSolution (check regularity)
4. `ShenWork/Paper2/Statements.lean` — look for `intervalDomainClassicalRegularity`
5. `ShenWork/PDE/IntervalDomainAPriori*.lean` — check what a priori bounds exist

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserUniformization.lean
```
