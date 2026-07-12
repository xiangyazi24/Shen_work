# Task 35: Close PointwiseUniformizationResidual via Uniform Real Induction

## Goal

Create `ShenWork/PDE/P3MoserUniformRealInduction.lean` that proves
`PointwiseUniformizationResidual` for `intervalDomain` by tracking uniform
bounds through the real induction.

## The Problem

`PointwiseUniformizationResidual` asks:
```
IsPaper2ClassicalSolution → BoundedBeforeOnSubinterval u T T →
  ∃ M, ∀ t ∈ (0,T), ∀ x, |u t x| ≤ M
```

`BoundedBeforeOnSubinterval u T T` gives per-t bounds (∀ t, ∃ M_t, ...) which
are trivially true for classical solutions on intervalDomain. The residual asks
for a UNIFORM M, which is the real content.

## Key Insight

The existing chain already has uniform bounds at each step — they just get
converted to per-t bounds in the `ExtensionByContinuityResidual` interface.
The assembly (`SubintervalAssemblyResidual`) produces `∃ M, ∀ t ∈ [0,τ], ∀ x, |u t x| ≤ M`.

We can prove the uniformization by running a PARALLEL real induction that
tracks the bound explicitly.

## Strategy: Uniform Bounded-Before

Define a stronger predicate:
```lean
def UniformBoundedBefore (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (M τ : ℝ) : Prop :=
  ∀ t, 0 < t → t < τ → ∀ x, |u t x| ≤ M
```

Then prove:

### Step 1: Short-time gives uniform bound

From `ShortTimeBoundedBeforeResidual`, we get `∃ τ₀ > 0, BoundedBeforeOnSubinterval u τ₀ T`.
For intervalDomain, u is jointly continuous on (0,T) × [0,1]. On the compact set
[τ₀/4, τ₀] × [0,1] ⊆ (0,T) × [0,1], u is bounded by some M₀'.
For t ∈ (0, τ₀/4), use the classical solution's initial regularity (or another
compactness argument on [ε, τ₀/4] × [0,1] for any ε > 0).

Actually, the simplest approach: the assembly already gives a uniform bound on [0,τ₀].
So use `SubintervalAssemblyResidual` at τ₀ (with the bootstrap data from T31) to get
`∃ M₀, ∀ t ∈ [0, τ₀], ∀ x, |u t x| ≤ M₀`.

### Step 2: Extension preserves uniform bound (with growth)

Given `UniformBoundedBefore u M τ` and τ < T:
1. Apply the assembly at τ: produces `∃ M', ∀ t ∈ [0, τ], ∀ x, |u t x| ≤ M'`
   (Note: M' might be different from M)
2. Apply extension: produces BoundedBeforeOnSubinterval u (τ+δ) T
3. For intervalDomain, on the compact set [τ/2, τ+δ] × [0,1] ⊆ (0,T) × [0,1],
   u is continuous hence bounded by some M''
4. `UniformBoundedBefore u (max M' M'') (τ+δ)` holds

### Step 3: Real induction with uniform bound

The sSup argument from T32 still applies, but now tracking M:
- S = {τ | ∃ M, UniformBoundedBefore u M τ}
- S is nonempty (from step 1)
- S is bounded above by T
- τ* = sSup S
- If τ* < T: UniformBoundedBefore u M* τ* → extend → UniformBoundedBefore u M** (τ*+δ)
  But τ*+δ > τ* = sSup S, contradiction
- So τ* = T: ∃ M, UniformBoundedBefore u M T = ∃ M, ∀ t ∈ (0,T), ∀ x, |u t x| ≤ M ✓

### The Subtlety: τ* membership

To show `UniformBoundedBefore u M* τ*` where τ* = sSup S:
- For any t ∈ (0, τ*), there exists τ' > t with τ' ∈ S
- So ∃ M', UniformBoundedBefore u M' τ'
- In particular, ∀ x, |u t x| ≤ M'
- But M' depends on which τ' we choose! Different τ' have different M'.

This is the crux: the bound M might grow as we approach τ*. The sSup of S has
τ elements with DIFFERENT M values. Taking the sSup of the M values doesn't
work because there could be infinitely many, and the sequence might not converge.

## Better Strategy: Use assembly bound directly

The assembly (`SubintervalAssemblyResidual`) takes specific bootstrap parameters
(rho, p0, CrossDiffusion, AbstractLpBootstrap, Gap) and produces a bound M.
The bound M depends on these parameters, which are FIXED (from T31's canonical
choice of rho = 2γ, p0 = ...).

Key observation: with FIXED bootstrap parameters, the assembly bound M is
determined by those parameters alone, not by τ. Let's call it M_assembly.

Then:
- Short-time: ∃ τ₀ > 0, assembly at τ₀ gives M_assembly on [0, τ₀]
- Extension: from [0, τ] to [0, τ+δ], the assembly at τ+δ gives the SAME
  M_assembly (because the bootstrap parameters are the same)

Wait, is this true? Does the assembly bound depend on τ or just on the
bootstrap parameters?

Read `SubintervalAssemblyResidual` carefully. It takes:
- IsPaper2ClassicalSolution p T u v (global)
- BoundedBeforeOnSubinterval u τ T (the subinterval)
- CrossDiffusionBootstrapEstimate p τ rho u v (the SPECIFIC bootstrap on [0,τ])
- AbstractLpBootstrapHypothesis u N τ rho p0 (bootstrap on [0,τ])
- LpBootstrapEnergyInequalityWithGap u τ rho p0 (gap on [0,τ])

The bootstrap parameters (rho, p0) are FIXED. But the bootstrap ESTIMATES
(CrossDiffusion, AbstractLpBootstrap, Gap) are for the specific subinterval
[0,τ], and their constants MIGHT depend on τ.

Actually, from T31's proof:
- CrossDiffusionBootstrapEstimate is derived from the classical solution restricted
  to [0,τ] — pointwise in time, so the constants don't depend on τ
- AbstractLpBootstrapHypothesis requires LpPowerBoundedBefore on [0,τ] — the Lp bound
  DOES depend on τ (via SubintervalLpPowerBoundResidual)
- LpBootstrapEnergyInequalityWithGap is from T26 — also pointwise in time

So the only τ-dependent part is the Lp bound in AbstractLpBootstrapHypothesis.
If the Lp bound grows with τ, the assembly bound might grow too.

## Practical Approach

Rather than proving this from first principles, use the EXISTING assembly structure:

1. From the real induction (T32), we have `BoundedBeforeOnSubinterval u T T`
2. This is `∀ t ∈ (0,T), ∃ M_t, ∀ x, |u t x| ≤ M_t`
3. For intervalDomain, M_t = sSup {|u t x| : x ∈ [0,1]}
4. The function t ↦ M_t is the supNorm of each slice
5. We need: ∃ M, ∀ t ∈ (0,T), M_t ≤ M

For this, we need t ↦ M_t to be locally bounded on (0,T).

The function t ↦ sSup {|u t x| : x ∈ [0,1]} IS the supNorm, and for
jointly continuous u, this function is CONTINUOUS in t (by the extreme
value theorem on compact [0,1]).

Actually, t ↦ supNorm(u t) is UPPER SEMICONTINUOUS (the sup of continuous
functions is lsc, so the sup of |u t ·| is... hmm, it's the composition
of continuity properties).

For joint continuity: if (t,x) ↦ u(t,x) is continuous, then for each
fixed t, x ↦ |u(t,x)| is continuous on [0,1] hence attains its max.
The max value as a function of t: t ↦ max_{x ∈ [0,1]} |u(t,x)| is
continuous if u is jointly continuous (standard result: the max of a
jointly continuous function over a compact set is continuous in the
parameter).

So t ↦ supNorm(u t) IS continuous on (0,T)!

A continuous function on (0,T) is bounded on every compact subset [a,b] ⊆ (0,T).
For any ε > 0, supNorm is bounded on [ε, T-ε].
But we need it bounded on ALL of (0,T), including near 0 and T.

Near T: supNorm(u t) is continuous and extends by continuity to any [a, T-ε].
As ε → 0, the bound might grow, but if the limit exists (supNorm(u(T-)) is finite),
it works.

Near 0: similarly, if supNorm(u(0+)) is finite.

These limits existing is exactly the content of the uniform bound — which is
what the Moser iteration proves.

## PRAGMATIC APPROACH FOR LEAN

Since the abstract argument is circular, use the CONCRETE structure:

1. Joint continuity of u on (0,T) × [0,1] gives continuity of t ↦ supNorm(u t)
2. On any [ε, T-ε] ⊂ (0,T), this is bounded (continuous on compact)
3. The assembly gives a uniform bound M_0 on [0, τ₀] (from short-time + assembly)
4. Pick ε = τ₀/2. Then [τ₀/2, T-τ₀/2] × [0,1] is compact and in (0,T) × [0,1].
   The supNorm is bounded by some M_1 on [τ₀/2, T-τ₀/2].
5. For t ∈ (0, τ₀/2]: supNorm(u t) ≤ M_0 (from the assembly bound on [0, τ₀])
6. For t ∈ [τ₀/2, T-τ₀/2]: supNorm(u t) ≤ M_1 (from compactness)
7. For t ∈ [T-τ₀/2, T): need another argument. Use joint continuity on
   [T-τ₀, T-τ₀/4] × [0,1] (compact), get M_2.

Wait, step 7 doesn't work because [T-τ₀/2, T) is not compact (open at T).

The issue near T is genuine. The solution might blow up as t → T. But if
it does, the Moser iteration would have detected it. So the uniform bound
IS a consequence of the assembly, but tracking it through the current
formalization requires restructuring.

## SIMPLEST LEAN APPROACH

Leave `PointwiseUniformizationResidual` as a CONDITIONAL hypothesis when
producing `IsPaper2BoundedBefore`. The full `boundedBefore_of_classical_and_assembly`
theorem (T25) already carries it as a condition, and the downstream chain
handles it.

Actually, looking at T25's `boundedBefore_of_classical_and_assembly`:

```lean
theorem boundedBefore_of_classical_and_assembly
    {D : BoundedDomainData} {p : CM2Params}
    {T : ℝ} {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hshort : ShortTimeBoundedBeforeResidual D p)
    (hassembly : SubintervalAssemblyResidual D p)
    (hextend : ExtensionByContinuityResidual D p) :
    IsPaper2BoundedBefore D T u
```

This already produces `IsPaper2BoundedBefore` (= uniform bound) from the 4 residuals.
ALL 4 residuals are now discharged (A=T29, B=T27, C=T30, D=T28+T32+...).

Wait — D is `FirstCrossingSupremumClosureResidual`, which IS the one that needs
`PointwiseUniformizationResidual`. Let me trace the full dependency again.

T25: `boundedBefore_of_classical_and_assembly` needs A, B, C, D
D: `FirstCrossingSupremumClosureResidual` — from T28
T28: `intervalDomain_FirstCrossingSupremumClosureResidual` needs
  SubintervalMoserInputResidual + FirstCrossingPointwiseUniformClosureResidual
FirstCrossingPointwiseUniformClosureResidual — from T32
T32: needs PointwiseUniformizationResidual

So the chain bottom-out is PointwiseUniformizationResidual. This is the ONLY
remaining piece.

## THE RIGHT APPROACH

The right approach is to NOT use the per-t `BoundedBeforeOnSubinterval` in the
real induction at all. Instead, track the UNIFORM bound throughout.

Create a self-contained proof of `PointwiseUniformizationResidual` that:

1. Gets `BoundedBeforeOnSubinterval u T T` (the hypothesis)
2. For intervalDomain, asserts joint continuity of u on (0,T) × [0,1]
3. Uses the compactness argument on FINITE UNIONS of compact subsets that
   cover (0,T):
   - For any n, let K_n = [1/n, T-1/n] × [0,1] (compact)
   - u is bounded on K_n by M_n (continuous on compact)
   - BUT we need finitely many K_n to cover (0,T)...
   
Actually, (0,T) = ⋃_n K_n is an infinite union. We need a finite subcover.

THE CRITICAL FACT: (0,T) is NOT compact, so we can't get a finite subcover.
The function CAN blow up at the endpoints.

This means: `PointwiseUniformizationResidual` is NOT provable from just
joint continuity on (0,T) × [0,1]. It requires additional PDE-specific
information (the Moser iteration bounds).

## CORRECT SOLUTION

The correct solution is to strengthen the real induction to carry a uniform bound,
using `SubintervalAssemblyResidual`'s output directly.

Define:
```lean
def UniformBoundedBeforeStrong (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (M τ T : ℝ) : Prop :=
  τ ≤ T ∧ ∀ t, 0 < t → t ≤ τ → ∀ x, |u t x| ≤ M
```
(Note: CLOSED at τ, using the assembly's closed [0,τ] bound.)

Then prove the analog of the real induction:
1. Short-time + assembly → UniformBoundedBeforeStrong M₀ τ₀ T
2. Extension: from UniformBoundedBeforeStrong M τ T with τ < T,
   apply assembly at τ+δ → UniformBoundedBeforeStrong M' (τ+δ) T
3. sSup → τ* = T
4. UniformBoundedBeforeStrong M* T T → ∀ t ∈ (0,T), ∀ x, |u t x| ≤ M*

The key difference from the existing chain: step 2 needs the assembly to give
a bound M' that works on ALL of [0, τ+δ]. This comes from combining:
- M on [0, τ] (from the induction hypothesis)
- Assembly bound on [0, τ+δ] (from SubintervalAssemblyResidual at τ+δ)

Take M' = the assembly's output bound (which already covers [0, τ+δ]).

This should work! The assembly bound covers the closed interval [0, τ+δ],
so M' ≥ M on [0, τ] (or we take max).

## Implementation plan

1. Define UniformBoundedBeforeStrong
2. Prove short-time + assembly → initial uniform bound
3. Prove extension step with uniform bound
4. Run the sSup real induction (same as T32 but with uniform bound)
5. Conclude PointwiseUniformizationResidual

This file should import:
- P3MoserRealInductionClosure (for PointwiseUniformizationResidual)
- P3MoserSubintervalInput (for SubintervalMoserInputResidual, canonical rho/p0)
- P3MoserFirstCrossingContinuation (for SubintervalAssemblyResidual, ExtensionByContinuityResidual, ShortTimeBoundedBeforeResidual)
- P3MoserShortTimeBounded (intervalDomain_shortTimeBoundedBeforeResidual)
- P3MoserContinuityExtension (intervalDomain_extensionByContinuityResidual)

The proof needs to combine:
- T31's SubintervalMoserInputResidual (conditional on SubintervalLpPowerBoundResidual)
- T33's bridge (PointwiseUniformizationResidual → SubintervalLpPowerBoundResidual)

Wait — this is CIRCULAR! T33 shows PointwiseUniform → SubintervalLp. And
SubintervalMoserInput (T31) needs SubintervalLp. So:
- SubintervalMoserInput needs SubintervalLp needs PointwiseUniform
- But PointwiseUniform is what we're trying to prove!

Hmm. The circularity is: to get the uniform bound, we need the assembly's output.
To feed the assembly (via SubintervalMoserInput), we need the Lp bound. To get
the Lp bound, we need the uniform bound. Circular.

This is the SAME circularity that T25 was supposed to break! But it wasn't
fully broken — it was deferred to the uniformization residual.

The way OUT: the assembly's SubintervalAssemblyResidual does NOT require
PointwiseUniformizationResidual. It requires BoundedBeforeOnSubinterval
(per-t, trivially true) + bootstrap data. The bootstrap data (from T31)
requires SubintervalLpPowerBoundResidual. And SubintervalLpPowerBoundResidual
requires PointwiseUniformizationResidual (from T33).

So the ACTUAL dependency is:
SubintervalLpPowerBoundResidual ← PointwiseUniformizationResidual (T33)

If we can discharge SubintervalLpPowerBoundResidual WITHOUT going through
PointwiseUniformizationResidual, we break the cycle.

SubintervalLpPowerBoundResidual asks: given classical solution + bounded-before
on [0,τ) + τ > 0, produce LpPowerBoundedBefore on [0,τ).

LpPowerBoundedBefore on [0,τ) means: ∃ C, ∀ t ∈ (0,τ), integral(|u|^p) ≤ C.

For intervalDomain, each time slice has integral(|u|^p) ≤ M_t^p (since domain
has measure 1 and |u| ≤ M_t). But we need UNIFORM C across t.

This is the same uniformization problem! The Lp version is equivalent to the L∞
version (on measure-1 domain).

So the circularity is genuine. To break it, we need to bypass T33's bridge
and prove SubintervalLpPowerBoundResidual DIRECTLY, without going through
the uniform L∞ bound.

## DIRECT APPROACH TO SubintervalLpPowerBoundResidual

For a classical solution on intervalDomain, we need:
∃ C, ∀ t ∈ (0,τ), ∫_{[0,1]} |u(t,x)|^p dx ≤ C

The function t ↦ ∫|u(t,·)|^p is continuous on (0,τ) (from joint space-time
continuity and dominated convergence). On [ε, τ-ε] ⊂ (0,τ), it's bounded
(continuous on compact).

For a GLOBAL bound on (0,τ): if we knew the integral stays bounded as
t → 0+ and t → τ-, we'd be done. The Moser iteration gives this.

But wait — the short-time step (T29) already gives boundedness near t = 0.
The bound near t = τ comes from the assembly.

Actually, the INITIAL DATA bound helps: if the initial datum u₀ has bounded
Lp norm, and the solution is continuous in time (in Lp), then the Lp norm
stays bounded near t = 0.

Let me look at what's available from the classical solution.

## Files to read first

1. ShenWork/PDE/P3MoserRealInduction.lean — current residual definitions
2. ShenWork/PDE/P3MoserFirstCrossingContinuation.lean — SubintervalAssemblyResidual
3. ShenWork/PDE/P3MoserSubintervalInput.lean — SubintervalLpPowerBoundResidual
4. ShenWork/PDE/P3MoserUniformization.lean — T33 bridge
5. ShenWork/Paper2/Statements.lean — IsPaper2ClassicalSolution, LpPowerBoundedBefore
6. ShenWork/PDE/IntervalDomainAPriori*.lean — available a priori bounds

## Approach (choose the cleanest one that compiles)

OPTION A: Prove PointwiseUniformizationResidual by running a UNIFORM real
induction. This requires proving that SubintervalAssemblyResidual's bound
is attainable WITHOUT the Lp seed from SubintervalLpPowerBoundResidual.
Check if SubintervalAssemblyResidual can work with the trivially-true
BoundedBeforeOnSubinterval alone (without the full bootstrap data).

OPTION B: Prove SubintervalLpPowerBoundResidual DIRECTLY, without T33's
bridge (bypassing the uniform L∞ bound). Use the joint continuity of
t ↦ ∫|u|^p and compactness on interior subsets.

OPTION C: Strengthen the INITIAL predicate. Instead of BoundedBeforeOnSubinterval
(per-t, trivially true), use UniformBoundedBeforeStrong (uniform, with
explicit M). Modify the real induction to track M explicitly. This gives
the uniform bound as an output of the real induction itself.

OPTION D: Leave as a named residual and document clearly. If none of
A/B/C can be closed, write a theorem that states the exact remaining gap.

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`
- If you can't close the full uniformization, write whatever partial progress
  you can (bridges, equivalences, reductions) and leave the irreducible core
  as a named residual.

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserUniformRealInduction.lean
```
