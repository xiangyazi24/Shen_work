# Task 30: Discharge Residual C — ExtensionByContinuityResidual

## Goal

Create `ShenWork/PDE/P3MoserContinuityExtension.lean` that proves
`ExtensionByContinuityResidual` for `intervalDomain`.

## Background

Residual C is defined in `P3MoserFirstCrossingContinuation.lean`:

```lean
def ExtensionByContinuityResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T τ M : ℝ} {u v : ℝ → D.Point → ℝ},
    τ < T →
      IsPaper2ClassicalSolution D p T u v →
        (∀ x, |u τ x| ≤ M) →
          ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
            BoundedBeforeOnSubinterval D u (τ + δ) T
```

## What this means

Given a classical solution and a pointwise bound at time τ < T, we need to show
that u stays bounded on some interval [τ, τ + δ) for some δ > 0, and τ + δ ≤ T.

Combined with bounded-before on [0, τ), this gives bounded-before on [0, τ + δ).

## Proof strategy

`BoundedBeforeOnSubinterval D u (τ + δ) T` is:
```
τ + δ ≤ T ∧ ∀ t, 0 < t → t < τ + δ → ∃ M, ∀ x, |u t x| ≤ M
```

The tricky part: we need to show u is bounded on each time slice t ∈ (0, τ + δ).
For t < τ, this follows from the existing bounded-before... BUT we don't have
bounded-before on [0, τ) as a hypothesis — we only have the pointwise bound AT τ.

Wait, re-reading the definition: `ExtensionByContinuityResidual` only provides
the bound AT τ and produces bounded-before on [0, τ + δ). So the proof needs to
show that knowing u(τ, ·) ≤ M AND the classical solution property, u stays bounded
near τ.

The argument uses TIME CONTINUITY of the classical solution:
1. At time τ, |u(τ, x)| ≤ M for all x
2. By time continuity of u at τ (which comes from classical regularity), for each x,
   |u(t, x)| is close to |u(τ, x)| when t is close to τ
3. More precisely: fix any x. The function t ↦ u(t, x) is differentiable at τ (from
   classical regularity). So it's continuous at τ. Hence |u(t, x)| ≤ M + 1 for t in
   (τ - δ_x, τ + δ_x).
4. Since we need this for ALL x ∈ intervalDomainPoint = Icc 0 1 (compact), and the
   time derivative field is jointly continuous (from classical regularity), we can get
   a UNIFORM δ.

**Practical approach in Lean:**

The key fact needed: at each fixed x, `t ↦ u t x` is differentiable (hence continuous)
at τ ∈ (0, T). This comes directly from `intervalDomainClassicalRegularity`:
```
∀ x : intervalDomainPoint, ∀ t ∈ Ioo 0 T →
  DifferentiableAt ℝ (fun s => u s x) t
```

From differentiability → continuity → for each x, ∃ δ_x such that |u(t,x) - u(τ,x)| < 1
for t ∈ (τ - δ_x, τ + δ_x).

For the uniform δ: use the joint continuity field of classical regularity, or use a
compactness argument over x.

**IMPORTANT NOTE**: `BoundedBeforeOnSubinterval D u (τ + δ) T` asks for boundedness
on ALL of (0, τ + δ), not just (τ, τ + δ). So the theorem actually needs to show
that IF we already have bounded-before on (0, τ) (from the previous step in the
continuation) AND the extension holds on (τ, τ + δ), THEN bounded-before on (0, τ+δ).

But wait — looking at the definition again, the theorem `ExtensionByContinuityResidual`
PRODUCES `BoundedBeforeOnSubinterval D u (τ + δ) T` which includes the FULL (0, τ+δ).
But its input is only the bound at τ, not bounded-before on (0, τ).

This means the theorem should probably use T25's existing `boundedBeforeOnSubinterval_extend_right`
which does:
```
theorem boundedBeforeOnSubinterval_extend_right
    (hprev : BoundedBeforeOnSubinterval D u τ T)
    (hδT : τ + δ ≤ T)
    (hnew : ∃ M, ∀ t, τ ≤ t → t < τ + δ → ∀ x, |u t x| ≤ M) :
    BoundedBeforeOnSubinterval D u (τ + δ) T
```

But `ExtensionByContinuityResidual` doesn't take `BoundedBeforeOnSubinterval D u τ T`
as input. It only takes the bound at τ. So either:
1. The residual definition assumes the caller provides bounded-before on (0, τ) separately
   and the residual only needs to show the extension part (τ, τ+δ)
2. Or the residual produces bounded-before on (0, τ+δ) from just the bound at τ

Looking at how it's used in `boundedBefore_of_classical_and_assembly`, the caller
(Residual D's proof) would combine the existing bounded-before on (0, τ) with the
extension result.

So the correct reading is: `ExtensionByContinuityResidual` produces
`BoundedBeforeOnSubinterval D u (τ + δ) T`, which means FULL bounded-before on (0, τ+δ).
It gets this by:
- For t ∈ (0, τ): each time slice is bounded (this was established in the previous
  continuation step, but we don't have it as an explicit hypothesis here)

Hmm, this is a design issue. Let me re-read the definition...

Actually, looking at T25's actual code, `BoundedBeforeOnSubinterval D u (τ + δ) T`
really is the full (0, τ+δ) condition. And the extension residual only takes the bound
at τ as input.

The pragmatic approach: the extension residual should produce the bounded-before on
(0, τ+δ) by:
1. For t < τ: the bound at τ plus classical regularity implies u is bounded at all
   EARLIER times too (by the maximum principle or just by continuity in time)
2. For t ∈ [τ, τ+δ): by continuity at τ

Actually this is wrong. Knowing u(τ,·) ≤ M doesn't tell us u(0.5τ, ·) ≤ anything.

The real usage pattern: in the continuation argument (Residual D), the caller already
has `BoundedBeforeOnSubinterval D u τ T` and uses Residual C to extend. But Residual C
doesn't receive the previous bounded-before as input.

**SIMPLEST FIX**: Make the extension theorem produce just the NEW part: ∃ δ > 0 such
that ∀ t ∈ [τ, τ+δ), ∀ x, |u t x| ≤ M+1. Then the caller uses
`boundedBeforeOnSubinterval_extend_right` to combine.

But this doesn't match the residual definition... Let me think again.

OK, re-reading the residual definition one more time:
```
∃ δ, 0 < δ ∧ τ + δ ≤ T ∧ BoundedBeforeOnSubinterval D u (τ + δ) T
```

This DOES produce the full bounded-before on (0, τ+δ). The proof must:
- Show u is bounded on each time slice t ∈ (0, τ+δ)
- For t < τ: by the same classical regularity argument as Residual A (each time slice
  is bounded because it's a C² function on a bounded domain)
- For τ ≤ t < τ+δ: by continuity in time from the bound at τ

So the proof of Residual C essentially subsumes the proof of Residual A for any fixed
time. The key is: each time slice of a classical solution on intervalDomain is bounded.

**APPROACH**: Define a helper predicate `ClassicalSliceBounded`:
```
∀ t ∈ (0, T), ∃ M, ∀ x, |u t x| ≤ M
```
and carry it as a residual if needed. Then the extension is straightforward.

## Files to read first

1. `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — residual definitions + monotone + extend
2. `ShenWork/PDE/IntervalDomain.lean` lines 2768-2860 — classical regularity
3. `ShenWork/Paper2/Statements.lean` lines 70-130 — classical solution

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`
- If the full continuity argument is too complex, define a named residual predicate
  for the missing piece and prove the extension conditional on it. AXIOM-CLEAN.

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserContinuityExtension.lean
```
