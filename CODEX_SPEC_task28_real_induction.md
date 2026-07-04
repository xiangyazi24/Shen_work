# Task 28: Discharge Residual D — FirstCrossingSupremumClosureResidual

## Goal

Create `ShenWork/PDE/P3MoserRealInduction.lean` that proves
`FirstCrossingSupremumClosureResidual` for `intervalDomain`.

## Background

Residual D is defined in `P3MoserFirstCrossingContinuation.lean`:

```lean
def FirstCrossingSupremumClosureResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ShortTimeBoundedBeforeResidual D p →
        SubintervalAssemblyResidual D p →
          ExtensionByContinuityResidual D p →
            IsPaper2BoundedBefore D T u
```

This is the topological closure argument. Given:
- A: `ShortTimeBoundedBeforeResidual` — classical → bounded on (0,τ) for some τ > 0
- B: `SubintervalAssemblyResidual` — assembly → closed-time pointwise bound
- C: `ExtensionByContinuityResidual` — pointwise bound at τ + classical → extends past τ

Conclude: `IsPaper2BoundedBefore D T u` = `∃ M, ∀ t, 0 < t → t < T → D.supNorm (u t) ≤ M`

## Proof strategy (real induction on ℝ)

This is a standard "bootstrap continuation" argument. Define:
```
S = { τ ∈ (0, T] | BoundedBeforeOnSubinterval D u τ T }
```

1. **S is nonempty**: by Residual A, ∃ τ₀ > 0 with bounded before on (0, τ₀)
2. **S is upward-closed** (below T): if τ ∈ S and τ < T, then:
   - Use Residual B (assembly) to get a closed-time bound at τ
   - Use Residual C (extension) to extend past τ
   - So τ + δ ∈ S for some δ > 0
3. **Conclusion**: take τ* = sup S. If τ* < T, then τ* ∈ S (by taking a sequence below τ*), and step 2 extends past τ*, contradiction. So τ* = T.
4. **Convert** `BoundedBeforeOnSubinterval` at τ* = T to `IsPaper2BoundedBefore`

## IMPORTANT: The conversion from BoundedBeforeOnSubinterval to IsPaper2BoundedBefore

`BoundedBeforeOnSubinterval D u T T` gives `∀ t, 0 < t → t < T → ∃ M_t, ∀ x, |u t x| ≤ M_t`
(the M depends on t)

`IsPaper2BoundedBefore D T u` needs `∃ M, ∀ t, 0 < t → t < T → D.supNorm (u t) ≤ M`
(one uniform M)

This requires an additional argument (uniform bound from pointwise bounds). This might
need compactness or an explicit construction. Options:
- If the assembly (Residual B) gives a UNIFORM bound on [0,τ], use that
- Use the fact that D.supNorm (u t) ≤ supNorm of the M from the assembly

If this conversion is non-trivial, leave it as a named residual predicate (call it
`UniformBoundFromPointwiseResidual`) and prove the rest of the real induction
argument. Mark this with a clear TODO.

## Practical approach

Since the argument involves defining a sup and showing it equals T, which requires
careful handling of completeness of ℝ in Lean/Mathlib, the most practical approach
might be to use `Real.sSup` or `sSup` on the set `{τ | BoundedBeforeOnSubinterval ...}`.

Alternatively, use proof by contradiction: assume `IsPaper2BoundedBefore` fails, derive
a maximal time of bounded existence, show it can be extended, contradiction.

If the direct real induction is too complex, an ALTERNATIVE approach: define the
result as a conditional theorem carrying a named residual for the sSup/compactness step.

## Files to read first

1. `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — all residual definitions
2. `ShenWork/Paper2/Statements.lean` lines 350-380 — `IsPaper2BoundedBefore` definition

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`
- Target: AXIOM CLEAN

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserRealInduction.lean
```
