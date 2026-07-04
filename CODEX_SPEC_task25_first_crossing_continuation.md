# CODEX_SPEC Task 25: First-crossing continuation (break circularity)

## Goal

Write a theorem that produces `IsPaper2BoundedBefore` from the existing
assembly infrastructure WITHOUT circular inputs, using the first-crossing
continuation argument.

## The circularity (from task 24's confirmed finding)

```
hBoundedBefore
  → WeightedGradientBridgeBefore (u^rho ≤ M^rho)
  → RelativeMoserInterpolationBefore
  → IntegratedMoserDissipationDropBefore
  → IntegratedMoserFirstCrossingStep
  → all-Lp-bounded
  → hBoundedBefore
```

Task 24 confirmed: the weighted gradient bridge GENUINELY needs a pointwise u^rho bound.
The 1D GN/Young route gives superlinear terms that don't match the interface.

## The continuation argument (Fable's oracle insight)

The key observation: for a CLASSICAL solution, bounded-before on a FINITE time
interval [0,τ] is automatic (classical regularity implies continuity, hence
sup on compact sets is finite). The circularity only arises because we're trying
to prove bounded-before on the FULL interval [0,T).

The continuation argument:

1. Define τ* = sup { τ ∈ (0,T] : the solution is bounded on [0,τ) }
2. By classical regularity, τ* > 0 (solution is smooth near t=0)
3. For any τ < τ*, the solution IS bounded on [0,τ), so:
   - bounded-before holds on [0,τ)
   - the assembly produces the full Moser iteration on [0,τ)
   - Moser iteration gives Lp → L∞ improvement: ‖u(τ)‖_∞ ≤ C * ‖u‖_Lp
   - This is a STRICT improvement: the bound at τ is controlled by the
     initial Lp norm, NOT by the bounded-before value M
4. By continuity, there exists δ > 0 such that bounded-before holds on [0,τ+δ)
5. This contradicts τ* < T, so τ* = T

## What to produce

Write `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean`:

### Step 1: Read the existing infrastructure

Read carefully:
- `ShenWork/PDE/IntervalDomainExistence.lean` — look for `hbounded` instances,
  `IsPaper2BoundedBefore`, `IsBoundedForAllPExpBefore`
- `ShenWork/PDE/P3MoserRegularityProducer.lean` — the crossing step producer
- `ShenWork/PDE/P3MoserBoundedBeforeProducer.lean` — task 21's investigation
- `ShenWork/PDE/P3MoserAssemblyFiller.lean` — the assembly filler
- `ShenWork/Paper2/Statements.lean` — `IsPaper2BoundedBefore` definition

### Step 2: Define the continuation predicate

```lean
def BoundedBeforeOnSubinterval
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (τ T : ℝ) : Prop :=
  τ ≤ T ∧ ∀ t, 0 < t → t < τ → ∃ M, ∀ x, |u t x| ≤ M
```

### Step 3: Write the key components

1. **Short-time bounded-before** from classical regularity:
   ```
   theorem short_time_boundedBefore_of_classical
     (hsol : IsPaper2ClassicalSolution ...)
     : ∃ τ > 0, BoundedBeforeOnSubinterval D u τ T
   ```

2. **Assembly on subinterval** — show the assembly produces results on [0,τ):
   ```
   theorem assembly_on_subinterval
     (hsub : BoundedBeforeOnSubinterval D u τ T)
     (hgap : LpBootstrapEnergyInequalityWithGap ...)
     ... (remaining assembly inputs)
     : ∃ M, ∀ t ∈ Set.Icc 0 τ, ∀ x, |u t x| ≤ M
   ```

3. **Extension lemma** — strict improvement means the bound extends:
   ```
   theorem extension_of_assembly_output
     (hbound_at_τ : ∀ x, |u τ x| ≤ M)
     (hsol : ...)
     : ∃ δ > 0, BoundedBeforeOnSubinterval D u (τ + δ) T
   ```

4. **Main theorem** — by connectedness/real-induction:
   ```
   theorem boundedBefore_of_classical_and_assembly
     : IsPaper2BoundedBefore D T u
   ```

### Step 4: If full proof is too complex

If steps 2-4 are too complex to close in one task, deliver:
- The framework definitions (BoundedBeforeOnSubinterval, etc.)
- Step 1 (short-time) which should be straightforward
- Step 4 as a conditional theorem: "if the assembly works on subintervals, then bounded-before"
- Precise residuals for steps 2-3

## Key Lean patterns

The real-induction / connectedness argument can be formalized via:
- `sSup` of a set of times where the bound holds
- `IsClosed` + `IsOpen` argument (connected set)
- Or direct Zorn-like construction via `csInf`/`csSup`

Check if Mathlib has:
- `IsConnected.eq_univ_of_nonempty_isClopen` or similar
- `Real.isLUB_sSup` for the supremum argument

## Rules

- 0 sorry, 0 custom axiom
- Write ONLY `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean`
- Read the existing infrastructure EXTENSIVELY before writing
- The framework definitions should be compiling even if the hard proofs
  are decomposed into precise residuals
- Add `#print axioms` for all theorems
- Verify: `lake env lean ShenWork/PDE/P3MoserFirstCrossingContinuation.lean`
