# Task: Audit frontier #1 (zeroRightDerivative) for satisfiability

## Context

`IntervalDomainL2SeedZeroRightDerivative u` is defined at
`ShenWork/Paper2/IntervalDomainL2SeedFrontierProducer.lean:79` and requires:

```lean
HasDerivWithinAt (fun τ => intervalDomainLpAbsEnergy 2 u τ)
    (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0) (Set.Ici 0) 0
```

**Potential satisfiability issue:** `deriv` in Mathlib is the TWO-SIDED derivative.
If the energy function E(τ) = intervalDomainLpAbsEnergy 2 u τ is not two-sided
differentiable at τ=0, then `deriv E 0` returns junk value 0.

For `intervalDomainWithInitialSlice u₀ u`:
- At τ > 0: u(τ) = the classical solution, E is smooth → `deriv` = actual derivative
- At τ = 0: u(0) = u₀ (set by definition)
- At τ < 0: u(τ) = the raw mild solution (or undefined) — NOT controlled by the PDE

The statement says `HasDerivWithinAt E (deriv E 0) (Ici 0) 0`. The inner `deriv E 0`
uses the full two-sided derivative, not the one-sided derivative. If E is not
differentiable (two-sided) at 0, then `deriv E 0 = 0` by Mathlib convention.

But `HasDerivWithinAt E 0 (Ici 0) 0` would mean E has right-derivative 0, which
is generically FALSE (the energy has genuine dissipation slope from the PDE).

## Goal

### Step 1: Audit satisfiability

1. Read the EXACT definition of `IntervalDomainL2SeedZeroRightDerivative` at
   `ShenWork/Paper2/IntervalDomainL2SeedFrontierProducer.lean:79`

2. Check ALL consumers of `zeroRightDerivative`:
   ```bash
   rg -n 'zeroRightDerivative\|ZeroRightDerivative' --glob '*.lean'
   ```
   For each consumer, determine: does it use the VALUE `deriv E 0`, or just
   the existence of `HasDerivWithinAt`?

3. Check how `intervalDomainWithInitialSlice u₀ u` behaves for τ < 0:
   Read `P3MoserEnergyContinuity.lean:181` for the definition.
   Then check: is E(τ) = intervalDomainLpAbsEnergy 2 (intervalDomainWithInitialSlice u₀ u) τ
   differentiable (two-sided) at τ = 0?

4. If `intervalDomainWithInitialSlice` uses `if t = 0 then u₀ else u t`, then
   for τ < 0, u(τ) = u(τ) (the raw solution), and E(-ε) = ∫|u(-ε)|^2.
   Check: is lim_{ε→0+} (E(-ε) - E(0))/(-ε) well-defined?

### Step 2: Determine the fix

If the statement IS satisfiable as-is: report WHY (show that E is two-sided differentiable at 0).

If NOT satisfiable (rawMoserDrop déjà vu):
- Report the counterexample/obstruction
- Propose fix: replace `deriv` with `derivWithin (Set.Ici 0)` in the definition
- Check impact: list all consumers that would need updating
- Check Mathlib: `HasDerivWithinAt f d (Ici 0) 0` with `d = derivWithin f (Ici 0) 0`
  is the correct one-sided version

### Step 3: If fix is needed, implement it

Create a file `ShenWork/PDE/P3MoserZeroDerivAudit.lean` that:
1. Documents the issue
2. Provides the corrected definition (using `derivWithin`)
3. Provides a converter from the corrected definition to whatever consumers need
4. If possible, proves the corrected `HasDerivWithinAt` for re-anchored trajectories

Key Mathlib theorem to look for:
`hasDerivAt_interval_left_endpoint_of_tendsto_deriv` — proves existence of
one-sided derivative at an endpoint given interior differentiability + limit of derivative.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserZeroDerivAudit.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- This is an AUDIT task — understanding and reporting is more important than code
- Work only in /Users/huangx/repos/Shen_work/
- Report findings in comments at the top of the file
