# CODEX_SPEC Task 22: p-dependent ε refactor for LpBootstrapEnergyInequalityWithGap

## Critical context

The current energy inequality in `IntervalDomainLpBootstrapEnergyInequality.lean`
uses a FIXED ε choice:
```
eps = A0 / (2 * (chiBound + 1))
```
where A0 = pExp - 1, chiBound = |χ₀| * (pExp - 1).

This causes `pExp * Acoef → 2 from below` as pExp → ∞ when χ₀ ≠ 0.
The gap condition `2 < pExp * A` in `LpBootstrapEnergyInequalityWithGap`
(P3MoserIntegratedDissipationPDEv2.lean:30) is then UNSATISFIABLE for
χ₀ ≥ 1, making ALL downstream theorems vacuously true.

## The fix

Use a p-dependent ε:
```
eps = A0 / (pExp * (chiBound + 1))
```

This gives `pExp * Acoef → 4 from below`, making the gap provable for
all pExp ≥ p*(χ₀) with p* explicit.

Numerical verification (Python, confirmed):
- χ₀ = 0:   gap holds for all p > 2 (unchanged)
- χ₀ = 0.5: gap holds for p ≥ 3
- χ₀ = 1.0: gap holds for p ≥ 3.1
- χ₀ = 2.0: gap holds for p ≥ 5

## What to produce

Write `ShenWork/PDE/P3MoserEnergyGapRefactor.lean`:

1. Define `AcoefPDep` — the coefficient with p-dependent ε:
   ```
   AcoefPDep (pExp chi0 : ℝ) : ℝ :=
     let A0 := pExp - 1
     let chiBound := |chi0| * A0
     let eps := A0 / (pExp * (chiBound + 1))
     let cGrad := (pExp / 2) ^ 2
     (A0 - chiBound * eps) / cGrad
   ```

2. Prove `pExp * AcoefPDep pExp chi0 > 2` for sufficiently large pExp:
   - Show `pExp * AcoefPDep pExp chi0 = 4 * (pExp - 1) / pExp * (c + pExp) / (c + 1)`
     where c = |chi0| * (pExp - 1). (Simplify the expression algebraically.)
   - Show the limit is 4 and find the explicit threshold p*(χ₀).

3. Prove that the energy inequality STILL HOLDS with the new ε choice:
   - The energy inequality proof uses Young's inequality with parameter ε.
   - Changing ε only affects the complementary constant 1/(4ε) on the
     mass/residual term. With eps ~ 1/p, this constant grows like p —
     but that's OK because the Moser iteration absorbs polynomial-in-p
     constants.
   - Write a theorem `lpBootstrapEnergyInequalityWithGap_of_classical_pDep`
     with the same signature as the existing energy inequality producer
     but using AcoefPDep.

4. Bridge lemma: show that for χ₀ = 0, the two definitions agree (or at
   least the gap condition is equivalent).

## Migration strategy (protect compiled tower)

DO NOT modify `IntervalDomainLpBootstrapEnergyInequality.lean` or its
existing definitions. Instead:
- Define the new coefficients alongside the old ones.
- Write bridge/conversion theorems.
- The assembly filler can then use the new producer.

## Rules

- 0 sorry, 0 custom axiom
- Write ONLY `ShenWork/PDE/P3MoserEnergyGapRefactor.lean`
- The algebraic part should be verified first (compute the expressions,
  check they simplify correctly)
- Add `#print axioms` for all theorems
- Verify: `lake env lean ShenWork/PDE/P3MoserEnergyGapRefactor.lean`

## Key files to read first

- `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean` lines 300-590
  (the existing energy inequality proof, coefficient definitions)
- `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` lines 30-70
  (the gap definition and its consumer)
- `ShenWork/PDE/P3MoserAssemblyFiller.lean` lines 60-75 (hGap hypothesis)
