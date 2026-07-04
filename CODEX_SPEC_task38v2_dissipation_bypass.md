# Task 38v2: IntegratedMoserDissipationDropBefore bypass (interior FTC + limit)

## Goal

OVERWRITE `ShenWork/PDE/P3MoserDissipationFromClassical.lean` with a NEW file that produces
`IntegratedMoserDissipationDropBefore intervalDomain u T rho p0` from:
- `hsol : IsPaper2ClassicalSolution intervalDomain params T u v`
- `hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0`
- `hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0`
- `hEndCont : IntervalDomainPowerEnergyEndpointContinuity u T p0`

WITHOUT taking:
- `IntegratedMoserEnergyWindowFTC` (the frontier we bypass)
- `IntegratedMoserFirstCrossingRegularity` (contains gradientTimeIntegrable — another frontier)

## Why v1 failed

v1 produced a re-wrapper that still took `hFTC` and `hreg` as inputs.
Root cause: the spec pointed to `IntervalDomainExistence.lean` for the interior
derivative theorem, but it lives in `IntervalDomainLpTimeLeibniz.lean:86`.

## Critical API (read these FIRST)

1. **`intervalDomainPowerEnergy_hasDerivAt`** at `ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean:86`
   ```
   theorem intervalDomainPowerEnergy_hasDerivAt
       {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
       (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
       {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
       HasDerivAt (fun s => intervalDomainPowerEnergy q u s)
         (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u t y) t
   ```
   This gives HasDerivAt for the energy at EVERY interior point t ∈ (0,T).

2. **`intervalDomainPowerDeriv_continuousOn`** at `ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean:49`
   ```
   theorem intervalDomainPowerDeriv_continuousOn
       {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
       (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
       ContinuousOn (Function.uncurry (intervalDomainPowerDeriv q u))
         (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
   ```
   Joint continuity of the integrand on (0,T) × [0,1].

3. **`intervalDomain_integratedMoserEnergy_eq_powerEnergy`** at `ShenWork/PDE/P3MoserEnergyContinuity.lean:991`
   ```
   theorem intervalDomain_integratedMoserEnergy_eq_powerEnergy
       (p : ℝ) (u : ℝ → intervalDomain.Point → ℝ) :
       (fun t => integratedMoserEnergy intervalDomain u p t) =
         fun t => intervalDomainPowerEnergy p u t
   ```
   The two energy definitions are the same function.

4. **`ContinuousOn.intervalIntegrable`** in Mathlib (`MeasureTheory.Integral.IntervalIntegral.Basic`)
   ```
   theorem ContinuousOn.intervalIntegrable {u : ℝ → E} {a b : ℝ}
       (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u volume a b
   ```

5. **`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`** — the FTC in Mathlib
   ```
   theorem integral_eq_sub_of_hasDerivAt_of_le (hab : a ≤ b)
       (hcont : ContinuousOn f (Icc a b))
       (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
       (hint : IntervalIntegrable f' volume a b) :
       ∫ x in a..b, f' x = f b - f a
   ```

6. **`intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity`** at `ShenWork/PDE/P3MoserEnergyContinuity.lean` (search for it)
   ```
   ContinuousOn (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
     (Set.Icc (0 : ℝ) T)
   ```
   Energy is ContinuousOn the FULL closed interval [0,T] (including endpoints).

7. **`intervalDomain_integratedMoserEnergyNonnegativity_of_classical`** — produces non-negativity of energy

8. **Relative interpolation integration**: `RelativeMoserInterpolationBefore` gives pointwise
   `E_{p+ρ}(t) ≤ ε·G(t) + Cε·E(t)` for t ∈ (0,T). Integration over any window gives
   `∫E_{p+ρ} ≤ ε·∫G + Cε·∫max(1,E)` (since E ≤ max(1,E)).

## Proof strategy (THREE-CASE STRUCTURE)

Produce `IntegratedMoserDissipationDropBefore` by proving the inequality for each case:

### Case A: Interior (0 < t₁ ≤ t₂ < T)

Everything is compact inside (0,T). Steps:

1. **HasDerivAt**: `intervalDomainPowerEnergy_hasDerivAt` at each s ∈ (t₁, t₂) ⊂ (0,T)

2. **IntervalIntegrable of derivative on [t₁, t₂]**: The derivative at s equals
   `∫ y in 0..1, intervalDomainPowerDeriv q u s y` (from HasDerivAt).
   By `intervalDomainPowerDeriv_continuousOn`, the integrand is jointly continuous on (0,T)×[0,1].
   For fixed y, the slice is ContinuousOn (0,T).
   The parametric integral `s ↦ ∫ y, f(s,y) dy` is ContinuousOn (0,T).
   On compact [t₁,t₂] ⊂ (0,T): ContinuousOn → IntervalIntegrable.

   **Lean approach**: Use `HasDerivAt.continuousAt` to get ContinuousAt of the energy derivative
   at each s ∈ (t₁, t₂) ⊂ (0,T). This gives ContinuousOn of the derivative on (t₁,t₂).
   Since [t₁,t₂] ⊂ (0,T) (closed, compact), and the function is ContinuousOn on the open set
   (0,T) which contains [t₁,t₂], restrict to get ContinuousOn [t₁,t₂].
   Apply `ContinuousOn.intervalIntegrable`.

3. **ContinuousOn of energy on [t₁,t₂]**: From `intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity` restricted.

4. **FTC**: `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` gives ∫E' = E(t₂) - E(t₁).

5. **Pointwise inequality**: `LpBootstrapEnergyInequalityWithGap` gives
   (1/p)E'(s) + A·G(s) + B·E(s) ≤ K·E_{p+ρ}(s) + L for s ∈ (0,T).
   Multiply by p, integrate over [t₁,t₂], combine with FTC.

6. **Absorption**: Use relative interpolation to absorb K·∫E_{p+ρ}.

### Case B: Right boundary (0 < t₁, t₂ = T)

Apply Case A with t₂ₙ = T - 1/(n+1) for n = 0,1,2,...

The inequality at [t₁, t₂ₙ] holds with the SAME constant C (C depends on p, not on the window).
Take n → ∞:
- E(t₂ₙ) → E(T) by `IntervalDomainPowerEnergyEndpointContinuity.atRight`
- ∫_{t₁}^{t₂ₙ} G is INCREASING (G ≥ 0) and bounded ⟹ converges
- ∫_{t₁}^{t₂ₙ} max(1,E) → ∫_{t₁}^{T} max(1,E) (monotone convergence, max(1,E) ≥ 1)

Use `le_of_tendsto` or `ge_of_tendsto` to pass the inequality to the limit.

### Case C: Left boundary (t₁ = 0, t₂ > 0)

Apply Case A (or B if t₂ = T) with t₁ₙ = 1/(n+1) for n = 0,1,2,...

The inequality at [t₁ₙ, t₂] holds with the SAME constant C.
Take n → ∞:
- E(t₁ₙ) → E(0) by `IntervalDomainPowerEnergyEndpointContinuity.atZero`
- ∫_{t₁ₙ}^{t₂} G is INCREASING and bounded ⟹ converges
- ∫_{t₁ₙ}^{t₂} max(1,E) → ∫_{0}^{t₂} max(1,E) (monotone convergence)

### Trivial case: t₁ = t₂ (all integrals = 0, difference = 0)

## What to prove

### Main theorem

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_classical_bypass
    {params : CM2Params}
    {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hEndCont : IntervalDomainPowerEnergyEndpointContinuity u T p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

### If full theorem is too hard

Deliver TWO theorems:

1. **Interior theorem** (should be achievable):
```lean
theorem intervalDomain_integratedMoserDissipationDrop_interior
    ...same hypotheses...
    (p : ℝ) (hp : p0 ≤ p) :
    ∃ C, 0 ≤ C ∧
      ∀ t1 ∈ Set.Ioo (0 : ℝ) T, ∀ t2 ∈ Set.Ioo t1 T,
        integratedMoserEnergy intervalDomain u p t2 -
            integratedMoserEnergy intervalDomain u p t1 +
          2 * ∫ s in t1..t2,
            integratedMoserGradientEnergy intervalDomain u p s ≤
        C * p * ∫ s in t1..t2,
          max 1 (integratedMoserEnergy intervalDomain u p s)
```

2. **Report what blocks the limit extension** — be specific: which Lean tactic/API is missing.

## Imports

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2
import ShenWork.PDE.P3MoserDissipationShape
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz  -- THIS IS NEW AND CRITICAL
import ShenWork.Paper2.IntervalDomainMoserClosure
```

You may add additional Mathlib imports as needed.

## Lean proof hints

### Getting HasDerivAt for integratedMoserEnergy from intervalDomainPowerEnergy

```lean
have hYeq := intervalDomain_integratedMoserEnergy_eq_powerEnergy p u
-- hYeq : (fun t => integratedMoserEnergy ...) = (fun t => intervalDomainPowerEnergy ...)
have hpow := intervalDomainPowerEnergy_hasDerivAt (q := p) hsol ⟨hs0, hsT⟩
-- hpow : HasDerivAt (fun s => intervalDomainPowerEnergy p u s) (...) s
-- Rewrite to get HasDerivAt for integratedMoserEnergy:
rw [hYeq] at ...  -- or use congrFun hYeq s
```

### Getting IntervalIntegrable of the derivative

The derivative `deriv (fun t => integratedMoserEnergy D u p t) s` equals
`∫ y in 0..1, intervalDomainPowerDeriv p u s y` at each s ∈ (0,T) (from HasDerivAt).

Since HasDerivAt implies ContinuousAt of the function AND identifies the derivative,
we know `deriv f` is continuous at each interior point. More precisely:

```lean
-- At each s ∈ (0,T), HasDerivAt gives the derivative exists
-- HasDerivAt f v s → deriv f s = v
-- The RHS v = ∫ y, powerDeriv s y is continuous in s (from joint continuity)
-- Hence deriv f is ContinuousOn (0,T)
-- On [t₁, t₂] ⊂ (0,T): ContinuousOn → IntervalIntegrable
```

### Integrating the pointwise inequality

The pointwise inequality holds for all s ∈ (0,T). On [t₁,t₂] ⊂ (0,T):
```lean
-- hfull s hs0 hsT gives the pointwise bound for each s
-- Use intervalIntegral.integral_mono_of_nonneg or similar to integrate
-- Or: compute ∫E' from FTC, then bound using ∫(RHS) ≥ ∫(LHS) = ∫E' + coeff·∫G
```

### For the limit argument

```lean
-- Use le_of_tendsto or ge_of_tendsto_of_frequently:
-- If f n → L and ∀ n, f n ≤ C, then L ≤ C
-- Symmetrically: if ∀ n, f n ≥ g n, f n → L, g n → M, then L ≥ M

-- For monotone integrals:
-- ∫_{1/n}^{t₂} f → ∫_{0}^{t₂} f  (for f ≥ 0 integrable)
-- Use: ∫₀^{t₂} f = ∫₀^{1/n} f + ∫_{1/n}^{t₂} f (integral_add_adjacent_intervals)
-- and ∫₀^{1/n} f → 0 (integral over shrinking interval of integrable function)
```

## Constraints

- NO sorry, NO axiom
- `#print axioms` must give only `[propext, Classical.choice, Quot.sound]`
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3MoserDissipationFromClassical`
- If the full theorem is too hard, deliver the interior version (Ioo instead of Icc)
  and a precise report of what blocks the boundary extension

## Files to read

Read in this order:
1. `ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean` — **THE KEY FILE** (HasDerivAt, ContinuousOn)
2. `ShenWork/PDE/P3MoserDissipationShape.lean:60-80` — target definition
3. `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean:1-60` — pointwise energy inequality
4. `ShenWork/PDE/P3MoserEnergyContinuity.lean:991-1003` — energy equality
5. `ShenWork/PDE/P3MoserEnergyContinuity.lean:122-133` — endpoint continuity structure
6. `ShenWork/PDE/P3MoserEnergyContinuity.lean:1131-1177` — existing FTC proof (pattern to follow)
7. `ShenWork/Paper2/IntervalDomainMoserClosure.lean:371-379` — relative interpolation definition
