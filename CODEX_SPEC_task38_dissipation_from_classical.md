# Task 38: IntegratedMoserDissipationDropBefore from classical regularity

## Goal

Create `ShenWork/PDE/P3MoserDissipationFromClassical.lean` that produces
`IntegratedMoserDissipationDropBefore` directly from classical regularity +
energy inequality, WITHOUT needing `IntegratedMoserEnergyWindowFTC` or
`IntervalDomainIntegratedMoserClassicalRegularityData` (which require
`zeroRightDerivative` and `gradientTimeIntegrable`).

## The bypass

The existing route:
```
ClassicalRegularityData (needs gradientTimeIntegrable)
  → higherPowerWindowCoeffFrontier
    → IntegratedMoserDissipationDropBefore
```

The NEW route (this task):
```
Classical solution + energy inequality + energy continuity at t=0
  → Interior FTC on (ε, t₂) for all ε > 0
    → Dissipation drop at t₁ > 0
      → Limit as t₁ → 0  (using energy continuity)
        → Full IntegratedMoserDissipationDropBefore (including t₁ = 0)
```

## Files to read first

1. `ShenWork/PDE/P3MoserDissipationShape.lean` (lines 60-80) — `IntegratedMoserDissipationDropBefore` definition
2. `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` (lines 1-60) — `LpBootstrapEnergyInequalityWithGap` definition
3. `ShenWork/PDE/P3MoserEnergyContinuity.lean` (lines 1125-1180) — how `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` is used for FTC
4. `ShenWork/PDE/P3MoserIntegratedClosure.lean` (lines 900-960) — how `integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative` absorbs higher-power terms
5. `ShenWork/PDE/P3MoserEnergyContinuity.lean` (search for `intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity`) — energy continuity on [0,T]
6. `ShenWork/PDE/IntervalDomainExistence.lean` (search for `intervalDomainPowerEnergy_hasDerivAt`) — interior differentiability of energy

## Key mathematical content

### Step 1: Interior dissipation drop (t₁ > 0)

For t₁ > 0, t₂ ∈ [t₁, T]:
- Energy E(t) = integratedMoserEnergy (= ∫|u(t)|^p) is C¹ on (0,T)
- `intervalDomainPowerEnergy_hasDerivAt` gives `HasDerivAt E (deriv E t) t` for t ∈ (0,T)
- Standard FTC `integral_eq_sub_of_hasDerivAt_of_le` gives ∫_{t₁}^{t₂} E'(s) ds = E(t₂) - E(t₁)
- Energy inequality (LpBootstrapEnergyInequalityWithGap) gives pointwise bound on E'(s) for s ∈ (0,T)
- Integrate and absorb → dissipation drop on [t₁, t₂]

Key: for t₁ > 0, the derivative E' is CONTINUOUS on [t₁, t₂] (from classical regularity on (0,T)). So E' is bounded on [t₁, t₂], hence interval-integrable. ALL integrability issues vanish for interior windows.

### Step 2: Extension to t₁ = 0 (limit argument)

For t₂ > 0: the inequality holds at t₁ = 1/n for each n ≥ 1 (from Step 1).

As n → ∞:
- E(1/n) → E(0) (energy continuous at t=0, from `intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity`)
- G_integral: ∫_{1/n}^{t₂} G(s) ds is INCREASING in n (G ≥ 0, domain grows) and BOUNDED:
  from the inequality, 2·∫G ≤ C·p·∫max(1,E) - (E(t₂) - E(1/n)) ≤ C·p·∫_0^{t₂} max(1,E) + |E(0)| + |E(t₂)|
- max1E_integral: ∫_{1/n}^{t₂} max(1,E(s)) ds → ∫_0^{t₂} max(1,E(s)) ds (monotone convergence, max(1,E) ≥ 1)

Therefore: E(t₂) - E(0) + 2·∫_0^{t₂} G ≤ C·p·∫_0^{t₂} max(1,E)

For t₁ = 0 ∧ t₂ = 0: trivial (all terms = 0).

### Step 3: Absorb higher-power term

The raw energy inequality from `LpBootstrapEnergyInequalityWithGap` gives a WINDOW inequality:
```
E(t₂) - E(t₁) + A·∫G ≤ C₀·p·∫max(1,E) + K·∫E_{q+ρ} + L·∫max(1,E)
```

Use relative interpolation (from `RelativeMoserInterpolationBefore`):
```
∫E_{q+ρ} ≤ ε·∫G + Cε·∫max(1,E)
```

Choose ε = (A - 2)/(2K) to absorb the higher-power term and leave coefficient 2 on ∫G.

The output is `IntegratedMoserDissipationDropBefore` with C = C₀ + (K·Cε + L)/p.

## What to prove

### Theorem 1: Interior dissipation drop producer

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_interior_of_classical
    {p : CM2Params}
    {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    ∀ q, p0 ≤ q → ∃ C, 0 ≤ C ∧
      ∀ t1 ∈ Set.Ioo (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        integratedMoserEnergy intervalDomain u q t2 -
            integratedMoserEnergy intervalDomain u q t1 +
          2 * ∫ s in t1..t2,
            integratedMoserGradientEnergy intervalDomain u q s ≤
        C * q * ∫ s in t1..t2,
          max 1 (integratedMoserEnergy intervalDomain u q s)
```

### Theorem 2: Full dissipation drop (including t₁ = 0)

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_classical_gap_rel
    {p : CM2Params}
    {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hEndCont : IntervalDomainPowerEnergyEndpointContinuity u T p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

### Key Lean tactics and library tools

- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` — FTC for interior
- `intervalDomainPowerEnergy_hasDerivAt` — HasDerivAt for energy on interior
- `intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity` — ContinuousOn for energy
- `ContinuousOn.intervalIntegrable` — continuous functions are interval-integrable
- `intervalIntegral.integral_mono_of_nonneg` or `MeasureTheory.set_integral_mono_set` — for monotonicity of integrals
- `Filter.Tendsto` — for the limit argument

### For the limit argument (Step 2)

The limit argument can use `le_of_tendsto_of_tendsto`:
1. Show LHS_n → LHS_0 (using Tendsto for energy + monotone convergence for integrals)
2. Show RHS_n → RHS_0 (monotone convergence)
3. Since LHS_n ≤ RHS_n for all n, conclude LHS_0 ≤ RHS_0

For monotone convergence of interval integrals:
```
∫ s in (1/n)..t2, f s → ∫ s in 0..t2, f s   (as n → ∞, for f ≥ 0 measurable)
```

This follows from: ∫ s in 0..t2, f s = ∫ s in 0..(1/n), f s + ∫ s in (1/n)..t2, f s, and the first term → 0 (integral over shrinking interval). Use `intervalIntegral.integral_add_adjacent_intervals` and show the small interval's integral → 0.

Actually, the SIMPLEST approach for the limit might be:

For the special case t₁ = 0: use the fact that for continuous, nonneg f:
∫ s in 0..t2, f s = sup_{n} ∫ s in (1/n)..t2, f s

But in Lean, the cleanest approach might be to avoid the limit entirely and handle t₁ = 0 as:
- ∫ s in 0..t2, f s = ∫ s in 0..ε, f s + ∫ s in ε..t2, f s (for small ε)
- The second integral satisfies the inequality (interior case)
- Show the first integral is small as ε → 0

OR: just use the fact that for continuous functions on [0, t₂]:
- f continuous on [0, t₂] → ∫ s in 0..t2, f s = lim_{ε→0} ∫ s in ε..t2, f s
- This is just `intervalIntegral.integral_add_adjacent_intervals` + small interval vanishing

## Constraints

- NO sorry, NO axiom
- `#print axioms` must give only `[propext, Classical.choice, Quot.sound]`
- File should be ≤ 400 lines
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3MoserDissipationFromClassical`

## Imports

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2
import ShenWork.PDE.P3MoserDissipationShape
```

You may need additional imports for Mathlib measure theory / interval integrals.

## If stuck

If the full limit argument for t₁ = 0 is too complex:
1. Deliver Theorem 1 (interior only, t₁ > 0) — this is valuable on its own
2. Report exactly what's blocking the t₁ = 0 extension
3. Do NOT use sorry — deliver what compiles
