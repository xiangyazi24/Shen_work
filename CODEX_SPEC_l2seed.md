# Task: Build IntervalDomainL2SeedRegularityFrontier producer

## Goal
Create file `ShenWork/Paper2/IntervalDomainL2SeedFrontierProducer.lean` that produces
`IntervalDomainL2SeedRegularityFrontier T u` from a classical solution + endpoint continuity data.

## Target theorem

```lean
theorem intervalDomainL2SeedRegularityFrontier_of_classical_and_endpointContinuity
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hendpoint : IntervalDomainPowerEnergyEndpointContinuity u T 2) :
    IntervalDomainL2SeedRegularityFrontier T u
```

## The four fields to fill

### 1. energyContinuous
`ContinuousOn (fun t => intervalDomainLpAbsEnergy 2 u t) (Set.Icc 0 T)`

Build from:
- `intervalDomain_energyContinuousOn_Ioo` (interior, in `P3MoserEnergyContinuity.lean:91`)
- `hendpoint` (endpoints)

For positive solutions `|u t x|^p = (u t x)^p`, so the two energy notions coincide.
Use `ContinuousOn` on Ioo + ContinuousWithinAt at endpoints → ContinuousOn on Icc.

### 2. energyHasDerivWithin
`∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (fun τ => intervalDomainLpAbsEnergy 2 u τ) (deriv ...) (Set.Ici t) t`

For `t ∈ (0,T)`: use `intervalDomainPowerEnergy_hasDerivAt` (in `IntervalDomainLpTimeLeibniz.lean:86`).
`HasDerivAt → HasDerivWithinAt`. Reconcile energy notions via positivity.

For `t = 0`: downstream consumers NEVER use t=0 (checked: the call at line 1090 of
IntervalDomainAPrioriGlobal.lean always has `hr0 : 0 < r`). But the type demands it.
If proving the right derivative at 0 is hard, take it as an explicit hypothesis or
construct it from the endpoint continuity data + the energy derivative formula.

### 3. initialBound
`∃ δ0, 0 ≤ δ0 ∧ intervalDomainLpAbsEnergy 2 u 0 ≤ δ0`

Trivial: `⟨intervalDomainLpAbsEnergy 2 u 0, intervalDomainLpAbsEnergy_nonneg ..., le_refl _⟩`.
The nonneg follows from integral of nonneg. If `intervalDomainLpAbsEnergy_nonneg` doesn't
exist, prove it inline (it's an integral of `|x|^2 ≥ 0`).

### 4. derivativeAlignment
`∀ t ∈ Set.Ico 0 T, deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t = 2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t`

Key identity: for positive u, `intervalDomainLpAbsEnergy 2 u t = 2 * intervalDomainL2HalfEnergy u t`.
Because:
- `intervalDomainLpAbsEnergy 2 u t = ∫ |u t x|^2 = ∫ (u t x)^2` (positive solutions)
- `intervalDomainL2HalfEnergy u t = (1/2) * ∫ (u t x)^2`

So `LpAbsEnergy 2 = 2 * L2HalfEnergy`, and `deriv(f) = deriv(2g) = 2*deriv(g)`.

Use `deriv_congr` to transfer from the extensional equality, then `deriv_const_mul`.

## Key definitions (look these up to get exact types)
- `intervalDomainLpAbsEnergy` in `ShenWork/Paper2/IntervalDomainLpMonotonicity.lean:184`
- `intervalDomainL2HalfEnergy` in `ShenWork/Paper2/IntervalDomainEnergyStep.lean:1578`
- `IntervalDomainL2SeedRegularityFrontier` in `ShenWork/PDE/IntervalDomainAPrioriGlobal.lean:377`
- `IntervalDomainPowerEnergyEndpointContinuity` in `ShenWork/PDE/P3MoserEnergyContinuity.lean:122`
- `intervalDomain_energyContinuousOn_Ioo` in `ShenWork/PDE/P3MoserEnergyContinuity.lean:91`
- `intervalDomainPowerEnergy_hasDerivAt` in `ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean:86`
- `IsPaper2ClassicalSolution.u_pos'` (positivity of solution at interior times)

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/Paper2/IntervalDomainL2SeedFrontierProducer.lean 2>&1 | tail -30
```

First run `lake build ShenWork.PDE.IntervalDomainAPrioriGlobal ShenWork.PDE.P3MoserEnergyContinuity ShenWork.Paper2.IntervalDomainLpTimeLeibniz` to ensure upstream oleans are fresh.

## Rules
- No sorry, no axiom, no native_decide
- If `t = 0` case of `energyHasDerivWithin` is genuinely hard, split:
  provide a version that takes a `HasDerivWithinAt ... 0` hypothesis for t=0
- File should be ≤ 300 lines
- If stuck, deliver what compiles + precise stall report (which field, which Lean error)
