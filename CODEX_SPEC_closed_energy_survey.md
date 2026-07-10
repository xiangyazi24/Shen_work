# Task: Survey what's needed to produce ClosedEnergyIdentityTraceData

## Context

`ClosedEnergyIdentityTraceData` (at `P3MoserLemmaDischarge.lean:42`) is carried universally
in the assembly chain. Its fields are:

```lean
structure ClosedEnergyIdentityTraceData (T : ℝ) (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) where
  nonnegT : 0 ≤ T
  g : ℝ → ℝ
  g_integrable : IntegrableOn g (Set.uIcc 0 T) volume
  energy_eq :
    ∀ t ∈ Set.Icc 0 T,
      intervalDomainLpAbsEnergy 2 u t =
        intervalDomainLpAbsEnergy 2 u 0 + ∫ s in 0..t, g s
  initial_trace_energy :
    intervalDomainLpAbsEnergy 2 u 0 =
      intervalDomain.integral (fun x => |u₀ x| ^ (2 : ℝ))
  energyHasDerivWithin :
    ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun τ => intervalDomainLpAbsEnergy 2 u τ)
        (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
        (Set.Ici t) t
  derivativeAlignment :
    ∀ t ∈ Set.Ico 0 T,
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t =
        2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t
```

## Goal

Survey the codebase and produce whatever fields can be discharged from
`IsPaper2ClassicalSolution` + `InitialTrace` + `PaperPositiveInitialDatum`.

### Step 1: Survey existing infrastructure

Grep for ALL of these and read what you find:
- `intervalDomainLpAbsEnergy` — how is it defined? What continuity/differentiability results exist?
- `intervalDomainL2HalfEnergy` — definition and results
- `HasDerivWithinAt.*LpAbsEnergy` or `HasDerivWithinAt.*Energy`
- `deriv.*LpAbsEnergy` or `deriv.*Energy`
- `energy_eq` or `FTC` or `integral.*energy`
- `derivativeAlignment` — the frontier producer already proved this (IntervalDomainL2SeedFrontierProducer.lean)
- `initial_trace_energy` — check if this relates to the endpoint-zero results

### Step 2: Field-by-field analysis

For each field, determine:
- Can it be proved from classical solution + trace? If yes, prove it.
- If not, what's the precise obstruction?

Expected results:
- `nonnegT`: trivial from `0 < T` (use `le_of_lt`)
- `derivativeAlignment`: ALREADY PROVED in `IntervalDomainL2SeedFrontierProducer.lean`
- `energy_eq`: this is FTC — `E(t) = E(0) + ∫₀ᵗ E'(s) ds`. Needs `E` absolutely continuous on `[0,T]`
- `initial_trace_energy`: `E(0) = ∫|u₀|²` — needs `u(0) = u₀` or re-anchoring
- `g_integrable`: `g` is the derivative `E'`, so this is about integrability of the energy derivative
- `energyHasDerivWithin`: `HasDerivWithinAt` of `E` — from classical regularity on `(0,T)`, but t=0 is hard

### Step 3: Produce what you can

Create a file `ShenWork/PDE/P3MoserClosedEnergyProducer.lean` with:
- A partial producer that fills as many fields as possible
- Clear documentation of which fields are filled and which remain open
- Helper lemmas as needed

If ALL fields can be filled (unlikely), produce the full `ClosedEnergyIdentityTraceData`.
If not, produce a structure with the filled fields + a converter that takes the remaining
fields and produces the full data.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserClosedEnergyProducer.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- This is a RESEARCH + BUILD task — investigate thoroughly, then build what compiles
- Work only in /Users/huangx/repos/Shen_work/
