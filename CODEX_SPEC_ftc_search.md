# Task: Search for FTC / zero-right-derivative infrastructure

## Context

`ClosedEnergyIdentityTraceRemainingData` (P3MoserClosedEnergyProducer.lean:156) has 4 fields
that are the irreducible remainder of `ClosedEnergyIdentityTraceData`:

1. `g : ℝ → ℝ` — the energy derivative function
2. `g_integrable : IntegrableOn g (Set.uIcc 0 T) volume`
3. `energy_eq : ∀ t ∈ Icc 0 T, E(t) = E(0) + ∫₀ᵗ g(s) ds` — the FTC representation
4. `zeroRightDerivative : IntervalDomainL2SeedZeroRightDerivative u` — HasDerivWithinAt at t=0

## Goal

Survey the ENTIRE codebase for anything that helps discharge these. This is a RESEARCH task.

### Step 1: Exhaustive grep

Search for ALL of the following patterns:
```bash
rg -n 'IntervalDomainL2SeedZeroRightDerivative' --glob '*.lean'
rg -n 'zeroRightDerivative\|zero_right_deriv\|ZeroRightDeriv' --glob '*.lean'
rg -n 'HasDerivWithinAt.*LpAbsEnergy.*0\|HasDerivWithinAt.*Energy.*zero' --glob '*.lean'
rg -n 'FTC\|fundamentalTheorem\|integral_eq_sub' --glob '*.lean'
rg -n 'energy_eq\|energyFTC\|energy_integral' --glob '*.lean'
rg -n 'IntegratedMoserDissipation.*Zero\|dissipation.*zero\|energyDerivative.*zero' --glob '*.lean'
rg -n 'absolutelyContinuous.*energy\|AbsolutelyContinuous.*Energy' --glob '*.lean'
```

### Step 2: Read relevant results

For EACH grep hit:
- Read the surrounding context (±20 lines)
- Determine if it's relevant to discharging any of the 4 fields
- Note the exact theorem/def name, file, line

### Step 3: Analysis and report

For each of the 4 remaining fields, write a section:
- What existing infrastructure is relevant?
- Can it be discharged from classical solution + existing results?
- If not, what's the precise gap?

### Step 4: Build anything that closes

If your survey reveals that any field CAN be discharged, create the proof in a new file
`ShenWork/PDE/P3MoserFTCInfrastructure.lean`.

If nothing closes but you find partial connections, create a file that documents the
connections (theorems that reduce the fields to simpler statements).

## Build command (if file created)
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserFTCInfrastructure.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- This is primarily a RESEARCH/SURVEY task — understanding what exists is more valuable than
  producing new code that doesn't close
- Work only in /Users/huangx/repos/Shen_work/
- Report findings clearly: for each of the 4 fields, state "FOUND: [theorem] discharges this" or
  "GAP: [precise statement of what's missing]"
