# Task: Produce `pdeCombinedInitial` for frontier #6

## Context

`IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData` has 2 fields:
- `atZero` — ALREADY PROVED (task 4, `P3MoserEnergyContinuity.lean`)
- `pdeCombinedInitial` — THIS IS THE TARGET

`pdeCombinedInitial` has type:
```lean
IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0
```

## Goal

### Step 1: Read the definition

1. Read the EXACT definition of `IntervalDomainLpPDECombinedInitialWindowIntegrability`
   ```bash
   rg -n 'IntervalDomainLpPDECombinedInitialWindowIntegrability' --glob '*.lean' | head -20
   ```
   Then read the defining file to understand what fields/conditions it requires.

2. Read existing producers/consumers:
   ```bash
   rg -n 'pdeCombinedInitial\|PdeCombinedInitial\|PDECombinedInitial\|pde_combined' --glob '*.lean' | head -30
   ```

3. Read what `IsPaper2GlobalClassicalSolution` gives you:
   ```bash
   rg -n 'IsPaper2GlobalClassicalSolution\b' --glob '*.lean' | head -20
   ```
   Then read its definition — understand what regularity you have access to.

4. Understand the combined PDE scalar:
   The combined PDE scalar near t=0 is:
   ```
   q * DiffusionIntegral - q * χ₀ * ChemotaxisIntegral + q * LogisticIntegral
   ```
   Read files that define these individual integrals:
   ```bash
   rg -n 'DiffusionIntegral\|ChemotaxisIntegral\|LogisticIntegral' --glob '*.lean' | head -30
   ```

### Step 2: Check existing intermediate producers

The file `P3MoserEnergyContinuity.lean` has:
```
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_powerInit
```

Read these theorems — they may already show you what intermediate data is needed
and what remains.

### Step 3: Produce `pdeCombinedInitial`

The key insight (from both oracle consultations):
- Global classical regularity gives smoothness on (0,∞)
- The difficulty is integrability near t=0 of the combined PDE terms
- For the diffusion integral: from the energy inequality, ∫₀ᵇ ∫|∇u|² dt ≤ C (bounded by initial energy)
- For the chemotaxis integral: ∫₀ᵇ ∫u|∇v|² dt — needs v-gradient bound (from heat semigroup)
- For the logistic integral: ∫₀ᵇ ∫u^{m+1} dt — bounded by Lp integrability

Use the following approach:
1. Positive time: global classical solution gives smooth integrands → IntegrableOn on (0,T)
2. Near t=0: use InitialTrace continuity + a priori bounds to dominate each term
3. `IntervalDomainLpPDECombinedInitialWindowIntegrability` likely requires integrability on `Ioc 0 b`
   (not `Icc 0 b`), since t=0 is the singular point

Create `ShenWork/PDE/P3MoserPDECombinedInitialProducer.lean`.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserPDECombinedInitialProducer.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Work only in /Users/huangx/repos/Shen_work/
- If the definition is complex, prove what you can and report precisely what blocks
- Read ALL existing infrastructure before writing ANY code
