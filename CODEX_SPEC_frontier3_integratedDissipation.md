# Task: Prove integratedMoserDissipation (frontier #3) — the core PDE energy estimate

## Context

This is the MAIN PDE estimate. All other frontiers either depend on it (#2, #5) or
feed into it (#4, #6). It produces `IntegratedMoserDissipationDropBefore`.

## Dependencies (will be available as hypotheses)

1. `IntegratedMoserEnergyWindowFTC intervalDomain u T p0` — from frontier #6
2. `RelativeMoserInterpolationBefore intervalDomain u T rho p0` — from frontier #4
   (or equivalently, the 4-tuple `relativeMassGradient`)
3. `CrossDiffusionBootstrapEstimate intervalDomain p T rho u v` — ALREADY PROVED
   (`intervalDomain_crossDiffusionBootstrapEstimate_of_classical` at
   IntervalDomainCrossDiffusionBootstrap.lean:591)

## Target

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

Defined at `P3MoserDissipationShape.lean:67`:
```lean
structure IntegratedMoserDissipationDropBefore ... where
  C : ℝ
  hC : 0 < C
  drop : ∀ t1 t2, 0 < t1 → t1 < t2 → t2 ≤ T →
    ∀ p, p0 ≤ p →
      intervalDomainLpAbsEnergy (p + rho) u t2 + C * ... ≤
        intervalDomainLpAbsEnergy (p + rho) u t1 + C * p * ∫ t in t1..t2, ...
```

(Read the exact definition — the shape above is approximate.)

## Proof strategy (synthesized from two independent oracle consultations)

### The PDE energy inequality route

1. **Leibniz differentiation:** `d/dt Y_p(t) = p ∫ u^{p-1} ∂_t u`. The Leibniz
   differentiation `intervalDomainPowerEnergy_hasDerivAt` already exists.

2. **Substitute the PDE:** `∂_t u = Δu - χ₀ ∇·(u∇v) + f(u)`. After IBP with
   Neumann BCs:
   - Diffusion: `∫ u^{p-1} Δu = -(4(p-1)/p²) ∫ |∂_x(u^{p/2})|²`
   - Chemotaxis: `∫ u^{p-1} ∇·(u∇v)` — absorbed by cross-diffusion bootstrap
   - Reaction: `∫ u^{p-1} f(u)` — controlled by logistic growth

3. **Time integration on [t1,t2]:** Use FTC (IntegratedMoserEnergyWindowFTC) to
   integrate the derivative from t1 to t2.

4. **Higher-power absorption:** The chemotaxis term produces a `∫ u^{p+rho}`
   term. Apply `RelativeMoserInterpolationBefore` with eps chosen by
   `exists_pos_eps_mul_le_sub_of_coeff_gap` to absorb the higher power into the
   gradient term. The remainder is a lower-order term.

5. **Package:** Use `integratedMoserDissipationDropBefore_of_integrated_energy`
   or `integratedMoserDissipationDropBefore_of_coeff_ge_two`.

### IMPORTANT: Track C(p) growth as polynomial

Frontier #5 (quantitativeEndpoint) needs `C(p) ≤ C₀ · p^a` for the Moser
iteration to converge. The proved Agmon theorem constructs Ceps explicitly.
Extract its growth rather than existentially forgetting it.

## Step-by-step instructions

### Step 1: Read ALL existing infrastructure

```bash
# The dissipation shape and existing wrappers
rg -n 'IntegratedMoserDissipationDropBefore\b' --glob '*.lean' | head -20

# The FTC infrastructure
rg -n 'IntegratedMoserEnergyWindowFTC\b' --glob '*.lean' | head -20

# The relative interpolation
rg -n 'RelativeMoserInterpolationBefore\b' --glob '*.lean' | head -20

# The Leibniz differentiation of power energy
rg -n 'intervalDomainPowerEnergy_hasDerivAt\|powerEnergy.*hasDeriv' --glob '*.lean' | head -20

# The IBP for u^{p-1} Δu
rg -n 'ibp\|IBP\|gradIBP\|neumann.*integration' --glob '*.lean' | head -20

# The scalar absorption
rg -n 'scalar_absorb_higherPower\|exists_pos_eps_mul_le_sub_of_coeff_gap' --glob '*.lean' | head -20

# The cross-diffusion bootstrap
rg -n 'CrossDiffusionBootstrapEstimate\b' --glob '*.lean' | head -20

# Existing energy inequality
rg -n 'LpBootstrapEnergyInequality\|energyInequality\|energy_inequality' --glob '*.lean' | head -20
```

Read EVERY file returned. Understand the existing machinery before writing code.

### Step 2: Identify gaps

After reading, determine:
- Is there already an Lp energy inequality `d/dt Y_p ≤ -gradient + C·p·Y_p + ...`?
- Is the IBP `∫u^{p-1}Δu = -(4(p-1)/p²)∫|∂_x(u^{p/2})|²` proved?
- Is the time integration already done?
- What exactly is missing?

### Step 3: Prove the missing pieces and assemble

Create `ShenWork/PDE/P3MoserIntegratedDissipationPDE.lean`.

The theorem should be conditional on frontiers #4 and #6:
```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

### Step 4: If the integrated energy inequality already exists

If you find that the Lp energy inequality and its time integration are already
proved in some form, then this task reduces to:
1. Wire the FTC + relative interpolation + cross-diffusion into the existing framework
2. Package with the `integratedMoserDissipationDropBefore_of_*` wrappers

### Step 5: If the Lp energy inequality does NOT exist

Prove it from:
- The Leibniz rule (existing)
- IBP with Neumann BCs (check if existing or prove inline)
- The cross-diffusion absorption (existing CrossDiffusionBootstrapEstimate)
- Logistic control (should be in IsPaper2ClassicalSolution or a nearby file)

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserIntegratedDissipationPDE.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Work only in /Users/huangx/repos/Shen_work/
- Read ALL existing infrastructure FIRST — this codebase has 9000+ compiled jobs
- If genuinely blocked, deliver what compiles + precise stall report
- Track C(p) growth explicitly (polynomial, not existential)
