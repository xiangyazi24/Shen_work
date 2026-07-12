# Task: Prove quantitativeEndpoint (frontier #5) — Moser iteration L∞ bound

## Context

The Moser iteration bootstrap: given Lp bounds for increasing p, produce L∞.
The dyadic root tower scalar lemmas are ALREADY PROVED in the codebase.

## Target

The `quantitativeEndpoint` field in `IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals`:
```lean
quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

## Existing infrastructure (ALREADY PROVED)

Read these files FIRST:
```bash
rg -n 'dyadic_root_tower\|dyadic_inv_sum\|dyadic_k_inv\|dyadicMoserFactor' --glob '*.lean' | head -20
rg -n 'IntervalDomainMoserQuantitativeEndpoint\|MoserQuantitativeEndpoint' --glob '*.lean' | head -20
rg -n 'IntervalDomainMoserPointwisePowerControlBefore\|MoserLpAbsRootBound' --glob '*.lean' | head -20
rg -n 'IntervalDomainMoserLadderAtoms\|moser_ladder\|moserLadder' --glob '*.lean' | head -20
rg -n 'boundedBefore_of_moser\|boundedBefore_of_pointwise' --glob '*.lean' | head -20
```

Key files:
- `IntervalDomainMoserActualAtoms.lean` — dyadic root tower lemmas
- `IntervalDomainMoserClosure.lean` — `IntervalDomainMoserQuantitativeEndpoint` definition and L∞ conversion
- `IntervalDomainMoserLadderAtoms.lean` — ladder atoms, step-level interfaces
- `P3MoserActualWiring.lean` — Proposition 2.5 consumers

## Proof strategy (from oracle consultation)

### The dyadic Moser iteration

Set `p_k = 2^k · p_start`. At each step k:
```
M_{k+1} ≤ (C · 2^k)^{1/2^k} · M_k
```
where `M_k = sup_t ‖u(t)‖_{p_k}`.

The telescoping product:
```
M_n ≤ M_0 · ∏_{k=0}^{n-1} (C · 2^k)^{1/2^k}
```

The product converges because `∑ log(C·2^k)/2^k < ∞` (geometric series).
This is `dyadic_root_tower_bound`.

### Deriving the per-step bound

From the integrated Moser dissipation (#3):
```
Y_{p+ρ}(t₂) + C·∫_{t₁}^{t₂} gradient_term ≤ Y_{p+ρ}(t₁) + C·p·∫_{t₁}^{t₂} Y_p
```

Dropping the gradient term:
```
sup_{t∈[t₁,t₂]} Y_{p+ρ}(t) ≤ Y_{p+ρ}(t₁) + C·p·(t₂-t₁)·sup Y_p
```

Taking (p+ρ)-th root:
```
‖u‖_{L^{p+ρ}(sup)} ≤ (‖u₀‖_{p+ρ}^{p+ρ} + C·p·T·‖u‖_{L^p(sup)}^p)^{1/(p+ρ)}
```

This is the per-step recurrence that feeds the tower.

### The continuity contradiction (Lp→pointwise alternative)

If the tower approach is hard to wire, use this alternative for the
`IntervalDomainMoserPointwisePowerControlBefore` field:

If `|u(t₀,x₀)| > M+ε` and u is continuous, there exists an interval J
with `|u| ≥ M+ε/2` on J. Then:
```
Y_p(t₀) ≥ |J| · (M+ε/2)^p
```
But the root bound gives `Y_p(t)^{1/p} ≤ M·(1+o(1))` for large p.
Contradiction for large enough p.

## Instructions

### Step 1: Survey existing infrastructure
Read ALL of the files listed above. Understand what's proved and what's missing.

### Step 2: Identify what connects the integrated dissipation to the per-step bound
The per-step bound is the key. It should come from dropping the gradient term
in the integrated dissipation and using energy continuity.

### Step 3: Write the producer
Create `ShenWork/PDE/P3MoserQuantitativeEndpointDischarge.lean`.

The theorem should be conditional on the integrated dissipation if needed:
```lean
theorem intervalDomain_moserQuantitativeEndpoint_of_integrated_dissipation
    ...
    (hdiss : IntegratedMoserDissipationDropBefore ...)
    ...
    : IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Then package into the assembly's `quantitativeEndpoint` field.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserQuantitativeEndpointDischarge.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Work only in /Users/huangx/repos/Shen_work/
- Read ALL existing infrastructure FIRST
- Use the proved `dyadic_root_tower_bound` — do NOT re-prove it
- If genuinely blocked, deliver what compiles + precise stall report
