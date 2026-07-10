# Task: Derive gradientTimeIntegrable from integratedMoserDissipation (frontier #2)

## Context

This frontier is NOT independent — it's a COROLLARY of frontier #3
(IntegratedMoserDissipationDropBefore). Both oracle consultations agreed on this.

## The argument

From `IntegratedMoserDissipationDropBefore`:
```
Y_{p+ρ}(t₂) + C·∫_{t₁}^{t₂} G_p ≤ Y_{p+ρ}(t₁) + C·p·∫_{t₁}^{t₂} f(Y_p)
```

where G_p ≥ 0 is the gradient energy. Rearranging:
```
C·∫_{t₁}^{t₂} G_p ≤ Y_{p+ρ}(t₁) - Y_{p+ρ}(t₂) + C·p·∫_{t₁}^{t₂} f(Y_p)
```

The right side is bounded for t₁ = ε, t₂ = T-ε:
- Y_{p+ρ} is bounded on [0,T] (endpoint continuity + compactness)
- The integral ∫f(Y_p) is finite (Y_p is bounded continuous)

Since G_p ≥ 0, by monotone convergence as ε → 0:
```
C·∫₀ᵀ G_p ≤ Y_{p+ρ}(0) - Y_{p+ρ}(T) + C·p·∫₀ᵀ f(Y_p) < ∞
```

This gives `IntegrableOn G_p [0,T]`, which is `gradientTimeIntegrable`.

## Existing bridge

`P3MoserIntegratedClosure.lean` has:
```
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
```
This takes `IntegratedMoserDissipationDropBefore` + endpoint/time-integral bounds
and yields a bound on ∫G_p. Check if this already produces the integrability.

## Step-by-step

### Step 1: Read existing infrastructure
```bash
rg -n 'gradientTimeIntegrable\|GradientTimeIntegrable' --glob '*.lean' | head -20
rg -n 'integratedMoser_gradientIntegral_le' --glob '*.lean' | head -10
rg -n 'IntervalDomainRawMoserGradientTimeIntegrability' --glob '*.lean' | head -10
```

Read P3MoserIntegratedClosure.lean to understand the existing gradient integral bound.
Read P3MoserGradientIntegrability.lean (task 5 output) for the regularity data interface.

### Step 2: Prove the corollary

Create `ShenWork/PDE/P3MoserGradientIntegrabilityFromDissipation.lean`.

The theorem:
```lean
theorem intervalDomain_gradientTimeIntegrable_of_integratedDissipation
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    -- plus whatever endpoint/integrability data is needed
    : IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

### Step 3: Wire into the assembly

Show how this fills the `gradientTimeIntegrable` field of
`IntervalDomainIntegratedMoserClassicalRegularityData`.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserGradientIntegrabilityFromDissipation.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Work only in /Users/huangx/repos/Shen_work/
- This should be SHORT — it's a corollary, not a hard theorem
- Read existing infrastructure FIRST
