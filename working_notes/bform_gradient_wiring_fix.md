# B-form Gradient Wiring Fix — Status 2026-07-08

## Summary

Making Paper 2 Theorem 1.1 unconditional by closing all sorries in
`IntervalTruncatedPositiveTimeBootstrap.lean`.

## Completed (0 sorry)

| File | Status |
|------|--------|
| IntervalTruncatedLeftProfile.lean | 0 sorry (committed 82ec3819) |
| IntervalResolverContinuity.lean | 0 sorry (committed 9b046684) |

## In Progress

### IntervalTruncatedPositiveTimeBootstrap.lean — 21 sorries

**Critical wiring (4 sorries):**

| Line | Field | Status | Approach |
|------|-------|--------|----------|
| L126 | product rule | Codex dispatched | ChatGPT Q3974 architecture: algebraic envelope + HasDerivAt |
| L233 | hleft | ChatGPT cron2 dispatched | Left Volterra profile, structural induction |
| L239 | hbase | Codex dispatched | Restart: S(t')=S(t'-a)(S(a)(u₀)), |S(a)(u₀)|≤M from hbase_ball |
| L273 | hkernel_step | Codex dispatched | ChatGPT Q3973: restart + triangle + gradDuhamel_shifted_sup_bound |

**Secondary (2 sorries):**

| Line | Description | Status |
|------|-------------|--------|
| L290 | DifferentiableAt iterate | Semigroup smoothing at positive time |
| L730-731 | Downstream caller | Passes sorry for hcontr_grad |

**Sobolev ladder (14 sorries, L789-L1035):**
Deep spectral theory, depends on wiring sorries being closed first.

### IntervalResolverWeakODEBridge.lean — 1 sorry

| Sorry | Status |
|-------|--------|
| resolverGradReal_sub_eq_integral_lapPhysicalReal | ChatGPT cron1 dispatched (spectral route) |

### IntervalResolverWeakLapBound.lean — 1 sorry

| Sorry | Status |
|-------|--------|
| resolverGradReal_hasDerivAt_physicalLap_of_continuousOn | Auto-closes once ODE bridge sorry closes |

## Key Architectural Insights (from ChatGPT Q3973-Q3974)

1. **Restart identity**: U(n+1,t) = S(t-a)(U(n+1,a)) + ∫_a^t S(t-s)(Src n s) ds.
   The ball bound |U(n+1,a)| ≤ M comes from hbase_ball at positive time a, NOT from ||u₀||∞.

2. **Product rule**: F(y) = u⁺ · R' / (1+R)^β. Three-term derivative:
   |F'| ≤ G·Γ + M·H + β·M·Γ² = (M·H + β·M·Γ²) + Γ·G.
   Key: |(1+R)^(-β)| ≤ 1 since R ≥ 0 → 1+R ≥ 1.

3. **Integrated weak ODE**: R'(b)-R'(a) = ∫_a^b (μR-ρ) dx via spectral identity
   Σ(-λ_k c_k)∫φ_k on both sides. Avoids FTC circularity.
