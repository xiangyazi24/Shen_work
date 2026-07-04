# CODEX_SPEC Task 24: RelativeMoserInterpolationBefore without hBoundedBefore

## Goal

Investigate and (if possible) produce `RelativeMoserInterpolationBefore`
from `(hsol, hcross, hboot)` WITHOUT requiring `IsPaper2BoundedBefore`.

## Why this matters

The assembly filler's circularity:
```
hBoundedBefore → relativeMassGradient (uses bounded-before for u^rho bound)
  → integratedMoserDissipation → crossing step → all-Lp → bounded-before
```

If we can produce `RelativeMoserInterpolationBefore` without bounded-before,
the circle breaks: we get dissipation + crossing step + endpoint → bounded-before,
all WITHOUT the circular input.

## The current route (requires bounded-before)

In `P3MoserRelativeMassGradientProducer.lean`, the relative interpolation is
produced using:
```
intervalDomain_relativeMassGradient_of_classical_boundedBefore
```
which uses bounded-before to control `∫ u^(p+rho)`:

  u^rho * u^(p-2)|∇u|² ≤ M^rho * u^(p-2)|∇u|²

where M = sup_t ‖u(t)‖_∞ from bounded-before.

## The alternative route (1D GN/Young, no bounded-before)

On a bounded 1D domain, the Gagliardo-Nirenberg-Sobolev inequality gives:

  ‖f‖_{L^q}^q ≤ C * ‖f‖_{H^1}^a * ‖f‖_{L^r}^b

For the cross-diffusion term `∫ u^(p+rho)` with f = u^{p/2}:

  ∫ u^(p+rho) = ‖u^{p/2}‖_{L^{(p+rho)/(p/2)}}^{(p+rho)/(p/2)}

In 1D, with q = 2(p+rho)/p, r = 2:
  ‖f‖_q ≤ C * ‖f'‖_2^theta * ‖f‖_2^{1-theta}

where theta = (1/2 - p/(2(p+rho))) / (1/2 + 1/2) = rho/(p+rho).

This gives:
  ∫ u^{p+rho} ≤ eps * ∫ |∇(u^{p/2})|² + C_eps * (∫ u^p)^{(p+rho)/p}

The key: the RIGHT side uses `∫ u^p` (which is the CURRENT Lp norm from
the bootstrap) and `∫ |∇(u^{p/2})|²` (gradient energy). No sup-norm /
bounded-before is needed.

## What to produce

Write `ShenWork/PDE/P3MoserRelativeInterpolationNoBound.lean`:

1. Check what exists in the codebase for 1D GN/Sobolev:
   - Grep for `GagliardoNirenberg`, `Sobolev`, `interpolation`,
     `unitInterval_regular_power_GNYoung`, `massGradientInterpolation`
   - Read `ShenWork/Paper2/IntervalDomainMCL.lean` for existing interpolation

2. Investigate the route:
   `relativeMoserInterpolationBefore_of_massGradient` — what does it need?
   `intervalDomain_massGradientInterpolation_of_classical` — producer?
   `MoserMassPowerToCurrentLpLowerOrder` — what's this?

3. If the no-bounded-before route is achievable:
   Write `intervalDomain_relativeMoserInterpolationBefore_of_classical_noBound`
   producing `RelativeMoserInterpolationBefore` from `(hsol, hcross, hboot)`.

4. If NOT achievable, write a precise report:
   - What exactly requires bounded-before
   - Whether it's the u^rho factor specifically or something else
   - Whether a weaker substitute (e.g., local-in-time L^∞ bound) would suffice

## Files to read

1. `ShenWork/PDE/P3MoserRelativeMassGradientProducer.lean` — current producer
2. `ShenWork/Paper2/IntervalDomainMCL.lean` — existing interpolation infrastructure
3. `ShenWork/PDE/P3MoserDissipationShape.lean` — how interpolation is consumed
4. `ShenWork/PDE/IntervalDomainMoserActualAtoms.lean` — the all-Lp route

## Rules

- 0 sorry, 0 custom axiom
- Write ONLY `ShenWork/PDE/P3MoserRelativeInterpolationNoBound.lean`
- This is INVESTIGATION + WIRING — read extensively before writing
- Add `#print axioms` for any theorems
- Verify: `lake env lean ShenWork/PDE/P3MoserRelativeInterpolationNoBound.lean`
