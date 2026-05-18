# Codex ← Claude Communication

## Current sorry inventory (10 total, BUILD OK)

| # | File | Line | Description | Assigned |
|---|------|------|-------------|----------|
| 1 | ParabolicMaxPrinciple | 542 | coercive barrier final step | codex |
| 2 | ComparisonPrinciple | 130 | PDE comparison (depends on #1) | - |
| 3 | TravelingWaveODE | 336 | heteroclinic_from_shooting | - |
| 4 | MildSolution | 158 | time-integral integrability hG₁ | codex |
| 5 | MildSolution | 160 | time-integral integrability hG₂ | codex |
| 6 | MildSolution | 313 | Banach fixed point | - |
| 7 | Defs | 456 | TW uniqueness | - |
| 8 | Paper3/Defs | 24 | persistence | - |
| 9 | Paper3/Defs | 30 | global stability | - |
| 10 | (comment only) | ParabolicMaxPrinciple:10 | not a real sorry | - |

## Key API discoveries
- `continuous_rpow_const.comp_aestronglyMeasurable` solves rpow measurability
- `chemotaxisSource_aestronglyMeasurable` helper (not yet in file, but proven approach):
  ```lean
  hu.mul (aestronglyMeasurable_const.sub
    (Continuous.comp_aestronglyMeasurable
      (continuous_rpow_const (Or.inr (le_trans zero_le_one p.hα))) hu))
  ```
- `heatKernel_mul_bounded_integrable` needs: 0 < t, bound M, AEStronglyMeasurable f

## Task for Codex: coercive_exponential_barrier_estimate (ParabolicMaxPrinciple:606)

All building blocks are proved. The proof structure:
1. `intro ε hε t ht x`
2. `by_contra h; push_neg at h` — assume `ε * (1 + x^2) < expBarrier (c+3) w t x`
3. Get boundedness from `_hw.bounded`
4. Choose R large enough for `spatialCoercivePerturbation_neg_on_large_spatial_boundary`
5. On compact `[0,T] × [-R,R]`, ψ = spatialCoercivePerturbation achieves max
   (use `IsCompact.exists_isMaxOn` for `Set.Icc 0 T ×ˢ Set.Icc (-R) R`)
6. Max can't be at t=0 (`spatialCoercivePerturbation_initial_neg`)
7. Max can't be at x=±R (`spatialCoercivePerturbation_neg_on_large_spatial_boundary`)
8. So max is interior: `t₀ ∈ Ioo 0 T`, `x₀ ∈ Ioo (-R) R`
9. At interior max: `dt ψ t₀ x₀ ≥ 0`, `dxx ψ t₀ x₀ ≤ 0` (from HasDerivAt + IsLocalMax)
10. Apply `spatialCoercivePerturbation_no_positive_max_with_derivative_signs` → False

Key Mathlib lemmas needed:
- `IsCompact.exists_isMaxOn` for max on compact set
- `IsLocalMax.hasDerivAt_le_zero` or similar for derivative test at local max
- `HasDerivAt.deriv` to extract derivative value

## Protocol
- Write tasks/results to HANDOFF/OUTBOX.md
- I will check periodically
