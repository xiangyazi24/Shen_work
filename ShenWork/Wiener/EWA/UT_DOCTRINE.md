# u_t (time regularity) — DOCTRINE

Goal: extend the χ₀<0 source-form local existence from the SPATIAL classical slice
(`sourceClassical_spatial_existence_clean`, C² in x + Neumann, committed 1d64c9b) to TIME
regularity — `∂_t u` exists/continuous — toward the full classical solution.

## Avenues (ranked)
(a) **Connect to the committed interval-domain time-regularity stack.** Substantial machinery
    exists (χ₀=0 / interval track): `IntervalChemDivTimeDerivative`, `IntervalChemDivTimeDerivClosed`,
    `IntervalCoupledClassicalCorePAR`, `IntervalCoupledRegularityBootstrap`, `DuhamelSourceTimeC1On`,
    heat `HasDerivAt` lemmas (`unitIntervalCosineHeatValue_deriv_of_summable_bound`). If the
    interval track already proves time regularity for the mild solution, χ₀<0 u_t = wire
    `realSlice u_star` (the EWA fixed point's slice) into it, carrying the standard time-C¹ source
    data (`logSrc : DuhamelSourceTimeC1`, already a carried input upstream).
(b) **Direct Duhamel time-derivative.** Differentiate the source-form Duhamel formula in t: the
    heat-semigroup time-derivative + the time-C¹ source (`DuhamelSourceTimeC1`) give `∂_t` of the
    spectral coefficients; sum via the same ℓ¹/eigenvalue machinery as the C² spatial bootstrap.
(c) **Grade-2 EWA.** A heavier route if (a)/(b) stall — a grade-2 envelope giving an extra
    derivative. Last resort.

## Terminal conditions
- success: `∂_t (realSlice u_star · ·)` exists + continuous at interior (t,x), proved/connected.
- proof-of-failure: a precise Mathlib/infra gap (named) that blocks (a) AND (b).

## Status
- SCOUT dispatched (map the interval time-regularity stack + the exact χ₀<0 connection point).
- Codex out of credits till Jun 18 → Opus carries labor.
