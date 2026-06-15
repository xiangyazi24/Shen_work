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

## SCOUT VERDICT (done) — Avenue (a′): weight-1 re-instantiation
The χ₀=0 time engine `IntervalResolverDirectTimeRegularity.lean` (`resolverSeries_hasDerivAt_time`
:137, `resolver_direct_jointTimeDerivClosed` :445) proves the right SHAPE by the right METHOD
(`hasDerivAt_tsum_of_isPreconnected` + `DuhamelSourceTimeC1`) but is hardcoded to the RESOLVER weight
`wₖ=1/(μ+λₖ)`. The χ₀<0 synthesis is the BARE weight-1 series `∑ fullSourceCoeff·cosineMode`. So the
lemmas are RE-PROVED for weight 1 — every analytic atom already exists. No Mathlib gap. u_t is an
INTERIOR `Ioo 0 T` statement (heat ∂_t majorant `λₙe^{-tλₙ}` degenerates at t↓0).

Committed per-mode ∂_t atoms (all of them):
- heat: `Real.exp(-t·λₙ)` derivative (one-liner) [scout's heatPointWeight atom is for the x-synthesis]
- chemDiv/logistic Duhamel: `duhamelSpectralCoeff_hasDerivAt` (IntervalSourceCoefficientTimeC1.lean:200),
  `bₙ′=aₙ−λₙbₙ`; majorant `duhamelSpectralCoeff_deriv_abs_summable` :276
- value summability: `SourceStrongSolutionData.eigenvalue_summable` (∑λₙ|b̂ₙ|<∞, SourceStrongSolution:315)
- heat majorant: `unitIntervalCosineEigenvalue_mul_exp_summable` (IntervalMildRegularityBootstrap:41)

## BRICK PLAN
1. [DISPATCHED a3846aa6] `fullSourceCoeffDot` + `fullSourceCoeff_term_hasDerivAt_time` (per-mode ∂_t;
   pure .add/.const_mul of the committed atoms; carries the 2 DuhamelSourceTimeC1 packages).
2. summable majorant for `fullSourceCoeffDot` (eigenvalue_summable + heat λe^{-tλ}; interior [c,T]).
3. `fullSourceCoeff_hasDerivAt_time` (tsum HasDerivAt via hasDerivAt_tsum_of_isPreconnected) →
   `jointTimeDerivClosed` → `isClassicalTimeSlice` (extend SourceStrongSolutionData :336).

Biggest risk: weight-1-vs-resolver bookkeeping (redo majorants against λₙ|b̂ₙ| not wₖ) — mechanical.
- Codex out of credits till Jun 18 → Opus carries labor.
