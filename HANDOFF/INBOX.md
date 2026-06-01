# Shen_work — Current Task (updated 2026-05-31 23:00 CDT)

## Build
```bash
export PATH="$HOME/.elan/bin:$PATH" && cd ~/repos/shen_work && lake build
```
Build green (8387 jobs).

## Sorry Count
```
IntervalMildExistence.lean: 2 (BCF approach, superseded by Picard)
IntervalMildPicard.lean:    1 (main theorem — MildExistenceData construction)
IntervalDuhamelIntegrability.lean: 2 (gradient edge case + flux integrability)
```
Total: 5 sorry. Active: 3.

## What Is Proved (0 sorry)

### Picard fixed-point theory (IntervalMildPicard.lean)
- picardIter + picardLimit definitions
- real_cauchySeq_of_geometric_bound
- picardIter_pointwise_convergent
- picardIter_pointwise_tail_bound (dist_le_tsum)
- picardIter_uniform_convergence
- picardLimit_bounded (le_of_tendsto)
- picardLimit_hasContinuousSlices (uniform limit)
- picardLimit_is_mildSolution (contraction squeeze)
- intervalMildSolution_of_bounds
- picardIter_ball (+ HasContinuousSlices, mutual induction)
- picardIter_geometric
- MildExistenceData structure
- intervalMildSolution_of_data (assembly)
- hbase_ball (semigroup L∞ bound)

### Integrability chain (IntervalDuhamelIntegrability.lean)
- continuousOn_aestronglyMeasurable_intervalMeasure
- intervalDomainLift_aestronglyMeasurable_of_continuous
  KEY PROOF: Set.restrict (Icc 0 1) (intervalDomainLift f) = f
  via continuousOn_iff_continuous_restrict
- logisticLifted_integrable_of_continuous
  (rpow_const + lift measurability + bounded finite measure)
- valueDuhamel_sup_bound_universal (integral_undef for non-integrable)

## Remaining Gaps (priority order)

### GAP 1: Semigroup smoothing for general bounded input (DEEP)
`hbase_cont` and `hcont_preserved` need: S(t) maps bounded → C²(Icc 0 1).
The spectral form `unitIntervalCosineHeatValue_contDiff_two` is proved for
bounded coefficient sequences. But connecting `intervalFullSemigroupOperator`
(kernel integral) to `unitIntervalCosineHeatValue` (spectral sum) requires
the kernel↔spectral bridge (Parseval for Neumann cosine expansion).

This bridge is partially built:
- `heatKernel_lattice_poisson` (Poisson summation) — proved
- `intervalNeumannFullKernel` (full image kernel) — defined
- The connection needs: `∫ K(t,x,y)f(y)dy = ∑ e^{-λt} f̂_n cos(nπx)`
  where `f̂_n = ∫ f(y) cos(nπy) dy`. This is in `CosineParsevalBridge.lean`
  but not yet connected to `intervalFullSemigroupOperator`.

Estimate: multi-day work.

### GAP 2: chemFluxLifted integrability (MEDIUM)
`chemFluxLifted_integrable_of_continuous` — flux = w · resolverGrad / (1+R)^β.
Needs: resolverGradReal and resolverR are continuous when w is continuous.
These are cosine/sine series (from IntervalNeumannEllipticResolverR.lean)
with summable coefficients. Continuity follows from continuous_tsum.
Estimate: hours.

### GAP 3: hmapsTo / hcontr instantiation (MEDIUM)
Once integrability is available (Gap 2), connect to Duhamel bounds:
- gradDuhamel_sup_bound for flux
- valueDuhamel_sup_bound for logistic (DONE — universal version)
- gradDuhamel_diff_sup_bound for flux difference
- valueDuhamel_diff_sup_bound for logistic difference
Then choose T from exists_small_contraction_time.
Estimate: hours, assuming Gap 2 closed.

### GAP 4: Gradient edge case (LOW priority)
gradDuhamel_sup_bound_universal: spatial non-integrable + time integrable.
Never occurs for spatially continuous trajectories.
Can be left as sorry without blocking any real proof.

## Strategy
1. Close Gap 2 (flux integrability via continuous_tsum for resolver)
2. Close Gap 3 (hmapsTo/hcontr from Duhamel bounds + integrability)
3. Sorry Gap 1 (semigroup smoothing — needs Parseval bridge, multi-day)
4. Accept Gap 4 sorry (edge case)
5. Main theorem assembles with 2 sorry (Gap 1 + Gap 4)
