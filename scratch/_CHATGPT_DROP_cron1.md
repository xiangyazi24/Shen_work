# Q1473 (cron1) -- rpow composition and heat Neumann search

Repository: `xiangyazi24/Shen_work`
Branch: `chatgpt-scratch`
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only repository search. I did not change Lean source. Direct `fetch_file` of `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` at `chatgpt-scratch` returned 404, but GitHub code search exposed the file at indexed snapshot:

```text
7db6d8e4b01d279823281613bb824200483faddd
```

The names below are from that snapshot. This report is committed to `chatgpt-scratch`.

## Useful imports

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalResolverPowerDecay
import ShenWork.Paper2.IntervalCkComposition
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalDuhamelClosedC2
```

## Target obligations

The target call is in:

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

It invokes:

```lean
ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
```

The relevant fields are:

```lean
hsliceC2 : forall i, i <= 2 -> forall t, 0 < t ->
  ContDiffOn R 2 ((sliceFam srcSlice srcSlice1 srcSlice2 i) t) (Icc 0 1)

hsliceNeumann : forall i, i <= 2 -> forall t, 0 < t ->
  Tendsto (deriv ((sliceFam srcSlice srcSlice1 srcSlice2 i) t)) (nhdsWithin 0 (Ioi 0)) (nhds 0) /\
  Tendsto (deriv ((sliceFam srcSlice srcSlice1 srcSlice2 i) t)) (nhdsWithin 1 (Iio 1)) (nhds 0) /\
  deriv ((sliceFam srcSlice srcSlice1 srcSlice2 i) t) 0 = 0 /\
  deriv ((sliceFam srcSlice srcSlice1 srcSlice2 i) t) 1 = 0
```

The asked formula `srcSlice p u t x = p.nu * (intervalDomainLift (u t) x)^p.gamma` is the `i = 0` case. The actual obligation also includes `i = 1,2`.

## rpow / ContDiffOn API found

Core Mathlib names already used in this repo:

```lean
ContDiffOn.rpow_const_of_ne
ContinuousOn.rpow_const
HasDerivAt.rpow_const
Real.contDiffAt_rpow_const_of_ne
```

Repo wrappers and patterns:

```lean
ShenWork.IntervalMildPicardRegularity.exists_pos_neighborhood_of_compact_positive
ShenWork.IntervalMildPicardRegularity.contDiffOn_rpow_of_contDiff_pos
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_contDiffOn_of_contDiff_pos
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_contDiffOn_Icc

ShenWork.Paper2.IntervalCkComposition.contDiff_two_rpow_of_pos
ShenWork.Paper2.IntervalCkComposition.contDiff_two_one_add_rpow_neg
ShenWork.Paper2.IntervalCkComposition.memHSigma_rpow_of_contDiff_two
ShenWork.Paper2.IntervalCkComposition.memHSigma_one_add_rpow_neg_of_contDiff_two

ShenWork.Paper2.ResolverPowerDecay.powerSourceFun_hasDerivAt
ShenWork.Paper2.ResolverPowerDecay.Fp1_hasDerivAt
ShenWork.Paper2.ResolverPowerDecay.deriv_powerSource_eq_Fp1
ShenWork.Paper2.ResolverPowerDecay.secondDeriv_powerSource_eq_Fp2
ShenWork.Paper2.ResolverPowerDecay.powerSourceFun_secondDeriv_abs_integral_le
ShenWork.Paper2.ResolverPowerDecay.powerSourceFun_cosineCoeff_quadratic_decay_explicit
```

Most directly relevant wrapper:

```lean
theorem contDiffOn_rpow_of_contDiff_pos
    {g : R -> R} {alpha : R} {U : Set R}
    (hg : ContDiff R 2 g) (_hU : IsOpen U)
    (hpos : forall x in U, 0 < g x) :
    ContDiffOn R 2 (fun x => g x ^ alpha) U :=
  hg.contDiffOn.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))
```

For a source of the form `nu * u^gamma`, the existing local pattern is in `IntervalResolverPowerDecay`: use `ContDiffOn.rpow_const_of_ne`, then `.const_smul nu`, then `.congr` to rewrite scalar multiplication as ordinary multiplication.

For the zeroth source slice, the schematic proof shape is:

```lean
have hpow : ContDiffOn R 2 (fun x => (intervalDomainLift (u t) x) ^ p.gamma) (Set.Icc 0 1) :=
  hg.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))
simpa [smul_eq_mul] using hpow.const_smul p.nu
```

## Heat semigroup regularity names

Positive-time spatial smoothing in `IntervalHeatSemigroupHighRegularity.lean`:

```lean
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_eigenvalueSq_summable
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_contDiff_four
```

`heatSemigroup_contDiff_four` is for the cosine-series representative of `S(t)u0`. It uses:

```lean
ShenWork.Paper2.ParabolicDuhamelGainNonCircular.cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
```

Joint positive-time C2 names in the same file:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatSeries_contDiff_two
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSeries_eventuallyEq_cutoff
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

Level 0 of the conjugate Picard iterate is exactly the heat semigroup:

```lean
ShenWork.IntervalConjugatePicard.conjugatePicardIter
-- 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u0) x.1
```

## Neumann API found

Core cosine-series endpoint lemmas:

```lean
ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero
ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one
```

Heat-value / full semigroup endpoint bridge:

```lean
ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_deriv_at_zero
ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_deriv_at_one
ShenWork.IntervalSemigroupNeumann.deriv_eq_left_of_eqOn_Ioo_of_contDiff
ShenWork.IntervalSemigroupNeumann.deriv_eq_right_of_eqOn_Ioo_of_contDiff
ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_zero
ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_one
ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_limit_left
ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_limit_right
```

Zero-extension / slice bridge names:

```lean
ShenWork.IntervalCosineSliceRegularity.intervalDomainLift_deriv_left_endpoint_zero_of_ne
ShenWork.IntervalCosineSliceRegularity.intervalDomainLift_deriv_right_endpoint_zero_of_ne
ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_conjunct7
ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_contDiffOn_Ioo
ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_neumann_limit_left
ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_neumann_limit_right
```

Positive-slice endpoint wrappers:

```lean
ShenWork.IntervalSemigroupNeumann.mildSolution_neumann_deriv_zero_of_pos
ShenWork.IntervalSemigroupNeumann.mildSolution_neumann_deriv_one_of_pos
ShenWork.IntervalSemigroupNeumann.mildSolution_neumann_of_positive_time
```

Composed-source Neumann patterns:

```lean
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_deriv_zero_at_zero
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_deriv_zero_at_one
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_tendsto_deriv_left
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_tendsto_deriv_right
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_intervalWeakH2Neumann
ShenWork.EWA.realSlice_logSource_C2Neumann
```

For the power source, I found endpoint derivative and second-derivative machinery, but not standalone names `powerSourceFun_tendsto_deriv_left/right`. The one-sided endpoint-limit proof is effectively inside `powerSourceFun_cosineCoeff_quadratic_decay_explicit`: it builds continuity of `Fp1`, identifies `deriv (fun y => nu * u y ^ gamma)` with `Fp1`, and obtains the two `Tendsto` facts from `ContinuousOn.continuousWithinAt` plus endpoint derivative equalities.

Suggested extraction before closing `hsliceNeumann`:

```lean
powerSourceFun_deriv_zero_at_zero
powerSourceFun_deriv_zero_at_one
powerSourceFun_tendsto_deriv_left
powerSourceFun_tendsto_deriv_right
```

Then `hsliceNeumann` for `i = 0` should follow the same shape as `realSlice_logSource_C2Neumann`, replacing the logistic-source lemmas with the extracted power-source lemmas and using the heat semigroup Neumann lemmas for the underlying profile.

## Search log

```text
IntervalHeatSemigroupHighRegularity
ContDiffOn.rpow
rpow_const ContDiffOn
rpow_const_of_ne
continuousOn.rpow_const
intervalFullSemigroupOperator_neumann_at_zero
cosineCoeffSeries_deriv_at_zero
heatSemigroup_flooredSourceTimeData hsliceC2 hsliceNeumann
conjugatePicardIter 0 intervalFullSemigroupOperator
```
