# Q1472 (cron1) -- heat semigroup floor and datum positivity

Repository: `xiangyazi24/Shen_work`
Branch: `chatgpt-scratch`
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only repository search. I did not run Lean locally and did not edit Lean source.

As in Q1473, direct fetch of `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` at `chatgpt-scratch` returned 404, but GitHub code search exposed the indexed snapshot:

```text
7db6d8e4b01d279823281613bb824200483faddd
```

The names below are from that snapshot. This report is committed to `chatgpt-scratch`.

## Finding

Yes: if the intended proof of the line-832 floor is to use the existing theorem

```lean
ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
```

then `heatSemigroup_level0_resolverJointC2Data` should take an additional hypothesis

```lean
(hu0_pos : forall x : intervalDomainPoint, 0 < u0 x)
```

because the current theorem only has

```lean
(hu0_bound : forall k, |cosineCoeffs (intervalDomainLift u0) k| <= M0)
(hu0_cont : Continuous u0)
```

and those do not imply strict positivity of the heat slice. For arbitrary real `p.gamma`, strict positivity is also analytically needed for the `u^gamma` source-slice smoothness route.

The local patch shape is:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

-- in heatSemigroup_level0_resolverJointC2Data, add:
--   (hu0_pos : forall x : intervalDomainPoint, 0 < u0 x)

(hfloor := by
  intro t ht x hx
  exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
    (p := p) hu0_cont hu0_pos (t := t) ht (x := x) hx)
```

Then the immediate wrapper

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatResolverJointContDiffAt_two
```

should also take `hu0_pos` and pass it into `heatSemigroup_level0_resolverJointC2Data`.

## Why downstream does not currently supply this automatically

### 1. `coupledChemical_jointContDiffAt_two`

Located in:

```lean
ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
```

The theorem

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
```

takes only:

```lean
(H : PhysicalResolverJointC2Data p u Bt)
(hx : x in Ioo 0 1)
```

It is a resolver-series regularity assembler. It does not know anything about the original datum `u0`, and it has no positivity hypothesis that can produce

```lean
forall x, 0 < u0 x
```

So it cannot discharge the heat base floor.

### 2. `resolver_jointC2At_of_spectralAgreement`

The wrapper in

```lean
ShenWork.PDE.IntervalCoupledResolverJointC2
```

is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration_resolver_jointC2At
```

It calls

```lean
resolver_jointC2At_of_spectralAgreement
```

with spectral agreement, time-window facts, an interior-space witness, and a local spectral `hC2` producer. This path is independent of `u0` strict positivity. It is not a source of `hu0_pos`.

The strengthened C2-coefficient path

```lean
resolver_jointC2At_of_spectralAgreement_c2Data
```

also only unpacks restart spectral data. It does not carry positivity of initial datum either.

### 3. FAC chain

The relevant FAC structure is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorFACInputs
```

and its slab predicate:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.FACLocalSlabInputs
```

`FACLocalSlabInputs` contains:

```lean
(forall s, Continuous (u s))
(forall s, forall x : intervalDomainPoint, 0 <= u s x)
```

but not strict positivity of the original datum. The file explicitly says the resolver floor is not a carried input; it is proved from nonnegativity and continuity via

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemical_floor_pos_of_nonneg_continuous
```

This gives strict positivity of `1 + v`, not strict positivity of `u0`.

So the FAC package does not directly supply the `hu0_pos` needed by `heatSemigroup_pos_of_pos`.

## Positivity structures found

The requested structure exists here:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper.BoundedLipschitzPositiveOnUnit
```

It has fields:

```lean
m_pos : 0 < m
lower_bound : forall x in Set.Icc 0 1, m <= u x
bounded : exists M, forall x in Set.Icc 0 1, |u x| <= M
lipschitz : exists K : R>=0, LipschitzOnWith K u (Set.Icc 0 1)
```

But search only found it in `IntervalMildSourceDecayHelper.lean`; it is part of weak H2 / source coefficient decay packaging:

```lean
PowerSourceH2NeumannData
powerSourceH2NeumannData_of_source_contDiffOn
```

I did not find it feeding `CoupledChemDivFluxFactorFACInputs` or `heatSemigroup_level0_resolverJointC2Data`.

Other strict-positive-datum bridges found:

```lean
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_uniformFloor_of_continuous_pos
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_paperPositiveInitialDatum_of_continuous_pos
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_mildExistenceData_of_continuous_positiveDatum
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_gradientMildSolutionData_of_continuous_positiveDatum
```

These show that `Continuous u0` plus `forall x, 0 < u0 x` is already a recognized route to a uniform floor / paper-positive datum.

There is also a cone route in

```lean
ShenWork.IntervalMildPicardConeData.coneGradientMildSolutionData_exists_with_data
```

that assumes nonnegative datum plus positive somewhere and proves positive heat/Picard slices for positive times. That is weaker than `forall x, 0 < u0 x`, but it is not connected to the local `heatSemigroup_pos_of_pos` theorem used for the line-832 floor.

## Recommendation

For the current local gap, add `hu0_pos` to `heatSemigroup_level0_resolverJointC2Data` and to `heatResolverJointContDiffAt_two`, then discharge line 832 with `heatSemigroup_pos_of_pos`.

This is the smallest honest patch because:

1. the theorem is not semantically true for arbitrary sign-changing or zero-valued data when the source is `u^gamma` with real `gamma`;
2. the existing proof theorem already requires strict positive initial datum;
3. repository search did not find any downstream resolver/FAC API that can synthesize `hu0_pos` for this theorem;
4. direct callers of `heatSemigroup_level0_resolverJointC2Data` appear local to `IntervalHeatSemigroupHighRegularity.lean`, so the API blast radius is small.

If later the FAC chain wants compatibility with the cone route, the better abstraction would be to generalize the heat theorem with a direct floor hypothesis:

```lean
(hfloor : forall t, 0 < t -> forall x in Set.Icc (0:R) 1,
  0 < intervalDomainLift (conjugatePicardIter p u0 0 t) x)
```

and then provide two corollaries:

```lean
-- strict positive datum route
..._of_posDatum (hu0_pos : forall x, 0 < u0 x)

-- cone/nonnegative-positive-somewhere route, if/when the needed heat positivity theorem is wired
..._of_heatFloor hfloor
```

But for the concrete line-832 `sorry`, `hu0_pos` is the correct immediate missing hypothesis.

## Search log

```text
BoundedLipschitzPositiveOnUnit
coupledChemical_jointContDiffAt_two
resolver_jointC2At_of_spectralAgreement
IntervalChemDivFluxFactorFAC
structure CoupledChemDivFluxFactorFACInputs
heatSemigroup_level0_resolverJointC2Data
heatResolverJointContDiffAt_two
hu0_pos / hu₀_pos
PositiveInitialDatum intervalDomain u0
heatSemigroup_pos_of_pos
```
