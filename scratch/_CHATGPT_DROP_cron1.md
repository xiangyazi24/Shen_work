# Q1483 (cron1) -- caller trace for heat resolver positivity fix

Repository: `xiangyazi24/Shen_work`
Branch: `chatgpt-scratch`
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only repository search. I did not run Lean locally and did not edit Lean source.

As in the preceding cron drops, direct fetch of some files at branch `chatgpt-scratch` was incomplete, but GitHub code search exposed the indexed snapshot:

```text
7db6d8e4b01d279823281613bb824200483faddd
```

The `file:line` entries below are from that snapshot. This report is committed to `chatgpt-scratch`.

## Bottom line

Adding

```lean
(hu0_pos : forall x : intervalDomainPoint, 0 < u0 x)
```

is still the smallest local fix for `hfloor` in `heatSemigroup_level0_resolverJointC2Data`.

Search result summary:

* `heatResolverJointContDiffAt_two` has no code caller outside its defining file. Search found only `IntervalHeatSemigroupHighRegularity.lean` and `UNDERSTANDING.md`.
* The FAC chain does **not** call `heatResolverJointContDiffAt_two`; it calls the generic physical resolver theorem `coupledChemical_jointContDiffAt_two H` from a supplied `PhysicalResolverJointC2Data`.
* The generic FAC callers carry `hu_cont`, `hu_nonneg`, and a strict floor for `1 + v`; they do not carry `BoundedLipschitzPositiveOnUnit` or `forall x, 0 < u0 x`.
* `BoundedLipschitzPositiveOnUnit` appears only in `IntervalMildSourceDecayHelper.lean` in this search; it is not wired into these call sites.

So propagating `hu0_pos` through `heatSemigroup_level0_resolverJointC2Data` and `heatResolverJointContDiffAt_two` should have a tiny code blast radius.

## Direct heat chain

### `heatSemigroup_level0_resolverJointC2Data`

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:822
```

Signature currently has only:

```lean
(hu0_bound : forall k, |cosineCoeffs (intervalDomainLift u0) k| <= M0)
(hu0_cont : Continuous u0)
```

The missing floor is exactly:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:832
```

```lean
(hfloor := by intro t ht x hx; sorry)
```

This is the spot to replace with:

```lean
(hfloor := by
  intro t ht x hx
  exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
    (p := p) hu0_cont hu0_pos (t := t) ht (x := x) hx)
```

This requires adding `hu0_pos` to the theorem.

### `heatResolverJointContDiffAt_two`

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:866
```

This wrapper currently takes:

```lean
(hu0_bound : forall k, |cosineCoeffs (intervalDomainLift u0) k| <= M0)
(hu0_cont : Continuous u0)
```

It calls `heatSemigroup_level0_resolverJointC2Data` here:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:878
```

and then calls the generic resolver assembler here:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:880
```

```lean
exact coupledChemical_jointContDiffAt_two hBt hx0
```

Therefore `heatResolverJointContDiffAt_two` should also take `hu0_pos` and pass it into `heatSemigroup_level0_resolverJointC2Data`.

### Who calls `heatResolverJointContDiffAt_two`?

Code search result:

```text
heatResolverJointContDiffAt_two
```

returned only:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
UNDERSTANDING.md
```

I found no Lean code caller outside the defining file. `UNDERSTANDING.md` mentions it as a documented route / option, not as a Lean call.

Conclusion: adding `hu0_pos` to `heatResolverJointContDiffAt_two` should not require a cascade through other Lean files, unless unindexed/local branch files differ from the searched snapshot.

## Direct callers of `coupledChemical_jointContDiffAt_two`

### Definition

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean:116
```

The theorem is:

```lean
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : Real -> intervalDomainPoint -> Real} {Bt : Nat -> Nat -> Real}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : Real} (hx : x in Ioo 0 1) :
    ContDiffAt Real 2
      (fun q : Real x Real =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

It has no positivity hypothesis. It consumes only `PhysicalResolverJointC2Data p u Bt` plus interior space `hx`.

### Caller 1: heat wrapper

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:880
```

Inside `heatResolverJointContDiffAt_two`:

```lean
exact coupledChemical_jointContDiffAt_two hBt hx0
```

This is the only direct bridge from the heat-level package to the generic resolver theorem.

Current positivity at this wrapper: none, only `hu0_bound` and `hu0_cont`. This is the place where adding `hu0_pos` matters.

### Caller 2: FAC commute discharge, inner commute theorem

File:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:21
```

The theorem is:

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2
    {p : CM2Params} {u : Real -> intervalDomainPoint -> Real} {Bt : Nat -> Nat -> Real}
    (H : PhysicalResolverJointC2Data p u Bt) {s y : Real} (hy : y in Ioo 0 1) : ...
```

It calls `coupledChemical_jointContDiffAt_two` at:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:30
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:38
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:50
```

Its inputs are only `H : PhysicalResolverJointC2Data p u Bt` and an interior-space point. No `u0`, no `hu0_pos`, no `BoundedLipschitzPositiveOnUnit`.

### Caller 3: FAC time-bridge theorem

File:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:68
```

The theorem is:

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
    {p : CM2Params} {u : Real -> intervalDomainPoint -> Real} {Bt : Nat -> Nat -> Real}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_c2 : forall x in Ioo 0 1, forall s : Real,
      ContDiffAt Real 2 (fun q => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : forall s : Real, forall x : Real,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    ...
```

It calls:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:84
  coupledChemical_jointContDiffAt_two H hy

ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:85
  coupledChemical_grad_jointContDiffAt_two H hy

ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:88
  coupledChemical_innerCommute_of_physicalJointC2 H hy
```

The positivity hypothesis here is only:

```lean
hbase : forall s x, 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

That is a resolver-denominator floor, not strict positivity of the original datum `u0`.

### Caller 4: physical FAC input producer

File:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:99
```

The theorem is:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    {p : CM2Params} {u : Real -> intervalDomainPoint -> Real} {Bt : Nat -> Nat -> Real}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : forall s : Real, Continuous (u s))
    (hu_nonneg : forall s : Real, forall x : intervalDomainPoint, 0 <= u s x)
    (other : ...)
```

It constructs:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:113
```

```lean
hbase : forall s x,
  0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

from:

```lean
coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg
```

and calls the time-bridge theorem at:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:120
```

Again, the positivity in this caller is only nonnegativity of the evolving `u s` plus continuity, used to prove `1+v > 0`. It does not provide `forall x, 0 < u0 x`.

## FAC input positivity package

File:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:21
```

`FACLocalSlabInputs` includes:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:28
  forall s, Continuous (u s)

ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:29
  forall s, forall x : intervalDomainPoint, 0 <= u s x
```

The FAC package is:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:49
```

and the resolver floor theorem is:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:60
```

```lean
theorem coupledChemical_floor_pos_of_nonneg_continuous
    (hu_cont : forall s, Continuous (u s))
    (hu_nonneg : forall s, forall x, 0 <= u s x)
    (s x : Real) :
    0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

So the FAC route deliberately carries nonnegativity and resolver denominator positivity, not strict initial-datum positivity.

## `BoundedLipschitzPositiveOnUnit`

Global search for:

```text
BoundedLipschitzPositiveOnUnit
```

found only:

```text
ShenWork/PDE/IntervalMildSourceDecayHelper.lean:38
```

The structure is:

```lean
structure BoundedLipschitzPositiveOnUnit (u : Real -> Real) (m : Real) where
  m_pos : 0 < m
  lower_bound : forall x in Set.Icc 0 1, m <= u x
  bounded : exists M, forall x in Set.Icc 0 1, abs (u x) <= M
  lipschitz : exists K : RealNN, LipschitzOnWith K u (Set.Icc 0 1)
```

It is used in the source-decay/H2 package, not in the heat resolver call chain above.

## Comments / non-call references

Search also found comment/doc references:

```text
ShenWork/PDE/IntervalIteratePicardJointC2.lean:21
```

This says the iterate u-side C2 assembly mirrors `coupledChemical_jointContDiffAt_two`, but it is not a caller.

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:46-48
```

This is a comment describing the chain ending in `coupledChemical_jointContDiffAt_two`, not a caller.

```text
UNDERSTANDING.md:114-128 approximately
```

This is architecture/status prose mentioning `coupledChemical_jointContDiffAt_two` and `heatResolverJointContDiffAt_two`, not Lean code.

## Recommendation

Patch only the heat-level API:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    ...
    (hu0_bound : ...)
    (hu0_cont : Continuous u0)
    (hu0_pos : forall x : intervalDomainPoint, 0 < u0 x) :
    exists Bt, PhysicalResolverJointC2Data p (conjugatePicardIter p u0 0) Bt := by
  ...
  (hfloor := by
    intro t ht x hx
    exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
      (p := p) hu0_cont hu0_pos (t := t) ht (x := x) hx)
```

and update the local wrapper:

```lean
theorem heatResolverJointContDiffAt_two
    ...
    (hu0_bound : ...)
    (hu0_cont : Continuous u0)
    (hu0_pos : forall x : intervalDomainPoint, 0 < u0 x)
    ... := by
  obtain <Bt, hBt> := heatSemigroup_level0_resolverJointC2Data
    (p := p) hu0_bound hu0_cont hu0_pos
  exact coupledChemical_jointContDiffAt_two hBt hx0
```

No current Lean code caller outside `IntervalHeatSemigroupHighRegularity.lean` needs updating according to the search. The FAC callers are generic over `PhysicalResolverJointC2Data`; they should not receive `hu0_pos` unless a later theorem specializes them to the heat-semigroup level-0 data.

## Search log

```text
heatResolverJointContDiffAt_two
coupledChemical_jointContDiffAt_two
coupledChemical_grad_jointContDiffAt_two
BoundedLipschitzPositiveOnUnit
FACLocalSlabInputs
CoupledChemDivFluxFactorFACInputs
heatSemigroup_level0_resolverJointC2Data
```
