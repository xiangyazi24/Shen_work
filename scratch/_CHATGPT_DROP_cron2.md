# Q1077 (cron2) — Does a `PhysicalResolverJointC2Data`-only 3G bridge exist?

Static GitHub-connector inspection only; I did **not** run Lean locally.

## Verdict

No: I did **not** find an existing proved theorem of the shape

```lean
import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete

example
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {Bt : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ := by
  -- No existing theorem found that closes this from H alone.
  sorry
```

The committed bridge `chemDivMixedTimeDerivClosedRepr_of_mkWitness` still needs the u-side iterate data:

```lean
import ShenWork.PDE.IntervalChemDivMixedReprWitness

open ShenWork.IntervalChemDivMixedReprWitness
open ShenWork.IntervalIteratePicardJointC2
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalCoupledRegularityBootstrap

#check ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
-- {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ}
-- {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ} →
--   PhysicalResolverJointC2Data p u Bt →
--   IteratePicardJointC2Data u c Btu →
--   Summable (boundedWeightJointGradMajorant Btu 2) →
--   (∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q) →
--   boundary_agree →
--   ChemDivMixedTimeDerivClosedRepr p u τ δ
```

So the answer to the main question is: **no, not via the current witness bridge, and I found no wrapper that removes `IteratePicardJointC2Data`.**

## Exact existing producers / wrappers found

### 1. Generic data constructor

```lean
import ShenWork.PDE.IntervalChemDivMixedReprConstruct

#check ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data
-- ChemDivMixedReprData p u τ δ →
--   ChemDivMixedTimeDerivClosedRepr p u τ δ
```

This is the lowest-level constructor.  It takes the full `ChemDivMixedReprData` bundle: ten continuous representatives, the global floor, and closed-slab agreement with `mixedAlgebra`.

### 2. Witness-bundle constructor

```lean
import ShenWork.PDE.IntervalChemDivMixedReprWitness

#check ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_witness
-- ChemDivMixedReprWitnessData p u τ δ →
--   ChemDivMixedTimeDerivClosedRepr p u τ δ
```

This only replaces `ChemDivMixedReprData` by the richer witness bundle.  It still does not take `PhysicalResolverJointC2Data` directly.

### 3. Main spectral witness bridge

```lean
import ShenWork.PDE.IntervalChemDivMixedReprWitness

#check ShenWork.IntervalChemDivMixedReprWitness.mkWitnessData
#check ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

This is the direct bridge found in Q1067.  Its dependencies are exactly:

```lean
(H : PhysicalResolverJointC2Data p u Bt)
(Hu : IteratePicardJointC2Data u c Btu)
(Hg2u : Summable (boundedWeightJointGradMajorant Btu 2))
(hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
(bdry : ... boundary agreement ...)
```

It uses `H` for the resolver-side reps

```text
Vc, Vxc, Vxxc, Vtc, Vtxc, Vtxxc
```

but it uses `Hu` and `Hg2u` for the u-side reps

```text
Uc, Utc, Utxc, Uxc
```

That is the essential reason `PhysicalResolverJointC2Data` alone is insufficient for this theorem.

### 4. Iterate-gradient wrapper

```lean
import ShenWork.PDE.IntervalIterateGradMajorant

#check ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
-- PhysicalResolverJointC2Data p u Bt →
-- IteratePicardJointC2Data u c Btu →
-- (∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Btu m)) →
-- floor → boundary →
-- ChemDivMixedTimeDerivClosedRepr p u τ δ
```

This wrapper only packages the iterate gradient summability leg.  It still requires `IteratePicardJointC2Data`.

### 5. Heat-Level0 direct skeleton

```lean
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

#check ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0
#check ShenWork.Paper2.Level0HeatMixedRepr.level0HeatCoeff
#check ShenWork.Paper2.Level0HeatMixedRepr.level0HeatGmix
```

This file is important because it is the only thing I found that intentionally avoids passing `IteratePicardJointC2Data` into the mixed-repr bridge.  But it is **not** a `PhysicalResolverJointC2Data`-only wrapper.  It directly constructs cutoff-patched heat/resolver representatives and then feeds `chemDivMixedTimeDerivClosedRepr_of_data`.

Its theorem signature is heat-specific:

```lean
{p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ} →
  0 < τ →
  (∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) →
  Continuous u₀ →
  ChemDivMixedTimeDerivClosedRepr
    p (conjugatePicardIter p u₀ 0) τ (min (1 : ℝ) (τ / 2))
```

The implementation shown in the file is still a skeleton with `sorry`s for continuity, floor, and agreement of the ten cutoff reps.  It is a separate proof route, not an already-available wrapper around `PhysicalResolverJointC2Data`.

## Search result for `IteratePicardJointC2Data`

The structure is:

```lean
import ShenWork.PDE.IntervalIteratePicardJointC2

#check ShenWork.IntervalIteratePicardJointC2.IteratePicardJointC2Data
#check ShenWork.IntervalIteratePicardJointC2.iterate_lift_jointContDiffAt_two
#check ShenWork.IntervalIteratePicardJointC2.iterate_hu_c2_slab
```

`IteratePicardJointC2Data u c Bt` requires:

```lean
lift_eq_series : ∀ {t x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
  intervalDomainLift (u t) x = ∑' k : ℕ, c k t * cosineMode k x

coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (c k)

coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (c k) t‖ ≤ Bt i k

value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointMajorant Bt m)
```

I did **not** find a heat-Level0 constructor such as any of these names:

```lean
heatSemigroup_iteratePicardJointC2Data
level0Heat_iteratePicardJointC2Data
iteratePicardJointC2Data_level0
IteratePicardJointC2Data.of_heatSemigroup
```

I also searched for the combination `IteratePicardJointC2Data level0HeatCoeff` and `IteratePicardJointC2Data conjugatePicardIter`; no direct constructor showed up.

## Is `IteratePicardJointC2Data` trivially constructible for heat Level0?

Not as the structure is currently typed.

For Level0 the natural coefficient family is

```lean
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

#check ShenWork.Paper2.Level0HeatMixedRepr.level0HeatCoeff
-- level0HeatCoeff u₀ k t =
--   Real.exp (-t * unitIntervalCosineEigenvalue k) *
--     cosineCoeffs (intervalDomainLift u₀) k
```

The heat semigroup does have local positive-time joint regularity:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

#check ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

but that theorem gives only `ContDiffAt ℝ 2` of the uncurried heat series at points with positive time.  It does **not** package the coefficient representation, global-in-time coefficient envelopes, and `boundedWeightJointMajorant` summability demanded by `IteratePicardJointC2Data`.

Moreover, the raw heat coefficients are not globally uniformly bounded in time for negative `t`:

```lean
-- For k > 0, λ_k > 0, so
--   exp (-t * λ_k)
-- blows up as t → -∞.
-- Thus a finite envelope Bt i k independent of t cannot bound
--   ‖iteratedFDeriv ℝ i (level0HeatCoeff u₀ k) t‖
-- for arbitrary u₀ and all t : ℝ.
```

That is why the heat regularity proof uses a positive-time cutoff to obtain local/global representatives near the desired slab, rather than trying to force the raw heat coefficient family into a global `IteratePicardJointC2Data` bundle.

## Practical conclusion for 3G

For the current committed bridges:

```text
PhysicalResolverJointC2Data alone is enough for the resolver V-side reps,
but not enough for the u-side U, Ut, Utx, Ux reps.
```

So 3G cannot currently be closed by only applying a `PhysicalResolverJointC2Data` bridge.  One of these extra pieces is still needed:

1. keep using `chemDivMixedTimeDerivClosedRepr_of_mkWitness`, and provide `IteratePicardJointC2Data` plus `Hg2u`, floor, and boundary; or
2. finish the heat-specific direct route in `ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0`; or
3. add a new positive-slab/cutoff witness theorem whose u-side assumptions are the heat-specific closed-slab representatives, not global `IteratePicardJointC2Data`.

The shortest honest statement of the missing bridge would look closer to this than to an `H`-only theorem:

```lean
import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.IntervalConjugatePicard

-- Proposed shape, not found as an existing theorem:
theorem level0_heat_mixedClosedRepr_of_physicalResolver_and_heatReps
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {Bt : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt)
    -- plus heat-specific closed-slab reps/continuity/agreement/floor/boundary data
    : ChemDivMixedTimeDerivClosedRepr p (conjugatePicardIter p u₀ 0) τ δ := by
  sorry
```

## Bottom line

Exact existing theorem names:

```text
ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_witness
ShenWork.IntervalChemDivMixedReprWitness.mkWitnessData
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0
ShenWork.IntervalIteratePicardJointC2.IteratePicardJointC2Data
ShenWork.IntervalIteratePicardJointC2.iterate_lift_jointContDiffAt_two
ShenWork.IntervalIteratePicardJointC2.iterate_hu_c2_slab
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

No exact existing theorem found:

```text
PhysicalResolverJointC2Data p u Bt → ChemDivMixedTimeDerivClosedRepr p u τ δ
```

and no heat-Level0 theorem found that constructs `IteratePicardJointC2Data` for `conjugatePicardIter p u₀ 0` / `level0HeatCoeff`.