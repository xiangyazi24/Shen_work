# Q1128 (cron2) — sorry 3G closed-slab continuity

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Result

The shortest code path for sorry 3G is already present as a scaffold.

Add:

```lean
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr
```

Then the 3G field can be replaced by:

```lean
      -- Field 3: ContinuousOn of time derivative on closed slab.
      simpa using
        ShenWork.IntervalCoupledRegularityBootstrap
          .chemDivMixedTimeDeriv_jointContinuousOn_closed
          (ShenWork.Paper2.Level0HeatMixedRepr
            .chemDivMixedTimeDerivClosedRepr_level0
              (p := p) (u₀ := u₀) (M₀ := M₀) (τ := s)
              hs_pos _hu₀_bound _hu₀_cont)
```

This matches the local choice

```lean
δ = min 1 (s / 2)
```

because `chemDivMixedTimeDerivClosedRepr_level0` produces

```lean
ChemDivMixedTimeDerivClosedRepr
  p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2))
```

This is the fastest way to fill the local sorry. It does not remove the deeper analytic debt, because `IntervalLevel0HeatMixedRepr.lean` still contains internal sorries.

## What exists

### `IntervalLevel0HeatMixedRepr.lean`

This file exists at:

```text
ShenWork/Paper2/IntervalLevel0HeatMixedRepr.lean
```

It defines the level-0 heat coefficient family:

```lean
def level0HeatCoeff (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ → ℝ :=
  fun k t =>
    Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k
```

It defines the canonical positive-time slab cutoff:

```lean
def canonicalSlabLeft (τ : ℝ) : ℝ :=
  τ - min 1 (τ / 2)

def level0SlabCutoff (τ : ℝ) : ℝ → ℝ :=
  smoothRightCutoff (canonicalSlabLeft τ / 4) (canonicalSlabLeft τ / 2)
```

and proves:

```lean
lemma level0SlabCutoff_eq_one_on_slab {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Icc (τ - min (1 : ℝ) (τ / 2)) (τ + min (1 : ℝ) (τ / 2))) :
    level0SlabCutoff τ t = 1
```

The main theorem is:

```lean
theorem chemDivMixedTimeDerivClosedRepr_level0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ (min (1 : ℝ) (τ / 2))
```

Internally it builds a `Gmix` from ten cutoff-patched series:

```lean
mixedAlgebra p.β
  (cutoffRep τ (valueSeriesRep cH))
  (cutoffRep τ (iterateDtValue cH))
  (cutoffRep τ (iterateDtGrad cH))
  (cutoffRep τ (gradSeriesRep cH))
  (cutoffRep τ (valueSeriesRep (resolverTimeCoeff p u)))
  (cutoffRep τ (gradSeriesRep (resolverTimeCoeff p u)))
  (cutoffRep τ (grad2SeriesRep (resolverTimeCoeff p u)))
  (cutoffRep τ (resolverDtValue p u))
  (cutoffRep τ (resolverDtGrad p u))
  (cutoffRep τ (resolverDtGrad2 p u))
```

The missing pieces in this scaffold are:

```lean
hUc hUtc hUtxc hUxc
hVc hVxc hVxxc hVtc hVtxc hVtxxc
hfloor
hagree
```

So `chemDivMixedTimeDerivClosedRepr_level0` is already the right API, but it is not yet analytically closed.

### `coupledChemDivTimeDerivativeLift`

In `IntervalChemDivTimeDerivative.lean`, the chemical time derivative is:

```lean
def coupledChemicalTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => intervalDomainLift (coupledChemicalConcentration p u r) x) s
```

The chem-div derivative field is:

```lean
def coupledChemDivTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv
    (fun y : ℝ =>
      let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
      let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
      ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
          (1 + v y) ^ p.β +
        intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
        p.β * intervalDomainLift (u s) y * deriv v y * vt y /
          (1 + v y) ^ (p.β + 1))
    x
```

So it is exactly the spatial derivative of the chain-rule expression for the time derivative of

```lean
u * deriv v / (1 + v)^β
```

where `slopeSlice u s y` is the `u` time derivative and `coupledChemicalTimeDerivativeLift p u s` is the `v` time derivative.

### The closed-slab continuity theorem

`IntervalChemDivTimeDerivative.lean` has continuity for `coupledChemicalTimeDerivativeLift`, i.e. for `vt`, but not directly for `coupledChemDivTimeDerivativeLift`.

The theorem needed for 3G is in `IntervalChemDivTimeDerivClosed.lean`:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

and:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

This is exactly the Field 3 goal after instantiating `τ := s` and `δ := min 1 (s/2)`.

## What still needs to be proved for a no-new-sorry closure

The generic infrastructure is mostly present:

```lean
ShenWork.IntervalChemDivMixedReprConstruct.mixedAlgebra
ShenWork.IntervalChemDivMixedReprConstruct.ChemDivMixedReprData
ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data
ShenWork.IntervalChemDivMixedReprWitness.ChemDivMixedReprWitnessData
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_witness
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

The most useful existing constructor is:

```lean
chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

For level 0, instantiate it with:

```lean
u  := conjugatePicardIter p u₀ 0
cH := ShenWork.Paper2.Level0HeatMixedRepr.level0HeatCoeff u₀
```

It requires:

```lean
H      : PhysicalResolverJointC2Data p u Bt
Hu     : IteratePicardJointC2Data u cH Btu
Hg2u   : Summable (boundedWeightJointGradMajorant Btu 2)
hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q
bdry   : endpoint agreement for x ∈ ({0, 1} : Set ℝ)
```

So the real remaining work is not the final `ContinuousOn` transfer. The remaining work is proving the level-0 witness data:

1. heat-side `IteratePicardJointC2Data` for `level0HeatCoeff u₀`;
2. resolver-side `PhysicalResolverJointC2Data`, probably via `IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor` after building the source-time `C²` package for `ν * (S(t)u₀)^γ`;
3. the denominator floor for the resolver value representative;
4. endpoint agreement for the mixed algebra.

## Recommended shortest route

For the immediate Q1128 3G patch, use the one-line fill through:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
  (Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0 ...)
```

For actual proof debt reduction, finish `IntervalLevel0HeatMixedRepr.lean` by routing through `chemDivMixedTimeDerivClosedRepr_of_mkWitness` rather than manually redoing all ten continuity and agreement proofs.
