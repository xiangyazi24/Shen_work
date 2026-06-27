# Q1102 (cron3): 3G without `IteratePicardJointC2Data`?

## Verdict

Yes, the alternative route is viable, and the repo already contains a Level0-specific scaffold for exactly this approach:

```lean
ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0
```

in

```text
ShenWork/Paper2/IntervalLevel0HeatMixedRepr.lean
```

This route avoids constructing `IteratePicardJointC2Data` for heat Level0. It instead builds the 3G object directly:

```lean
ChemDivMixedTimeDerivClosedRepr p (conjugatePicardIter p u₀ 0) τ δ
```

by supplying a `ChemDivMixedReprData` bundle to:

```lean
ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data
```

Then the existing theorem

```lean
ShenWork.IntervalCoupledRegularityBootstrap.chemDivMixedTimeDeriv_jointContinuousOn_closed
```

turns that representative into the desired closed-slab `ContinuousOn` of:

```lean
Function.uncurry (coupledChemDivTimeDerivativeLift p u)
```

So the answer is: **yes, prove 3G by direct representative construction, not through `IteratePicardJointC2Data`.**

## Why this avoids `IteratePicardJointC2Data`

The current `IteratePicardJointC2Data` route exists to manufacture the u-side representatives:

```lean
valueSeriesRep c
iterateDtValue c
iterateDtGrad c
gradSeriesRep c
```

from an abstract coefficient family `c`. For heat Level0, the coefficient family is explicit:

```lean
def level0HeatCoeff (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ → ℝ :=
  fun k t =>
    Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k
```

So you can use the heat coefficients directly, add a positive-time cutoff, and prove continuity of the ten smooth representative fields directly.

## Existing Level0 scaffold

`IntervalLevel0HeatMixedRepr.lean` defines the direct route.

### Canonical positive slab and cutoff

```lean
def canonicalSlabLeft (τ : ℝ) : ℝ :=
  τ - min 1 (τ / 2)

lemma canonicalSlabLeft_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < canonicalSlabLeft τ

def level0SlabCutoff (τ : ℝ) : ℝ → ℝ :=
  smoothRightCutoff (canonicalSlabLeft τ / 4) (canonicalSlabLeft τ / 2)

lemma level0SlabCutoff_eq_one_on_slab {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Icc (τ - min (1 : ℝ) (τ / 2)) (τ + min (1 : ℝ) (τ / 2))) :
    level0SlabCutoff τ t = 1
```

### Smooth representative

```lean
def cutoffRep (τ : ℝ) (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => level0SlabCutoff τ q.1 * F q
```

The proposed Level0 `Gmix` is:

```lean
def level0HeatGmix (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (τ : ℝ) :
    ℝ × ℝ → ℝ :=
  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
  let cH : ℕ → ℝ → ℝ := level0HeatCoeff u₀
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

### Main direct theorem target

```lean
theorem chemDivMixedTimeDerivClosedRepr_level0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ (min (1 : ℝ) (τ / 2))
```

The file already sets up all ten representatives and then calls:

```lean
chemDivMixedTimeDerivClosedRepr_of_data D
```

not

```lean
chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

So it bypasses `IteratePicardJointC2Data`.

## Current remaining work in the direct Level0 file

The theorem is scaffolded but not complete. The remaining `sorry`s are exactly the direct-representative obligations:

### Continuity of the ten representatives

```lean
hUc    : Continuous Uc
hUtc   : Continuous Utc
hUtxc  : Continuous Utxc
hUxc   : Continuous Uxc
hVc    : Continuous Vc
hVxc   : Continuous Vxc
hVxxc  : Continuous Vxxc
hVtc   : Continuous Vtc
hVtxc  : Continuous Vtxc
hVtxxc : Continuous Vtxxc
```

These are heat/resolver cosine-series continuity proofs with a time cutoff.

### Denominator floor

```lean
hfloor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
```

The intended proof is: outside the active positive-time region the cutoff makes the representative harmless; on the slab, use resolver positivity and agreement with the actual elliptic resolver. This may require a clean lemma about the cutoff range/nonnegativity, depending on how `smoothRightCutoff` is packaged.

### Closed-slab agreement

```lean
hagree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
  coupledChemDivTimeDerivativeLift p u t x =
    mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

On the slab, `level0SlabCutoff_eq_one_on_slab` reduces every representative to the raw spectral series. Then:

* interior `x ∈ Ioo 0 1`: use the product/quotient/rpow chain rule giving `mixedAlgebra`;
* endpoints `x = 0,1`: use Neumann/sine-series endpoint vanishing to match the zero-extension/junk derivative behavior.

This is exactly the split already implemented abstractly by `witness_agree` in `IntervalChemDivMixedReprWitness.lean`, but here it must be redone with heat-specific reps rather than `IteratePicardJointC2Data`.

## Existing joint-continuity theorems found

### Heat value/time-derivative series

The exact names exist in `ShenWork/Wiener/EWA/SourceJointRegularity.lean`, but they are **private**:

```lean
private theorem heatValueSeries_jointContinuousOn
private theorem heatDerivSeries_jointContinuousOn
```

They prove joint continuity on:

```lean
Ioi (0 : ℝ) ×ˢ univ
```

for:

```lean
(t,x) ↦ ∑' n, exp(-tλ_n) * u₀cos n * cosineMode n x
(t,x) ↦ ∑' n, -λ_n * exp(-tλ_n) * u₀cos n * cosineMode n x
```

Since they are private, they cannot be imported directly. But their proof pattern is exactly reusable: local `continuousOn_tsum` on a box `Ioo c (t₀+1) ×ˢ univ` with exponential majorants.

### Duhamel value/time-derivative series

These are public in `ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean` under namespace `ShenWork.IntervalSourceCoefficientTimeC1`:

```lean
theorem duhamelSeries_jointContinuousOn
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    ContinuousOn
      (Function.uncurry
        (fun (τ : ℝ) (x : ℝ) =>
          ∑' n, duhamelSpectralCoeff a τ n * cosineMode n x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
```

```lean
theorem duhamelDerivSeries_jointContinuousOn
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    ContinuousOn
      (Function.uncurry
        (fun (τ : ℝ) (x : ℝ) =>
          ∑' n, (a τ n - unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a τ n) * cosineMode n x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
```

These are useful for restart/Duhamel lanes, but heat Level0 can use the simpler heat exponential coefficients directly.

### Restart derivative series

No theorem literally named `restartSeries_jointContinuousOn` was found. The relevant public theorem is:

```lean
ShenWork.IntervalRestartDerivJointContinuity.restartDerivField_continuousOn_joint
```

Shape:

```lean
theorem restartDerivField_continuousOn_joint
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a p.1 n) * cosineMode n p.2)
      (Ioi (0 : ℝ) ×ˢ univ)
```

This gives joint continuity of the **time-derivative field** of a restart series. It combines:

```lean
duhamelDerivSeries_continuousOn
homDerivSeries_continuousOn
```

So for future non-Level0 restart legs, this is the theorem to use for the time derivative; for the value series, use homogeneous heat value + `duhamelSeries_jointContinuousOn` or prove/export a value analogue.

### Generic continuous cosine-series reps

`IntervalChemDivMixedReprWitness.lean` also has generic global `continuous_tsum` helpers:

```lean
theorem valueSeriesRep_continuous
    (hcont : ∀ k, Continuous (c k))
    (hb : ∀ k t, |c k t| ≤ B0 k)
    (hsum : Summable B0) :
    Continuous (valueSeriesRep c)
```

```lean
theorem gradSeriesRep_continuous
    (hcont : ∀ k, Continuous (c k))
    (hb : ∀ k t, |c k t| ≤ B0 k)
    (hsum : Summable (fun k => |(k : ℝ) * Real.pi| * B0 k)) :
    Continuous (gradSeriesRep c)
```

```lean
theorem grad2SeriesRep_continuous
    (hcont : ∀ k, Continuous (c k))
    (hb : ∀ k t, |c k t| ≤ B0 k)
    (hsum : Summable (fun k => unitIntervalCosineEigenvalue k * B0 k)) :
    Continuous (grad2SeriesRep c)
```

These require a **global** envelope `B0`. For raw heat coefficients no such envelope exists on all `ℝ` because of `t → -∞`, but after multiplying by the `level0SlabCutoff`, a cutoff-specific version of these lemmas is exactly the right tool/pattern.

## Exact viable proof architecture for Level0 3G

The direct route should be:

```text
1. Define heat coefficient cH := level0HeatCoeff u₀.
2. Define cutoffRep τ F := level0SlabCutoff τ q.1 * F q.
3. Define the ten representatives:
   Uc,Utc,Utxc,Uxc,Vc,Vxc,Vxxc,Vtc,Vtxc,Vtxxc.
4. Prove all ten are Continuous:
   - u-side by heat exponential coefficient estimates + cutoff;
   - v-side by resolverTimeCoeff = elliptic weight * source coefficient, or from
     PhysicalResolverJointC2Data if already available;
   - time-derivative reps by differentiating the coefficient families.
5. Prove floor `∀ q, 0 < 1 + Vc q`.
6. Prove closed-slab agreement using `level0SlabCutoff_eq_one_on_slab` and
   interior/boundary split.
7. Package `ChemDivMixedReprData`.
8. Call `chemDivMixedTimeDerivClosedRepr_of_data`.
9. Call `chemDivMixedTimeDeriv_jointContinuousOn_closed` wherever the old 3G
   `ContinuousOn` field is needed.
```

The key Lean shape is already in the file:

```lean
let D : ChemDivMixedReprData p u τ δ :=
  { Uc := Uc
    Utc := Utc
    Utxc := Utxc
    Uxc := Uxc
    Vc := Vc
    Vxc := Vxc
    Vxxc := Vxxc
    Vtc := Vtc
    Vtxc := Vtxc
    Vtxxc := Vtxxc
    cont_Uc := hUc
    cont_Utc := hUtc
    cont_Utxc := hUtxc
    cont_Uxc := hUxc
    cont_Vc := hVc
    cont_Vxc := hVxc
    cont_Vxxc := hVxxc
    cont_Vtc := hVtc
    cont_Vtxc := hVtxc
    cont_Vtxxc := hVtxxc
    floor := hfloor
    agree := hagree }

exact chemDivMixedTimeDerivClosedRepr_of_data D
```

## Is the boundary part viable?

Yes, but it is not automatic from continuity. The boundary equality must be proved as an algebraic endpoint fact:

* the smooth sine-series gradient reps vanish at `x = 0,1`;
* the zero-extension derivative/junk convention makes the committed `coupledChemDivTimeDerivativeLift` boundary value match;
* the remaining cosine-series value reps agree with the actual fields on `[0,1]` because the cutoff is one on the slab.

So “zero-extension kills it” is the right intuition, but the formal proof should use the smooth representative and endpoint sine/Neumann facts rather than relying only on raw `deriv` simplification.

## Bottom line

For heat Level0, 3G **can** be proved without `IteratePicardJointC2Data`. The repo already has the intended file:

```lean
ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0
```

It is currently a scaffold with the correct architecture and remaining analytic sorries. The most useful existing theorem names are:

```lean
-- public Duhamel/restart derivative tools
ShenWork.IntervalSourceCoefficientTimeC1.duhamelSeries_jointContinuousOn
ShenWork.IntervalSourceCoefficientTimeC1.duhamelDerivSeries_jointContinuousOn
ShenWork.IntervalRestartDerivJointContinuity.restartDerivField_continuousOn_joint

-- private heat templates in EWA, reusable/exportable if desired
ShenWork.EWA.heatValueSeries_jointContinuousOn      -- private
ShenWork.EWA.heatDerivSeries_jointContinuousOn      -- private

-- generic rep constructors/continuity tools
ShenWork.IntervalChemDivMixedReprWitness.valueSeriesRep_continuous
ShenWork.IntervalChemDivMixedReprWitness.gradSeriesRep_continuous
ShenWork.IntervalChemDivMixedReprWitness.grad2SeriesRep_continuous
ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data
ShenWork.IntervalCoupledRegularityBootstrap.chemDivMixedTimeDeriv_jointContinuousOn_closed
```

No existing theorem named exactly `restartSeries_jointContinuousOn` was found; use `restartDerivField_continuousOn_joint` for derivative fields, and compose heat-value + Duhamel-value joint continuity for restart values if needed.
