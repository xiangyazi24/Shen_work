# Q583 / cron1: `ChemDivMixedReprWitnessData` for the heat semigroup

## Executive verdict

`ChemDivMixedReprWitnessData` is already a substantial **assembled witness interface** on `chatgpt-scratch`, and the repo already has two capstone producers:

```lean
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
```

These produce

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

which is exactly the closed-slab representative needed to discharge the `htime_cont` field in the FAC chain.

For the heat semigroup, I found **no direct specialized producer** by search for `conjugatePicardIter` / heat.  The intended route is to instantiate the general capstone with:

```lean
u := conjugatePicardIter p u₀ 0
c k t := Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k
```

and then supply the honest heat-level data:

1. `PhysicalResolverJointC2Data p u Bt` for the elliptic resolver;
2. `IteratePicardJointC2Data u c Btu` for the heat iterate;
3. iterate gradient majorant summability `∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Btu m)` or at least the order-2 instance;
4. global denominator floor for the resolver value-series representative;
5. endpoint/boundary agreement `bdry`.

The closest already-packaged endpoint is therefore **not** the raw `ChemDivMixedReprWitnessData` constructor but:

```lean
ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
```

which packages the witness and immediately returns `ChemDivMixedTimeDerivClosedRepr`.

## `ChemDivMixedTimeDerivClosedRepr`

Defined in `ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:45-49`:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

The consumer theorem is `chemDivMixedTimeDeriv_jointContinuousOn_closed`, lines `56-61`, which turns this representative into:

```lean
ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

and `coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged`, lines `87-103`, consumes it inside the FAC route.

## `ChemDivMixedReprData`

Defined in `ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean:72-97`.

It packages ten globally continuous representatives:

```lean
structure ChemDivMixedReprData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc : ℝ × ℝ → ℝ
  Utc : ℝ × ℝ → ℝ
  Utxc : ℝ × ℝ → ℝ
  Uxc : ℝ × ℝ → ℝ
  Vc : ℝ × ℝ → ℝ
  Vxc : ℝ × ℝ → ℝ
  Vxxc : ℝ × ℝ → ℝ
  Vtc : ℝ × ℝ → ℝ
  Vtxc : ℝ × ℝ → ℝ
  Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

The constructor-to-target theorem is `chemDivMixedTimeDerivClosedRepr_of_data`, lines `104-145`: it takes `ChemDivMixedReprData` and builds `ChemDivMixedTimeDerivClosedRepr` by using `mixedAlgebra ...` as the global continuous `Gmix`.

## `ChemDivMixedReprWitnessData`: fields

Defined in `ShenWork/PDE/IntervalChemDivMixedReprWitness.lean:181-251`.

It refines `ChemDivMixedReprData` by replacing the single `agree` field with more primitive field-equality and spatial derivative facts.  Fields:

### Ten representative functions

```lean
Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ
```

### Continuity fields

```lean
cont_Uc cont_Utc cont_Utxc cont_Uxc : Continuous ...
cont_Vc cont_Vxc cont_Vxxc cont_Vtc cont_Vtxc cont_Vtxxc : Continuous ...
```

### Floor and closed-slab value matches

```lean
floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
Uc_eq  : Uc  (t,x) = intervalDomainLift (u t) x
Utc_eq : Utc (t,x) = slopeSlice u t x
Vc_eq  : Vc  (t,x) = intervalDomainLift (coupledChemicalConcentration p u t) x
Vtc_eq : Vtc (t,x) = coupledChemicalTimeDerivativeLift p u t x
```

all on `t ∈ Icc (τ-δ) (τ+δ), x ∈ Icc 0 1`.

### Interior spatial derivative legs

```lean
hUx    : HasDerivAt (fun y => intervalDomainLift (u t) y) (Uxc (t,x)) x
hUtx   : HasDerivAt (fun y => slopeSlice u t y) (Utxc (t,x)) x
hVx    : HasDerivAt (fun y => intervalDomainLift (coupledChemicalConcentration p u t) y) (Vxc (t,x)) x
hVxx   : HasDerivAt (fun y => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y) (Vxxc (t,x)) x
hVtx   : HasDerivAt (fun y => coupledChemicalTimeDerivativeLift p u t y) (Vtxc (t,x)) x
hVtxx  : HasDerivAt (fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y) (Vtxxc (t,x)) x
```

for `x ∈ Ioo 0 1`.

### Interior derivative-value equalities

```lean
Vxc_eq  : Vxc (t,x) = deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
Vtxc_eq : Vtxc (t,x) = deriv (coupledChemicalTimeDerivativeLift p u t) x
```

for `x ∈ Ioo 0 1`.

### Boundary leg

```lean
boundary_agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
  coupledChemDivTimeDerivativeLift p u t x =
    mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

This is the remaining endpoint/junk-value Neumann matching fact.

## Witness assembly chain

The internal chain is:

```lean
ChemDivMixedReprWitnessData p u τ δ
  ── witnessData ──▶
ChemDivMixedReprData p u τ δ
  ── chemDivMixedTimeDerivClosedRepr_of_data ──▶
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

The two theorems are:

```lean
-- IntervalChemDivMixedReprWitness.lean:141-153
def witnessData
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedReprData p u τ δ

-- IntervalChemDivMixedReprWitness.lean:159-164
theorem chemDivMixedTimeDerivClosedRepr_of_witness
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  chemDivMixedTimeDerivClosedRepr_of_data (witnessData W)
```

`witness_agree`, lines `88-138`, is the key proof deriving the closed-slab `agree` field.  It splits `[0,1]` into interior plus endpoints; interior uses `fluxTimeDeriv_hasDerivAt_space`, while endpoints use `boundary_agree`.

## Main existing producer

The full general producer is `mkWitnessData`, in `IntervalChemDivMixedReprWitness.lean:1038-1127`:

```lean
def mkWitnessData {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c : ℕ → ℝ → ℝ} {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (Hg2u : Summable (boundedWeightJointGradMajorant Btu 2))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
      coupledChemDivTimeDerivativeLift p u t x =
        mixedAlgebra p.β (valueSeriesRep c) (iterateDtValue c) (iterateDtGrad c)
          (gradSeriesRep c) (valueSeriesRep (resolverTimeCoeff p u))
          (gradSeriesRep (resolverTimeCoeff p u))
          (grad2SeriesRep (resolverTimeCoeff p u)) (resolverDtValue p u)
          (resolverDtGrad p u) (resolverDtGrad2 p u) (t, x)) :
    ChemDivMixedReprWitnessData p u τ δ
```

It sets:

```lean
Uc    := valueSeriesRep c
Utc   := iterateDtValue c
Utxc  := iterateDtGrad c
Uxc   := gradSeriesRep c
Vc    := valueSeriesRep (resolverTimeCoeff p u)
Vxc   := gradSeriesRep (resolverTimeCoeff p u)
Vxxc  := grad2SeriesRep (resolverTimeCoeff p u)
Vtc   := resolverDtValue p u
Vtxc  := resolverDtGrad p u
Vtxxc := resolverDtGrad2 p u
```

and discharges all continuity/equality/interior derivative fields from `H`, `Hu`, and `Hg2u`.  The only externally supplied non-series fields are `hfloor` and `bdry`.

The immediate target producer is:

```lean
-- IntervalChemDivMixedReprWitness.lean:96-112 of the final chunk
theorem chemDivMixedTimeDerivClosedRepr_of_mkWitness
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (Hg2u : Summable (boundedWeightJointGradMajorant Btu 2))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ...endpoint equality...) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

## Higher-level producer with iterate gradient family

`ShenWork/PDE/IntervalIterateGradMajorant.lean` wraps the previous theorem with the iterate gradient family:

```lean
-- lines 106-123
theorem chemDivMixedClosedRepr_of_iterateGradSummable
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ...endpoint equality...) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  chemDivMixedTimeDerivClosedRepr_of_mkWitness H Hu
    (iterate_Hg2u_of_gradSummable HuGrad) hfloor bdry
```

This is the cleanest theorem to call if your heat-level data naturally supplies all gradient-majorant orders.

## For the heat semigroup

Search found no theorem directly named for:

```lean
ChemDivMixedReprWitnessData p (conjugatePicardIter p u₀ 0) ...
chemDivMixed... conjugatePicardIter
mkWitnessData ... heat
```

So the heat-level task is to instantiate the generic producer.  Minimal plan:

```lean
let u := conjugatePicardIter p u₀ 0
let c : ℕ → ℝ → ℝ := fun k t =>
  Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k

have H : PhysicalResolverJointC2Data p u Bt := ...
have Hu : IteratePicardJointC2Data u c Btu := ...
have HuGrad : ∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointGradMajorant Btu m) := ...
have hfloor : ∀ q, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q := ...
have bdry : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0,1} : Set ℝ),
  coupledChemDivTimeDerivativeLift p u t x = mixedAlgebra ... (t,x) := ...

exact ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
  H Hu HuGrad hfloor bdry
```

For heat data, `Hu` and `HuGrad` should be the easiest analytic part: the coefficients are explicit exponentials times initial coefficients, so their time derivatives and weighted summability follow from Gaussian damping on any positive window.  However the existing `IteratePicardJointC2Data` is global in `t` and not windowed, so if your proof only works on `[c,T]`, a windowed variant may be more natural.

The two genuinely nontrivial remaining inputs are likely:

1. `H : PhysicalResolverJointC2Data p u Bt`, unless already available from the source-time-C²/floor route for this `u`;
2. `bdry`, the endpoint matching of the junk-value `coupledChemDivTimeDerivativeLift` with the mixed algebra.  The design comments say this should follow from Neumann sine-series boundary vanishing, but it is intentionally an explicit input to the producer.

## Bottom line

`ChemDivMixedReprWitnessData` itself is not the best thing to construct manually.  Use:

```lean
chemDivMixedClosedRepr_of_iterateGradSummable
```

or one level lower:

```lean
chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

The repo already builds the ten representatives and all continuity/interior derivative fields.  For the heat semigroup, the remaining work is to produce the resolver joint-C² data, the heat iterate joint-C² data plus gradient-majorant summability, the positive denominator floor, and the endpoint `bdry` equality.
