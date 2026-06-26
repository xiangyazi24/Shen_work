# Q757 / cron1: `ChemDivMixedTimeDerivClosedRepr` definition and producers

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

`ChemDivMixedTimeDerivClosedRepr` is **not a structure**. It is a `def ... : Prop` containing an existential closed-slab representative:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

Location:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

So its “fields,” after `rcases H with ⟨Gmix, hGmix_cont, hagree⟩`, are:

```lean
Gmix       : ℝ × ℝ → ℝ
hGmix_cont : Continuous Gmix
hagree     : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
               coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

This is exactly the hypothesis consumed by:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

## Note on the comment vs. actual definition

The docstring says agreement on the time window `Ioo (τ-δ) (τ+δ)`, but the actual definition uses the **closed** interval:

```lean
∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1, ...
```

For sub-sorry 3G, the actual `Icc` version is the one that matters.

## Existing producers

There are producers, but I did **not** find an unconditional theorem of the form

```lean
∀ p u τ δ, ChemDivMixedTimeDerivClosedRepr p u τ δ
```

or anything that produces it for an arbitrary trajectory without additional analytic data. The producers all require witness/regularity inputs.

### 1. Producer from `ChemDivMixedReprData`

Location:

```text
ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean
```

The structure:

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

Producer:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (D : ChemDivMixedReprData p u τ δ) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

What it does: sets

```lean
Gmix := mixedAlgebra p.β D.Uc D.Utc D.Utxc D.Uxc D.Vc D.Vxc D.Vxxc
          D.Vtc D.Vtxc D.Vtxxc
```

proves `Continuous Gmix` from the ten `Continuous` fields and `floor`, then uses `D.agree` for the closed-slab equality.

### 2. Producer from `ChemDivMixedReprWitnessData`

Location:

```text
ShenWork/PDE/IntervalChemDivMixedReprWitness.lean
```

There is a stronger witness structure:

```lean
structure ChemDivMixedReprWitnessData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
```

Its fields include the same ten representatives and their continuities:

```lean
Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ
cont_Uc cont_Utc cont_Utxc cont_Uxc : Continuous ...
cont_Vc cont_Vxc cont_Vxxc cont_Vtc cont_Vtxc cont_Vtxxc : Continuous ...
floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
```

plus closed-slab value agreement fields:

```lean
Uc_eq  : Uc  (t, x) = intervalDomainLift (u t) x
Utc_eq : Utc (t, x) = ShenWork.Paper2.PicardLimitK1.slopeSlice u t x
Vc_eq  : Vc  (t, x) = intervalDomainLift (coupledChemicalConcentration p u t) x
Vtc_eq : Vtc (t, x) = coupledChemicalTimeDerivativeLift p u t x
```

plus interior `HasDerivAt` fields:

```lean
hUx    : HasDerivAt (fun y => intervalDomainLift (u t) y) (Uxc (t, x)) x
hUtx   : HasDerivAt (fun y => slopeSlice u t y) (Utxc (t, x)) x
hVx    : HasDerivAt (fun y => intervalDomainLift (coupledChemicalConcentration p u t) y) (Vxc (t, x)) x
hVxx   : HasDerivAt (fun y => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y) (Vxxc (t, x)) x
hVtx   : HasDerivAt (fun y => coupledChemicalTimeDerivativeLift p u t y) (Vtxc (t, x)) x
hVtxx  : HasDerivAt (fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y) (Vtxxc (t, x)) x
```

plus interior derivative-value agreement:

```lean
Vxc_eq  : Vxc (t, x) = deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
Vtxc_eq : Vtxc (t, x) = deriv (coupledChemicalTimeDerivativeLift p u t) x
```

and the endpoint/boundary leg:

```lean
boundary_agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
  coupledChemDivTimeDerivativeLift p u t x =
    mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

The file derives the closed-slab `agree` field by splitting `x ∈ Icc 0 1` into endpoints and interior:

```lean
theorem witness_agree
    (W : ChemDivMixedReprWitnessData p u τ δ)
    (t : ℝ) (ht : t ∈ Icc (τ - δ) (τ + δ)) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β W.Uc W.Utc W.Utxc W.Uxc W.Vc W.Vxc W.Vxxc
        W.Vtc W.Vtxc W.Vtxxc (t, x)
```

Then it packages witness data into `ChemDivMixedReprData`:

```lean
def witnessData
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedReprData p u τ δ
```

Producer:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_witness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Implementation:

```lean
chemDivMixedTimeDerivClosedRepr_of_data (witnessData W)
```

### 3. Producer from physical resolver + iterate data

Location:

```text
ShenWork/PDE/IntervalChemDivMixedReprWitness.lean
```

Producer:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_mkWitness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ}
    {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ}
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
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Implementation:

```lean
chemDivMixedTimeDerivClosedRepr_of_witness (mkWitnessData H Hu Hg2u hfloor bdry)
```

This is a meaningful trajectory-level producer, but it is **not unconditional**: it requires resolver physical joint C² data, iterate joint C² data, iterate order-2 gradient summability, a global floor for the resolver value series, and endpoint boundary agreement.

### 4. Capstone producer using iterate gradient summability field

Location:

```text
ShenWork/PDE/IntervalIterateGradMajorant.lean
```

Producer:

```lean
theorem chemDivMixedClosedRepr_of_iterateGradSummable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ}
    {Bt Btu : ℕ → ℕ → ℝ} {τ δ : ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    (HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m))
    (hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
    (bdry : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
      coupledChemDivTimeDerivativeLift p u t x =
        mixedAlgebra p.β (valueSeriesRep c) (iterateDtValue c) (iterateDtGrad c)
          (gradSeriesRep c) (valueSeriesRep (resolverTimeCoeff p u))
          (gradSeriesRep (resolverTimeCoeff p u))
          (grad2SeriesRep (resolverTimeCoeff p u)) (resolverDtValue p u)
          (resolverDtGrad p u) (resolverDtGrad2 p u) (t, x)) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Implementation:

```lean
chemDivMixedTimeDerivClosedRepr_of_mkWitness H Hu
  (iterate_Hg2u_of_gradSummable HuGrad) hfloor bdry
```

This appears to be the highest-level committed producer for `ChemDivMixedTimeDerivClosedRepr`.

## FAC wrapper that consumes the representative

Location:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

The FAC wrapper:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This does not produce `ChemDivMixedTimeDerivClosedRepr`; it expects it in `other`, then internally calls:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

## Practical closure routes

### If sub-sorry 3G already has `Hrepr`

```lean
exact chemDivMixedTimeDeriv_jointContinuousOn_closed Hrepr
```

### If it has `ChemDivMixedReprData`

```lean
have Hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data D
exact chemDivMixedTimeDeriv_jointContinuousOn_closed Hrepr
```

### If it has `ChemDivMixedReprWitnessData`

```lean
have Hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_witness W
exact chemDivMixedTimeDeriv_jointContinuousOn_closed Hrepr
```

### If it has physical resolver + iterate data

```lean
have Hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
    H Hu HuGrad hfloor bdry
exact chemDivMixedTimeDeriv_jointContinuousOn_closed Hrepr
```

## Bottom line

`ChemDivMixedTimeDerivClosedRepr` is an existential representative datum: a continuous `Gmix` plus closed-slab equality with `coupledChemDivTimeDerivativeLift`. The repo has multiple producers, culminating in `chemDivMixedClosedRepr_of_iterateGradSummable`, but no producer for a completely arbitrary trajectory without the honest physical resolver/iterate/floor/boundary data.
