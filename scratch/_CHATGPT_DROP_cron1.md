# Q751 / cron1: `coupledChemDivTimeDerivativeLift` closed-slab continuity

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

Yes. The repo already has the closed-slab joint-continuity theorem for sub-sorry 3G:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Location:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

So if sub-sorry 3G has a local hypothesis

```lean
hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ
```

then the close is just:

```lean
exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

If the local context has the lower-level physical/iterate data instead, the repo also has constructors for `hrepr`; see the closure route below.

## 1. `chemDivMixedTimeDeriv_jointContinuousOn_closed` or similar

Found exact theorem:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

It appears in:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

The proof is a clean transfer from a globally continuous representative `Gmix`: it obtains

```lean
⟨Gmix, hGmix_cont, hagree⟩ := H
```

sets

```lean
S := Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1
```

then proves pointwise agreement on `S` and uses `ContinuousWithinAt.congr_of_eventuallyEq`.

This is exactly the requested target:

```lean
ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc (τ-δ) (τ+δ) ×ˢ Icc 0 1)
```

No theorem named `coupledChemDivTimeDerivative_jointContinuousOn_closed` was found; the committed name is `chemDivMixedTimeDeriv_jointContinuousOn_closed`.

## 2. `ChemDivMixedTimeDerivClosedRepr` and what it provides

Defined in the same file:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

So `ChemDivMixedTimeDerivClosedRepr` itself is the closed-slab representative datum: a globally continuous `Gmix` agreeing with the committed mixed time-derivative lift on the closed time-space slab. It provides the requested `ContinuousOn` only when fed to:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

There are several constructor layers for this representative.

### Constructor from explicit continuous representatives

In:

```text
ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean
```

The file defines:

```lean
def mixedAlgebra ... : ℝ × ℝ → ℝ
```

and a bundle:

```lean
structure ChemDivMixedReprData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ
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

Then:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_data
    (D : ChemDivMixedReprData p u τ δ) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

This theorem proves `Continuous` for `mixedAlgebra` from the ten continuous reps plus the floor, then uses `D.agree` for slab equality.

### Constructor from witness data

In:

```text
ShenWork/PDE/IntervalChemDivMixedReprWitness.lean
```

Found:

```lean
def witnessData
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedReprData p u τ δ
```

and:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_witness
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

The same file defines the spectral/time-series reps for the resolver `d_t` legs:

```lean
def resolverDtValue (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : ℝ × ℝ → ℝ

def resolverDtGrad (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : ℝ × ℝ → ℝ

def resolverDtGrad2 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : ℝ × ℝ → ℝ
```

with continuity lemmas:

```lean
resolverDtValue_continuous
resolverDtGrad_continuous
resolverDtGrad2_continuous
```

and the closed-slab equality of the committed `coupledChemicalTimeDerivativeLift` with the resolver `d_t` cosine series:

```lean
resolver_timeDeriv_eq_series
```

### Constructor from physical resolver + iterate data

Still in:

```text
ShenWork/PDE/IntervalChemDivMixedReprWitness.lean
```

Found:

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

This reduces the representative to:

* `PhysicalResolverJointC2Data p u Bt`
* iterate `IteratePicardJointC2Data u c Btu`
* order-2 iterate gradient summability
* a global floor for the resolver value series
* endpoint/boundary agreement on `{0,1}`

### Capstone with iterate gradient summability field

In:

```text
ShenWork/PDE/IntervalIterateGradMajorant.lean
```

Found:

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

This is likely the highest-level available constructor for `hrepr` before entering the FAC factor pipeline.

## 3. Any theorem giving `ContinuousOn` of the time derivative of the chemDiv source?

There are two relevant meanings.

### A. Joint continuity of the pointwise source time derivative field

The pointwise chain-rule field is:

```lean
coupledChemDivTimeDerivativeLift p u : ℝ → ℝ → ℝ
```

The theorem that gives its joint closed-slab `ContinuousOn` is exactly:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

from `IntervalChemDivTimeDerivClosed.lean`, provided `ChemDivMixedTimeDerivClosedRepr` is available.

This field also appears as an explicit hypothesis/field in older packages:

```lean
CoupledChemDivLocalChainRule.exists_local_slab
CoupledChemDivPointwiseChainAtoms.exists_local_slab
FACLocalSlabInputs
CoupledChemDivFluxFactorJointC2Inputs
```

Those packages do not prove the continuity by themselves; they store or pass it. The `IntervalChemDivTimeDerivClosed.lean` route is the committed theorem that discharges it from the representative.

### B. Continuity of coefficient time derivatives `coupledChemDivAdot`

In:

```text
ShenWork/Wiener/EWA/ChemDivAdot.lean
```

Found:

```lean
theorem chemDivAdot_continuousOn_of_jointCont
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n) (Set.Icc (0 : ℝ) T)
```

This is not the same as the requested 3G target; it is downstream. It consumes joint continuity of `coupledChemDivTimeDerivativeLift` and produces per-mode coefficient continuity. The same file also packages:

```lean
theorem chemDivAdot_deriv_legs_of_smoothness
    (hchain : CoupledChemDivLocalChainRule p u)
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s)
    ∧ (∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n)
        (Set.Icc (0 : ℝ) T))
```

So `ChemDivAdot.lean` gives coefficient continuity once the requested 3G-style joint continuity is already supplied.

## Factor pipeline use

`IntervalChemDivTimeDerivClosed.lean` also provides the FAC-facing theorem:

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

This wraps the prior `coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged` and fills the formerly open `htime_cont` field by:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

## Practical closure route for sub-sorry 3G

### Case 1: local context already has the representative

```lean
-- hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ
exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

### Case 2: local context has physical + iterate witness data

If the context has:

```lean
H      : PhysicalResolverJointC2Data p u Bt
Hu     : IteratePicardJointC2Data u c Btu
HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
           Summable (boundedWeightJointGradMajorant Btu m)
hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q
bdry   : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
           coupledChemDivTimeDerivativeLift p u t x =
             mixedAlgebra p.β (valueSeriesRep c) (iterateDtValue c) (iterateDtGrad c)
               (gradSeriesRep c) (valueSeriesRep (resolverTimeCoeff p u))
               (gradSeriesRep (resolverTimeCoeff p u))
               (grad2SeriesRep (resolverTimeCoeff p u)) (resolverDtValue p u)
               (resolverDtGrad p u) (resolverDtGrad2 p u) (t, x)
```

then close by building `hrepr` first:

```lean
have hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
    H Hu HuGrad hfloor bdry
exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

### Case 3: local context is assembling FAC factor inputs

Prefer the already-committed wrapper:

```lean
coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

It expects the `other` slab package to contain `ChemDivMixedTimeDerivClosedRepr p u τ δ` instead of the raw `ContinuousOn` field, and it discharges `htime_cont` internally.
