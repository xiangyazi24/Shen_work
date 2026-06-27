# Q1072 (cron3): Tower sorry #3 chemDiv successor cascade

## Short verdict

Tower sorry #3 does **not** close automatically from the Level0 result.

`IntervalFlooredSourceTimeDataIterate.lean` does provide the iterate-level analogue of `FlooredSourceTimeData`: the structure `IterateSourceTimeData` and the producer `flooredSourceTimeData_of_iterate`. It also provides the iterate-to-FAC wrapper `coupledChemDivFluxFactorJointC2Inputs_of_iterate`.

But the current tower induction in `IntervalConjugateBFormSourceTower.lean` only carries the predecessor B-form source `DuhamelSourceTimeC1On`. It does **not** carry the much stronger iterate regularity residual needed for chemDiv at level `n+1`: `IterateSourceTimeData`, weighted source summability `hval/hgrad`, FAC slab data, weak-H²/decay/zeroth bounds, and `adot` continuity/bounds.

So the exact closure sequence is known, but the tower must be strengthened to produce/pass a residual for each iterate. Level0 does not imply the successor automatically.

## Imports for the mapped call sequence

```lean
import ShenWork.Paper2.IntervalConjugateBFormSourceTower
import ShenWork.Paper2.IntervalChemDivWinDischarge
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalChemDivFluxJointC2Producer
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
```

## The tower target

In `ShenWork/Paper2/IntervalConjugateBFormSourceTower.lean`, the successor case has:

```lean
have _hchem : DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c DB.T := by
  sorry -- Needs chemDiv C² for iterate n+1 (same gap as level 0)
```

Let

```lean
let uS : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ (n + 1)
```

The minimal exact replacement, once the iterate-level residual exists, is:

```lean
have R : ShenWork.IntervalChemDivWinDischarge.ChemDivSolutionRegularityResidual p uS := by
  -- this is the genuine successor regularity residual, not supplied by `ih`
  -- fields: hiter, hval, hgrad, other, H2/decay/zero, hadotcont/Mdot
  exact ?Rsucc

have hglob : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
    (coupledChemDivSourceCoeffs p uS) :=
  ShenWork.IntervalChemDivWinDischarge.coupledChemDivSource_duhamelSourceTimeC1_of_residual
    (p := p) (u := uS) R

exact ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
  hglob c DB.T (le_of_lt hc)
```

That is the shortest call sequence for the tower sorry **if** the iterate residual has already been produced.

## Expanded exact theorem-call sequence inside `R`

The current residual wrapper in `IntervalChemDivWinDischarge.lean` expands as follows.

### Step 0: residual data for the specific iterate

For `uS := conjugatePicardIter p u₀ (n + 1)`, you need:

```lean
R : ChemDivSolutionRegularityResidual p uS
```

Its fields include:

```lean
R.du       : ℝ → ℝ → ℝ
R.d2u      : ℝ → ℝ → ℝ
R.hiter    : IterateSourceTimeData p uS R.du R.d2u
R.hval     : ∀ m, (m : ℕ∞) ≤ 2 → Summable (... builtEs ...)
R.hgrad    : ∀ m, (m : ℕ∞) ≤ 2 → Summable (... builtEs ...)
R.other    : FAC-style local slab data
R.hH2      : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p uS s)
R.hdecay   : ∀ s, 0 ≤ s → ∀ k, 1 ≤ k → |cosineCoeffs ... k| ≤ R.Cchem / ((k:ℝ) * π)^2
R.hzero    : ∀ s, 0 ≤ s → |cosineCoeffs ... 0| ≤ R.Cchem
R.hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p uS s n)
R.hMdot    : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p uS s n| ≤ R.MchemDot
```

This is the data the current tower induction does not carry.

### Step 1: iterate source data to floored source data

```lean
have Hfloor :
    ShenWork.IntervalPhysicalSourceTimeC2Concrete.FlooredSourceTimeData
      p uS
      (ShenWork.IntervalFlooredSourceTimeDataIterate.srcSlice1 p uS R.du)
      (ShenWork.IntervalFlooredSourceTimeDataIterate.srcSlice2 p uS R.du R.d2u) :=
  ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
    (p := p) (u := uS) (du := R.du) (d2u := R.d2u) R.hiter
```

This is the iterate analogue of the Level0 `FlooredSourceTimeData` construction.

### Step 2: floored source data to physical source-time C²

```lean
have Hsrc :
    ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2
      p uS (ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs Hfloor) :=
  ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
    Hfloor R.hval R.hgrad
```

Caveat from current `main`: after the positive-time weakening, this file still has local sorries in the positive-time-to-global assembly (`srcTimeCoeff_contDiffAt`, `srcTimeCoeff_iteratedDeriv2`, and the `src_contDiff` / `src_bound` fields of `physicalSourceTimeC2_of_floored`). If by “Option A lands” we mean those are also filled or the downstream structures are retyped positive-time, then this call is the intended one.

### Step 3: physical source-time C² to physical resolver joint C²

```lean
have Hres :
    ShenWork.IntervalResolverJointC2PhysicalConcrete.PhysicalResolverJointC2Data
      p uS
      (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
        ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs Hfloor i k) :=
  ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor
    Hsrc
```

This is automatic once `Hsrc` exists.

### Step 4: factor-level FAC inputs

The current residual route uses:

```lean
have Hfac : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs p uS :=
  ShenWork.IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
    (p := p) (u := uS) (du := R.du) (d2u := R.d2u)
    R.hiter R.hval R.hgrad R.other
```

Internally this is:

```lean
flooredSourceTimeData_of_iterate R.hiter
  |> physicalSourceTimeC2_of_floored ... R.hval R.hgrad
  |> physicalResolverJointC2Data_of_floor
  |> coupledChemDivFluxFactorJointC2Inputs_of_physical
```

and it discharges the resolver value/gradient joint C² fields physically. The non-resolver slab fields still come from `R.other`.

### Step 4′: modern htime-discharged alternative

If you do not want to carry the old stronger `R.other` with time bridge and mixed-continuity already inside it, use the newer split route instead:

```lean
have Hrepr :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr p uS τ δ :=
  ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
    (p := p) (u := uS)
    Hres
    Hu              -- IteratePicardJointC2Data uS cCoeff Btu
    Hg2u            -- Summable (boundedWeightJointGradMajorant Btu 2)
    hfloor          -- ∀ q, 0 < 1 + valueSeriesRep (resolverTimeCoeff p uS) q
    bdry            -- endpoint algebra agreement

have Hfac' : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs p uS :=
  ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    Hres hu_cont hu_nonneg other'
```

where `other'` supplies only:

```lean
source_continuity ∧ hu_c2 ∧ ChemDivMixedTimeDerivClosedRepr p uS τ δ
```

This route is cleaner, but it requires extra iterate-side data `Hu`, `Hg2u`, `hfloor`, and `bdry`. It is not currently the wrapper used by `ChemDivSolutionRegularityResidual`.

### Step 5: factor-level FAC inputs to flux joint C²

```lean
have Hflux : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp p uS :=
  ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    Hfac
```

or simply:

```lean
have Hflux : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp p uS :=
  ShenWork.IntervalChemDivWinDischarge.fluxJointC2Hyp_of_residual
    (p := p) (u := uS) R
```

### Step 6: flux joint C² plus H²/decay/adot data to global chemDiv TimeC1

Expanded call:

```lean
have hglob : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
    (coupledChemDivSourceCoeffs p uS) :=
  ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSource_timeC1_of_fluxJointC2
    R.Cchem R.hCchem R.hH2 R.hdecay R.hzero
    Hflux
    R.hadotcont R.MchemDot R.hMdot
```

Wrapper call:

```lean
have hglob : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
    (coupledChemDivSourceCoeffs p uS) :=
  ShenWork.IntervalChemDivWinDischarge.coupledChemDivSource_duhamelSourceTimeC1_of_residual
    (p := p) (u := uS) R
```

### Step 7: global chemDiv TimeC1 to tower window `[c, DB.T]`

```lean
have hchem : DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p uS) c DB.T :=
  ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
    hglob c DB.T (le_of_lt hc)
```

This is exactly the target of Tower sorry #3.

## Answers to the three questions

### 1. Does `IntervalFlooredSourceTimeDataIterate` provide the iterate-level analogue?

Yes. The structure is:

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData
```

and the conversion theorem is:

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
```

The file also provides the direct iterate-to-factor wrapper:

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
```

So the iterate-level analogue exists.

### 2. After Option A weakening, does the iterate version also become fillable?

Only conditionally.

The **conversion** `IterateSourceTimeData → FlooredSourceTimeData` is mechanical after positive-time weakening. In current `main`, `FlooredSourceTimeData` is already positive-time in `d0`, `d1`, `sliceC2`, `sliceNeumann`, `zerothBound`, and `laplBound`; `flooredSourceTimeData_of_iterate` has already been adjusted with unused positive-time arguments such as `d0 τ _hτ` and `sliceC2 i hi t _ht`.

But the structure `IterateSourceTimeData` itself still asks for actual iterate regularity data:

```lean
floor
time1
time2
sliceC2
sliceNeumann
zerothBound
laplBound
```

There is no theorem in the fetched files that constructs these fields for `conjugatePicardIter p u₀ (n+1)` from only the predecessor B-form source `TimeC1On`. To make it fillable, the induction must supply positive-time parabolic regularity for the iterate, including the `du/d2u` fields and the spatial C²/Neumann/decay bounds.

Also, in current `main`, `physicalSourceTimeC2_of_floored` still contains source-coefficient positive-time-to-global sorries. So even after the signature weakening, this part must be completed or the downstream `PhysicalSourceTimeC2` type must be retyped positive-time as well.

### 3. Is Level0 → iterate `n+1` automatic by induction?

No. The current induction hypothesis in `conjBFormSourceTimeC1OnUpTo_all` is only:

```lean
ih : ConjBFormSourceTimeC1OnUpTo p u₀ n DB.T
```

which means:

```lean
∀ c, 0 < c → c < DB.T →
  DuhamelSourceTimeC1On (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) c DB.T
```

This is far weaker than the residual needed for chemDiv at `n+1`. It does not contain:

```lean
IterateSourceTimeData p (conjugatePicardIter p u₀ (n+1)) du d2u
weighted hval/hgrad for builtEs
FAC other / or htime-discharged source-continuity + hu_c2 + mixed repr
IntervalWeakH2Neumann for coupledChemDivSourceLift
quadratic decay / zeroth coefficient bounds
hadotcont and Mdot for coupledChemDivAdot
```

Therefore each iterate needs separate work, or better: strengthen the tower induction to carry a richer invariant, e.g.

```lean
∀ n, ChemDivSolutionRegularityResidual p (conjugatePicardIter p u₀ n)
```

or a decomposed version containing:

```lean
IterateSourceTimeData
IteratePicardJointC2Data
weighted hval/hgrad
source continuity
ChemDivMixedTimeDerivClosedRepr data
H²/decay/adot bounds
```

Then Tower sorry #3 becomes a short wrapper call to `coupledChemDivSource_duhamelSourceTimeC1_of_residual` followed by `DuhamelSourceTimeC1.toOn`.

## Practical replacement shape for the tower file

The current successor branch should not try to derive chemDiv from `ih` alone. The honest target is to add a stronger induction/residual hypothesis. With such a residual in scope:

```lean
-- In the successor branch:
let uS : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ (n + 1)

have Rchem : ShenWork.IntervalChemDivWinDischarge.ChemDivSolutionRegularityResidual p uS := by
  -- supplied by strengthened tower induction / generic successor regularity theorem
  exact ?Rchem_succ

have hchemGlob : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1
    (coupledChemDivSourceCoeffs p uS) :=
  ShenWork.IntervalChemDivWinDischarge.coupledChemDivSource_duhamelSourceTimeC1_of_residual
    (p := p) (u := uS) Rchem

have _hchem : DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p uS) c DB.T :=
  ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
    hchemGlob c DB.T (le_of_lt hc)
```

That is the exact theorem-call closure once the real iterate-level regularity invariant exists.

## Final answer

* `IntervalFlooredSourceTimeDataIterate` **does** provide the iterate-level analogue.
* Option A makes the positive-time **conversion** plausible/mechanical, but does not create the actual `IterateSourceTimeData` or the extra summability/FAC/H²/adot data.
* The cascade is not automatic from Level0. The tower induction must be strengthened to carry a chemDiv regularity residual for every iterate, or each iterate must be proved separately by a generic successor theorem.
