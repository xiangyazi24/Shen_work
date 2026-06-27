# Q1067 (cron2) — Level0 SORRY 3G: closed-slab time-derivative continuity

Static GitHub-connector inspection only; I did **not** run Lean locally.

## Verdict

The existing bridge is **not** a theorem of the shape

```lean
PhysicalResolverJointC2Data p u Bt →
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

by itself.

The direct producer in the files requested is:

```lean
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

It consumes

```lean
(H      : PhysicalResolverJointC2Data p u Bt)
(Hu     : IteratePicardJointC2Data u c Btu)
(Hg2u   : Summable (boundedWeightJointGradMajorant Btu 2))
(hfloor : ∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q)
(bdry   : endpoint boundary agreement for mixedAlgebra)
```

and returns

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

The cleaner capstone wrapper found by searching for this bridge is:

```lean
ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
```

It consumes `PhysicalResolverJointC2Data`, `IteratePicardJointC2Data`, an iterate gradient-summability provider

```lean
HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointGradMajorant Btu m)
```

plus `hfloor` and `bdry`, then internally calls

```lean
chemDivMixedTimeDerivClosedRepr_of_mkWitness H Hu
  (iterate_Hg2u_of_gradSummable HuGrad) hfloor bdry
```

Once the `ChemDivMixedTimeDerivClosedRepr` is obtained, the 3G `ContinuousOn` goal is closed by:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.chemDivMixedTimeDeriv_jointContinuousOn_closed
```

So: **3G closes immediately if the Level0 local context already has the resolver data plus the u-side iterate/heat witness, iterate gradient summability, floor, and boundary agreement. It does not close from `PhysicalResolverJointC2Data` alone.**

## Exact drop-in proof for SORRY 3G using the capstone bridge

This is the replacement for the Field 3 `sorry` in the `hlocal_slab` block after the `refine ⟨min 1 (s / 2), ...⟩`, assuming the following local names are available:

```lean
Hphys : PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
Hu    : IteratePicardJointC2Data (conjugatePicardIter p u₀ 0) cH Btu
HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointGradMajorant Btu m)
hfloor : ∀ q : ℝ × ℝ,
  0 < 1 + valueSeriesRep
    (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)) q
hbdry : ∀ t ∈ Icc (s - min (1 : ℝ) (s / 2)) (s + min (1 : ℝ) (s / 2)),
  ∀ x ∈ ({0, 1} : Set ℝ),
    coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) t x =
      mixedAlgebra p.β (valueSeriesRep cH) (iterateDtValue cH) (iterateDtGrad cH)
        (gradSeriesRep cH)
        (valueSeriesRep (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
        (gradSeriesRep (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
        (grad2SeriesRep (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
        (resolverDtValue p (conjugatePicardIter p u₀ 0))
        (resolverDtGrad p (conjugatePicardIter p u₀ 0))
        (resolverDtGrad2 p (conjugatePicardIter p u₀ 0)) (t, x)
```

Full import context and a standalone theorem:

```lean
import ShenWork.PDE.IntervalIterateGradMajorant
import ShenWork.Paper2.IntervalConjugatePicard

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalChemDivMixedReprWitness
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data resolverTimeCoeff)
open ShenWork.IntervalIteratePicardJointC2
  (IteratePicardJointC2Data)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- The Level0 3G closed-slab continuity proof, once the mixed-representative
witness inputs have been built. -/
theorem level0_sorry_3G_from_mixed_repr_bridge
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {Bt Btu : ℕ → ℕ → ℝ} {cH : ℕ → ℝ → ℝ} {s : ℝ}
    (Hphys : PhysicalResolverJointC2Data
      p (conjugatePicardIter p u₀ 0) Bt)
    (Hu : IteratePicardJointC2Data
      (conjugatePicardIter p u₀ 0) cH Btu)
    (HuGrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m))
    (hfloor : ∀ q : ℝ × ℝ,
      0 < 1 + valueSeriesRep
        (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)) q)
    (hbdry : ∀ t ∈ Icc (s - min (1 : ℝ) (s / 2))
        (s + min (1 : ℝ) (s / 2)),
      ∀ x ∈ ({0, 1} : Set ℝ),
        coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) t x =
          mixedAlgebra p.β
            (valueSeriesRep cH)
            (iterateDtValue cH)
            (iterateDtGrad cH)
            (gradSeriesRep cH)
            (valueSeriesRep
              (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
            (gradSeriesRep
              (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
            (grad2SeriesRep
              (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
            (resolverDtValue p (conjugatePicardIter p u₀ 0))
            (resolverDtGrad p (conjugatePicardIter p u₀ 0))
            (resolverDtGrad2 p (conjugatePicardIter p u₀ 0))
            (t, x)) :
    ContinuousOn
      (Function.uncurry
        (coupledChemDivTimeDerivativeLift p
          (conjugatePicardIter p u₀ 0)))
      (Icc (s - min (1 : ℝ) (s / 2))
          (s + min (1 : ℝ) (s / 2)) ×ˢ Icc (0 : ℝ) 1) := by
  have hrepr :
      ChemDivMixedTimeDerivClosedRepr
        p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2)) :=
    ShenWork.IntervalIterateGradMajorant
      .chemDivMixedClosedRepr_of_iterateGradSummable
        (H := Hphys)
        (Hu := Hu)
        (HuGrad := HuGrad)
        (hfloor := hfloor)
        (bdry := hbdry)
  exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

Inside the existing `hlocal_slab` proof, this reduces to the shorter drop-in block:

```lean
    · -- Field 3: ContinuousOn of time derivative on closed slab.
      have hrepr :
          ChemDivMixedTimeDerivClosedRepr
            p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2)) :=
        ShenWork.IntervalIterateGradMajorant
          .chemDivMixedClosedRepr_of_iterateGradSummable
            (H := Hphys)
            (Hu := Hu)
            (HuGrad := HuGrad)
            (hfloor := hfloor)
            (bdry := hbdry)
      exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

## If the Level0 context has only `Hg2u`, not `HuGrad`

Use the lower-level producer directly:

```lean
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.Paper2.IntervalConjugatePicard

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalChemDivMixedReprWitness
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data resolverTimeCoeff)
open ShenWork.IntervalIteratePicardJointC2
  (IteratePicardJointC2Data)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- Same 3G proof, using the lower-level witness bridge when `Hg2u` is already
available. -/
theorem level0_sorry_3G_from_mkWitness
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {Bt Btu : ℕ → ℕ → ℝ} {cH : ℕ → ℝ → ℝ} {s : ℝ}
    (Hphys : PhysicalResolverJointC2Data
      p (conjugatePicardIter p u₀ 0) Bt)
    (Hu : IteratePicardJointC2Data
      (conjugatePicardIter p u₀ 0) cH Btu)
    (Hg2u : Summable (boundedWeightJointGradMajorant Btu 2))
    (hfloor : ∀ q : ℝ × ℝ,
      0 < 1 + valueSeriesRep
        (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)) q)
    (hbdry : ∀ t ∈ Icc (s - min (1 : ℝ) (s / 2))
        (s + min (1 : ℝ) (s / 2)),
      ∀ x ∈ ({0, 1} : Set ℝ),
        coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) t x =
          mixedAlgebra p.β
            (valueSeriesRep cH)
            (iterateDtValue cH)
            (iterateDtGrad cH)
            (gradSeriesRep cH)
            (valueSeriesRep
              (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
            (gradSeriesRep
              (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
            (grad2SeriesRep
              (resolverTimeCoeff p (conjugatePicardIter p u₀ 0)))
            (resolverDtValue p (conjugatePicardIter p u₀ 0))
            (resolverDtGrad p (conjugatePicardIter p u₀ 0))
            (resolverDtGrad2 p (conjugatePicardIter p u₀ 0))
            (t, x)) :
    ContinuousOn
      (Function.uncurry
        (coupledChemDivTimeDerivativeLift p
          (conjugatePicardIter p u₀ 0)))
      (Icc (s - min (1 : ℝ) (s / 2))
          (s + min (1 : ℝ) (s / 2)) ×ˢ Icc (0 : ℝ) 1) := by
  have hrepr :
      ChemDivMixedTimeDerivClosedRepr
        p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2)) :=
    ShenWork.IntervalChemDivMixedReprWitness
      .chemDivMixedTimeDerivClosedRepr_of_mkWitness
        (H := Hphys)
        (Hu := Hu)
        (Hg2u := Hg2u)
        (hfloor := hfloor)
        (bdry := hbdry)
  exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

## How this maps to the files

`IntervalChemDivTimeDerivClosed.lean` defines `ChemDivMixedTimeDerivClosedRepr` and proves:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed :
  ChemDivMixedTimeDerivClosedRepr p u τ δ →
  ContinuousOn
    (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

`IntervalChemDivMixedReprConstruct.lean` proves:

```lean
chemDivMixedTimeDerivClosedRepr_of_data :
  ChemDivMixedReprData p u τ δ →
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

`IntervalChemDivMixedReprWitness.lean` proves the bridge from the honest witness bundle:

```lean
chemDivMixedTimeDerivClosedRepr_of_witness :
  ChemDivMixedReprWitnessData p u τ δ →
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

and the useful producer from resolver/iterate data:

```lean
chemDivMixedTimeDerivClosedRepr_of_mkWitness :
  PhysicalResolverJointC2Data p u Bt →
  IteratePicardJointC2Data u c Btu →
  Summable (boundedWeightJointGradMajorant Btu 2) →
  (∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q) →
  boundary agreement →
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

`IntervalIterateGradMajorant.lean` adds the wrapper:

```lean
chemDivMixedClosedRepr_of_iterateGradSummable :
  PhysicalResolverJointC2Data p u Bt →
  IteratePicardJointC2Data u c Btu →
  (∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Btu m)) →
  (∀ q : ℝ × ℝ, 0 < 1 + valueSeriesRep (resolverTimeCoeff p u) q) →
  boundary agreement →
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

## Bottom line for 3G

The exact 3G proof is just:

```lean
have hrepr : ChemDivMixedTimeDerivClosedRepr
    p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2)) :=
  ShenWork.IntervalIterateGradMajorant
    .chemDivMixedClosedRepr_of_iterateGradSummable
      (H := Hphys)
      (Hu := Hu)
      (HuGrad := HuGrad)
      (hfloor := hfloor)
      (bdry := hbdry)
exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

provided `Hphys`, `Hu`, `HuGrad`, `hfloor`, and `hbdry` are actually in the Level0 local context. If only `PhysicalResolverJointC2Data` is available, then 3G is **not** closed yet; the missing work is exactly the Level0 construction of the u-side heat witness, the iterate gradient summability leg, the global floor for the chosen representative, and the endpoint boundary agreement.
