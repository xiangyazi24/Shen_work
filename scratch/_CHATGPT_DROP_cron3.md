# Q1053 (cron3): Level0 floor-weakening cascade

## Verdict

No: Option (A) floor-weakening is a good first domino, but it does **not** by itself make the whole Level0 chain close automatically.

What becomes automatic after the source-side data exists:

* `FlooredSourceTimeData` + weighted summability `hval/hgrad` gives `PhysicalSourceTimeC2` via `physicalSourceTimeC2_of_floored`.
* `PhysicalSourceTimeC2` gives `PhysicalResolverJointC2Data` via `physicalResolverJointC2Data_of_floor`.
* `PhysicalResolverJointC2Data` directly closes the resolver value/gradient joint `C²` fields 3C/3D via `coupledChemical_jointContDiffAt_two` and `coupledChemical_grad_jointContDiffAt_two`.
* `PhysicalResolverJointC2Data` directly closes the resolver inner commute part of 3F via `coupledChemical_innerCommute_of_physicalJointC2`, and the chem-div flux time bridge via `coupledChemDivFlux_timeBridge_of_physicalJointC2`, assuming the u-side joint `C²` and positivity inputs.

What is **not** automatic from floor-weakening alone:

* the weighted source summability inputs `hval/hgrad` required by `physicalSourceTimeC2_of_floored`;
* the u-side joint `C²` / 3A input, which comes from `IteratePicardJointC2Data`, not from `FlooredSourceTimeData`;
* the source-continuity slab `hsrc` for `coupledChemDivSourceLift`;
* the closed-slab mixed representative 3G, which is produced only from `PhysicalResolverJointC2Data` **plus** `IteratePicardJointC2Data`, u-gradient summability, a global resolver floor, and a boundary algebra agreement;
* the old spectral Level0 theorem `resolverHasSpectralAgreementC2Coeff_heatLevel0`, whose `DuhamelSourceTimeC2Coeff` lane is explicitly bypassed by the physical route and still has separate `sorry`s.

So the correct answer is: **the physical resolver/FAC cascade is wired, but the entire Level0 closure is not automatic unless the remaining non-resolver/u-side/summability/mixed-boundary inputs are also supplied.**

## Imports for the mapped cascade

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.PDE.IntervalIteratePicardJointC2
import ShenWork.Paper2.IntervalResolverLevel0SpectralC2Coeff
```

## Source-side first domino

The Level0 heat source theorem is:

```lean
ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
```

It returns:

```lean
FlooredSourceTimeData p (conjugatePicardIter p u₀ 0)
  (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
  (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀))
```

The six current obligations are exactly:

```lean
d0
d1
sliceC2
sliceNeumann
zerothBound
laplBound
```

Assuming Option (A) retypes the local slab/floor hypotheses so the positive-time heat semigroup proofs fit, these six are the source-side `FlooredSourceTimeData` target.

## FlooredSourceTimeData → PhysicalSourceTimeC2

The next theorem is:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
```

Shape:

```lean
theorem physicalSourceTimeC2_of_floored
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

Important non-automatic point: `hval` and `hgrad` are not fields of `FlooredSourceTimeData`; they are additional weighted bounded-majorant summability inputs. The file proves the coefficient bounds by `srcTimeCoeff_bound`, but the weighted joint summability still has to be supplied.

## PhysicalSourceTimeC2 → PhysicalResolverJointC2Data

The next theorem is:

```lean
ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor
```

Shape:

```lean
theorem physicalResolverJointC2Data_of_floor
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

This part is automatic once `PhysicalSourceTimeC2` exists. It transfers source coefficient `C²` and bounds through the constant elliptic weight using:

```lean
resolverTimeCoeff_eq_weight_smul
resolverTimeCoeff_bound
```

## PhysicalResolverJointC2Data → resolver joint C²: 3C/3D

These close directly from `PhysicalResolverJointC2Data`:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two
```

Shapes:

```lean
theorem coupledChemical_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

So 3C/3D are genuinely automatic from `PhysicalResolverJointC2Data`.

## PhysicalResolverJointC2Data → resolver inner commute / FAC time bridge: 3F

The resolver inner commute theorem is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemical_innerCommute_of_physicalJointC2
```

Shape:

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2
    (H : PhysicalResolverJointC2Data p u Bt) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s
```

The chem-div flux time bridge theorem is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_timeBridge_of_physicalJointC2
```

Shape:

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : ∀ s : ℝ, ∀ x : ℝ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))
```

This means the bridge part of 3F is automatic only after the separate u-side `hu_c2` and positivity `hbase` inputs are present.

The combined FAC producer with the time bridge discharged is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

It still requires:

```lean
(H : PhysicalResolverJointC2Data p u Bt)
(hu_cont : ∀ s : ℝ, Continuous (u s))
(hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
(other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
  source_continuity ∧ hu_c2 ∧ htime_cont)
```

The resolver floor used inside is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemical_floor_pos_of_nonneg_continuous
```

## 3G / closed-slab mixed time derivative

The closed-slab representative target is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
```

Definition shape:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

The closed-slab continuity theorem is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.chemDivMixedTimeDeriv_jointContinuousOn_closed
```

and the FAC producer with `htime_cont` discharged is:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

Shape:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      source_continuity ∧ hu_c2 ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

But `ChemDivMixedTimeDerivClosedRepr` is **not** produced from `PhysicalResolverJointC2Data` alone. The existing full producer is:

```lean
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_mkWitness
```

Shape:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_mkWitness
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

So 3G still has real residuals: `Hu`, `Hg2u`, `hfloor`, and `bdry`.

## 3A / u-side joint C²

The u-side field is not produced by `FlooredSourceTimeData`. It comes from:

```lean
ShenWork.IntervalIteratePicardJointC2.IteratePicardJointC2Data
```

with producer:

```lean
ShenWork.IntervalIteratePicardJointC2.iterate_lift_jointContDiffAt_two
ShenWork.IntervalIteratePicardJointC2.iterate_hu_c2_slab
```

Shape:

```lean
theorem iterate_hu_c2_slab
    (H : IteratePicardJointC2Data u c Bt) :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)
```

Thus 3A requires a Level0/iterate proof of `IteratePicardJointC2Data`; it is not a corollary of the source-side `FlooredSourceTimeData` package.

## Old direct iterate-to-FAC route

There is also:

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
```

Shape:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
    (H : IterateSourceTimeData p u du d2u)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) → Summable ...)
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) → Summable ...)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      source_continuity ∧ hu_c2 ∧ hbase ∧ time_bridge ∧ htime_cont) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This confirms the same diagnosis: `IterateSourceTimeData` / `FlooredSourceTimeData` is not enough; the route still explicitly takes weighted summability and the non-resolver FAC slab data.

## Old spectral Level0 theorem remains separate

The old spectral C² coefficient route is:

```lean
ShenWork.Paper2.ResolverLevel0SpectralC2Coeff.resolverHasSpectralAgreementC2Coeff_heatLevel0
```

It still has explicit `sorry` blocks for:

```lean
hresolver_series
ha0_bound
srcC2 : DuhamelSourceTimeC2Coeff a
hcoeff_deriv
hcoeff_deriv_cont
```

The file itself says the physical resolver lane bypasses `DuhamelSourceTimeC2Coeff`. Therefore floor-weakening plus the physical route does **not** automatically close this spectral theorem.

## Full dependency cascade

```text
Option (A) floor weakening
  ↓
heatSemigroup_flooredSourceTimeData
  fills: d0, d1, sliceC2, sliceNeumann, zerothBound, laplBound
  ↓ plus hval/hgrad (not automatic)
physicalSourceTimeC2_of_floored
  ↓
physicalResolverJointC2Data_of_floor
  ↓
PhysicalResolverJointC2Data
  ├─ coupledChemical_jointContDiffAt_two       → resolver value joint C² (3C)
  ├─ coupledChemical_grad_jointContDiffAt_two  → resolver gradient joint C² (3D)
  ├─ coupledChemical_innerCommute_of_physicalJointC2 → resolver inner commute (3F part)
  └─ with hu_c2 + hbase:
       coupledChemDivFlux_timeBridge_of_physicalJointC2 → FAC time bridge (3F part)

For full FAC:
  PhysicalResolverJointC2Data
  + hu_cont + hu_nonneg
  + source_continuity
  + hu_c2 from IteratePicardJointC2Data / iterate_hu_c2_slab
  + ChemDivMixedTimeDerivClosedRepr
    from chemDivMixedTimeDerivClosedRepr_of_mkWitness
      requiring Hu + Hg2u + hfloor + bdry
  ↓
  coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

## Bottom line by labels

* **3C/3D:** yes, automatic once `PhysicalResolverJointC2Data` exists.
* **3F:** mostly automatic from `PhysicalResolverJointC2Data`, but needs u-side `hu_c2` and positivity inputs for the flux bridge.
* **3E:** resolver positivity floor is covered by `coupledChemical_floor_pos_of_nonneg_continuous`, but it requires `hu_cont` and `hu_nonneg`.
* **3G:** not automatic; needs `chemDivMixedTimeDerivClosedRepr_of_mkWitness` inputs (`Hu`, `Hg2u`, `hfloor`, `bdry`).
* **3A:** not automatic; needs `IteratePicardJointC2Data` and `iterate_hu_c2_slab`.
* **1A / 2A-sup:** if these refer to source-side Level0 heat data and weighted summability, then the six `heatSemigroup_flooredSourceTimeData` fields are fillable under Option (A), but the weighted `hval/hgrad` summability required by `physicalSourceTimeC2_of_floored` is still a separate theorem/input.

So the honest cascade is: **Option (A) closes the floor/time wall and unlocks the physical resolver lane, but the full Level0 closure still needs explicit producers for weighted summability, u-side joint C², source continuity, mixed closed-slab representation, and boundary agreement.**
