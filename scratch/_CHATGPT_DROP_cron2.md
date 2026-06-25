# Q375 (cron2): `CoupledDuhamelClassicalResidualAfterT6`

## Executive verdict

I read the current definition in `ShenWork/PDE/IntervalCoupledRegularityBanked.lean`.

`CoupledDuhamelClassicalResidualAfterT6 p T u` is a **seven-field classical-regularity residual**. It is not the whole mild-to-classical gap. It is specifically the part of `intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u)` that is **not supplied by the banked T6 Duhamel closed-slice atom**.

The T6 atom, under source time-`C¹` and slice agreement,

```lean
hsrc   : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u)
hagree : CoupledDuhamelT6SliceAgreement p T u
```

supplies only the **u-side closed spatial `C²` package** and the **u-side Neumann one-sided/endpoint data** for each positive time slice:

```lean
ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1)
Filter.Tendsto (deriv (intervalDomainLift (u t))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
Filter.Tendsto (deriv (intervalDomainLift (u t))) (nhdsWithin 1 (Set.Iio 1)) (nhds 0)
deriv (intervalDomainLift (u t)) 0 = 0
deriv (intervalDomainLift (u t)) 1 = 0
```

`CoupledDuhamelClassicalResidualAfterT6` carries the complement needed to build the full seven-atom `intervalDomainClassicalRegularity` package: resolver/v-side spatial regularity and Neumann data, plus all time/joint continuity regularity for both `u` and the coupled chemical concentration.

So, yes: **relative to the banked T6 spectral/source data, this is exactly the named residual for the classical-regularity part that T6 cannot close.** But it is not the full “mild solution → classical solution” gap, because it does **not** include:

* positivity of `u`,
* the pointwise parabolic PDE `pde_u`,
* initial trace,
* resolver nonnegativity/PDE/boundary facts discharged by the coupled core.

Those are packaged one level up in `CoupledDuhamelResidualAfterBankedT6` / `CoupledDuhamelBankedT6Frontier`. In the gradient-mild route, positivity and trace are already banked, so the remaining frontier becomes `pde_u + CoupledDuhamelClassicalResidualAfterT6`. In the χ₀=0 spectral route, `pde_u` can be closed by spectral agreement, leaving this classical residual as the named remaining coupled regularity obligation.

## Lean probes used

```lean
import ShenWork.PDE.IntervalCoupledRegularityBanked

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

#check CoupledDuhamelT6SliceAgreement
#check coupledDuhamel_T6_closedSlicePack
#check CoupledDuhamelClassicalResidualAfterT6
#check intervalDomainClassicalRegularity_of_T6_source_and_residual
#check CoupledDuhamelResidualAfterBankedT6
#check regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual

end ShenWork.IntervalCoupledRegularityBootstrap
```

```lean
import ShenWork.PDE.IntervalCoupledClassicalResidualAfterT6FromBanked

open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring

#check coupledDuhamelClassicalResidualAfterT6_of_frontier
#check coupledDuhamelClassicalResidualAfterT6_of_banked_resolver_O1_T6

end ShenWork.IntervalCoupledRegularityBootstrap
```

```lean
import ShenWork.PDE.IntervalCoupledResidualAfterBankedT6Discharge

open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalDomainPdeUProducer
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDuhamelClosedC2

#check CoupledDuhamelBankedT6Frontier
#check CoupledDuhamelBankedT6ChiZeroFrontier
#check coupledDuhamelResidualAfterBankedT6_of_gradientMild_frontier
#check coupledDuhamelResidualAfterBankedT6_of_gradientMild_chiZero_spectral
#check regularityBootstrap_of_gradientMild_bankedT6_chiZero_spectral

end ShenWork.IntervalCoupledRegularityBootstrap
```

## Exact definition read

The current definition is:

```lean
import ShenWork.PDE.IntervalCoupledRegularityBanked

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

/-- The residual classical-regularity atoms after T6 has supplied the u-side
closed-spatial regularity and one-sided Neumann limits. -/
structure CoupledDuhamelClassicalResidualAfterT6
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  v_interiorC2 :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2
        (intervalDomainLift (coupledChemicalConcentration p u t))
        (Set.Ioo (0 : ℝ) 1)
  timeC1 :
    ∀ x : intervalDomainPoint, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      (DifferentiableAt ℝ (fun s : ℝ => u s x) t ∧
          DifferentiableAt ℝ
            (fun s : ℝ => coupledChemicalConcentration p u s x) t) ∧
        (ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => u r x) s)
            (Set.Ioo (0 : ℝ) T) ∧
          ContinuousOn
            (fun s : ℝ =>
              deriv (fun r : ℝ => coupledChemicalConcentration p u r x) s)
            (Set.Ioo (0 : ℝ) T))
  jointTimeDeriv :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun s : ℝ =>
                intervalDomainLift (coupledChemicalConcentration p u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)
  v_neumannLimits :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      Filter.Tendsto
          (deriv (intervalDomainLift (coupledChemicalConcentration p u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift (coupledChemicalConcentration p u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  v_closedC2 :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2
          (intervalDomainLift (coupledChemicalConcentration p u t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (coupledChemicalConcentration p u t)) 0 = 0 ∧
        deriv (intervalDomainLift (coupledChemicalConcentration p u t)) 1 = 0
  closedJointTimeDeriv :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun s : ℝ =>
                intervalDomainLift (coupledChemicalConcentration p u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  jointValue :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (coupledChemicalConcentration p u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)

end ShenWork.IntervalCoupledRegularityBootstrap
```

## Field-by-field interpretation

### 1. `v_interiorC2`

This is **v-side interior spatial `C²`**:

```lean
∀ t ∈ (0,T),
  ContDiffOn ℝ 2
    (intervalDomainLift (coupledChemicalConcentration p u t))
    (Set.Ioo 0 1)
```

T6 supplies u-side closed `C²` from the Duhamel profile. It does not prove this resolver/v-side interior spatial regularity.

### 2. `timeC1`

This is **pointwise-in-space time differentiability and time-derivative continuity** for both `u` and the coupled chemical concentration:

```lean
∀ x, ∀ t ∈ (0,T),
  (DifferentiableAt ℝ (fun s => u s x) t ∧
   DifferentiableAt ℝ (fun s => coupledChemicalConcentration p u s x) t) ∧
  (ContinuousOn (fun s => deriv (fun r => u r x) s) (Set.Ioo 0 T) ∧
   ContinuousOn
     (fun s => deriv
       (fun r => coupledChemicalConcentration p u r x) s)
     (Set.Ioo 0 T))
```

This is not a spatial T6 conclusion. T6 is a per-time-slice closed `C²`/Neumann statement for the u-profile, not a time-`C¹` statement for the solution trajectory and resolver trajectory.

### 3. `jointTimeDeriv`

This is **open-spatial joint continuity of time derivatives** for both lifted `u` and lifted `v`:

```lean
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      deriv (fun s => intervalDomainLift (u s) x) t))
  (Set.Ioo 0 T ×ˢ Set.Ioo 0 1)
∧
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      deriv
        (fun s =>
          intervalDomainLift (coupledChemicalConcentration p u s) x) t))
  (Set.Ioo 0 T ×ˢ Set.Ioo 0 1)
```

Again: not provided by T6 closed-slice spatial regularity.

### 4. `v_neumannLimits`

This is **v-side one-sided Neumann limit data**:

```lean
∀ t ∈ (0,T),
  Filter.Tendsto
    (deriv (intervalDomainLift (coupledChemicalConcentration p u t)))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  ∧
  Filter.Tendsto
    (deriv (intervalDomainLift (coupledChemicalConcentration p u t)))
    (nhdsWithin 1 (Set.Iio 1)) (nhds 0)
```

T6 supplies the analogous u-side one-sided Neumann limits; this field carries the resolver/v-side analog.

### 5. `v_closedC2`

This is **v-side closed spatial `C²` plus endpoint `deriv = 0` values**:

```lean
∀ t ∈ (0,T),
  ContDiffOn ℝ 2
    (intervalDomainLift (coupledChemicalConcentration p u t))
    (Set.Icc 0 1)
  ∧
  deriv (intervalDomainLift (coupledChemicalConcentration p u t)) 0 = 0
  ∧
  deriv (intervalDomainLift (coupledChemicalConcentration p u t)) 1 = 0
```

T6 supplies the analogous u-side closed `C²` and endpoint derivative values; this field carries the v-side analog.

### 6. `closedJointTimeDeriv`

This is **closed-spatial joint continuity of time derivatives** for both lifted `u` and lifted `v`:

```lean
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      deriv (fun s => intervalDomainLift (u s) x) t))
  (Set.Ioo 0 T ×ˢ Set.Icc 0 1)
∧
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      deriv
        (fun s =>
          intervalDomainLift (coupledChemicalConcentration p u s) x) t))
  (Set.Ioo 0 T ×ˢ Set.Icc 0 1)
```

This is stronger in the spatial component than `jointTimeDeriv` because the spatial slab is closed `[0,1]`, not open `(0,1)`.

### 7. `jointValue`

This is **closed-spatial joint continuity of the lifted values** of both `u` and `v`:

```lean
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
  (Set.Ioo 0 T ×ˢ Set.Icc 0 1)
∧
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      intervalDomainLift (coupledChemicalConcentration p u t) x))
  (Set.Ioo 0 T ×ˢ Set.Icc 0 1)
```

This is value-level joint continuity on `(0,T) × [0,1]` for both the population and resolver signal.

## How T6 and the residual reconstruct `intervalDomainClassicalRegularity`

The file immediately uses the residual here:

```lean
import ShenWork.PDE.IntervalCoupledRegularityBanked

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

#check intervalDomainClassicalRegularity_of_T6_source_and_residual

-- theorem intervalDomainClassicalRegularity_of_T6_source_and_residual
--     {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
--     (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
--     (hagree : CoupledDuhamelT6SliceAgreement p T u)
--     (R : CoupledDuhamelClassicalResidualAfterT6 p T u) :
--     intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u)

end ShenWork.IntervalCoupledRegularityBootstrap
```

The proof pattern is important:

```lean
-- hpack := coupledDuhamel_T6_closedSlicePack hsrc hagree
--
-- intervalDomainClassicalRegularity_of_atoms
--   { interiorC2 :=
--       -- u-side from hpack, v-side from R.v_interiorC2
--     timeC1 := R.timeC1
--     jointTimeDeriv := R.jointTimeDeriv
--     neumannLimits :=
--       -- u-side from hpack, v-side from R.v_neumannLimits
--     closedC2 :=
--       -- u-side from hpack, v-side from R.v_closedC2
--     closedJointTimeDeriv := R.closedJointTimeDeriv
--     jointValue := R.jointValue }
```

So the split is exactly:

| Atom in `intervalDomainClassicalRegularity` | u-side source | v-side / time source |
|---|---|---|
| `interiorC2` | T6 `hpack` restricted from closed to open | `R.v_interiorC2` |
| `timeC1` | `R.timeC1` | `R.timeC1` |
| `jointTimeDeriv` | `R.jointTimeDeriv` | `R.jointTimeDeriv` |
| `neumannLimits` | T6 `hpack` | `R.v_neumannLimits` |
| `closedC2` | T6 `hpack` | `R.v_closedC2` |
| `closedJointTimeDeriv` | `R.closedJointTimeDeriv` | `R.closedJointTimeDeriv` |
| `jointValue` | `R.jointValue` | `R.jointValue` |

This shows the residual is deliberately the **post-T6 complement** of the full classical regularity atom list.

## What it is not carrying

It does not carry `u_pos`, `pde_u`, or `InitialTrace`. Those are in the next wrapper:

```lean
import ShenWork.PDE.IntervalCoupledRegularityBanked

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

-- structure CoupledDuhamelResidualAfterBankedT6
--     (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
--     (u : ℝ → intervalDomainPoint → ℝ) : Prop where
--   u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
--   pde_u : ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
--     intervalDomain.timeDeriv u t x =
--       intervalDomain.laplacian (u t) x
--         - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
--             (coupledChemicalConcentration p u t) x
--         + u t x * (p.a - p.b * (u t x) ^ p.α)
--   classicalResidual : CoupledDuhamelClassicalResidualAfterT6 p T u
--   initialTrace : InitialTrace intervalDomain u₀ u
#check CoupledDuhamelResidualAfterBankedT6

end ShenWork.IntervalCoupledRegularityBootstrap
```

And after using gradient-mild positivity plus the banked initial-approach theorem, the remaining frontier is:

```lean
import ShenWork.PDE.IntervalCoupledResidualAfterBankedT6Discharge

open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalDomainPdeUProducer
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDuhamelClosedC2

-- structure CoupledDuhamelBankedT6Frontier
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     (D : GradientMildSolutionData p u₀) : Prop where
--   pde_u : ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
--     intervalDomain.timeDeriv D.u t x =
--       intervalDomain.laplacian (D.u t) x
--         - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
--             (coupledChemicalConcentration p D.u t) x
--         + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
--   classicalResidual : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u
#check CoupledDuhamelBankedT6Frontier

end ShenWork.IntervalCoupledRegularityBootstrap
```

And in the χ₀=0 spectral specialization:

```lean
import ShenWork.PDE.IntervalCoupledResidualAfterBankedT6Discharge

open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalDomainPdeUProducer
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDuhamelClosedC2

-- structure CoupledDuhamelBankedT6ChiZeroFrontier
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     (D : GradientMildSolutionData p u₀) : Prop where
--   hpde : HasSpectralPdeAgreement p D.T D.u
--   classicalResidual : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u
#check CoupledDuhamelBankedT6ChiZeroFrontier

end ShenWork.IntervalCoupledRegularityBootstrap
```

That confirms the layering:

```text
T6 hsrc+hagree
  closes: u closed C² + u Neumann slice data

CoupledDuhamelClassicalResidualAfterT6
  carries: v spatial/Neumann data + all u/v time/joint/value continuity

CoupledDuhamelResidualAfterBankedT6
  carries: u positivity + pde_u + classicalResidual + initialTrace

GradientMildData + banked initial approach
  closes: u positivity + initialTrace

Spectral PDE producer, in χ₀=0 or full-source form
  closes: pde_u

Remaining named post-banked-T6 frontier
  often reduces to: CoupledDuhamelClassicalResidualAfterT6
```

## Can it be discharged from existing banked spectral/frontier data?

There is a theorem that turns the already banked regularity frontier into this residual:

```lean
import ShenWork.PDE.IntervalCoupledClassicalResidualAfterT6FromBanked

open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring

-- theorem coupledDuhamelClassicalResidualAfterT6_of_frontier
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     (D : GradientMildSolutionData p u₀)
--     (F : GradientMildClassicalRegularityFrontierData p D) :
--     CoupledDuhamelClassicalResidualAfterT6 p D.T D.u
#check coupledDuhamelClassicalResidualAfterT6_of_frontier

-- theorem coupledDuhamelClassicalResidualAfterT6_of_banked_resolver_O1_T6
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     (D : GradientMildSolutionData p u₀)
--     (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
--     (Hv : HasResolverDirectSpectralData D.T
--       (mildChemicalConcentration p D.u) p)
--     (Hrestart : HasRestartCosineRepresentations D.T D.u)
--     (Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
--       0 < mildChemicalConcentration p D.u t x) :
--     CoupledDuhamelClassicalResidualAfterT6 p D.T D.u
#check coupledDuhamelClassicalResidualAfterT6_of_banked_resolver_O1_T6

end ShenWork.IntervalCoupledRegularityBootstrap
```

That theorem says the residual is available if you have the older/banked regularity frontier data:

* `Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u`,
* `Hv : HasResolverDirectSpectralData D.T (mildChemicalConcentration p D.u) p`,
* `Hrestart : HasRestartCosineRepresentations D.T D.u`,
* `Hvpos : strict positivity of mildChemicalConcentration`.

But that is not “T6 source data alone.” It uses the regularity-frontier machinery to provide the time/joint/v-side atoms.

## Answer to the direct question

For `CoupledDuhamelClassicalResidualAfterT6 p D.T D.u`, the fields are exactly:

1. `v_interiorC2` — v/resolver interior spatial `C²` on `(0,1)`.
2. `timeC1` — pointwise time `C¹` data for both `D.u` and `coupledChemicalConcentration p D.u`.
3. `jointTimeDeriv` — joint continuity of time derivatives on `(0,D.T) × (0,1)` for both lifted fields.
4. `v_neumannLimits` — v/resolver one-sided Neumann derivative limits at `0` and `1`.
5. `v_closedC2` — v/resolver closed-interval `C²` plus endpoint derivative equalities.
6. `closedJointTimeDeriv` — joint continuity of time derivatives on `(0,D.T) × [0,1]` for both lifted fields.
7. `jointValue` — joint continuity of lifted values on `(0,D.T) × [0,1]` for both lifted fields.

It is the **post-T6 classical-regularity residual**, not the full mild-to-classical residual. T6 closes the u spatial/Neumann slice atoms; this structure carries the v-side and temporal/joint atoms still needed to assemble `intervalDomainClassicalRegularity`.
