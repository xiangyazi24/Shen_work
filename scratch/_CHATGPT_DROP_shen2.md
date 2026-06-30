# Q2341 shen2: Paper2 interval-domain Proposition 2.5 route audit

Repo target: `xiangyazi24/Shen_work`, `main` at commit `6eccd68f`.

## Executive answer

There is a real net-reduction for

```lean
Proposition_2_5 intervalDomain p
```

that does **not** use the refuted global `IntervalDomainInterpolation` route and does **not** just carry old `Paper2BootstrapEstimateBranchData`.

The best current route is the **actual-atoms / nonnegative-B Moser route**:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring
  .intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

It reduces Prop 2.5 to exactly three analytic atom families:

```lean
MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
RelativeMoserInterpolationBefore intervalDomain u T rho p0
quantitative endpoint / root tower:
  ∃ pSeq rootBound,
    (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
      IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

This is a genuine improvement over the old branch-data route.  The remaining atoms are still serious PDE/Moser frontiers, but they are smaller than `Proposition_2_5` itself.

## Routes found, by honesty

### 1. BranchData wrapper: not a net reduction

File:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

Current wrapper:

```lean
theorem intervalDomainPaper2_Proposition_2_5_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_5 intervalDomain p :=
  Proposition_2_5.of_branchData hData
```

This is not useful for reducing Prop 2.5.  The old branch-data record already contains a `prop25` field, and the generic branch-data package is known not to be constructible uniformly from the abstract API.  The repo even has obstruction theorems such as:

```lean
theorem not_forall_branchData_after_lpi :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p)
```

in `ShenWork/Paper2/IntervalDomainLPI.lean`.

Also in `IntervalDomainStatementAssembly.lean`, the thin section-2 wrapper is honest but does not produce Prop 2.5:

```lean
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hProp25 : Proposition_2_5 intervalDomain p) :
    IntervalDomainPaper2BootstrapEstimateTargets p
```

It explicitly takes `hProp25`.  It is a consumer of a Prop 2.5 route, not a producer.

### 2. LPI structured-data wrapper: honest but still coarse

File:

```text
ShenWork/Paper2/IntervalDomainLPI.lean
```

The first honest Prop 2.5 producer is:

```lean
theorem Proposition_2_5_intervalDomain_of_structured_moser_data
    {p : CM2Params}
    (hdata : ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {Tmax : ℝ}, 0 < Tmax →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
        ∀ pExp,
          max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
          LpPowerBoundedBefore intervalDomain pExp Tmax u →
            IntervalDomainStructuredMoserBootstrapData u Tmax) :
    Proposition_2_5 intervalDomain p
```

This is honest because `IntervalDomainStructuredMoserBootstrapData` contains the actual Moser components and its `.boundedBefore` field is computed by `MoserClosure`; it is not equivalent to `Proposition_2_5`.  But it is still coarse: a caller must produce an entire structured Moser package for each solution/exponent.

The file also proves the interval heat endpoint:

```lean
intervalDomainHeat_Lp_Linfty_pointwise_from_memLp
intervalDomainHeat_Lp_Linfty_bound_from_memLp
intervalDomainSemigroupEstimateData_Lp_Linfty_bound_from_memLp
```

Those are useful analytic atoms, but they do not themselves produce Prop 2.5.  The file says that explicitly in its header.

### 3. Structured Moser frontiers: cleaner package

File:

```text
ShenWork/Paper2/IntervalDomainStructuredMoserData.lean
```

Key structure:

```lean
structure Prop25MoserFrontiers
    (u : ℝ → intervalDomain.Point → ℝ) (T pExp : ℝ) where
  pSeq : ℕ → ℝ
  rootBound : ℕ → ℝ
  energy : LpBootstrapEnergyInequality intervalDomain u T 1 pExp
  dissipation : MoserDissipationDropBefore intervalDomain u T 1 pExp
  relative : RelativeMoserInterpolationBefore intervalDomain u T 1 pExp
  powerIntegrable :
    ∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        MeasureTheory.volume 0 1
  endpoint :
    (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
      IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Producer:

```lean
theorem Proposition_2_5_intervalDomain_of_prop25_moser_frontiers
    {params : CM2Params}
    (hfront :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) < pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          Prop25MoserFrontiers u T pExp) :
    Proposition_2_5 intervalDomain params
```

This is a genuine net-reduction relative to `Prop25` and `BranchData`, but not the smallest current reduction.  It carries `energy`, `dissipation`, `relative`, `powerIntegrable`, and `endpoint` as fields; several of these can now be produced from regularity and actual atoms in later files.

Useful supporting definitions/theorems in this file:

```lean
abstractBootstrapHypothesis_of_prop25_exponent
lpMono_of_classical_solution_power_integrable
structuredMoserBootstrapData_of_solution_frontiers
structuredMoserBootstrapData_of_prop25_frontiers
```

### 4. MCL route: warns about false old GN input

File:

```text
ShenWork/Paper2/IntervalDomainMCL.lean
```

This file contains a theorem:

```lean
theorem Proposition_2_5_intervalDomain_of_MCL_frontiers
    {params : CM2Params}
    (hcross : ... → CrossDiffusionBootstrapEstimate intervalDomain params T 1 u v)
    (hdiss : ... → MoserDissipationDropBefore intervalDomain u T 1 pExp)
    (hGN : OldUnitIntervalPowerGNYoungForMoser)
    (hEndpoint : ... → ∃ pSeq rootBound, ...)
    : Proposition_2_5 intervalDomain params
```

Do **not** use this as the preferred route, because the same file explicitly labels:

```lean
def OldUnitIntervalPowerGNYoungForMoser : Prop := ...
```

as legacy and false for constant functions.  The comment states that the left side scales like `A^(p+rho)` while the lower-order term scales like `A^p`.  The replacement in the same file is:

```lean
def UnitIntervalPowerGNYoungForMoser : Prop := ...

theorem unitIntervalPowerGNYoungForMoser_proved :
    UnitIntervalPowerGNYoungForMoser
```

However, `Proposition_2_5_intervalDomain_of_MCL_frontiers` is still wired to the old `OldUnitIntervalPowerGNYoungForMoser`, so it is not the best honest headline route.

The useful theorem from `IntervalDomainMCL.lean` is instead:

```lean
def structuredMoserBootstrapData_of_regularity_MCL
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBefore intervalDomain u T rho p0)
    (hEndpoint : ...)
    : IntervalDomainStructuredMoserBootstrapData u T
```

It shows how regularity supplies energy, power-integrability, and Lp monotonicity, but it still uses the older pointwise `MoserDissipationDropBefore`, not the repaired nonnegative-B shape.

### 5. Actual atoms route: best current net-reduction

Files:

```text
ShenWork/PDE/IntervalDomainMoserActualAtoms.lean
ShenWork/PDE/P3MoserActualWiring.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

The older actual-atoms theorem is:

```lean
theorem intervalDomain_endpointBoundFromLp_of_quantitative_root_tower
    {params : CM2Params}
    (hcross : ... → CrossDiffusionBootstrapEstimate intervalDomain params T 1 u v)
    (hdiss : ... → MoserDissipationDropBefore intervalDomain u T 1 pExp)
    (hrel : ... → RelativeMoserInterpolationBefore intervalDomain u T 1 pExp)
    (hEndpoint : ... → ∃ pSeq rootBound, ...)
    : Proposition_2_5 intervalDomain params
```

It is honest, but it still carries the cross-diffusion bootstrap and the older pointwise dissipation shape.

The better theorem is in `ShenWork/PDE/P3MoserActualWiring.lean`:

```lean
theorem intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    {params : CM2Params}
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) < pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Proposition_2_5 intervalDomain params
```

Why this is the best route:

* `CrossDiffusionBootstrapEstimate` is produced internally from the classical solution via `intervalDomain_crossDiffusionBootstrapEstimate_of_classical`.
* The bootstrap seed is built internally by `abstract_prop25_bootstrap_two_gamma` using `rho = 2 * params.γ`.
* `LpBootstrapEnergyInequality` is produced internally by `intervalDomain_LpBootstrapEnergyInequality_of_regularity`.
* Lp monotonicity is produced internally from positivity and `intervalDomain_u_rpow_intervalIntegrable_of_regularity`.
* The final finite-horizon bound is obtained by `intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation` and the quantitative endpoint.

This is a genuine reduction to exactly the PDE/Moser atoms that still need proof.

### 6. Packaged version of the best route

File:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Best existing structure:

```lean
structure IntervalDomainMassLpSmoothingMoserLadderResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity : ...
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint : ...
```

Its Prop 2.5 projection is already present:

```lean
theorem IntervalDomainMassLpSmoothingMoserLadderResiduals.proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    h.moserDissipation h.relativeMoserInterpolation h.quantitativeEndpoint
```

This theorem only uses the three fields:

```lean
h.moserDissipation
h.relativeMoserInterpolation
h.quantitativeEndpoint
```

The other fields of `IntervalDomainMassLpSmoothingMoserLadderResiduals` are for the larger mass/Lp/smoothing route and `to_routeResiduals`, not for Prop 2.5 itself.

## Minimal Lean wiring plan

### Preferred minimal file/import

Use the actual-atoms theorem directly from the PDE namespace.  A Paper2-facing wrapper can live in a small file such as:

```text
ShenWork/Paper2/IntervalDomainProp25ActualAtoms.lean
```

with imports:

```lean
import ShenWork.PDE.IntervalDomainMoserLadderAtoms

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring

noncomputable section

namespace ShenWork.Paper2
```

### Smallest Prop25-only frontier

The current `IntervalDomainMassLpSmoothingMoserLadderResiduals` is a good package for the larger route, but for Prop 2.5 alone the smaller frontier is:

```lean
structure IntervalDomainPaper2Prop25ActualAtomFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Wrapper:

```lean
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation
    hData.relativeMoserInterpolation
    hData.quantitativeEndpoint
```

This is a compile-oriented net reduction: the wrapper is almost definitional, but the data are strictly smaller than `Proposition_2_5` and much smaller than `Paper2BootstrapEstimateBranchData`.

### Convenience wrapper from existing larger residual package

If using the larger route data already present in `IntervalDomainMoserLadderAtoms.lean`, just expose this Paper2-facing wrapper:

```lean
theorem intervalDomainPaper2_Proposition_2_5_of_moserLadderResiduals
    (p : CM2Params)
    (h : ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    Proposition_2_5 intervalDomain p :=
  h.proposition25
```

This is honest, but slightly less minimal because the structure carries fields not needed by Prop 2.5.

## Current route ranking

1. **Best current net-reduction**:

   ```lean
   intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
   ```

   or packaged as:

   ```lean
   IntervalDomainMassLpSmoothingMoserLadderResiduals.proposition25
   ```

2. **Good intermediate route**:

   ```lean
   Proposition_2_5_intervalDomain_of_prop25_moser_frontiers
   ```

   It reduces to `Prop25MoserFrontiers`, but still carries energy/dissipation/relative/power-integrability/endpoint per solution.

3. **Coarse but honest route**:

   ```lean
   Proposition_2_5_intervalDomain_of_structured_moser_data
   ```

   It reduces to a produced `IntervalDomainStructuredMoserBootstrapData` for every solution and qualifying exponent.

4. **Avoid as headline**:

   ```lean
   Proposition_2_5_intervalDomain_of_MCL_frontiers
   ```

   It uses `OldUnitIntervalPowerGNYoungForMoser`, explicitly marked false for constant functions.

5. **Not a reduction**:

   ```lean
   intervalDomainPaper2_Proposition_2_5_of_branchData
   intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
   ```

   The first consumes old branch data containing Prop25; the second takes `hProp25` directly.

## Concrete cleanup recommendation

Add a Paper2-facing file exposing only the actual-atoms route:

```lean
import ShenWork.PDE.IntervalDomainMoserLadderAtoms

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring

noncomputable section

namespace ShenWork.Paper2

structure IntervalDomainPaper2Prop25ActualAtomFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation
    hData.relativeMoserInterpolation
    hData.quantitativeEndpoint

end ShenWork.Paper2
```

Then change interval-domain statement assembly routes that currently accept a naked

```lean
hProp25 : Proposition_2_5 intervalDomain p
```

to optionally accept this smaller frontier and call:

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData p hProp25Atoms
```

This gives a real net-reduction while preserving the existing statement wrappers.

## Final warning

Do not use global `IntervalDomainInterpolation`.  Do not use `OldUnitIntervalPowerGNYoungForMoser` as a headline route.  Do not claim `Paper2BootstrapEstimateBranchData intervalDomain p` is produced by current code.  The honest current Prop25 route is the actual-atoms route through nonnegative-B dissipation, relative Moser interpolation, and quantitative endpoint/root tower.
