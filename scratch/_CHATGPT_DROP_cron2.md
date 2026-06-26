# Q927 (cron2) — direct resolver joint-C² route bypassing `PhysicalResolverJointC2Data`

Static repo inspection only; I did **not** run Lean.

## Short answer

Yes.  For the coupled chemotaxis model, bypass `PhysicalResolverJointC2Data` and use the already-existing **restart spectral cutoff** route:

```text
ResolverHasSpectralAgreementC2Coeff
  → coupledChemicalConcentration_resolver_jointC2At_c2Data
  → resolverSpectralJointC2At_of_restartSmoothCutoff
  → hv_c2 + hgradv_c2
  → coupledChemDivFluxFactorJointC2Inputs
  → coupledChemDivFluxJointC2Hyp
```

This avoids the current root cause entirely: no global-in-time `Bt`, no global `∀ t : ℝ` coefficient `ContDiff`, and no attempt to make `intervalFullSemigroupOperator` behave well at `t < 0`.  The positive-time / horizon constraints are carried by `ResolverHasSpectralAgreementC2Coeff.exists_c2_data` and by the local `FACLocalSlabInputs` time-window field.

## Exact theorem names already available

### Resolver restart / cutoff layer

File:

```text
ShenWork/PDE/IntervalResolverJointC2.lean
```

Available:

```lean
ShenWork.IntervalResolverJointC2.ResolverSpectralJointC2At
ShenWork.IntervalResolverJointC2.resolver_jointC2At_of_spectralAgreement
ShenWork.IntervalResolverJointC2.resolver_value_eventuallyEq_spectralSeries_of_agreement
ShenWork.IntervalResolverJointC2.resolver_grad_eventuallyEq_spectralGradSeries_of_agreement
```

File:

```text
ShenWork/PDE/IntervalResolverJointC2C2Coeff.lean
```

Available:

```lean
ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
ShenWork.IntervalResolverJointC2.resolver_jointC2At_of_spectralAgreement_c2Coeff
ShenWork.IntervalResolverJointC2.resolver_jointC2At_of_spectralAgreement_c2Data
```

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

Available:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete.resolverSpectralJointC2At_of_restartSmoothCutoff
ShenWork.IntervalResolverSpectralJointC2Concrete.concreteRestartValueMajorant_summable
ShenWork.IntervalResolverSpectralJointC2Concrete.concreteRestartGradMajorant_summable
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound
```

These are the exact analog of the heat cutoff pattern: build a globally C² cutoff series, use `contDiff_tsum`, then transfer back by eventual equality near the positive target time.

### Coupled resolver transfer layer

File:

```text
ShenWork/PDE/IntervalCoupledResolverJointC2.lean
```

Available:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration_resolver_jointC2At
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration_resolver_jointC2At_c2Coeff
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration_resolver_jointC2At_c2Data
```

The one to use is:

```lean
coupledChemicalConcentration_resolver_jointC2At_c2Data
```

because it consumes:

```lean
ResolverHasSpectralAgreementC2Coeff U (coupledChemicalConcentration p u)
```

and lets the concrete restart theorem consume the stored `DuhamelSourceTimeC2Coeff` directly.

### FAC / flux assembly layer

File:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
```

Available:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.FACLocalSlabInputs
ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorFACInputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemical_floor_pos_of_nonneg_continuous
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxFactorJointC2Inputs_of_FACInputs
```

This file already implements the direct bypass in spirit.  It derives resolver value/gradient joint-C² from the spectral agreement package and then constructs `CoupledChemDivFluxFactorJointC2Inputs`.

File:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

Available:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivOuterCommuteAtoms_of_factorJointC2Inputs
```

The final direct composition is:

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
  (coupledChemDivFluxFactorJointC2Inputs_of_FACInputs H)
```

modulo the positive-time/horizon refactor below.

## Minimal Paper2 target theorem statement

Create a Paper2 wrapper file, for example:

```lean
import ShenWork.PDE.IntervalChemDivFluxFactorFAC
import ShenWork.PDE.IntervalChemDivFluxJointC2Producer

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralJointC2Concrete
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.Cron2DirectResolver
```

Use a positive-time / finite-horizon variant of the FAC input package:

```lean
structure CoupledChemDivFluxFactorFACInputsPos
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ,
        FACLocalSlabInputs p u U τ δ
```

Minimal target theorem:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
  -- after refactoring `CoupledChemDivFluxFactorJointC2Inputs.exists_local_slab`
  -- to `∀ τ, 0 < τ → ...`, this is exactly the same proof as
  -- `coupledChemDivFluxFactorJointC2Inputs_of_FACInputs`, except `hslabs τ`
  -- becomes `hslabs τ hτ hτU` and the constructor takes `fun τ hτ => ...`.
  sorry
```

Then the Paper2-level capstone is:

```lean
theorem coupledChemDivFluxJointC2Hyp_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (coupledChemDivFluxFactorJointC2Inputs_of_FACInputsPos H)
```

If `CoupledChemDivFluxJointC2Hyp` is also refactored to positive-time-only, use the same statement with the positive-time version of that structure.  If the old all-`τ : ℝ` structure remains, no positive-time-only proof can fill it without reintroducing the bad `t < 0` obligation.

## Direct proof skeleton for `coupledChemDivFluxFactorJointC2Inputs_of_FACInputsPos`

This is the mechanical replacement for the current body of `coupledChemDivFluxFactorJointC2Inputs_of_FACInputs`.

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
  rcases H.resolver_package with ⟨U, HRc2, hslabs⟩
  refine ⟨fun τ hτ => ?_⟩

  -- If the target structure does not carry an upper horizon hypothesis, add it
  -- to the positive-time target; otherwise this theorem should target an
  -- `...On (Ioo 0 U)` style structure.
  have hτU : τ < U := by
    -- This must be an argument/field in the positive-domain version.
    -- Do not fake it from `hτ`.
    sorry

  rcases hslabs τ hτ hτU with
    ⟨δ, hδ, htime_window, hsource, hu_cont, hu_nonneg, hu_c2,
      htime_bridge, htime_cont⟩

  have hresolver_c2 :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
          (s, x) ∧
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
              q.2)
          (s, x) := by
    intro x hx s hs
    rcases htime_window s hs with ⟨hs0, hsU⟩
    exact coupledChemicalConcentration_resolver_jointC2At_c2Data
      (p := p) (u := u) (U := U) (s := s) (x := x)
      HRc2 hs0 hsU hx
      (by
        intro a₀ M _hM ha₀ a src offset hτoffset _hagree
        exact resolverSpectralJointC2At_of_restartSmoothCutoff
          (a₀ := a₀) (M := M) (a := a)
          (offset := offset) (s := s) (x := x)
          hτoffset ha₀ src)

  have hv_c2 :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
          (s, x) :=
    fun x hx s hs => (hresolver_c2 x hx s hs).1

  have hgradv_c2 :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
              q.2)
          (s, x) :=
    fun x hx s hs => (hresolver_c2 x hx s hs).2

  refine ⟨δ, hδ, hsource, hu_c2, hv_c2, hgradv_c2, ?_,
    htime_bridge, htime_cont⟩
  intro x _ s _
  exact coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg s x
```

If you have already added `δ ≤ τ / 2` to all positive-time slab structures, propagate the extra field through the constructor:

```lean
rcases hslabs τ hτ hτU with
  ⟨δ, hδ, hδhalf, htime_window, hsource, hu_cont, hu_nonneg, hu_c2,
    htime_bridge, htime_cont⟩
...
refine ⟨δ, hδ, hδhalf, hsource, hu_c2, hv_c2, hgradv_c2, ?_,
  htime_bridge, htime_cont⟩
```

## How to assemble `coupledChemDivFluxJointC2` from the direct route

Step list:

1. Prove or assume a positive-domain FAC package:

   ```lean
   H : CoupledChemDivFluxFactorFACInputsPos p u
   ```

2. Extract the resolver spectral package:

   ```lean
   rcases H.resolver_package with ⟨U, HRc2, hslabs⟩
   ```

3. For each positive target time `τ` inside the resolver horizon, get a local slab:

   ```lean
   rcases hslabs τ hτ hτU with ⟨δ, hδ, htime_window, hsource,
     hu_cont, hu_nonneg, hu_c2, htime_bridge, htime_cont⟩
   ```

4. For every `s ∈ Metric.ball τ δ`, use `htime_window s hs` to obtain:

   ```lean
   hs0 : 0 < s
   hsU : s < U
   ```

5. Apply the coupled resolver transfer:

   ```lean
   coupledChemicalConcentration_resolver_jointC2At_c2Data
     HRc2 hs0 hsU hx
     (by
       intro a₀ M _hM ha₀ a src offset hτoffset _hagree
       exact resolverSpectralJointC2At_of_restartSmoothCutoff
         (a₀ := a₀) (M := M) (a := a)
         (offset := offset) (s := s) (x := x)
         hτoffset ha₀ src)
   ```

   This returns both resolver value C² and resolver gradient C².

6. Define:

   ```lean
   hv_c2     := fun x hx s hs => (hresolver_c2 x hx s hs).1
   hgradv_c2 := fun x hx s hs => (hresolver_c2 x hx s hs).2
   ```

7. Discharge the resolver floor by nonnegativity/continuity of the Picard slice:

   ```lean
   coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg s x
   ```

8. Build `CoupledChemDivFluxFactorJointC2Inputs` (positive-time version).

9. Feed it to:

   ```lean
   coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
   ```

10. If needed, continue to:

   ```lean
   coupledChemDivOuterCommuteAtoms_of_factorJointC2Inputs
   coupledChemDivSource_timeC1_of_fluxJointC2
   ```

   but only after their local-slab structures have also been changed from all-time `∀ τ : ℝ` to positive-time/horizon-local quantification.

## What changes are needed to `IntervalResolverPhysicalC2` assumptions?

None for this direct route.

`ShenWork/PDE/IntervalResolverPhysicalC2.lean` is a fixed-time **spatial** C² theorem.  It proves facts like:

```lean
resolverR_contDiff_two_of_source_l1
resolverR_contDiffOn_Icc_of_source_l1
```

from source coefficient `ℓ¹` data at a single time slice.  The direct restart route does not need to alter this file and does not need to strengthen its assumptions.

The direct route replaces the entire `PhysicalResolverJointC2Data` lane with:

```lean
ResolverHasSpectralAgreementC2Coeff U (coupledChemicalConcentration p u)
```

plus local FAC slab data.  That is the correct home for time-local joint C².

## What changes are needed versus existing `coupledChemDivFluxJointC2Inputs` assumptions?

Use the current `CoupledChemDivFluxFactorFACInputs` as the model, not `PhysicalResolverJointC2Data`.

Existing `CoupledChemDivFluxFactorJointC2Inputs` requires these fields directly:

```lean
hu_c2
hv_c2
hgradv_c2
hbase
htime_bridge
htime_cont
```

The direct FAC package should require:

```lean
resolver_package :
  ∃ U, ResolverHasSpectralAgreementC2Coeff U (coupledChemicalConcentration p u) ∧
    ∀ τ, 0 < τ → τ < U → ∃ δ, FACLocalSlabInputs p u U τ δ
```

and `FACLocalSlabInputs` keeps only the non-resolver analytic fields:

```lean
0 < δ
∀ s ∈ Metric.ball τ δ, 0 < s ∧ s < U
∀ᶠ s in 𝓝 τ, ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
∀ s, Continuous (u s)
∀ s, ∀ x, 0 ≤ u s x
hu_c2
htime_bridge
htime_cont
```

Then the direct route internally proves:

```lean
hv_c2
hgradv_c2
hbase
```

So the assumption change is:

```text
remove caller-supplied hv_c2/hgradv_c2/hbase
add ResolverHasSpectralAgreementC2Coeff + positive-time local FAC slabs + hu_cont/hu_nonneg
```

No `PhysicalResolverJointC2Data`, no `PhysicalSourceTimeC2`, no `FlooredSourceTimeData`, and no global `Bt` are needed for resolver joint-C² in this route.

## Recommended implementation target

Do not spend effort repairing `heatSemigroup_level0_resolverJointC2Data` through `PhysicalResolverJointC2Data` for this goal.  Instead, add a positive-time wrapper around the already-existing direct FAC route:

```lean
import ShenWork.PDE.IntervalChemDivFluxFactorFAC
import ShenWork.PDE.IntervalChemDivFluxJointC2Producer

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.Cron2DirectResolver

structure CoupledChemDivFluxFactorFACInputsPos
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ,
        FACLocalSlabInputs p u U τ δ

theorem coupledChemDivFluxFactorJointC2Inputs_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
  -- same body as `coupledChemDivFluxFactorJointC2Inputs_of_FACInputs`,
  -- with positive-time/horizon parameters threaded through.
  sorry

theorem coupledChemDivFluxJointC2Hyp_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (coupledChemDivFluxFactorJointC2Inputs_of_FACInputsPos H)

end ShenWork.Paper2.Cron2DirectResolver
```

If `CoupledChemDivFluxFactorJointC2Inputs`/`CoupledChemDivFluxJointC2Hyp` have been refactored to positive-time-only, change only the codomain names and the constructor lambda (`fun τ hτ hτU => ...`) accordingly.
