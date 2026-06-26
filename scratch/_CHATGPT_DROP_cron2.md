# Q931 (cron2) — direct resolver joint-C² cutoff route

Static repo inspection only; I did **not** run Lean.

## Verdict

Yes.  For the coupled chemotaxis resolver, the clean bypass is not to repair
`PhysicalResolverJointC2Data`; it is to use the already-committed **restart
spectral cutoff** route:

```text
ResolverHasSpectralAgreementC2Coeff
  -> coupledChemicalConcentration_resolver_jointC2At_c2Data
  -> resolverSpectralJointC2At_of_restartSmoothCutoff
  -> hv_c2 + hgradv_c2
  -> CoupledChemDivFluxFactorJointC2InputsPos
  -> CoupledChemDivFluxJointC2HypPos
```

This is exactly the same shape as the heat semigroup cutoff proof:

```text
cutoff term is globally C²
  + summable derivative majorants
  + cutoff = 1 near the positive target time
  -> local ContDiffAt at the original, non-cutoff series
```

The current root cause is a **domain/quantifier mismatch**:

* `PhysicalResolverJointC2Data` is global in real time: `coeff_contDiff` is
  `ContDiff ℝ 2` on all of `ℝ`, and `coeff_bound` quantifies `∀ t : ℝ`.
* `CoupledChemDivFluxFactorFACInputs`, `CoupledChemDivFluxFactorJointC2Inputs`,
  and `CoupledChemDivFluxJointC2Hyp` are also currently all-`τ : ℝ` packages.
* The actual analytic data for Paper2 level 0 is positive-time / restart-window
  data: one only has `0 < s - offset`, and the coupled resolver package also has
  a finite spectral horizon `s < U`.

So the direct route should target a positive-time / horizon-local theorem.  If
we keep trying to fill the existing all-time structures from positive-time heat
or restart data, the bad `t < 0` obligation reappears.

Name check: I found the fixed-time physical resolver file as
`ShenWork/PDE/IntervalResolverPhysicalC2.lean`; I did **not** find a separate
file literally named `IntervalPhysicalResolverC2.lean`.  I interpret the
question's `IntervalPhysicalResolverC2` as this fixed-time physical resolver C²
file.

## Exact theorem names already available

### 1. Heat cutoff pattern already committed

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

Useful names:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.heatTerm
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatTerm
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatTerm_contDiff_two
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatTerm_iteratedFDeriv_bound
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatSeries_contDiff_two
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSeries_eventuallyEq_cutoff
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

The cutoff used there comes from:

```lean
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_contDiff
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eq_zero_of_le
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eq_one_of_ge
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eventually_eq_one
```

The theorem to imitate syntactically is:

```lean
theorem heatSemigroup_jointContDiffAt_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀)
```

### 2. Generic resolver cutoff engine

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

The generic engine is:

```lean
ShenWork.IntervalResolverSpectralJointC2Cutoff.resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
```

with supporting definitions:

```lean
ShenWork.IntervalResolverSpectralJointC2Cutoff.cutoffValueTerm
ShenWork.IntervalResolverSpectralJointC2Cutoff.cutoffGradTerm
```

This theorem is the abstract cutoff/extension form: prove global C² of the
cutoff value and gradient series by `contDiff_tsum`, then transfer back by
`EventuallyEq` near the target point.

### 3. Concrete restart cutoff resolver theorem

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

Concrete cutoff names:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_contDiff
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_eventually_eq_one
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_hasCompactSupport
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_iteratedFDeriv_bound_exists
ShenWork.IntervalResolverSpectralJointC2Concrete.restartCutoffDerivMajorant
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSlabMin
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSlabMax
ShenWork.IntervalResolverSpectralJointC2Concrete.restartSlabMin_pos
```

Concrete summable majorants and bounds:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete.restartCoeffCoreMajorant
ShenWork.IntervalResolverSpectralJointC2Concrete.restartCoeffCoreMajorant_summable
ShenWork.IntervalResolverSpectralJointC2Concrete.concreteRestartValueMajorant
ShenWork.IntervalResolverSpectralJointC2Concrete.concreteRestartGradMajorant
ShenWork.IntervalResolverSpectralJointC2Concrete.concreteRestartValueMajorant_summable
ShenWork.IntervalResolverSpectralJointC2Concrete.concreteRestartGradMajorant_summable
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffValueTerm_restartSmoothCutoff_contDiff
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffGradTerm_restartSmoothCutoff_contDiff
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound
```

Final theorem to use:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete.resolverSpectralJointC2At_of_restartSmoothCutoff
```

The exact application shape already used in the repo is:

```lean
exact resolverSpectralJointC2At_of_restartSmoothCutoff
  (a₀ := a₀) (M := M) (a := a)
  (offset := offset) (s := s) (x := x)
  hτoffset ha₀ src
```

### 4. Coupled resolver transfer layer

Files:

```text
ShenWork/PDE/IntervalResolverJointC2.lean
ShenWork/PDE/IntervalResolverJointC2C2Coeff.lean
ShenWork/PDE/IntervalCoupledResolverJointC2.lean
```

Core spectral target and transfer names:

```lean
ShenWork.IntervalResolverJointC2.ResolverSpectralJointC2At
ShenWork.IntervalResolverJointC2.resolver_jointC2At_of_spectralAgreement
ShenWork.IntervalResolverJointC2.resolver_value_eventuallyEq_spectralSeries_of_agreement
ShenWork.IntervalResolverJointC2.resolver_grad_eventuallyEq_spectralGradSeries_of_agreement
ShenWork.IntervalResolverJointC2.resolver_value_contDiffAt_of_spectral_eventuallyEq
ShenWork.IntervalResolverJointC2.resolver_grad_contDiffAt_of_spectral_eventuallyEq
```

C²-coefficient spectral agreement package:

```lean
ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff
ShenWork.IntervalResolverJointC2.resolver_jointC2At_of_spectralAgreement_c2Data
```

Coupled theorem to use:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration_resolver_jointC2At_c2Data
```

This theorem returns both required resolver factor facts:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
  (s, x)
∧
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
  (s, x)
```

### 5. FAC / flux assembly layer

Files:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

Already committed names:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.FACLocalSlabInputs
ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorFACInputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemical_floor_pos_of_nonneg_continuous
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxFactorJointC2Inputs_of_FACInputs
```

The theorem `coupledChemDivFluxFactorJointC2Inputs_of_FACInputs` already performs
the direct resolver cutoff assembly, but its input is still all-`τ : ℝ`.  The body
is the proof to clone/refactor to positive-time domains.

Flux factor and joint-hyp names:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_contDiffAt_of_factorJointC2
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivOuterCommuteAtoms_of_factorJointC2Inputs
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSource_timeC1_of_factorJointC2Inputs
```

The committed object corresponding to “`coupledChemDivFluxJointC2`” appears to be
`CoupledChemDivFluxJointC2Hyp`, produced by
`coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs`.

## Minimal Paper2 target theorem for positive-time-only domains

Create a Paper2 wrapper file, for example:

```lean
import ShenWork.PDE.IntervalChemDivFluxFactorFAC
import ShenWork.PDE.IntervalChemDivFluxJointC2Producer
import ShenWork.PDE.IntervalChemDivOuterCommuteProducer
import ShenWork.PDE.IntervalCoupledResolverJointC2
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralJointC2Concrete
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.Cron2DirectResolver
```

First define a positive-time FAC input wrapper.  This is the same as the existing
`CoupledChemDivFluxFactorFACInputs`, except the slab provider is restricted to
`0 < τ` and `τ < U`.

```lean
structure CoupledChemDivFluxFactorFACInputsPos
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      0 < U ∧
      ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ,
        FACLocalSlabInputs p u U τ δ
```

Then define the positive-time output factor package.  This is the positive-domain
version of `CoupledChemDivFluxFactorJointC2Inputs`: it has the same factor fields
but only for `τ ∈ (0,U)`.  I recommend including the `htime_window` field in the
output package too, because downstream positive-domain theorems will need to know
that their local slab remains inside `(0,U)`.

```lean
structure CoupledChemDivFluxFactorJointC2InputsPos
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ, 0 < δ ∧
    (∀ s : ℝ, s ∈ Metric.ball τ δ → 0 < s ∧ s < U) ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift
            (coupledChemicalConcentration p u q.1)) q.2)
        (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

The minimal direct theorem to prove in Paper2 is:

```lean
theorem coupledChemDivFluxFactorJointC2InputsPos_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    ∃ U : ℝ, CoupledChemDivFluxFactorJointC2InputsPos p u U := by
  rcases H.resolver_package with ⟨U, hUpos, HRc2, hslabs⟩
  refine ⟨U, ?_⟩
  refine ⟨fun τ hτ0 hτU => ?_⟩
  rcases hslabs τ hτ0 hτU with
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
            deriv (intervalDomainLift
              (coupledChemicalConcentration p u q.1)) q.2)
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

  refine ⟨δ, hδ, htime_window, hsource, hu_c2,
    (fun x hx s hs => (hresolver_c2 x hx s hs).1),
    (fun x hx s hs => (hresolver_c2 x hx s hs).2),
    ?_, htime_bridge, htime_cont⟩
  intro x _hx s _hs
  exact coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg s x
```

Then define a positive-domain version of `CoupledChemDivFluxJointC2Hyp`.  It is
literally the existing `CoupledChemDivFluxJointC2Hyp` with

```lean
∀ τ : ℝ, ∃ δ : ℝ, ...
```

replaced by

```lean
∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ, ...
```

and, preferably, with the same `htime_window` slab-retention field.

```lean
structure CoupledChemDivFluxJointC2HypPos
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ, 0 < δ ∧
    (∀ s : ℝ, s ∈ Metric.ball τ δ → 0 < s ∧ s < U) ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun r : ℝ => deriv (coupledChemDivFluxLift p u r) x) =ᶠ[𝓝 s]
        (fun r : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (r, x) (0, 1))) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

The positive analogue of the existing assembler is a mechanical clone of
`coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs`:

```lean
theorem coupledChemDivFluxJointC2HypPos_of_factorJointC2InputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : CoupledChemDivFluxFactorJointC2InputsPos p u U) :
    CoupledChemDivFluxJointC2HypPos p u U := by
  refine ⟨fun τ hτ0 hτU => ?_⟩
  rcases H.exists_local_slab τ hτ0 hτU with
    ⟨δ, hδ, htime_window, hsource_cont, hu_c2, hv_c2, hgradv_c2,
      hbase, htime, htime_cont⟩
  have hflux_joint_c2_from_product_quotient_rpow :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (Function.uncurry (coupledChemDivFluxLift p u)) (s, x) :=
    fun x hx s hs =>
      coupledChemDivFlux_contDiffAt_of_factorJointC2
        (hu_c2 x hx s hs) (hv_c2 x hx s hs) (hgradv_c2 x hx s hs)
        (hbase x hx s hs)
  -- The rest is copied from `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs`:
  -- build the spatial-deriv/fderiv bridge by differentiability of the flux C² fact,
  -- reuse `htime`, and reuse `htime_cont`.
  sorry
```

Capstone theorem:

```lean
theorem coupledChemDivFluxJointC2HypPos_of_FACInputsPos
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputsPos p u) :
    ∃ U : ℝ, CoupledChemDivFluxJointC2HypPos p u U := by
  rcases coupledChemDivFluxFactorJointC2InputsPos_of_FACInputsPos
      (p := p) (u := u) H with ⟨U, HF⟩
  exact ⟨U, coupledChemDivFluxJointC2HypPos_of_factorJointC2InputsPos HF⟩
```

Important: if the final target remains the old all-time
`CoupledChemDivFluxFactorJointC2Inputs` or `CoupledChemDivFluxJointC2Hyp`, then a
positive-time-only proof cannot inhabit it without reintroducing the bad all-real
obligation.  Either refactor those structures or introduce parallel `...Pos` /
`...On (Ioo 0 U)` structures and use them downstream.

## Step list to assemble the flux package from the direct route

1. Obtain the positive FAC package:

   ```lean
   Hpos : CoupledChemDivFluxFactorFACInputsPos p u
   ```

2. Extract the resolver spectral package and local slab provider:

   ```lean
   rcases Hpos.resolver_package with ⟨U, hUpos, HRc2, hslabs⟩
   ```

3. For a target time `τ` in the positive horizon, get a local slab:

   ```lean
   rcases hslabs τ hτ0 hτU with
     ⟨δ, hδ, htime_window, hsource, hu_cont, hu_nonneg, hu_c2,
       htime_bridge, htime_cont⟩
   ```

4. For each `s ∈ Metric.ball τ δ`, use the slab window:

   ```lean
   rcases htime_window s hs with ⟨hs0, hsU⟩
   ```

5. Apply the coupled resolver transfer:

   ```lean
   have hpair := coupledChemicalConcentration_resolver_jointC2At_c2Data
     (p := p) (u := u) (U := U) (s := s) (x := x)
     HRc2 hs0 hsU hx
     (by
       intro a₀ M _hM ha₀ a src offset hτoffset _hagree
       exact resolverSpectralJointC2At_of_restartSmoothCutoff
         (a₀ := a₀) (M := M) (a := a)
         (offset := offset) (s := s) (x := x)
         hτoffset ha₀ src)
   ```

6. Split the pair into the two factor fields:

   ```lean
   hv_c2     := fun x hx s hs => (hresolver_c2 x hx s hs).1
   hgradv_c2 := fun x hx s hs => (hresolver_c2 x hx s hs).2
   ```

7. Discharge the denominator floor with the existing positivity theorem:

   ```lean
   coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg s x
   ```

8. Build `CoupledChemDivFluxFactorJointC2InputsPos`.

9. Apply the positive clone of
   `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs`.  Its key inner step is
   already available:

   ```lean
   coupledChemDivFlux_contDiffAt_of_factorJointC2
     (hu_c2 x hx s hs) (hv_c2 x hx s hs) (hgradv_c2 x hx s hs)
     (hbase x hx s hs)
   ```

10. If downstream needs outer-commute or source-time-C¹, clone the existing
    producers to positive-domain packages:

    ```lean
    coupledChemDivOuterCommuteAtoms_of_factorJointC2Inputs
    coupledChemDivSource_timeC1_of_factorJointC2Inputs
    ```

    but with the same `∀ τ, 0 < τ → τ < U → ...` shape.  Do not feed
    positive-time data into the old all-time structures.

## What changes are needed to `IntervalResolverPhysicalC2` assumptions?

None.

The committed file is:

```text
ShenWork/PDE/IntervalResolverPhysicalC2.lean
```

It is a fixed-time **spatial** C² result.  Its main theorems are:

```lean
ShenWork.IntervalResolverPhysicalC2.resolverR_eigenWeighted_le_source
ShenWork.IntervalResolverPhysicalC2.resolverR_eigenWeighted_summable_of_sourceL1
ShenWork.IntervalResolverPhysicalC2.resolverR_contDiff_two_of_source_l1
ShenWork.IntervalResolverPhysicalC2.resolverR_contDiffOn_Icc_of_source_l1
```

These assumptions should not be changed for the direct joint-C² route.  The
positive-time issue is not a fixed-time elliptic issue; it is a joint-time domain
issue.  `IntervalResolverPhysicalC2` can remain the spatial elliptic bootstrap
from source coefficient `ℓ¹` data.

Also, do not weaken `PhysicalResolverJointC2Data` to positive-time unless you want
to build a second abstraction parallel to the restart cutoff route.  For this
Q931 route, it is simpler to bypass `PhysicalResolverJointC2Data` entirely and
consume:

```lean
ResolverHasSpectralAgreementC2Coeff U (coupledChemicalConcentration p u)
```

plus positive local slab data.

## What changes are needed versus existing `coupledChemDivFluxJointC2Inputs` assumptions?

There are three relevant committed packages:

```lean
CoupledChemDivFluxFactorFACInputs
CoupledChemDivFluxFactorJointC2Inputs
CoupledChemDivFluxJointC2Hyp
```

The required change is the same for all of them: replace all-time local slabs by
positive-time / horizon-local slabs.

### Current problematic shape

```lean
∀ τ : ℝ, ∃ δ : ℝ, ...
```

For `CoupledChemDivFluxFactorFACInputs`, the current field is:

```lean
resolver_package :
  ∃ U : ℝ,
    ResolverHasSpectralAgreementC2Coeff U
      (coupledChemicalConcentration p u) ∧
    ∀ τ : ℝ, ∃ δ : ℝ, FACLocalSlabInputs p u U τ δ
```

But `FACLocalSlabInputs` itself requires:

```lean
∀ s : ℝ, s ∈ Metric.ball τ δ → 0 < s ∧ s < U
```

That cannot hold for arbitrary `τ : ℝ`; it can only hold for `τ ∈ (0,U)`.

### Correct positive-domain shape

```lean
resolver_package :
  ∃ U : ℝ,
    0 < U ∧
    ResolverHasSpectralAgreementC2Coeff U
      (coupledChemicalConcentration p u) ∧
    ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ,
      FACLocalSlabInputs p u U τ δ
```

For `CoupledChemDivFluxFactorJointC2Inputs` and `CoupledChemDivFluxJointC2Hyp`,
use the same replacement:

```lean
exists_local_slab :
  ∀ τ : ℝ, 0 < τ → τ < U → ∃ δ : ℝ, ...
```

### What remains as assumptions in the FAC input?

Keep only the non-resolver fields in `FACLocalSlabInputs`:

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

The direct route internally proves the three fields that should **not** be
FAC assumptions:

```lean
hv_c2
hgradv_c2
hbase
```

### Bottom line

* `IntervalResolverPhysicalC2`: no assumption changes.
* `PhysicalResolverJointC2Data`: bypass; do not use for this positive-time Paper2 route.
* `CoupledChemDivFluxFactorFACInputs`: change `∀ τ` to `∀ τ, 0 < τ → τ < U →`.
* `CoupledChemDivFluxFactorJointC2Inputs` / `CoupledChemDivFluxJointC2Hyp`: either
  refactor similarly or create `...Pos` / `...On` versions.  Without this change,
  the direct positive-time proof cannot typecheck against the old all-time target.
