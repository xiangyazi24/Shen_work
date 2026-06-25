# Q569 / cron1: `CoupledChemDivFluxJointC2Hyp` for the heat semigroup

## Executive verdict

I found **no direct landed producer** for

```lean
CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
```

on `chatgpt-scratch`.

The generic producer chain is already in place:

```lean
CoupledChemDivFluxFactorJointC2Inputs p u
  ── coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs ──▶
CoupledChemDivFluxJointC2Hyp p u
  ── coupledChemDivOuterCommuteAtoms_of_fluxJointC2 ──▶
CoupledChemDivOuterCommuteAtoms p u
  ── coupledChemDivLocalChainRule_of_outerCommuteAtoms ──▶
CoupledChemDivLocalChainRule p u
```

For the heat semigroup level `u := conjugatePicardIter p u₀ 0`, the missing work is to prove the **factor-level analytic inputs**: joint `C²` of the heat trajectory, joint `C²` of the elliptic resolver value and gradient, positivity of `1+v`, the flux time-partial bridge, source continuity, and closed-slab continuity of `coupledChemDivTimeDerivativeLift`.

Important caveat: `CoupledChemDivFluxJointC2Hyp` is **global in time** (`∀ τ : ℝ`).  Heat-semigroup smoothing is naturally positive-window (`c > 0`).  If the consumer only needs `[c,T]`, a windowed version of this structure would be a better fit than trying to prove the global structure for all `τ`.

## Heat level 0 identity

`conjugatePicardIter` level 0 is definitionally the full Neumann heat semigroup:

```lean
-- ShenWork/Paper2/IntervalConjugatePicard.lean:26-32
/-- B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᴮ(u_n)`. -/
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

Searches for exact heat-specific producers such as:

```text
CoupledChemDivFluxJointC2Hyp p conjugatePicardIter
conjugatePicardIter p u₀ 0 fluxJointC2Hyp
CoupledChemDivFluxJointC2Hyp heat
```

returned no direct hit.

## `CoupledChemDivFluxJointC2Hyp`: fields

Defined in `ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean:128-148`:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
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

Its fields are therefore:

1. eventual `ContinuousOn` of the chem-div source slice;
2. joint `ContDiffAt ℝ 2` of the uncurried flux `(t,x) ↦ coupledChemDivFluxLift p u t x`;
3. spatial derivative / Fréchet spatial partial bridge;
4. time derivative / Fréchet time partial bridge for `coupledChemDivFluxTimeDerivativeLift`;
5. closed-slab joint continuity of `coupledChemDivTimeDerivativeLift`.

## Direct producers of `CoupledChemDivFluxJointC2Hyp`

### From factor-level inputs

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean:119-177`:

```lean
theorem coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

This is the main reusable producer.  It builds the flux joint `C²` field by product/quotient/rpow calculus and generates the spatial partial bridge internally.

The input structure is `CoupledChemDivFluxFactorJointC2Inputs`, defined in `IntervalChemDivFluxJointC2Producer.lean:81-109`.  Its fields are:

```lean
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
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
          deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
        (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

### From residual bundle

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:55-60`:

```lean
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (ShenWork.IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
      R.hiter R.hval R.hgrad R.other)
```

This is the highest-level wrapper already present.  To use it for the heat level, instantiate

```lean
u := conjugatePicardIter p u₀ 0
```

and build a `ChemDivSolutionRegularityResidual p u`.  The residual fields are listed in `IntervalChemDivWinDischarge.lean:12-51`: `du`, `d2u`, `hiter`, `hval`, `hgrad`, `other`, `Cchem`, `hH2`, `hdecay`, `hzero`, `hadotcont`, `MchemDot`, `hMdot`.

## Producers of factor-level inputs

### FAC / spectral route

`ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:51-57` defines:

```lean
structure CoupledChemDivFluxFactorFACInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, ∃ δ : ℝ, FACLocalSlabInputs p u U τ δ
```

`coupledChemDivFluxFactorJointC2Inputs_of_FACInputs` is in the same file at `IntervalChemDivFluxFactorFAC.lean:83-131` and produces `CoupledChemDivFluxFactorJointC2Inputs p u`.

Caveat: `FACLocalSlabInputs` at `IntervalChemDivFluxFactorFAC.lean:23-42` includes

```lean
∀ s : ℝ, s ∈ Metric.ball τ δ → 0 < s ∧ s < U
```

with `δ > 0`.  Since `τ ∈ Metric.ball τ δ`, this cannot hold for all `τ : ℝ`.  So this FAC wrapper is not the right final route for a genuine global heat-semigroup theorem unless the structure is windowed or otherwise restricted.

### Physical source route

`ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean:8-40` gives:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ... ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This route constructs resolver value/gradient joint `C²` from physical source time-`C²` data, without the `DuhamelSourceTimeC2Coeff` or eigen-cube route.  The source-side structure `PhysicalSourceTimeC2` is defined in `IntervalPhysicalResolverDataConcrete.lean:109-124`.

### Iterate source route

`ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean:5-45` gives:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) → Summable ...)
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) → Summable ...)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ... ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

`IterateSourceTimeData` is defined at `IntervalFlooredSourceTimeDataIterate.lean:111-147`; it packages the floor, time-`C¹`, time-`C²`, slice `C²`, Neumann, and coefficient-envelope facts for the source slices.

### Physical route with bridge/continuity discharged

There are two more refined producers:

1. `ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:101-122`

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ... htime_cont ... ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

It discharges the flux time-partial bridge using the resolver physical joint `C²`.  The inner commute theorem is `coupledChemical_innerCommute_of_physicalJointC2` at `IntervalChemDivFACCommuteDischarge.lean:23-28`, and the flux time bridge is `coupledChemDivFlux_timeBridge_of_physicalJointC2` at lines `70-81`.

2. `ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:87-103`

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ... ∧ ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This also discharges `htime_cont` from `ChemDivMixedTimeDerivClosedRepr`; that representation is defined in `IntervalChemDivTimeDerivClosed.lean:45-49`, and the transfer theorem is `chemDivMixedTimeDeriv_jointContinuousOn_closed` at lines `56-61`.

## `CoupledChemDivPointwiseChainAtoms`: fields and producers

Defined in `ShenWork/PDE/IntervalChemDivLocalChainRule.lean:19-30`:

```lean
structure CoupledChemDivPointwiseChainAtoms
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

The direct producer is `coupledChemDivLocalChainRule_of_pointwiseChainAtoms`, `IntervalChemDivLocalChainRule.lean:35-39`:

```lean
theorem coupledChemDivLocalChainRule_of_pointwiseChainAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivPointwiseChainAtoms p u) :
    CoupledChemDivLocalChainRule p u where
  exists_local_slab := A.exists_local_slab
```

The stronger route is through `CoupledChemDivOuterCommuteAtoms`, defined in `IntervalChemDivOuterCommute.lean:35-46`, and then:

```lean
-- IntervalChemDivOuterCommute.lean:50-69
theorem coupledChemDivLocalChainRule_of_outerCommuteAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivOuterCommuteAtoms p u) :
    CoupledChemDivLocalChainRule p u
```

It uses:

```lean
-- IntervalChemDivOuterCommute.lean:16-31
coupledChemDivSourceLift_eq_deriv_fluxLift_interior
coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
```

to turn the outer-commute derivative into the pointwise source chain rule.

## What this means for `u = conjugatePicardIter p u₀ 0`

On `chatgpt-scratch`, the clean current target is:

```lean
let u := conjugatePicardIter p u₀ 0
have Hfactor : CoupledChemDivFluxFactorJointC2Inputs p u := by
  -- heat-specific analytic work
  ...
exact coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs Hfactor
```

or, using the residual wrapper:

```lean
let u := conjugatePicardIter p u₀ 0
have R : ShenWork.IntervalChemDivWinDischarge.ChemDivSolutionRegularityResidual p u := by
  -- heat-specific analytic work
  ...
exact ShenWork.IntervalChemDivWinDischarge.fluxJointC2Hyp_of_residual R
```

The heat-specific analytic work should be organized around the physical/iterate route, not the global FAC spectral route:

```lean
u := conjugatePicardIter p u₀ 0
```

Required ingredients:

1. `hu_c2`: joint `ContDiffAt ℝ 2` of `(t,x) ↦ intervalDomainLift (u t) x`.  For the heat level this comes from the positive-time heat series.  On the default branch there is `IntervalHeatSemigroupHighRegularity.lean`, proving `heatSemigroup_contDiff_four`; this file was **not present on `chatgpt-scratch`** when fetched by ref.
2. Resolver joint `C²` data, preferably via `PhysicalSourceTimeC2` / `PhysicalResolverJointC2Data` rather than `ResolverHasSpectralAgreementC2Coeff`.
3. `hu_cont`, `hu_nonneg`, and denominator positivity `1+v>0`.
4. Source continuity on local slabs.
5. `ChemDivMixedTimeDerivClosedRepr p u τ δ` if using the strongest htime-discharged route.
6. If using `fluxJointC2Hyp_of_residual`, also the source envelope / `adot` residual fields from `ChemDivSolutionRegularityResidual`.

## Default-branch heat-level roadmap files

Code search found default-branch roadmap/prototype files for level 0:

* `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`
* `ShenWork/Paper2/IntervalChemDivSpatialC2.lean`
* `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`

but `fetch_file(..., ref := "chatgpt-scratch")` returned `Not Found` for these files during this run.  So they are useful as design references, not currently available on the target scratch branch.

The default-branch `IntervalConjugateLevel0BFormSourceOn.lean` confirms the intended heat-level route but still uses `sorry`s: it has a `Level0ChemDivSourceData` positive-window package, notes that the heat semigroup has exponential decay and the chemDiv source should inherit C²/Neumann regularity, then leaves the chain-rule/joint-continuity/Mdot legs as residuals.  See its comments around `level0_chemDiv_timeDerivData`: the local `CoupledChemDivLocalChainRule` and joint continuity of `coupledChemDivTimeDerivativeLift` are both `sorry` there.

It also contains a comment saying the resolver cosine series needs C⁴ for the per-slice H² route and that only C² was available in the codebase at the time.  In this conversation, Q547 added `IntervalResolverHighRegularity.lean` on `chatgpt-scratch`, which addresses the coefficient-level resolver C⁴ bridge, but the heat-level source/time-slab wiring is still not packaged as `CoupledChemDivFluxJointC2Hyp`.

## Bottom line

There is **no one-line existing theorem** for the heat-level target.  The nearest already-landed endpoint is:

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

So for the heat semigroup, prove a heat-specific

```lean
CoupledChemDivFluxFactorJointC2Inputs p (conjugatePicardIter p u₀ 0)
```

or instantiate `ChemDivSolutionRegularityResidual` and use `fluxJointC2Hyp_of_residual`.

If the desired theorem is only on a positive window `[c,T]`, do not fight the global `∀ τ : ℝ` in `CoupledChemDivFluxJointC2Hyp`; make a windowed analogue, or prove a global extension/clamping lemma first.
