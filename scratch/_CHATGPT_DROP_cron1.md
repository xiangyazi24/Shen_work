# Q688 / cron1: `CoupledChemDivFluxJointC2Hyp` producers and heat-semigroup difficulty

Repo/branch inspected: `xiangyazi24/Shen_work`, branch `chatgpt-scratch`.

## Verdict

There is **no completed exported theorem/def for a specific trajectory** such as the heat semigroup that constructs

```lean
CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
```

or the equivalent level-0 Picard heat trajectory.

There **is** one explicit heat-semigroup/level-0 construction site, but it is a **local `have ... := by sorry`** inside `level0_chemDiv_timeDerivData`:

```lean
have hfluxC2 : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp
    p (conjugatePicardIter p u₀ 0) := by
  sorry
```

File:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

That file states that `conjugatePicardIter p u₀ 0` is definitionally the level-0 heat-semigroup trajectory (`picardIter p u₀ 0`, i.e. `intervalFullSemigroupOperator t (intervalDomainLift u₀)`). So this is the relevant specific-trajectory example, but it is not discharged.

## 1. Theorem/def sites that produce `CoupledChemDivFluxJointC2Hyp`

### Completed generic producer

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

```lean
theorem coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivFluxJointC2Hyp p u := by
  ...
```

This is a real completed producer, but it is **generic in `u`**. It consumes `CoupledChemDivFluxFactorJointC2Inputs p u` and packages the five `exists_local_slab` fields of `CoupledChemDivFluxJointC2Hyp`.

Important detail: this theorem derives the spatial partial bridge internally from joint differentiability of the flux. It does not ask the caller to provide field (c) directly.

### Completed residual wrapper

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

```lean
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (ShenWork.IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
      R.hiter R.hval R.hgrad R.other)
```

This is also completed, but still **not a specific trajectory construction**. It works for arbitrary `u` once the large residual package `ChemDivSolutionRegularityResidual p u` is supplied.

The residual explicitly contains the remaining hard/non-free data: iterate time-`C²`/space-`C²`, source summability, the FAC slab `other`, chem-div source decay/H² envelopes, and `adot` continuity/bounds.

### Definition site, not a producer

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

This file defines the structure:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ...
```

It then **consumes** `CoupledChemDivFluxJointC2Hyp` to produce:

```lean
coupledChemDivOuterCommuteAtoms_of_fluxJointC2
coupledChemDivLocalChainRule_of_fluxJointC2
coupledChemDivSource_timeC1_of_fluxJointC2
```

Those are consumers/wiring theorems, not constructors of the hypothesis.

## 2. `sorry` sites that produce `CoupledChemDivFluxJointC2Hyp`

The only direct `sorry` I found that produces the structure for a specific trajectory is in:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Inside:

```lean
theorem level0_chemDiv_timeDerivData ... :
  ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ), ... := by
```

there is:

```lean
have hfluxC2 : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp
    p (conjugatePicardIter p u₀ 0) := by
  sorry
```

The surrounding comment says the intended route is:

```text
FluxJointC2Hyp → OuterCommuteAtoms → LocalChainRule
```

and says the `FluxJointC2Hyp` carries the five fields:

1. per-slab source continuity,
2. joint `C²` of the uncurried flux,
3. spatial `fderiv` bridge,
4. time `fderiv` bridge,
5. time-derivative continuity.

The comment also says that for the heat semigroup these should follow because `S(t)u₀` is jointly smooth for `t > 0`, the resolver inherits regularity by the spectral route, and the flux is a smooth composition. The `sorry` covers that heat-semigroup-specific wiring.

Related but not direct `CoupledChemDivFluxJointC2Hyp` sorries in the same file include the envelope/time-derivative infrastructure for the level-0 chem-div source. Those support the final level-0 source package, but the direct `CoupledChemDivFluxJointC2Hyp` construction is the `hfluxC2` sorry above.

## 3. Files importing `IntervalChemDivOuterCommuteProducer` and producing the structure

Direct import grep for:

```lean
import ShenWork.PDE.IntervalChemDivOuterCommuteProducer
```

found these relevant files:

### Produces `CoupledChemDivFluxJointC2Hyp`

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

It imports `IntervalChemDivOuterCommuteProducer` and exports the completed generic constructor:

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

### Imports it but does not directly produce `CoupledChemDivFluxJointC2Hyp`

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

This imports `IntervalChemDivOuterCommuteProducer`, but its main output is only:

```lean
CoupledChemDivFluxFactorJointC2Inputs p u
```

via:

```lean
coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

It discharges the time-partial bridge field physically from `PhysicalResolverJointC2Data`, but it does not itself call `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs`.

### Aggregator only

```text
ShenWork.lean
```

This is an import aggregator, not a producer.

## Nearby indirect producers of factor inputs

These do **not** directly return `CoupledChemDivFluxJointC2Hyp`, but they are the upstream path into the generic producer.

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate ... :
  CoupledChemDivFluxFactorJointC2Inputs p u := ...
```

This turns honest iterate time-`C²`/space-`C²` source data plus summability plus an `other` slab into the factor inputs.

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_floor ... :
  CoupledChemDivFluxFactorJointC2Inputs p u := ...
```

This discharges the resolver value/gradient joint-`C²` factor inputs from physical source-time-`C²` data.

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged ... :
  CoupledChemDivFluxFactorJointC2Inputs p u := ...
```

This discharges the time-partial bridge using the resolver inner commute.

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged ... :
  CoupledChemDivFluxFactorJointC2Inputs p u := ...
```

This discharges the closed-slab continuity of `coupledChemDivTimeDerivativeLift` from a spectral representative `Gmix`.

## 4. Which `exists_local_slab` fields are hardest?

For the five fields listed in the question:

### (a) Source continuity

```lean
∀ᶠ s in nhds τ,
  ContinuousOn (chemDivSourceLift ...) (Icc 0 1)
```

This is usually lower-order. It is often carried as `hsource`, `hsrc`, or part of `other`. It still requires continuity of the chem-div source slice, but it is not the main obstruction once the heat semigroup/resolver regularity is available.

### (b) Joint `C²` of the uncurried flux

```lean
ContDiffAt ℝ 2 (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

This is the **hardest field for the heat semigroup**.

Reason: the completed generic proof reduces it to joint `C²` of the factors:

```lean
u,
resolved value v = coupledChemicalConcentration p u,
resolved gradient ∂ₓv,
positivity of 1 + v.
```

The algebraic part is already done by:

```lean
coupledChemDivFlux_contDiffAt_of_factorJointC2
```

using product/quotient/`rpow` calculus. The hard part is not the final algebra; it is proving the resolver-side joint `C²` facts, especially joint `C²` of the gradient factor `∂ₓv`, for the heat semigroup trajectory by the spectral/elliptic route.

This matches comments in the repo: the factor-input file says the committed resolver API exposes joint continuity and fixed-time spatial `C²`, while the remaining analytic target is joint `C²` of `v` and `∂ₓv`. The level-0 heat-semigroup file also marks the heat-specific `FluxJointC2Hyp` wiring as the `sorry`.

### (c) Spatial fderiv bridge

```lean
spatial derivative = fderiv(0,1)
```

This is comparatively easy/formal. In the completed generic producer it is derived from joint differentiability of the flux using:

```lean
real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
```

So once (b) is available, (c) follows by a small Fréchet-derivative path argument.

### (d) Time fderiv bridge

```lean
time derivative = fderiv(1,0)
```

This is genuinely nontrivial, but the repo has a dedicated route for it.

The relevant theorem is:

```lean
coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
```

and the physically discharged version is:

```lean
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

This needs the chain rule for the explicit flux time derivative and the resolver inner commute

```text
∂ₜ∂ₓv = ∂ₓ∂ₜv
```

which is produced from physical resolver joint `C²`. Thus (d) is hard, but it is more of a bridge/commute wiring problem once the resolver joint `C²` data is in hand.

### (e) Closed-slab continuity of the time-derivative lift

```lean
ContinuousOn (Function.uncurry timeDerivative) on the slab
```

This is also a serious field because it is on the **closed** slab, including spatial endpoints. The repo isolates it in:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

via:

```lean
ChemDivMixedTimeDerivClosedRepr
chemDivMixedTimeDeriv_jointContinuousOn_closed
coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

So (e) is the main boundary/closed-slab continuity problem. It becomes manageable once one has a globally continuous spectral representative `Gmix` agreeing with the mixed time-derivative lift on the closed spatial domain.

## Bottom line on heat semigroup

For the heat semigroup, the hardest sub-condition is **(b) joint `C²` of the uncurried flux**, because it contains the real resolver regularity burden: prove joint `C²` of the resolved value and especially the resolved spatial gradient along the heat trajectory, then pass through the flux product/quotient/`rpow` expression.

The next-hardest fields are:

1. **(e)** closed-slab continuity of the mixed time-derivative lift, because endpoint continuity needs a spectral representative on the closed slab;
2. **(d)** time fderiv bridge, because it needs the time chain rule plus resolver inner commute.

Field **(c)** is formal once (b) is available, and field **(a)** is lower-order compared with the resolver joint-regularity and closed-slab mixed-derivative tasks.
