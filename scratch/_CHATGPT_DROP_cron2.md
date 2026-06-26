# Q684 (cron2): constructing `CoupledChemDivFluxJointC2Hyp` for the heat-semigroup level-0 trajectory

Static repo inspection only; I did not run a Lean build.

## Executive verdict

I did **not** find a completed trajectory-specific construction of

```lean
CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
```

for the heat-semigroup trajectory.  The only direct occurrence for level 0 is still a placeholder in

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

inside `level0_chemDiv_timeDerivData`:

```lean
have hfluxC2 : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp
    p (conjugatePicardIter p u₀ 0) := by
  sorry
have hchain : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivLocalChainRule
    p (conjugatePicardIter p u₀ 0) :=
  ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivLocalChainRule_of_fluxJointC2 hfluxC2
```

The surrounding comment says exactly what this sorry is meant to do: build the 5-field `FluxJointC2Hyp` for the heat semigroup, then feed the committed chain

```lean
FluxJointC2Hyp → OuterCommuteAtoms → LocalChainRule
```

So the answer is: **no existing finished heat-specific construction found**, but the repo has a fairly complete generic discharge pipeline.  The heat-specific work is to feed that pipeline with the right factor-level joint-C² and time-bridge data.

## The core structure and its five fields

`CoupledChemDivFluxJointC2Hyp` is defined in

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

with one field:

```lean
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

The same file proves the key consumer:

```lean
theorem coupledChemDivOuterCommuteAtoms_of_fluxJointC2
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivOuterCommuteAtoms p u
```

and then:

```lean
theorem coupledChemDivLocalChainRule_of_fluxJointC2
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivLocalChainRule p u
```

So once you build `CoupledChemDivFluxJointC2Hyp`, the outer-commute/local-chain-rule part is already wired.

## Main generic producer: reduce to factor-level joint C² inputs

The repo’s main producer is in

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

It defines a more factorized structure:

```lean
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    source_cont ∧
    hu_c2 ∧
    hv_c2 ∧
    hgradv_c2 ∧
    hbase ∧
    htime_bridge ∧
    htime_cont
```

and proves:

```lean
theorem coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

This theorem is the closest reusable construction of `CoupledChemDivFluxJointC2Hyp`.  It discharges the five target fields as follows.

### Field 1: source continuity near `τ`

Passed through unchanged from the factor-level input:

```lean
hsource_cont : ∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
```

Typical discharge: by composition/quotient/rpow continuity of the explicit chem-div source slice once `u`, resolver value `v`, resolver gradient, denominator positivity, and the needed spatial derivatives are continuous on `[0,1]`.  In the existing generic machinery, this is usually carried in a local slab package rather than automatically produced.

For the heat semigroup, this should come from fixed-time smoothness on any positive time slab and resolver regularity.  I did not find a finished heat-specific theorem packaging it.

### Field 2: joint C² of uncurried flux

Produced inside `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs` by:

```lean
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    (hu : ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2 (fun q => intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x))
    (hgradv : ContDiffAt ℝ 2 (fun q => deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2) (s, x))
    (hbase : 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2 (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

This is a formal product/quotient/rpow step:

- `hu` for the lifted `u` factor;
- `hv` for resolver value `v`;
- `hgradv` for `∂ₓ v`;
- `hbase` for nonzero denominator `1 + v`.

For heat level 0, this is the recommended way to discharge field 2: prove `hu_c2`, `hv_c2`, `hgradv_c2`, and positivity, then call this theorem rather than expanding the flux by hand.

### Field 3: spatial fderiv bridge

Automatically produced by `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs` from the just-produced flux `ContDiffAt`.

It uses:

```lean
theorem real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun y : ℝ => F (s, y)) x =
      fderiv ℝ F (s, x) (0, 1)
```

The implementation obtains a neighborhood in the time variable from `Metric.isOpen_ball.mem_nhds`, rebuilds flux joint C² for each nearby `r`, extracts differentiability, and rewrites the spatial derivative as the `(0,1)` Fréchet directional derivative.

So for heat level 0, you should not prove field 3 directly; prove field 2/factor inputs and let this theorem do it.

### Field 4: time fderiv bridge

In the basic factor producer, this is passed through as an input:

```lean
htime : ∀ x ∈ Ioo 0 1, ∀ s ∈ Metric.ball τ δ,
  (fun y => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
    (fun y => fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1,0))
```

But there is a later physical discharge route in

```text
ShenWork/PDE/IntervalChemDivFluxTimeBridge.lean
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

The central theorem is:

```lean
theorem coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
```

It proves the time bridge from:

- eventual joint C² of `u`;
- eventual joint C² of `v`;
- eventual joint C² of `∂ₓ v`;
- eventual positivity of `1+v`;
- an inner commute datum for the resolver gradient:

```lean
HasDerivAt
  (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
  (deriv (coupledChemicalTimeDerivativeLift p u s) y) s
```

Then `IntervalChemDivFACCommuteDischarge.lean` discharges this inner commute from physical resolver joint C²:

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2

theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
```

So field 4 can be either carried directly or produced from the physical resolver joint-C² package.

### Field 5: time-derivative `ContinuousOn` on the local slab

In the basic factor producer, this is also passed through as an input:

```lean
ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc 0 1)
```

There is a later discharge in

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

It introduces:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc 0 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

and proves:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc 0 1)
```

This is the standard “closed-slab spectral representative” route: construct a globally continuous `Gmix`, prove agreement on the closed slab, then transfer continuity.

For heat level 0, a direct smooth-composition proof of field 5 may also be possible, but the repo’s clean pattern is to supply a `Gmix` representative.

## Existing higher-level constructions

### A. `fluxJointC2Hyp_of_residual` for generic solution/iterate residuals

In

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

the structure

```lean
ChemDivSolutionRegularityResidual p u
```

bundles the true residual data:

- `hiter : IterateSourceTimeData p u du d2u`;
- resolver/source summability inputs `hval`, `hgrad`;
- an `other` slab package containing source continuity, `hu_c2`, positivity, time bridge, time-derivative continuity;
- weak-H²/decay/zero-mode data;
- `hadotcont` and `hMdot`.

It then proves:

```lean
theorem fluxJointC2Hyp_of_residual
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (coupledChemDivFluxFactorJointC2Inputs_of_iterate R.hiter R.hval R.hgrad R.other)
```

This is not heat-specific, but it is the most complete committed route from a residual bundle to `CoupledChemDivFluxJointC2Hyp`.

### B. `coupledChemDivFluxFactorJointC2Inputs_of_iterate`

In

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

the theorem

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
```

builds the factor-level inputs from:

```lean
IterateSourceTimeData p u du d2u
```

plus resolver source summability `hval`, `hgrad`, and the slab `other` field.

`IterateSourceTimeData` supplies the floor, time-`C¹` and time-`C²` source slices, per-time-order space-`C²` data, Neumann data, and coefficient envelopes.  This is the generic iterate route.  For heat semigroup level 0, the natural instantiation would be:

```lean
du  := ∂ₜ lift(S(t)u₀) = ∂ₓₓ lift(S(t)u₀)
d2u := ∂ₜ² lift(S(t)u₀) = ∂ₓₓₓₓ lift(S(t)u₀)
```

but I did not find a committed `IterateSourceTimeData` instance for `conjugatePicardIter p u₀ 0`.

### C. Physical resolver route

`IntervalPhysicalResolverDataConcrete.lean` defines:

```lean
PhysicalSourceTimeC2
PhysicalResolverJointC2Data
physicalResolverJointC2Data_of_floor
coupledChemDivFluxFactorJointC2Inputs_of_floor
```

This route says: if the source coefficients of `ν·u^γ` are `C²` in time with three time-order envelopes, then the resolver coefficients inherit the same time regularity via the constant elliptic weight `1/(μ+λ_k)`.  This produces resolver value and gradient joint C² (`hv_c2`, `hgradv_c2`) without an eigen-cube ladder.

`IntervalResolverJointC2PhysicalConcrete.lean` then supplies:

```lean
theorem coupledChemical_jointContDiffAt_two

theorem coupledChemical_grad_jointContDiffAt_two

theorem coupledChemDivFluxFactorJointC2Inputs_of_physical
```

These discharge the resolver-side fields and leave the non-resolver fields in an `other` slab hypothesis.

### D. FAC route with time bridge / htime_cont partially discharged

`IntervalChemDivFACCommuteDischarge.lean` discharges the flux time-partial bridge from physical resolver joint C²:

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2

theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

`IntervalChemDivTimeDerivClosed.lean` discharges `htime_cont` from a closed-slab representative:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed

theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

So the mature pipeline is progressively reducing the open fields.

## What this means for the heat-semigroup level-0 proof

There is no one-line existing construction.  The cleanest repo-native proof strategy is to instantiate the factor-level / physical route, not to fill the five fields by hand.

For `u = conjugatePicardIter p u₀ 0`, note the definition is:

```lean
conjugatePicardIter p u₀ 0 t x =
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

For positive time, this is the full Neumann heat semigroup.  A heat-specific construction should be organized as follows.

### Recommended heat-level construction plan

For each positive center `τ > 0`, choose a local slab with `δ < τ/2`, so all `s ∈ ball τ δ` are positive.

Then build the factor-level fields:

1. **Source continuity near `τ`.**
   Use fixed-time spatial smoothness of `S(s)u₀`, resolver regularity, positivity of `1+v`, and composition/quotient continuity to show `ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)` eventually near `τ`.

2. **`hu_c2`.**
   Use the heat cosine-series formula and a bounded-weight/joint-series theorem, or a heat-specific joint smoothness theorem.  The repo has fixed-time C⁴ spatial heat regularity (`heatSemigroup_contDiff_four`), but I did not find a named theorem giving `ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s,x)` jointly in `(s,x)` for `conjugatePicardIter 0`.  This appears to be one missing heat-level wrapper.

3. **`hv_c2` and `hgradv_c2`.**
   Prefer the physical resolver route: build `PhysicalSourceTimeC2` for `ν·(S(t)u₀)^γ`; then use `physicalResolverJointC2Data_of_floor`, `coupledChemical_jointContDiffAt_two`, and `coupledChemical_grad_jointContDiffAt_two`.

4. **Positivity `hbase`.**
   Use resolver positivity/nonnegativity already proved for the coupled chemical concentration.  The FAC route uses:

   ```lean
   coupledChemical_floor_pos_of_nonneg_continuous
   ```

   which gives `0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x` from continuity/nonnegativity of `u s`.

5. **Time fderiv bridge.**
   Do not prove directly if you have physical resolver joint C².  Use:

   ```lean
   coupledChemDivFlux_timeBridge_of_physicalJointC2
   ```

6. **Time-derivative continuity.**
   Either prove it directly from heat/resolver joint smoothness, or follow the repo pattern: construct a `ChemDivMixedTimeDerivClosedRepr` and use:

   ```lean
   chemDivMixedTimeDeriv_jointContinuousOn_closed
   ```

Finally call:

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

or one of its physical/FAC variants.

## Important caveat: global `∀ τ : ℝ` vs positive heat time

The current structure is global:

```lean
exists_local_slab : ∀ τ : ℝ, ...
```

But the mathematical claim “the heat semigroup is jointly smooth” is naturally for `t > 0`.  The level-0 use in `level0_chemDiv_timeDerivData` is on a positive window `[c,T]` with `0 < c`, but the `hfluxC2` package it asks for is still global.

This is worth watching.  A strictly clean API would be an `On`/windowed version of `CoupledChemDivFluxJointC2Hyp`, or a local-chain-rule-on-window theorem, so the heat proof only has to cover `τ ∈ [c,T]` or `τ > 0`.  Otherwise the heat-specific proof must also handle `τ ≤ 0` according to how `intervalFullSemigroupOperator` behaves there, which is not the core analytic target.

## Search-result summary

Searches performed around:

```text
CoupledChemDivFluxJointC2Hyp
exists_local_slab CoupledChemDivFluxJointC2Hyp
CoupledChemDivLocalChainRule p conjugatePicardIter
CoupledChemDivFluxJointC2Hyp p conjugatePicardIter
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
coupledChemDivFluxFactorJointC2Inputs_of_iterate
coupledChemDivFluxFactorJointC2Inputs_of_physical
```

Findings:

- No completed direct theorem for `CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)`.
- The direct level-0 attempt exists only as the `hfluxC2 := by sorry` placeholder in `IntervalConjugateLevel0BFormSourceOn.lean`.
- The repo’s committed construction pattern is:

  ```lean
  CoupledChemDivFluxFactorJointC2Inputs
    → CoupledChemDivFluxJointC2Hyp
    → CoupledChemDivOuterCommuteAtoms
    → CoupledChemDivLocalChainRule
  ```

- For Picard/mild/solution-level uses, the repo mostly carries a residual bundle (`ChemDivSolutionRegularityResidual`) and uses `fluxJointC2Hyp_of_residual` rather than constructing the heat-semigroup case directly.

## Bottom line

For the heat-semigroup level-0 trajectory, the simplest aligned fix is to add a heat-specific producer of the **factor-level inputs** (or a positive-window variant of them), then reuse the existing bridge.  The fields should be discharged in the same way the generic pipeline does:

- source continuity: local smooth composition;
- flux joint C²: `coupledChemDivFlux_contDiffAt_of_factorJointC2`;
- spatial bridge: automatic via `real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt` inside the factor producer;
- time bridge: `coupledChemDivFlux_timeBridge_of_physicalJointC2` once resolver physical joint C² is available;
- time-derivative continuity: `ChemDivMixedTimeDerivClosedRepr` → `chemDivMixedTimeDeriv_jointContinuousOn_closed`, or a direct heat-specific smoothness proof.
