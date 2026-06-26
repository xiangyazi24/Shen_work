# Q689 (cron2): shortest path to `CoupledChemDivFluxFactorJointC2Inputs` / `FluxJointC2Hyp` for heat level 0

Static repo inspection only; I did not run a Lean build.

Target trajectory:

```lean
u := conjugatePicardIter p u₀ 0
```

Goal:

```lean
CoupledChemDivFluxFactorJointC2Inputs p u
-- then
CoupledChemDivFluxJointC2Hyp p u
```

## Executive verdict

I did **not** find a completed heat-semigroup-specific theorem constructing

```lean
CoupledChemDivFluxFactorJointC2Inputs p (conjugatePicardIter p u₀ 0)
```

or

```lean
CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
```

The direct level-0 use is still the same placeholder in `IntervalConjugateLevel0BFormSourceOn.lean`:

```lean
have hfluxC2 :
    ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxJointC2Hyp
      p (conjugatePicardIter p u₀ 0) := by
  sorry
```

The **shortest repo-native route** is not to build `CoupledChemDivFluxJointC2Hyp` directly.  Build a factor-level input package, then call the one-argument producer:

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs H
```

The most reduced route for heat level 0 looks like:

```lean
-- build these heat-specific inputs:
Hphys  : PhysicalResolverJointC2Data p u Bt
hu_cont : ∀ s, Continuous (u s)
hu_nonneg : ∀ s, ∀ x : intervalDomainPoint, 0 ≤ u s x
other  : ∀ τ, ∃ δ, 0 < δ ∧
  (∀ᶠ s in 𝓝 τ, ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)) ∧
  (∀ x ∈ Ioo 0 1, ∀ s, ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s,x)) ∧
  ChemDivMixedTimeDerivClosedRepr p u τ δ

-- then:
have Hfac : CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    Hphys hu_cont hu_nonneg other

have Hflux : CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs Hfac
```

This route discharges the flux time-bridge and the closed-slab time-derivative continuity internally, leaving the heat-specific work concentrated in:

1. heat `u` continuity/nonnegativity;
2. heat `u` joint `C²`;
3. resolver physical joint `C²` data from source coefficient time-`C²` envelopes;
4. source-slice continuity;
5. a closed-slab representative for `coupledChemDivTimeDerivativeLift`.

If constructing `ChemDivMixedTimeDerivClosedRepr` is not yet available, the next-shortest route is `coupledChemDivFluxFactorJointC2Inputs_of_physical` / `_of_floor`, but then the `other` package must carry the time-bridge and `htime_cont` fields explicitly.

## 1. Exact signature of `CoupledChemDivFluxFactorJointC2Inputs`

Defined in:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

Exact structure:

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
          deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
            q.2)
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

So the fields are:

1. `hsource_cont`: eventual slice `ContinuousOn` for `coupledChemDivSourceLift`.
2. `hu_c2`: joint `ContDiffAt ℝ 2` of lifted `u`.
3. `hv_c2`: joint `ContDiffAt ℝ 2` of lifted resolver value `v`.
4. `hgradv_c2`: joint `ContDiffAt ℝ 2` of `∂ₓv`.
5. `hbase`: `0 < 1 + v`.
6. `htime`: time fderiv bridge for the flux.
7. `htime_cont`: closed-slab `ContinuousOn` of `coupledChemDivTimeDerivativeLift`.

## 2. How `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs` is called

Exact signature:

```lean
theorem coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

It takes **one argument**, the factor package `H`.

Internally it does:

```lean
rcases H.exists_local_slab τ with
  ⟨δ, hδ, hsource_cont, hu_c2, hv_c2, hgradv_c2, hbase,
    htime, htime_cont⟩
```

Then it produces the five `CoupledChemDivFluxJointC2Hyp` fields as follows:

### Field A: source continuity

Passed through directly:

```lean
hsource_cont_slab := hsource_cont
```

### Field B: joint C² of uncurried flux

Constructed by product/quotient/rpow calculus:

```lean
coupledChemDivFlux_contDiffAt_of_factorJointC2
  (hu_c2 x hx s hs) (hv_c2 x hx s hs) (hgradv_c2 x hx s hs)
  (hbase x hx s hs)
```

### Field C: spatial fderiv bridge

Constructed automatically from flux differentiability, using the theorem:

```lean
real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
```

It rebuilds flux joint C² at nearby `r ∈ Metric.ball τ δ`, extracts `DifferentiableAt`, and rewrites spatial `deriv` as the `(0,1)` Fréchet derivative.

### Field D: time fderiv bridge

Passed through directly:

```lean
htime_deriv_fderiv_bridge := htime
```

### Field E: time-derivative continuity

Passed through directly:

```lean
htime_derivative_continuous := htime_cont
```

Then it returns:

```lean
⟨δ, hδ, hsource_cont_slab,
  hflux_joint_c2_from_product_quotient_rpow,
  hspatial_deriv_fderiv_bridge,
  htime_deriv_fderiv_bridge,
  htime_derivative_continuous⟩
```

## 3. Existing physical / iterate routes

### 3.1 Physical resolver route: `_of_physical`

The resolver-side physical route lives in:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

It defines:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

Then it proves the resolver fields:

```lean
theorem coupledChemical_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo 0 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

and

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo 0 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

Finally:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical
    (H : PhysicalResolverJointC2Data p u Bt)
    (other : ∀ τ, ∃ δ, 0 < δ ∧
      hsource_cont ∧ hu_c2 ∧ hbase ∧ htime ∧ htime_cont) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This route fills `hv_c2` and `hgradv_c2` from `H`; the other five non-resolver fields remain in `other`.

### 3.2 Source-to-physical resolver route: `_of_floor`

In:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

there is:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      hsource_cont ∧ hu_c2 ∧ hbase ∧ htime ∧ htime_cont) :
    CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_physical
    (physicalResolverJointC2Data_of_floor H) other
```

`PhysicalSourceTimeC2` is the source-side data for `ν·u^γ`: source coefficient `C²` in time plus three time-order envelopes.  This is likely the most natural resolver route for heat semigroup: prove time-`C²` source coefficient bounds for `ν·(S(t)u₀)^γ`, then get resolver joint C² via the constant elliptic multiplier.

### 3.3 Iterate route: `_of_iterate`

In:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

there is:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k *
          builtEs (flooredSourceTimeData_of_iterate H) i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k *
          builtEs (flooredSourceTimeData_of_iterate H) i k) m))
    (other : ∀ τ, ∃ δ, 0 < δ ∧
      hsource_cont ∧ hu_c2 ∧ hbase ∧ htime ∧ htime_cont) :
    CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_floor
    (physicalSourceTimeC2_of_floored (flooredSourceTimeData_of_iterate H) hval hgrad)
    other
```

This route is heavier but useful if you already have `IterateSourceTimeData`.  For heat level 0 you would instantiate:

```lean
du  = ∂ₜ S(t)u₀ = ∂ₓₓ S(t)u₀
d2u = ∂ₜ² S(t)u₀ = ∂ₓₓₓₓ S(t)u₀
```

Then provide `hval`, `hgrad`, and `other`.

### 3.4 Time-bridge discharged route

In:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

there is:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ, ∃ δ, 0 < δ ∧
      hsource_cont ∧
      (∀ x ∈ Ioo 0 1, ∀ s, hu_c2_at s x) ∧
      htime_cont) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This internally creates:

```lean
hbase : ∀ s x, 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

via resolver nonnegativity:

```lean
coupledChemical_floor_pos_of_nonneg_continuous
```

and internally creates the time fderiv bridge using:

```lean
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

This is shorter than `_of_physical` if you can prove `hu_cont`, `hu_nonneg`, and global `hu_c2`.

### 3.5 Time-bridge + `htime_cont` discharged route

In:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

there is the shortest mature route:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)) ∧
      (∀ x ∈ Ioo 0 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This internally calls `_physical_commuteDischarged`, and internally turns

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

into `htime_cont` via:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

For heat level 0, this is probably the best target if you can build `H : PhysicalResolverJointC2Data` directly.

## 4. `ChemDivSolutionRegularityResidual` and `fluxJointC2Hyp_of_residual`

Defined in:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

The residual contains:

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  du : ℝ → ℝ → ℝ
  d2u : ℝ → ℝ → ℝ
  hiter : IterateSourceTimeData p u du d2u
  hval : ∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointMajorant ...)
  hgrad : ∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointGradMajorant ...)
  other : ∀ τ, ∃ δ, 0 < δ ∧
    hsource_cont ∧ hu_c2 ∧ hbase ∧ htime ∧ htime_cont
  Cchem : ℝ
  hCchem : 0 ≤ Cchem
  hH2 : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
  hdecay : ∀ s, 0 ≤ s → ∀ k, 1 ≤ k →
    |cosineCoeffs (coupledChemDivSourceLift p u s) k| ≤ Cchem / ((k:ℝ) * Real.pi)^2
  hzero : ∀ s, 0 ≤ s → |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot
```

And yes, it has:

```lean
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (coupledChemDivFluxFactorJointC2Inputs_of_iterate
      R.hiter R.hval R.hgrad R.other)
```

This is a complete route to `FluxJointC2Hyp`, but it is **overkill** if your only goal is `FluxJointC2Hyp`: the residual also carries weak-H²/decay/zero/adot continuity/uniform coefficient bounds needed later for `DuhamelSourceTimeC1`.

## Shortest path from heat semigroup regularity to `FluxJointC2Hyp`

For heat level 0, I would avoid the full `ChemDivSolutionRegularityResidual` unless later consumers also need the chem-div source time-C¹ package.  The shortest focused path is:

### Preferred target

Construct:

```lean
Hphys : PhysicalResolverJointC2Data p u Bt
hu_cont : ∀ s, Continuous (u s)
hu_nonneg : ∀ s, ∀ x, 0 ≤ u s x
other : ∀ τ, ∃ δ, 0 < δ ∧
  (∀ᶠ s in 𝓝 τ, ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)) ∧
  (∀ x ∈ Ioo 0 1, ∀ s, ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s,x)) ∧
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Then:

```lean
have Hfac : CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    Hphys hu_cont hu_nonneg other

have Hflux : CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs Hfac
```

### What remains heat-specific

For `u = conjugatePicardIter p u₀ 0`, the remaining heat-specific facts are:

1. `hu_cont`: each heat slice is continuous.
2. `hu_nonneg`: heat semigroup preserves nonnegativity, assuming the relevant initial data positivity/nonnegativity.
3. `hu_c2`: joint `ContDiffAt ℝ 2` of `(t,x) ↦ intervalDomainLift (S(t)u₀) x`.  The repo has fixed-time C⁴ spatial heat regularity (`heatSemigroup_contDiff_four`) but I did not find a named joint `ContDiffAt` heat wrapper.
4. `Hphys`: resolver coefficient physical joint C².  For heat this should come from source coefficient time-C² envelopes for `ν·(S(t)u₀)^γ` plus elliptic weight; either prove `PhysicalResolverJointC2Data` directly or first prove `PhysicalSourceTimeC2` and use `physicalResolverJointC2Data_of_floor`.
5. `hsource_cont`: continuity of `coupledChemDivSourceLift` near `τ`, by smooth composition.
6. `ChemDivMixedTimeDerivClosedRepr`: a continuous closed-slab representative of the mixed time-derivative.  For heat, this should be built from the explicit smooth heat/resolver series representation.

### If global `∀ τ` causes pain

All current structures are global in `τ : ℝ`.  Heat semigroup smoothness is naturally for `t > 0`; in the level-0 use you only need a positive window `[c,T]` with `0 < c`.  If `τ ≤ 0` is obstructive, the clean API fix is a windowed/positive-time version of `CoupledChemDivFluxFactorJointC2Inputs` or `CoupledChemDivFluxJointC2Hyp`, analogous to the repo’s other `...On` patterns.  Otherwise the heat proof must explain what happens at nonpositive `τ` for `intervalFullSemigroupOperator`.

## Search summary

Searches performed:

```text
CoupledChemDivFluxFactorJointC2Inputs
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
coupledChemDivFluxFactorJointC2Inputs_of_physical
coupledChemDivFluxFactorJointC2Inputs_of_iterate
ChemDivSolutionRegularityResidual fluxJointC2Hyp_of_residual
```

Results:

- Exact factor structure and producer are in `IntervalChemDivFluxJointC2Producer.lean`.
- `_of_physical` is in `IntervalResolverJointC2PhysicalConcrete.lean`; `_of_floor` is in `IntervalPhysicalResolverDataConcrete.lean`.
- `_of_iterate` is in `IntervalFlooredSourceTimeDataIterate.lean`.
- `ChemDivSolutionRegularityResidual` and `fluxJointC2Hyp_of_residual` are in `IntervalChemDivWinDischarge.lean`.
- No completed heat-level constructor was found.
