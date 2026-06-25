# Q549 (cron2): `CoupledChemDivLocalChainRule` for heat semigroup chemDiv

## Executive verdict

I found **generic producers** for `CoupledChemDivLocalChainRule p u`, but I did **not** find a theorem specialized to

```lean
CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ 0)
```

The committed route is layered:

```text
CoupledChemDivPointwiseChainAtoms
  → CoupledChemDivLocalChainRule

CoupledChemDivOuterCommuteAtoms
  → CoupledChemDivLocalChainRule

CoupledChemDivFluxJointC2Hyp
  → CoupledChemDivOuterCommuteAtoms
  → CoupledChemDivLocalChainRule

CoupledChemDivFluxFactorJointC2Inputs / FAC / physical resolver data
  → CoupledChemDivFluxJointC2Hyp
  → ...
```

For the heat semigroup, the most plausible target is therefore **not** to expand the `CoupledChemDivLocalChainRule` fields directly.  Prove a local `CoupledChemDivFluxJointC2Hyp` (or the slightly lower `CoupledChemDivFluxFactorJointC2Inputs`) for

```lean
u := conjugatePicardIter p u₀ 0
```

on positive slabs, then apply:

```lean
coupledChemDivLocalChainRule_of_fluxJointC2
```

Important caveat: the current `CoupledChemDivLocalChainRule` is **global in `τ : ℝ`**.  Heat semigroup smoothing naturally gives slabs with `τ > 0` and `δ < τ`.  If the actual consumer only needs `[c,T]` with `c > 0`, the cleanest design may be a **windowed/local chain-rule lemma** rather than forcing a global `∀ τ : ℝ` structure for a positive-time-only argument.

Branch note: the core infrastructure files below are present on `chatgpt-scratch`.  The previously discussed target file `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` returned 404 when fetched with `ref="chatgpt-scratch"`, so that particular level-0 theorem/sorry appears not to exist on this branch, even though it appears in the indexed/default repository search results.

## 0. The structure you need

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:78`

```lean
structure CoupledChemDivLocalChainRule
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

## 1. Existing `CoupledChemDivLocalChainRule` producers

### 1.1 Thin wrapper from identical pointwise atoms

`ShenWork/PDE/IntervalChemDivLocalChainRule.lean:17`

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

Producer:

`ShenWork/PDE/IntervalChemDivLocalChainRule.lean:33`

```lean
theorem coupledChemDivLocalChainRule_of_pointwiseChainAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivPointwiseChainAtoms p u) :
    CoupledChemDivLocalChainRule p u
```

This is only a packaging wrapper; it does not prove any heat-semigroup calculus.

### 1.2 Outer-commute atoms → local chain rule

`ShenWork/PDE/IntervalChemDivOuterCommute.lean:33`

```lean
structure CoupledChemDivOuterCommuteAtoms
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => deriv (coupledChemDivFluxLift p u r) x)
        (deriv (coupledChemDivFluxTimeDerivativeLift p u s) x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Producer:

`ShenWork/PDE/IntervalChemDivOuterCommute.lean:48`

```lean
theorem coupledChemDivLocalChainRule_of_outerCommuteAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivOuterCommuteAtoms p u) :
    CoupledChemDivLocalChainRule p u
```

It uses two definitional/interior bridges:

`ShenWork/PDE/IntervalChemDivOuterCommute.lean:14`

```lean
theorem coupledChemDivSourceLift_eq_deriv_fluxLift_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    coupledChemDivSourceLift p u s x =
      deriv (coupledChemDivFluxLift p u s) x
```

`ShenWork/PDE/IntervalChemDivOuterCommute.lean:26`

```lean
theorem coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ} :
    coupledChemDivTimeDerivativeLift p u s x =
      deriv (coupledChemDivFluxTimeDerivativeLift p u s) x
```

So if you can prove the outer commute

```lean
HasDerivAt
  (fun r => deriv (coupledChemDivFluxLift p u r) x)
  (deriv (coupledChemDivFluxTimeDerivativeLift p u s) x) s
```

plus source continuity and full mixed-derivative joint continuity, this producer converts it to the desired pointwise source derivative.

### 1.3 Primitive joint-`C²` flux package → outer-commute atoms → local chain rule

`ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean:126`

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

Producer to outer atoms:

`ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean:150`

```lean
theorem coupledChemDivOuterCommuteAtoms_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivOuterCommuteAtoms p u
```

Direct producer to local chain rule:

`ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean:180`

```lean
theorem coupledChemDivLocalChainRule_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivLocalChainRule p u
```

This is probably the best generic entry point for the heat semigroup.

The underlying Clairaut bridge is:

`ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean:84`

```lean
theorem real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
    {F Ft : ℝ → ℝ → ℝ} {s x : ℝ}
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (s, x))
    (hspatial :
      (fun r : ℝ => deriv (F r) x) =ᶠ[𝓝 s]
        (fun r : ℝ => fderiv ℝ (Function.uncurry F) (r, x) (0, 1)))
    (htime :
      (fun y : ℝ => Ft s y) =ᶠ[𝓝 x]
        (fun y : ℝ => fderiv ℝ (Function.uncurry F) (s, y) (1, 0))) :
    HasDerivAt (fun r : ℝ => deriv (F r) x) (deriv (Ft s) x) s
```

### 1.4 Factor-level joint-`C²` package → flux joint-`C²`

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean:79`

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

Producer:

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean:117`

```lean
theorem coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

The product/quotient/rpow regularity lemma is:

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean:20`

```lean
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x))
    (hgradv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x))
    (hbase : 0 <
      1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

### 1.5 FAC/physical resolver route

`ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:21`

```lean
def FACLocalSlabInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (U τ δ : ℝ) : Prop :=
  0 < δ ∧
    (∀ s : ℝ, s ∈ Metric.ball τ δ → 0 < s ∧ s < U) ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ s : ℝ, Continuous (u s)) ∧
    (∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

`ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:49`

```lean
structure CoupledChemDivFluxFactorFACInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, ∃ δ : ℝ, FACLocalSlabInputs p u U τ δ
```

Producer:

`ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean:81`

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_FACInputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputs p u) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

Physical/commute-discharge producer:

`ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:99`

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ContinuousOn
        (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This is closer to heat-semigroup use: for `u = S(t)u₀`, `hu_c2` should come from heat-smoothing, but `other` still needs the full mixed derivative `ContinuousOn` field.

## 2. How `coupledChemDivTimeDerivativeLift` is computed

The raw definition is in `ShenWork/PDE/IntervalChemDivTimeDerivative.lean:31`:

```lean
def coupledChemDivTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv
    (fun y : ℝ =>
      let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
      let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
      ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
          (1 + v y) ^ p.β +
        intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
        p.β * intervalDomainLift (u s) y * deriv v y * vt y /
          (1 + v y) ^ (p.β + 1))
    x
```

The inner flux and its time derivative are factored in `ShenWork/PDE/IntervalChemDivFluxChain.lean`.

Flux:

`ShenWork/PDE/IntervalChemDivFluxChain.lean:11`

```lean
def coupledChemDivFluxLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  intervalDomainLift (u s) y * deriv v y / (1 + v y) ^ p.β
```

Flux time derivative:

`ShenWork/PDE/IntervalChemDivFluxChain.lean:17`

```lean
def coupledChemDivFluxTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
  ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
      (1 + v y) ^ p.β +
    intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
    p.β * intervalDomainLift (u s) y * deriv v y * vt y /
      (1 + v y) ^ (p.β + 1)
```

Flux time derivative chain-rule theorem:

`ShenWork/PDE/IntervalChemDivFluxChain.lean:57`

```lean
theorem coupledChemDivFlux_hasDerivAt_time
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s y : ℝ}
    (hu : HasDerivAt (fun r => intervalDomainLift (u r) y)
      (ShenWork.Paper2.PicardLimitK1.slopeSlice u s y) s)
    (hgv : HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s)
    (hv : HasDerivAt
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)
      (coupledChemicalTimeDerivativeLift p u s y) s)
    (hbase : 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) y) :
    HasDerivAt (fun r => coupledChemDivFluxLift p u r y)
      (coupledChemDivFluxTimeDerivativeLift p u s y) s
```

The full `coupledChemDivTimeDerivativeLift` is definitionally the spatial derivative of the flux time derivative:

`ShenWork/PDE/IntervalChemDivOuterCommute.lean:26`

```lean
theorem coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ} :
    coupledChemDivTimeDerivativeLift p u s x =
      deriv (coupledChemDivFluxTimeDerivativeLift p u s) x
```

There is also a fully expanded mixed-algebra form for the outer spatial derivative:

`ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean:49`

```lean
def mixedAlgebra (β : ℝ)
    (Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ := ...
```

It represents the spatial derivative of

```text
Ut * Vx / (1+V)^β + U * Vtx / (1+V)^β - β * U * Vx * Vt / (1+V)^(β+1)
```

## 3. Joint-continuity theorems for `coupledChemDivTimeDerivativeLift`

### 3.1 Resolver `v_t` continuity only — not the full chemDiv time derivative

Definition of resolver time derivative:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:21`

```lean
def coupledChemicalTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => intervalDomainLift (coupledChemicalConcentration p u r) x) s
```

Joint continuity of `v_t` from spectral agreement:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:50`

```lean
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

Fixed-space closed positive-window continuity of `v_t`:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:60`

```lean
theorem coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U T c x : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T)
```

Convenience wrappers:

`ShenWork/PDE/IntervalChemDivLocalChainRule.lean:40`

```lean
theorem chemDiv_vt_jointContinuous_factor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

`ShenWork/PDE/IntervalChemDivLocalChainRule.lean:50`

```lean
theorem chemDiv_vt_continuousOn_factor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U T c x : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T)
```

These do **not** prove joint continuity of `coupledChemDivTimeDerivativeLift`; they only feed the `v_t` factor used inside it.

### 3.2 Closed-slab representative → full joint continuity of `coupledChemDivTimeDerivativeLift`

This is the direct theorem for the full mixed derivative.

Representative structure:

`ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:43`

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

Joint continuity theorem:

`ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:54`

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Data bundle producing the representative:

`ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean:70`

```lean
structure ChemDivMixedReprData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

Producer:

`ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean:102`

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (D : ChemDivMixedReprData p u τ δ) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ
```

Witness bundle for constructing `ChemDivMixedReprData`:

`ShenWork/PDE/IntervalChemDivMixedReprWitness.lean:178`

```lean
structure ChemDivMixedReprWitnessData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  Uc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Uc (t, x) = intervalDomainLift (u t) x
  Utc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Utc (t, x) = ShenWork.Paper2.PicardLimitK1.slopeSlice u t x
  Vc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Vc (t, x) = intervalDomainLift (coupledChemicalConcentration p u t) x
  Vtc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Vtc (t, x) = coupledChemicalTimeDerivativeLift p u t x
  hUx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => intervalDomainLift (u t) y) (Uxc (t, x)) x
  hUtx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => ShenWork.Paper2.PicardLimitK1.slopeSlice u t y)
      (Utxc (t, x)) x
  hVx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => intervalDomainLift (coupledChemicalConcentration p u t) y)
      (Vxc (t, x)) x
  hVxx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt
      (fun y => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y)
      (Vxxc (t, x)) x
  hVtx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => coupledChemicalTimeDerivativeLift p u t y) (Vtxc (t, x)) x
  hVtxx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y)
      (Vtxxc (t, x)) x
  Vxc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    Vxc (t, x) = deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
  Vtxc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    Vtxc (t, x) = deriv (coupledChemicalTimeDerivativeLift p u t) x
  boundary_agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

Witness producer:

`ShenWork/PDE/IntervalChemDivMixedReprWitness.lean:326`

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_witness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ
```

Physical route with `htime_cont` discharged by the representative:

`ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:87`

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

For the heat semigroup, this suggests a concrete plan: build `ChemDivMixedReprWitnessData` from heat/cosine series representatives for `U, U_t, U_{tx}, U_x` and resolver series representatives for `V, V_x, V_{xx}, V_t, V_{tx}, V_{txx}`, then use the witness theorem to discharge the `ContinuousOn (uncurry coupledChemDivTimeDerivativeLift)` field.

## 4. Source-slice continuity from spatial regularity

I did not find a standalone theorem named like

```lean
ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
```

specialized to the heat semigroup.  In the local-chain infrastructure it is consistently carried as the field

```lean
∀ᶠ s in 𝓝 τ, ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
```

inside `CoupledChemDivPointwiseChainAtoms`, `CoupledChemDivOuterCommuteAtoms`, `CoupledChemDivFluxJointC2Hyp`, `CoupledChemDivFluxFactorJointC2Inputs`, and the residual bundle below.

The spatial C² source file does have the relevant per-slice infrastructure:

`ShenWork/Paper2/IntervalChemDivSpatialC2.lean:95`

```lean
theorem chemDivLift_contDiffOn_two_of_global
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiff ℝ 4 (intervalDomainLift u))
    (hv : ContDiff ℝ 4 (intervalDomainLift v))
    (hv_pos : ∀ x, (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1)
```

and weak-H² from cosine representatives:

`ShenWork/Paper2/IntervalChemDivSpatialC2.lean:144`

```lean
noncomputable def chemDivSource_weakH2_of_cosineRep
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    {U_cos V_cos : ℝ → ℝ}
    (hu_cos : ContDiff ℝ 4 U_cos)
    (hv_cos : ContDiff ℝ 4 V_cos)
    (hv_cos_pos : ∀ x, (0 : ℝ) < 1 + V_cos x)
    (h_agree_u : ∀ x ∈ Icc (0 : ℝ) 1, intervalDomainLift u x = U_cos x)
    (h_agree_v : ∀ x ∈ Icc (0 : ℝ) 1, intervalDomainLift v x = V_cos x)
    (hu_even : ∀ x, U_cos (-x) = U_cos x)
    (hv_even : ∀ x, V_cos (-x) = V_cos x)
    (hu_symm1 : ∀ x, U_cos (2 - x) = U_cos x)
    (hv_symm1 : ∀ x, V_cos (2 - x) = V_cos x) :
    IntervalWeakH2Neumann (chemDivLift p u v)
```

For local-chain use, you likely need a small wrapper from `ContDiffOn ℝ 2` to `ContinuousOn`, then a definally/simp bridge from `chemDivLift`/`intervalDomainChemotaxisDiv` to `coupledChemDivSourceLift p u s`.

## 5. Other useful time-chain bridges

Time bridge from joint `C²` of factors to the time partial of the flux:

`ShenWork/PDE/IntervalChemDivFluxTimeBridge.lean:81`

```lean
theorem coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, y))
    (hv : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, y))
    (hgradv : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, y))
    (hbase : ∀ᶠ y in 𝓝 x,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) y)
    (hgv : ∀ᶠ y in 𝓝 x, HasDerivAt
      (fun r => deriv
        (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
          (s, y) (1, 0))
```

Physical inner-commute producer:

`ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:21`

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s
```

Physical time-bridge producer:

`ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:68`

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : ∀ s : ℝ, ∀ x : ℝ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))
```

## 6. Existing residual bundle documenting the bottom of the chain

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:79`

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  du : ℝ → ℝ → ℝ
  d2u : ℝ → ℝ → ℝ
  hiter : ShenWork.IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData p u du d2u
  hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (...)
  hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (...)
  other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in nhds τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[nhds x]
        (fun y : ℝ => fderiv ℝ
          (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))) ∧
    ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
  ...
```

Producer to flux joint-`C²`:

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:122`

```lean
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

This confirms the recursion-check story: the local chain rule is not currently derived from just a bare mild solution; it bottoms out in explicit time/space regularity residuals.

## 7. Practical heat-semigroup plan

For `u = conjugatePicardIter p u₀ 0`, the shortest proof shape is probably:

```lean
let u := conjugatePicardIter p u₀ 0
have Hflux : CoupledChemDivFluxJointC2Hyp p u := by
  -- prove local positive-time slabs using heat semigroup smoothing and resolver smoothness
  -- fields: source continuity, flux joint C², spatial fderiv bridge,
  -- time fderiv bridge, joint continuity of coupledChemDivTimeDerivativeLift
  ...
exact coupledChemDivLocalChainRule_of_fluxJointC2 Hflux
```

But if the only downstream need is the positive window `[c,T]`, this global theorem may be over-strong.  A cleaner local/windowed variant would ask only for:

```lean
∀ s ∈ Icc c T, ∀ n,
  HasDerivWithinAt
    (fun r => coupledChemDivSourceCoeffs p u r n)
    (coupledChemDivAdot p u s n) (Icc c T) s
```

using local slabs around `s ∈ [c,T]`, avoiding the need to satisfy `exists_local_slab` for all `τ ≤ 0`.

Bottom line: there is no heat-level0 producer already sitting in the repo.  The reusable machinery exists, and the best entry point is `coupledChemDivLocalChainRule_of_fluxJointC2`; the missing heat-specific work is a positive-time local `CoupledChemDivFluxJointC2Hyp` or a windowed replacement for `CoupledChemDivLocalChainRule`.