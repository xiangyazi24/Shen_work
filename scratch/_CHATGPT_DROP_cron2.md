# Q568 (cron2): `CoupledChemDivLocalChainRule` for heat semigroup level 0

## Executive verdict

I did **not** find an existing theorem proving

```lean
CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ 0)
```

on `chatgpt-scratch`.

What exists is a good generic ladder:

```text
CoupledChemDivFluxJointC2Hyp p u
  → CoupledChemDivOuterCommuteAtoms p u
  → CoupledChemDivLocalChainRule p u
```

and a lower-level pointwise wrapper:

```text
CoupledChemDivPointwiseChainAtoms p u
  → CoupledChemDivLocalChainRule p u
```

So the heat-semigroup proof should probably target one of these input bundles, especially `CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)`, rather than expanding `CoupledChemDivLocalChainRule` directly.

The important negative result: I found **no standalone theorem** of the form

```lean
HasDerivAt
  (fun r => coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r x)
  (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s x) s
```

nor even the generic version for arbitrary `u`, except as a **field** inside `CoupledChemDivLocalChainRule` / `CoupledChemDivPointwiseChainAtoms`, or indirectly via the outer-commute producer.  `ChemDivAdot.lean` and `ChemDivGcont.lean` consume `CoupledChemDivLocalChainRule`; they do not produce it.

One design warning: the current structure is global in `τ : ℝ`.  Heat semigroup smoothing is naturally positive-time only.  If the consumer only needs a positive window `[c,T]`, a windowed local-chain-rule structure/lemma may be easier and cleaner than proving the global `∀ τ` version.

## 1. The target structure

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

The derivative field itself is the explicit chain-rule candidate:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:31`

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

Here `coupledChemicalTimeDerivativeLift` is just the time derivative of the resolver value:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:21`

```lean
def coupledChemicalTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => intervalDomainLift (coupledChemicalConcentration p u r) x) s
```

## 2. Existing local-chain-rule producers

### 2.1 Direct pointwise-atoms wrapper

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

This is only a repackaging theorem.  It is useful if you already prove the three target fields directly for heat semigroup level 0.

### 2.2 Outer-commute route

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

This route uses the two key identities:

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

So this is the exact theorem that turns a flux-level `∂ₜ∂ₓ = ∂ₓ∂ₜ` proof into the required `HasDerivAt` for `coupledChemDivSourceLift`.

### 2.3 Joint-`C²` flux route

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

Producer to outer-commute atoms:

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

This is the best reusable entry point for the heat semigroup proof.

## 3. `ChemDivAdot.lean`: consumes `CoupledChemDivLocalChainRule`, does not produce it

`ShenWork/Wiener/EWA/ChemDivAdot.lean:79`

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s
```

This is coefficient-level, not pointwise source-lift level.  It uses the `hchain.exists_local_slab s` field and the generic `cosineCoeffs_hasDerivAt_of_smooth_param` theorem.

`ShenWork/Wiener/EWA/ChemDivAdot.lean:100`

```lean
theorem chemDivAdot_hasDerivWithinAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s
```

`ShenWork/Wiener/EWA/ChemDivAdot.lean:149`

```lean
theorem chemDivAdot_deriv_legs_of_smoothness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u)
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (coupledChemDivAdot p u s n) (Set.Icc 0 T) s)
      ∧ (∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n)
          (Set.Icc (0 : ℝ) T))
```

Conclusion for `ChemDivAdot.lean`: it proves `adot` coefficient derivative legs **from** `hchain`; it is not a source of `hchain`.

## 4. `ChemDivGcont.lean`: also consumes `CoupledChemDivLocalChainRule`

`ShenWork/Wiener/EWA/ChemDivGcont.lean:53`

```lean
theorem chemDiv_coeff_continuous_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (n : ℕ) :
    Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

`ShenWork/Wiener/EWA/ChemDivGcont.lean:74`

```lean
theorem chemDiv_coeff_timeContinuous
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

The file header explicitly says the route is: `CoupledChemDivLocalChainRule p u` → coefficient `HasDerivAt` via `ChemDivAdot.lean` → coefficient continuity.  It does **not** provide the missing pointwise source-lift `HasDerivAt` theorem.

## 5. `ChemDivWinDischarge.lean`: residual route, not heat level-0 producer

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:79`

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  du : ℝ → ℝ → ℝ
  d2u : ℝ → ℝ → ℝ
  hiter : ShenWork.IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData p u du d2u
  hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) → Summable (...)
  hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) → Summable (...)
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

Producer to the primitive flux package:

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:122`

```lean
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

Producer to source time-C¹:

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:131`

```lean
noncomputable def coupledChemDivSource_duhamelSourceTimeC1_of_residual
    {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u)
```

Window producer:

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:154`

```lean
noncomputable def coupledChemDivSource_timeC1On_window_of_gradientSolution
    (D : GradientMildSolutionData p u₀)
    (R : ChemDivSolutionRegularityResidual p D.u)
    {c' d' : ℝ} (hc' : 0 ≤ c') (hd' : d' ≤ D.T) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p D.u) c' d'
```

Conclusion for `ChemDivWinDischarge.lean`: it documents the residual regularity bottom and produces `DuhamelSourceTimeC1(On)` once the residual is supplied.  It does not directly prove `CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ 0)`.

## 6. Search result for direct `HasDerivAt` of `coupledChemDivSourceLift`

Searches for the literal pointwise target found only:

```lean
HasDerivAt
  (fun r => coupledChemDivSourceLift p u r x)
  (coupledChemDivTimeDerivativeLift p u s x) s
```

as fields inside:

- `CoupledChemDivLocalChainRule` (`IntervalChemDivTimeDerivative.lean:78`),
- `CoupledChemDivPointwiseChainAtoms` (`IntervalChemDivLocalChainRule.lean:17`),
- and indirectly via `CoupledChemDivOuterCommuteAtoms` (`IntervalChemDivOuterCommute.lean:33`) plus `coupledChemDivLocalChainRule_of_outerCommuteAtoms` (`IntervalChemDivOuterCommute.lean:48`).

I did not find a theorem whose conclusion is this pointwise source-lift `HasDerivAt` for heat semigroup level 0 or for arbitrary `u`.

## 7. Recommended path for heat semigroup level 0

For the heat semigroup, aim for:

```lean
have Hflux : CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0) := by
  -- positive-time heat smoothing + resolver smoothness + closed-slab mixed derivative continuity
  ...

exact coupledChemDivLocalChainRule_of_fluxJointC2 Hflux
```

The `Hflux` fields line up with the three analytic requirements you named:

1. source slice continuity near `τ`,
2. time derivative/chain rule via the flux-level outer commute,
3. joint continuity of `coupledChemDivTimeDerivativeLift`.

But because `CoupledChemDivLocalChainRule` asks for `∀ τ : ℝ`, the heat proof will hit the `τ ≤ 0` wall unless the heat trajectory is defined/smooth there in this formalization.  If the actual use is only on `[c,T]` with `c > 0`, a windowed variant is probably the right engineering move:

```lean
CoupledChemDivLocalChainRuleOn p u c T
```

or a direct windowed theorem producing the coefficient `HasDerivWithinAt`/`ContinuousOn` legs from positive-time slabs.