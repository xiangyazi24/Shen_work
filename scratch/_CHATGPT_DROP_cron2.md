# Q529 (cron2): `coupledChemDivSourceCoeffs` derivative/continuity infrastructure

## Executive verdict

The exact theorem you need exists on `chatgpt-scratch`:

```lean
coupledChemDivCoeff_hasDerivAt_of_chainRule
```

It proves

```lean
HasDerivAt
  (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
  (coupledChemDivAdot p u s n) s
```

from only

```lean
hchain : CoupledChemDivLocalChainRule p u
```

There are also wrappers giving the `HasDerivWithinAt` form for `coupledChemDivSourceCoeffs`, and `ContinuousOn (fun s => coupledChemDivAdot p u s n)` on `[0,T]` from joint continuity of `coupledChemDivTimeDerivativeLift` on `[0,T] × [0,1]`.

`ChemDivGcont.lean` is a separate small file: it uses the same `CoupledChemDivLocalChainRule` to show global time-continuity of the **source coefficients**

```lean
Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

not of `adot`.

The remaining analytic input is how to produce `CoupledChemDivLocalChainRule`.  The repo has several generic producers:

```text
CoupledChemDivPointwiseChainAtoms → CoupledChemDivLocalChainRule
CoupledChemDivOuterCommuteAtoms → CoupledChemDivLocalChainRule
CoupledChemDivFluxJointC2Hyp → CoupledChemDivLocalChainRule
```

but no theorem specialized to `u = conjugatePicardIter p u₀ 0` was found in these files.

## 1. Exact `HasDerivAt` theorem for the cosine coefficient

`ShenWork/Wiener/EWA/ChemDivAdot.lean:79`

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s
```

Internally it expands the local slab from `hchain.exists_local_slab s`:

```lean
rcases hchain.exists_local_slab s with
  ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
```

and applies:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
  (f := coupledChemDivSourceLift p u)
  (f' := coupledChemDivTimeDerivativeLift p u)
  (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv
```

So the only analytic package consumed is `CoupledChemDivLocalChainRule p u`; no H², decay, zeroth coefficient, or Mdot data is used.

## 2. `HasDerivWithinAt` wrapper for `coupledChemDivSourceCoeffs`

`ShenWork/Wiener/EWA/ChemDivAdot.lean:100`

```lean
theorem chemDivAdot_hasDerivWithinAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s
```

This is just the previous global `HasDerivAt`, rewritten through the definitional equality

```lean
coupledChemDivSourceCoeffs p u r n
  = cosineCoeffs (coupledChemDivSourceLift p u r) n
```

and restricted using `.hasDerivWithinAt`.

For a different closed interval such as `[c,T]`, the same pattern should work directly from

```lean
(coupledChemDivCoeff_hasDerivAt_of_chainRule hchain s n).hasDerivWithinAt
```

with `simpa [coupledChemDivSourceCoeffs]`.

## 3. `ContinuousOn` theorem for `coupledChemDivAdot` on a closed interval

`ShenWork/Wiener/EWA/ChemDivAdot.lean:125`

```lean
theorem chemDivAdot_continuousOn_of_jointCont
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n) (Set.Icc (0 : ℝ) T)
```

It uses the compact dominated-continuity lemma:

```lean
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
  (f := coupledChemDivTimeDerivativeLift p u)
  (c := (0 : ℝ)) (T := T) n hjointcont
```

and the definitional equality

```lean
coupledChemDivAdot p u s n
  = cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n
```

For a positive window `[c,T]`, use the same lower-level theorem directly with `(c := c) (T := T)` if you have

```lean
ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc c T ×ˢ Icc (0:ℝ) 1)
```

## 4. Combined derivative/continuity package in `ChemDivAdot.lean`

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

This is the ready-made `[0,T]` package for the derivative leg plus `adot` continuity leg.  It deliberately does not prove `Mdot`.

## 5. `CoupledChemDivLocalChainRule`: structure and meaning

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

So it packages exactly:

1. eventual per-slice continuity of the source lift near each time `τ`,
2. pointwise time `HasDerivAt` of the source lift on interior spatial points,
3. closed-slab joint continuity of the derivative field.

This is the core analytic input behind the coefficient `HasDerivAt` theorem.

## 6. Producers for `CoupledChemDivLocalChainRule`

### 6.1 Direct wrapper from pointwise atoms

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

This is a pure wrapper; it does not prove the analytic facts.

### 6.2 From outer-commute atoms

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

It relies on these two identities:

```lean
theorem coupledChemDivSourceLift_eq_deriv_fluxLift_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    coupledChemDivSourceLift p u s x =
      deriv (coupledChemDivFluxLift p u s) x
```

and

```lean
theorem coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ} :
    coupledChemDivTimeDerivativeLift p u s x =
      deriv (coupledChemDivFluxTimeDerivativeLift p u s) x
```

### 6.3 From primitive joint-`C²` flux regularity

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

Direct producer:

`ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean:180`

```lean
theorem coupledChemDivLocalChainRule_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivLocalChainRule p u
```

This is usually the best abstraction to target if you want to prove the chain rule from smoothness/Clairaut rather than from the pointwise source-lift formula directly.

## 7. What `ChemDivAdot.lean` provides

`ChemDivAdot.lean` provides exactly the `adot` derivative/continuity reductions:

1. global coefficient `HasDerivAt` from `CoupledChemDivLocalChainRule`,
2. `[0,T]` `HasDerivWithinAt` for `coupledChemDivSourceCoeffs`,
3. `[0,T]` `ContinuousOn` of `coupledChemDivAdot` from joint continuity of `coupledChemDivTimeDerivativeLift`,
4. a combined theorem bundling (2) and (3),
5. the `Mdot` residual converter from a supplied summable envelope.

The key exact theorems are:

```lean
coupledChemDivCoeff_hasDerivAt_of_chainRule
chemDivAdot_hasDerivWithinAt_of_chainRule
chemDivAdot_continuousOn_of_jointCont
chemDivAdot_deriv_legs_of_smoothness
chemDivAdot_Mdot_residual
```

It does **not** produce `CoupledChemDivLocalChainRule`; it consumes it.

It also does **not** produce the uniform-in-`n` `Mdot` bound from smoothness alone.  The comments explicitly isolate `Mdot` as a residual.

## 8. What `ChemDivGcont.lean` provides

`ShenWork/Wiener/EWA/ChemDivGcont.lean` imports `ChemDivAdot.lean` and proves global time-continuity of the source coefficient family from the same chain-rule package.

`ChemDivGcont.lean:53`

```lean
theorem chemDiv_coeff_continuous_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (n : ℕ) :
    Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

`ChemDivGcont.lean:74`

```lean
theorem chemDiv_coeff_timeContinuous
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

Proof route:

```lean
coupledChemDivCoeff_hasDerivAt_of_chainRule hchain s n
  → continuousAt
  → Continuous (fun s => cosineCoeffs (coupledChemDivSourceLift p u s) n)
  → simpa [coupledChemDivSourceCoeffs]
```

This file is about the source coefficient time-continuity `hGcont`; it is not about `adot` continuity and not about `Mdot`.

## Practical summary

For your target, the likely code shape is:

```lean
have hAt : HasDerivAt
    (fun r => coupledChemDivSourceCoeffs p u r n)
    (coupledChemDivAdot p u s n) s := by
  simpa [coupledChemDivSourceCoeffs] using
    coupledChemDivCoeff_hasDerivAt_of_chainRule
      (p := p) (u := u) hchain s n

exact hAt.hasDerivWithinAt
```

and for `adot` continuity on `[c,T]`, use the generic coefficient-continuity lemma behind `chemDivAdot_continuousOn_of_jointCont` with `(c := c)` and `(T := T)`, assuming the joint continuity of `coupledChemDivTimeDerivativeLift` on `Icc c T ×ˢ Icc 0 1`.