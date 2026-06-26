# Q723 / cron1: `PhysicalSourceTimeC2` and `srcTimeCoeff` for heat semigroup

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

`srcTimeCoeff` **is defined** in the repo, in:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

```lean
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re
```

The repo also proves the important identification:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ

 theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k
```

So for the heat trajectory `u t = conjugatePicardIter p u₀ 0 t`, the intended interpretation is exactly:

```lean
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  = cosineCoeffs
      (fun x => p.ν * intervalDomainLift ((conjugatePicardIter p u₀ 0) t) x ^ p.γ) k
```

up to `srcSlice` unfolding.

I did **not** find an existing heat-semigroup-specific theorem proving:

```lean
ContDiff ℝ (2 : ℕ∞)
  (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)
```

Nor did I find a theorem specifically about time-differentiability of

```lean
fun t => cosineCoeffs (fun x => p.ν * (S(t)u₀ x)^p.γ) k
```

for the level-0 heat semigroup trajectory.

What exists is a generic source-time `C²` pipeline: if you can supply `FlooredSourceTimeData` for a trajectory `u`, then the repo proves `srcTimeCoeff p u k` is `ContDiff ℝ 2`; if you also supply the two bounded-weight summability fields, it packages `PhysicalSourceTimeC2 p u ...`.

## 1. Where `srcTimeCoeff` is defined

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

Definition:

```lean
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re
```

This file explains it as the source cosine coefficient driving the resolver.  The resolver coefficient is factored by a constant elliptic multiplier:

```lean
theorem resolverTimeCoeff_eq_weight_smul
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    resolverTimeCoeff p u k t =
      intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

and also as a function equality:

```lean
theorem resolverTimeCoeff_eq_smul
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) :
    resolverTimeCoeff p u k =
      (intervalNeumannResolverWeight p k) • srcTimeCoeff p u k
```

## 2. Where `srcTimeCoeff` is identified with `cosineCoeffs(ν·u^γ)`

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

Definitions/theorem:

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ
```

```lean
theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k := by
  unfold srcTimeCoeff srcSlice
  simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
```

This is the exact bridge from the resolver-side source coefficient to the real cosine coefficient of `ν·u^γ`.

## 3. Generic result giving `ContDiff ℝ 2` of `srcTimeCoeff`

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

The generic hypothesis package is:

```lean
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  d0 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
    ContinuousOn (Function.uncurry s₁) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  d1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (s₁ s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => s₁ r x) (s₂ s x) s) ∧
    ContinuousOn (Function.uncurry s₂) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  sliceC2 : ...
  sliceNeumann : ...
  zerothBound : ...
  laplBound : ...
```

Then the repo proves:

```lean
theorem srcTimeCoeff_contDiff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

The proof route is:

* `srcTimeCoeff_deriv H k` proves

```lean
Differentiable ℝ (srcTimeCoeff p u k) ∧
deriv (srcTimeCoeff p u k) = fun t => cosineCoeffs (s₁ t) k
```

using `cosineCoeffs_hasDerivAt_of_smooth_param` and the identity `srcTimeCoeff_eq_cosineCoeffs`.

* `cosS1_deriv H k` proves

```lean
Differentiable ℝ (fun t => cosineCoeffs (s₁ t) k) ∧
deriv (fun t => cosineCoeffs (s₁ t) k) = fun t => cosineCoeffs (s₂ t) k
```

again using `cosineCoeffs_hasDerivAt_of_smooth_param`.

* `cosS2_continuous H k` proves continuity of the second-derivative coefficient from joint continuity of `s₂` on a local slab.

Then `srcTimeCoeff_contDiff` assembles `ContDiff ℝ 2` via `contDiff_succ_iff_deriv`.

## 4. Packaging `PhysicalSourceTimeC2`

Same file:

```lean
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

The fields are filled as:

```lean
src_contDiff k := srcTimeCoeff_contDiff H k
src_bound i k t hi := srcTimeCoeff_bound H i k t hi
value_summable := hval
grad_summable := hgrad
```

So the generic pipeline for your target is:

```text
FlooredSourceTimeData p (conjugatePicardIter p u₀ 0) s₁ s₂
+ weighted bounded-majorant summability
  ⟹ PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) (builtEs H)
```

But I did not find a theorem that already constructs this `FlooredSourceTimeData` or `PhysicalSourceTimeC2` for the heat semigroup trajectory.

## 5. Existing pointwise chain rules for `ν·u^γ`

There are two relevant generic sources.

### A. Iterate/floored source data route

File:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

It defines explicit first and second source time-derivative slices:

```lean
def srcSlice1 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * du t x
```

```lean
def srcSlice2 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du d2u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (p.γ - 1) * (intervalDomainLift (u t) x) ^ (p.γ - 1 - 1)
      * (du t x) ^ (2 : ℕ)
    + p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * d2u t x
```

It proves the pointwise chain rules:

```lean
theorem hasDerivAt_srcSlice
    (hpos : 0 < intervalDomainLift (u t) x)
    (hdu : HasDerivAt (fun r => intervalDomainLift (u r) x) (du t x) t) :
    HasDerivAt (fun r => srcSlice p u r x) (srcSlice1 p u du t x) t
```

```lean
theorem hasDerivAt_srcSlice1
    (hpos : 0 < intervalDomainLift (u t) x)
    (hdu : HasDerivAt (fun r => intervalDomainLift (u r) x) (du t x) t)
    (hd2u : HasDerivAt (fun r => du r x) (d2u t x) t) :
    HasDerivAt (fun r => srcSlice1 p u du r x) (srcSlice2 p u du d2u t x) t
```

and packages an `IterateSourceTimeData` into a `FlooredSourceTimeData`:

```lean
theorem flooredSourceTimeData_of_iterate
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u)
```

This is generic over `u`; no heat specialization was found.

### B. EWA power-source first derivative route

File:

```text
ShenWork/Wiener/EWA/SourcePowerCoeffDeriv.lean
```

This file targets the first time derivative of power-source cosine coefficients:

```lean
HasDerivAt
  (fun r => cosineCoeffs
    (fun x => p.ν * (intervalDomainLift (realSlice u_star r) x) ^ p.γ) k)
  (adotPow p (realSlice u_star) vdotL σ k) σ
```

It defines:

```lean
def adotPow (p : CM2Params) (v : ℝ → intervalDomainPoint → ℝ)
    (vdotL : ℝ → ℝ → ℝ) (σ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs
    (fun x => p.ν * p.γ * (intervalDomainLift (v σ) x) ^ (p.γ - 1) * vdotL σ x) k
```

and proves an abstract input theorem:

```lean
theorem hasDerivAt_powerCoeff_of_inputs
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} ... :
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (v r) x) ^ p.γ) k)
      (adotPow p v vdotL σ k) σ
```

then instantiates it for `realSlice u_star`:

```lean
theorem realSlice_powerCoeff_hasDerivAt ... :
  ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∀ k : ℕ,
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (realSlice u_star r) x) ^ p.γ) k)
      (adotPow p (realSlice u_star) vdotL σ k) σ
```

This is useful evidence for the coefficient-differentiation pattern, but it is:

* first derivative only, not `ContDiff ℝ 2`;
* for EWA `realSlice u_star`, not `conjugatePicardIter p u₀ 0`;
* stated on `σ ∈ Ioo 0 T`, not globally on all `ℝ`.

## 6. Heat-level time differentiability search result

Searches run:

```text
srcTimeCoeff
srcTimeCoeff_contDiff
conjugatePicardIter srcTimeCoeff
cosineCoeffs_hasDerivAt_of_smooth_param
heat semigroup cosineCoeffs ν u gamma HasDerivAt
ν·u^γ ContDiff time cosine coefficients heat
cosineCoeffs ν S(t)u₀ HasDerivAt
level0_chemDiv_timeDerivData
```

I found no theorem specifically proving time differentiability or `ContDiff ℝ 2` of the **power-source coefficient**

```lean
fun t => cosineCoeffs
  (fun x => p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ) k
```

for the heat semigroup trajectory.

The closest heat-level theorem found is in:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

```lean
theorem level0_chemDiv_timeDerivData ... :
  ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ), ...
```

But this theorem concerns the **chemDiv source coefficients**

```lean
coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0)
```

not `srcTimeCoeff`.  It uses a large `hfluxC2` `sorry` block for heat-specific flux/source regularity, then applies:

```lean
cosineCoeffs_hasDerivAt_of_smooth_param
```

to `coupledChemDivSourceLift` and `coupledChemDivTimeDerivativeLift`.  This is a different source: the divergence chemotaxis source, not the resolver source coefficient `ν·u^γ`.

## Important caveat: global vs positive-time heat regularity

`PhysicalSourceTimeC2` requires:

```lean
src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

which is a **global-on-ℝ** statement.  The heat semigroup smoothing argument naturally gives smoothness for `t > 0` or on positive windows `[c,T]` with `c > 0`.  Unless `conjugatePicardIter p u₀ 0` has a globally smooth extension in the repo, a windowed/local version of `PhysicalSourceTimeC2` may be more natural than the existing global structure.

## Bottom line

* `srcTimeCoeff` is defined in `IntervalPhysicalResolverDataConcrete.lean`.
* Its equality with `cosineCoeffs (ν·u^γ)` is proved in `IntervalPhysicalSourceTimeC2Concrete.lean` by `srcTimeCoeff_eq_cosineCoeffs`.
* The repo has a generic theorem `srcTimeCoeff_contDiff` proving `ContDiff ℝ 2` from `FlooredSourceTimeData`.
* The repo has a generic packager `physicalSourceTimeC2_of_floored` producing `PhysicalSourceTimeC2` from `FlooredSourceTimeData` plus summability.
* I did not find a heat-semigroup-specific theorem producing `FlooredSourceTimeData`, `PhysicalSourceTimeC2`, or `ContDiff ℝ 2 (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)`.
