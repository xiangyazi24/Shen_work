# Q870 / cron1: differentiating source cosine coefficients under the integral

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Refs inspected:

- `main` for `ShenWork/Paper2/IntervalMildPicardRegularity.lean`.
- `main` for `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean`.
- `main` for `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean`.
- `main` for `ShenWork/Wiener/EWA/SourcePowerCoeffDeriv.lean`.

The requested scratch file itself was updated on `chatgpt-scratch`.

## Verdict

Yes.  The repo has exactly the theorem you are looking for.

The generic differentiate-under-the-cosine-coefficient theorem is:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
```

in:

```text
ShenWork/Paper2/IntervalMildPicardRegularity.lean
```

It is already used to prove:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiff
```

in:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

So for `coeff_contDiff`, the best route is **not** to reprove the integral differentiation directly.  Use the existing pattern:

```lean
FlooredSourceTimeData
  → srcTimeCoeff_deriv
  → cosS1_deriv
  → cosS2_continuous
  → srcTimeCoeff_contDiff
```

For the heat semigroup, your real task is therefore to build the `FlooredSourceTimeData` inputs, or a positive-window analogue of them, for

```lean
u := conjugatePicardIter p u₀ 0
```

not to prove a new `cosineCoeffs` Leibniz theorem.

## Exact generic theorem

The theorem is documented as the time-Leibniz rule for cosine coefficients.  It rewrites `cosineCoeffs` as a real interval integral and then applies `intervalIntegral_hasDerivAt_time_of_local` with a dominated-convergence bound from slab continuity.

```lean
/-- **Time-Leibniz for cosine coefficients.**

If `f : ℝ → ℝ → ℝ` satisfies:
1. `f(s,·)` is continuous on `[0,1]` for `s` near `τ`,
2. Each spatial point `x ∈ (0,1)` has `HasDerivAt (fun s => f s x) (f' s x) s`
   for all `s ∈ Metric.ball τ δ`,
3. `f'` is jointly continuous on `[τ-δ, τ+δ] × [0,1]`,

then `HasDerivAt (fun s => cosineCoeffs (f s) n) (cosineCoeffs (f' τ) n) τ`. -/
theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 τ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ
```

The file also has the integral identity it uses:

```lean
theorem cosineCoeffs_eq_factor_mul_integral (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x
```

So this theorem is exactly the formal version of your calculation:

```text
∂ₜ cosineCoeff(f t) = cosineCoeff(∂ₜ f t)
```

under local continuity / dominated-convergence hypotheses.

## Existing `srcTimeCoeff` wrapper

The source time coefficient is defined in `IntervalPhysicalResolverDataConcrete.lean`:

```lean
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re
```

Then `IntervalPhysicalSourceTimeC2Concrete.lean` proves the identity:

```lean
theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k
```

where:

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ
```

This is precisely your

```text
ν · S(t)u₀(x)^γ
```

slice when `u = conjugatePicardIter p u₀ 0`.

## How `srcTimeCoeff_contDiff` is proved

`FlooredSourceTimeData` packages the two time-derivative slices:

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

  ...
```

Then the file proves, privately:

```lean
private theorem srcTimeCoeff_deriv
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Differentiable ℝ (srcTimeCoeff p u k) ∧
    deriv (srcTimeCoeff p u k) = fun t => cosineCoeffs (s₁ t) k
```

The core line is exactly:

```lean
have hH := cosineCoeffs_hasDerivAt_of_smooth_param (f := srcSlice p u)
  (f' := s₁) (τ := t) (δ := δ) (n := k) hδ hcont hdiff hcd
```

Then it proves, again privately:

```lean
private theorem cosS1_deriv
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Differentiable ℝ (fun t => cosineCoeffs (s₁ t) k) ∧
    deriv (fun t => cosineCoeffs (s₁ t) k) = fun t => cosineCoeffs (s₂ t) k
```

with:

```lean
exact cosineCoeffs_hasDerivAt_of_smooth_param (f := s₁) (f' := s₂)
  (τ := t) (δ := δ) (n := k) hδ hcont hdiff hcd
```

Finally it proves:

```lean
theorem srcTimeCoeff_contDiff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

by combining:

```lean
srcTimeCoeff_deriv H k
cosS1_deriv H k
cosS2_continuous H k
contDiff_succ_iff_deriv
```

So the exact reusable theorem for your current `coeff_contDiff` field is:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiff
```

## What this means for the heat semigroup base iterate

For

```lean
u := conjugatePicardIter p u₀ 0
```

one should define explicit time-derivative slices on the positive-time region:

```lean
U  t x := intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
Ut t x := ∂ₜ U t x
Utt t x := ∂ₜ² U t x

s₁ t x := p.ν * p.γ * (U t x) ^ (p.γ - 1) * Ut t x

s₂ t x := p.ν * p.γ *
  ((p.γ - 1) * (U t x) ^ (p.γ - 2) * (Ut t x)^2
    + (U t x) ^ (p.γ - 1) * Utt t x)
```

Then prove the two `FlooredSourceTimeData` derivative fields on a positive-time slab:

```lean
HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s
HasDerivAt (fun r => s₁ r x) (s₂ s x) s
```

These are pointwise `rpow` chain-rule facts using positivity of the heat semigroup on the slab.  Once those are in place, the coefficient part is automatic by `srcTimeCoeff_contDiff`.

## Important caution: global vs positive-window

`FlooredSourceTimeData` as currently written is global in time:

```lean
d0 : ∀ τ : ℝ, ...
d1 : ∀ τ : ℝ, ...
```

For the heat semigroup with the hard zero-extension at `t ≤ 0`, global `FlooredSourceTimeData` is likely the wrong target because of the `τ = 0` obstruction.  For Level0 on `[c,T]`, the cleaner route is a positive-window analogue:

```lean
FlooredSourceTimeDataOn p u s₁ s₂ c T
```

or directly a positive-window version of:

```lean
PhysicalSourceTimeC2
```

The under-integral theorem itself is local in `τ` and works perfectly on positive slabs.  The global packaging is the thing that can be too strong.

## Specialized power-source helper already exists

There is also a more specialized theorem in:

```text
ShenWork/Wiener/EWA/SourcePowerCoeffDeriv.lean
```

It defines:

```lean
def adotPow (p : CM2Params) (v : ℝ → intervalDomainPoint → ℝ)
    (vdotL : ℝ → ℝ → ℝ) (σ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs
    (fun x => p.ν * p.γ * (intervalDomainLift (v σ) x) ^ (p.γ - 1) * vdotL σ x) k
```

and proves:

```lean
theorem hasDerivAt_powerCoeff_of_inputs {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {σ δ : ℝ} (k : ℕ)
    (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 σ,
      ContinuousOn (fun x => p.ν * (intervalDomainLift (v s) x) ^ p.γ)
        (Set.Icc (0 : ℝ) 1))
    (hslice : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => intervalDomainLift (v r) x) (vdotL s x) s)
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      0 < intervalDomainLift (v s) x)
    (hderivcont : ContinuousOn
      (Function.uncurry
        (fun s x => p.ν * p.γ * (intervalDomainLift (v s) x) ^ (p.γ - 1) * vdotL s x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (v r) x) ^ p.γ) k)
      (adotPow p v vdotL σ k) σ
```

This is just the first-derivative version of your target, specialized to the power source.  It is useful because it applies `cosineCoeffs_hasDerivAt_of_smooth_param` with an **opaque** variable `v`, avoiding `whnf`/`isDefEq` blowups.

For your heat-level `src_contDiff`, you can copy this tactic style:

1. set `v : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0`;
2. keep `v` opaque while applying the coefficient-differentiation engine;
3. supply the heat-specific facts only as hypotheses/lemmas about `v`;
4. unfold back only at the boundary of the theorem.

## Recommended path for `coeff_contDiff`

For the current physical resolver data field:

```lean
coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞)
  (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k)
```

use the already committed resolver/source factorization:

```lean
resolverTimeCoeff p u k t = intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

Then reduce to:

```lean
ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

via:

```lean
srcTimeCoeff_contDiff H k
```

where `H` is `FlooredSourceTimeData p u s₁ s₂`, or its positive-window equivalent.

If staying with the current global structure, the Lean shape is:

```lean
have hsrc : ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k) :=
  ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiff H k

have hresolver : ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k) := by
  have : resolverTimeCoeff p u k =
      fun t => intervalNeumannResolverWeight p k * srcTimeCoeff p u k t := by
    funext t
    exact ShenWork.IntervalPhysicalResolverDataConcrete
      .resolverTimeCoeff_eq_weight_smul p u k t
  rw [this]
  exact contDiff_const.mul hsrc
```

But the stronger architectural suggestion is still: build this on a positive window, not globally through `t = 0`.

## Bottom line

The repo already has the theorem and the wrapper:

- Generic under-integral engine:
  ```lean
  cosineCoeffs_hasDerivAt_of_smooth_param
  ```
- Source-coefficient `C²` wrapper:
  ```lean
  srcTimeCoeff_contDiff
  ```
- Specialized first-derivative power-source helper:
  ```lean
  hasDerivAt_powerCoeff_of_inputs
  ```

So do not write a new dominated-convergence proof.  Prove the heat source time-slice data (`s₁`, `s₂`, positivity, continuity on positive slabs), then call `srcTimeCoeff_contDiff`.  If Lean starts reducing `conjugatePicardIter` too aggressively, copy the `SourcePowerCoeffDeriv.lean` approach: make the time-dependent slice an opaque local variable and pass all analytic inputs explicitly.