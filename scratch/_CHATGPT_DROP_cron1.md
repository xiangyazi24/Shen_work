# Q879 / cron1: time derivative of the heat semigroup cosine series

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Ref inspected: `main`

## Verdict

Yes, the repo has the **series-level** theorem you want:

```lean
ShenWork.IntervalSourceCoefficientTimeC1.homogeneousCosineSeries_hasDerivAt_time
```

File:

```text
ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean
```

Around line: `601`.

It proves exactly the homogeneous heat-cosine synthesis time derivative:

```lean
theorem homogeneousCosineSeries_hasDerivAt_time
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    HasDerivAt
      (fun t => ∑' n, Real.exp (-t * unitIntervalCosineEigenvalue n) *
        a₀ n * cosineMode n x)
      (∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-t₀ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x) t₀
```

This is precisely:

```text
∂ₜ ∑ₙ e^{-tλₙ} a₀ₙ cos(nπx)
  = ∑ₙ -λₙ e^{-tλₙ} a₀ₙ cos(nπx)
```

for `t₀ > 0`, assuming bounded initial coefficients `|a₀ n| ≤ M`.

## Direct `intervalFullSemigroupOperator` wrapper?

I did **not** find a direct theorem with the exact operator-level shape:

```lean
HasDerivAt (fun t => intervalFullSemigroupOperator t f x) ... t
```

The current reusable path is:

1. Use the spectral equality for the full Neumann propagator:

```lean
ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_clean
```

in:

```text
ShenWork/PDE/IntervalFullKernelSpectralClean.lean
```

Signature:

```lean
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_clean
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

or the closed-interval version:

```lean
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

2. Rewrite `unitIntervalCosineHeatValue` / heat value into the explicit cosine series.

3. Apply:

```lean
homogeneousCosineSeries_hasDerivAt_time
```

## Level-0 Picard bridge already uses this representation

For level 0, the repo has:

```lean
ShenWork.IntervalPicardIterateRepresentation.hagree_zero
```

in:

```text
ShenWork/Paper2/IntervalPicardIterateRepresentation.lean
```

It states that the lifted level-0 Picard iterate agrees on `[0,1]` with the damped cosine series:

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
```

and `iterateReprCoeff p u₀ 0 σ k` is definitionally:

```lean
Real.exp (-σ * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k
```

So for your heat-level source derivative input, the intended route is:

```lean
a₀ := cosineCoeffs (intervalDomainLift u₀)

homogeneousCosineSeries_hasDerivAt_time
  (a₀ := a₀)
  (M := M₀)
  hM₀_nonneg hu₀_bound ht x
```

then use the level-0 agreement theorem / spectral equality as needed to move between the lifted heat slice and the explicit series.

## Related Duhamel theorem

The same file also has the inhomogeneous analogue:

```lean
ShenWork.IntervalSourceCoefficientTimeC1.restartCosineSeries_hasDerivAt_time
```

around line `719`, proving

```lean
∂τ ∑ₙ localRestartCoeff a₀ a τ n cos(nπx)
  = ∑ₙ (a τ n - λₙ localRestartCoeff a₀ a τ n) cos(nπx).
```

But for pure heat semigroup level 0, use `homogeneousCosineSeries_hasDerivAt_time` directly.

## Bottom line

The theorem exists, but at the **cosine-series synthesis** level, not as a direct `intervalFullSemigroupOperator` API theorem.

Use:

```lean
ShenWork.IntervalSourceCoefficientTimeC1.homogeneousCosineSeries_hasDerivAt_time
```

with

```lean
a₀ k := cosineCoeffs (intervalDomainLift u₀) k
```

and bridge to `intervalFullSemigroupOperator` / `picardIter ... 0` using the existing spectral agreement theorems such as `hagree_zero` or `intervalFullSemigroupOperator_eq_cosineHeatValue_*`.