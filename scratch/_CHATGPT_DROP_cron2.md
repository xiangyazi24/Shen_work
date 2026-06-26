# Q756 (cron2): cutoff heat-term Leibniz bound pattern

Static repository inspection only; I did not run a Lean build.

## Executive answer

The existing resolver-lane theorem to copy is:

```lean
ShenWork.IntervalResolverSpectralJointC2CutoffBounds.cutoffValueTerm_leibniz_bound
```

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2CutoffBounds.lean
```

It is the direct `norm_iteratedFDeriv_mul_le` wrapper for a separated cutoff value term.  It rewrites

```lean
cutoffValueTerm φ a₀ a offset n
```

as the product

```lean
G q * H q
```

where

```lean
G q = φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n
H q = cosineMode n q.2
```

and proves

```lean
‖iteratedFDeriv ℝ k (cutoffValueTerm φ a₀ a offset n) q‖ ≤
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
    ‖iteratedFDeriv ℝ i
      (fun q : ℝ × ℝ =>
        φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
    ‖iteratedFDeriv ℝ (k - i)
      (fun q : ℝ × ℝ => cosineMode n q.2) q‖
```

The proof is very short: establish the definitional equality to `G * H`, cast `hk : (k : ℕ∞) ≤ 2` to the `WithTop` shape expected by mathlib, then call:

```lean
norm_iteratedFDeriv_mul_le hG hH q hk'
```

There is also the gradient analogue:

```lean
ShenWork.IntervalResolverSpectralJointC2CutoffBounds.cutoffGradTerm_leibniz_bound
```

which splits

```lean
cutoffGradTerm φ gradTerm n = fun q => φ q.1 * gradTerm n q
```

and applies the same `norm_iteratedFDeriv_mul_le` pattern.

## Full concrete value-term pattern

The theorem that actually computes the bound into a summable majorant is:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete.cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
```

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

Rough type:

```lean
theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a)
    {n k : ℕ} {q : ℝ × ℝ}
    (hL : restartCutoffLeftOuter offset s ≤ q.1)
    (hR : q.1 ≤ restartCutoffRightOuter offset s)
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q‖ ≤
      concreteRestartValueMajorant a₀ src offset s hτ k n
```

This is the closest complete template for the heat sorry.

It decomposes the value term in two Leibniz layers:

1. **Outer product**

   ```lean
   cutoffValueTerm = (φ * localRestartCoeff) * cosineMode
   ```

   This is handled by `cutoffValueTerm_leibniz_bound`.

2. **Inner product**

   ```lean
   φ * localRestartCoeff
   ```

   Inside the proof, it calls `norm_iteratedFDeriv_mul_le hφ hcoeff q hiTop` again to bound

   ```lean
   ‖iteratedFDeriv ℝ i
     (fun q => restartSmoothCutoff offset s q.1 *
       localRestartCoeff a₀ a (q.1 - offset) n) q‖
   ```

   by a second Leibniz sum over `j ≤ i`.

So the final finite expression is a nested binomial sum: outer split index `i`, inner split index `j`.

## How the product of cutoff derivative bound and exponential/cosine bound is computed

The concrete value majorant is:

```lean
def concreteRestartValueMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    (offset s : ℝ) (hτ : 0 < s - offset) (k n : ℕ) : ℝ :=
  concreteRestartValueLeibnizConstant offset s hτ k *
    restartCoeffCoreMajorant a₀ src
      (restartSlabMin offset s) (restartSlabMax offset s) n
```

The finite cutoff/Leibniz constant is:

```lean
def concreteRestartValueLeibnizConstant
    (offset s : ℝ) (hτ : 0 < s - offset) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
      restartCutoffDerivMajorant offset s hτ j
```

The `n`-dependent analytic payload is entirely pushed into:

```lean
restartCoeffCoreMajorant a₀ src τmin τmax n
```

and the proof shows each inner product term is bounded by

```lean
restartCutoffDerivMajorant offset s hτ j *
  restartCoeffCoreMajorant a₀ src τmin τmax n
```

up to binomial coefficients.

The key supporting lemmas are:

```lean
restartCutoffDerivMajorant_spec
```

for the cutoff derivative bound, via

```lean
norm_iteratedFDeriv_comp_fst_le
```

and

```lean
cosineMode_iteratedFDeriv_bound
```

for the cosine derivative bound, via

```lean
norm_iteratedFDeriv_comp_snd_le
```

and

```lean
shiftedLocalRestartCoeff_valueWeight_le_core
```

for the coefficient/cosine-weight product:

```lean
‖iteratedFDeriv ℝ r
  (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t‖ *
  valueCosWeight m n ≤
  restartCoeffCoreMajorant a₀ src τmin τmax n
```

Here

```lean
def valueCosWeight (m n : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => |(n : ℝ) * Real.pi|
  | _ => unitIntervalCosineEigenvalue n
```

So the cosine derivative contribution is absorbed into `valueCosWeight`, and then `shiftedLocalRestartCoeff_valueWeight_le_core` absorbs the coefficient derivative times `valueCosWeight` into the common core majorant.

## What `restartCoeffCoreMajorant` decomposes into

The core majorant is:

```lean
def restartCoeffCoreMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin τmax : ℝ) (n : ℕ) : ℝ :=
  restartCoeffZeroModeMajorant a₀ src τmax n +
    4 * restartCoeffCubeMajorant a₀ src τmin n +
      src.sourceEigenEnvelope n + src.sourceEigenSqEnvelope n +
        src.adotEigenEnvelope n
```

For the homogeneous/exponential part, the relevant sub-majorant is:

```lean
def restartHomogeneousCubeMajorant
    (a₀ : ℕ → ℝ) (τmin : ℝ) (n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n *
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (Real.exp (-τmin * unitIntervalCosineEigenvalue n) * |a₀ n|)))
```

and

```lean
def restartCoeffCubeMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin : ℝ) (n : ℕ) : ℝ :=
  restartHomogeneousCubeMajorant a₀ τmin n + src.sourceEigenSqEnvelope n
```

This is the resolver version of “exponential decay eats the polynomial/eigenvalue weights.”  It uses a positive left edge `τmin`, giving the exponential factor

```lean
Real.exp (-τmin * unitIntervalCosineEigenvalue n)
```

and then puts enough powers of `λ_n` in front to dominate all coefficient/cosine derivative combinations up to order 2.

## Translation to `cutoffHeatTerm_iteratedFDeriv_bound`

The heat term currently is:

```lean
def cutoffHeatTerm (u₀ : intervalDomainPoint → ℝ)
    (c : ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    ((Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
      cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n q.2)
```

and the remaining sorry is:

```lean
theorem cutoffHeatTerm_iteratedFDeriv_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) (k n : ℕ) (q : ℝ × ℝ)
    (hk : (k : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤
      (2 * k + 1) ^ k *
        (unitIntervalCosineEigenvalue n ^ k * M₀ *
          Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) := by
  sorry
```

The existing resolver proof suggests the robust route should introduce heat analogues of:

```lean
restartCutoffDerivMajorant
concreteRestartValueLeibnizConstant
concreteRestartValueMajorant
```

For heat, the “coefficient core” would be a direct exponential majorant, roughly:

```lean
heatCoeffCoreMajorant c M₀ k n :=
  unitIntervalCosineEigenvalue n ^ k * M₀ *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

but the cutoff part should probably be a finite constant depending on the cutoff derivative bounds for `smoothRightCutoff (c/2) c`, analogous to:

```lean
∑ i, (k.choose i) * ∑ j, (i.choose j) * cutoffDerivMajorant c j
```

rather than a magic universal constant.  The resolver lane deliberately keeps the cutoff derivative contribution in `restartCutoffDerivMajorant ... j` and only multiplies the summable `n`-majorant by a finite constant.

That is the main implementation lesson: do not try to make the cutoff derivative bound disappear.  Split by `norm_iteratedFDeriv_mul_le`, bound all cutoff-only derivatives by a finite `c`-dependent constant, bound the exp/coefficient/cos derivative product by the summable heat exponential majorant, then multiply finite constant × summable core exactly like `concreteRestartValueMajorant`.

## Theorem names to inspect/copy

Primary:

```lean
cutoffValueTerm_leibniz_bound
cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
concreteRestartValueLeibnizConstant
concreteRestartValueMajorant
```

Supporting:

```lean
restartCutoffDerivMajorant
restartCutoffDerivMajorant_spec
norm_iteratedFDeriv_comp_fst_le
norm_iteratedFDeriv_comp_snd_le
cosineMode_iteratedFDeriv_bound
valueCosWeight
shiftedLocalRestartCoeff_valueWeight_le_core
restartCoeffCoreMajorant
restartHomogeneousCubeMajorant
restartCoeffCubeMajorant
```

Gradient-side parallel pattern:

```lean
cutoffGradTerm_leibniz_bound
cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
concreteRestartGradLeibnizConstant
concreteRestartGradMajorant
resolverSpectralConcreteGradTerm_iteratedFDeriv_bound_of_mem_slab
```
