# Q1273 (cron2) — `src_bound` for nonpositive time

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Short answer

For an **arbitrary** trajectory `u : ℝ → intervalDomainPoint → ℝ`, `srcTimeCoeff p u k t` is **not** automatically constant for `t ≤ 0`.  By definition it is just

```lean
srcTimeCoeff p u k t = (intervalNeumannResolverSourceCoeff p (u t) k).re
```

so it depends on whatever value `u t` has.

For the specific level-0 heat seed

```lean
u = ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0
```

then yes: on nonpositive time the concrete full semigroup vanishes, so the heat seed is the zero interval function.  Consequently the source slice is the zero function, and

```lean
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0
```

for every `k` and `t ≤ 0`.

Thus, on the open negative half-line `t < 0`, the coefficient is locally constant zero and all time derivatives are zero.  The bound is the trivial one:

```text
‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ = 0 ≤ builtEs H i k.
```

The right-hand inequality is just nonnegativity of `builtEs`, from the nonnegative chosen constants in `H.zerothBound` and `H.laplBound`.

However, there is an important caveat at exactly `t = 0`: being constant on `t ≤ 0` does **not** give a two-sided neighborhood of constancy at `0`.  The concrete semigroup has `S 0 f = 0`, while the positive-time heat semigroup usually tends to `f` as `t → 0⁺`.  So the zero-before-zero extension is generally **not** globally `ContDiff ℝ 2` at `0` unless additional flatness/compatibility assumptions force the right jets to vanish.  This means the global `src_contDiff : ContDiff ℝ 2 ...` obligation cannot honestly be closed from positive-time floor data plus “constant for `t ≤ 0`” alone.

## What I found in the repo

### 1. `srcTimeCoeff` definition

In `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean`, the definition is:

```lean
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re
```

`intervalNeumannResolverSourceCoeff` is the Neumann cosine coefficient of the source

```lean
p.ν * intervalDomainLift u x ^ p.γ
```

from `ShenWork/PDE/IntervalNeumannEllipticResolverR.lean`.

So the question “is it constant at `t ≤ 0`?” reduces entirely to what `u t` is for `t ≤ 0`.

### 2. `conjugatePicardIter` level 0

In `ShenWork/Paper2/IntervalConjugatePicard.lean`, level 0 is exactly the pure full-semigroup heat trajectory:

```lean
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

Therefore, for level 0, it is enough to understand `intervalFullSemigroupOperator t f` at nonpositive `t`.

### 3. Full semigroup definition

In `ShenWork/PDE/IntervalNeumannFullKernel.lean`:

```lean
def intervalNeumannFullKernel (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, (heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k))

/-- The full periodised-image Neumann heat propagator on `[0,1]`. -/
def intervalFullSemigroupOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1
```

The heat kernel is the concrete formula from `ShenWork/PDE/HeatSemigroup.lean`:

```lean
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))
```

For `t ≤ 0`, `4 * Real.pi * t ≤ 0`, hence `Real.sqrt (4 * Real.pi * t) = 0`, and Lean’s real division convention gives `1 / 0 = 0`.  Hence the prefactor is zero and `heatKernel t x = 0` for all `x`.

The repo already proves the `t = 0` special case in `ShenWork/PDE/IntervalSemigroupAtZero.lean`:

```lean
theorem intervalNeumannFullKernel_zero (x y : ℝ) :
    intervalNeumannFullKernel 0 x y = 0 := by
  unfold intervalNeumannFullKernel
  simp [heatKernel_zero]

/-- **The actual value of the propagator at time `0`.**
`intervalFullSemigroupOperator 0 f x = 0` for every `f`, `x`. -/
theorem intervalFullSemigroupOperator_zero (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_zero]
```

I did not find an existing lemma named like `intervalFullSemigroupOperator_nonpos`; add the nonpositive variant by the same definitional argument.

## The useful nonpositive-time atoms

The first atom should live near `IntervalSemigroupAtZero.lean` or `IntervalNeumannFullKernel.lean`.

```lean
import ShenWork.PDE.IntervalSemigroupAtZero
import ShenWork.PDE.IntervalNeumannFullKernel

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

/-- With the concrete Lean definition of `heatKernel`, the kernel is zero for
nonpositive time.  This is a definitional extension convention, not the analytic
heat kernel at positive time. -/
lemma heatKernel_eq_zero_of_nonpos {t x : ℝ} (ht : t ≤ 0) :
    heatKernel t x = 0 := by
  unfold heatKernel
  have harg : 4 * Real.pi * t ≤ 0 := by
    nlinarith [Real.pi_pos, ht]
  rw [Real.sqrt_eq_zero_of_nonpos harg]
  simp

/-- The full periodised Neumann kernel is zero for nonpositive time. -/
lemma intervalNeumannFullKernel_eq_zero_of_nonpos {t x y : ℝ} (ht : t ≤ 0) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  simp [heatKernel_eq_zero_of_nonpos ht]

/-- The full semigroup operator is zero for nonpositive time. -/
lemma intervalFullSemigroupOperator_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0)
    (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_eq_zero_of_nonpos ht]

end ShenWork.IntervalNeumannFullKernel
```

Then, for the source coefficient of the level-0 heat seed:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalSemigroupAtZero
import ShenWork.Paper2.IntervalConjugatePicard

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalPhysicalResolverDataConcrete
open ShenWork.IntervalPhysicalSourceTimeC2Concrete

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Nonnegativity of the constructed envelope. -/
lemma builtEs_nonneg
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) {i k : ℕ} (hi : i ≤ 2) :
    0 ≤ builtEs H i k := by
  rw [builtEs, dif_pos hi]
  by_cases hk : k = 0
  · simp [hk, (Classical.choose_spec (H.zerothBound i hi)).1]
  · have hM : 0 ≤ Classical.choose (H.laplBound i hi) :=
      (Classical.choose_spec (H.laplBound i hi)).1
    have hden : 0 ≤ ((k : ℝ) * Real.pi) ^ 2 := sq_nonneg _
    simp [hk, div_nonneg hM hden]

/-- For the level-0 heat seed, `srcTimeCoeff` is zero at nonpositive time.  The
last `simp` step is the zero-source cosine coefficient simplification: the
source is `p.ν * 0 ^ p.γ = 0`, since `p.hγ : 0 < p.γ`. -/
lemma srcTimeCoeff_heat_seed_eq_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (k : ℕ)
    {t : ℝ} (ht : t ≤ 0) :
    srcTimeCoeff p (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0) k t = 0 := by
  unfold srcTimeCoeff ShenWork.IntervalConjugatePicard.conjugatePicardIter
  have hzero_slice :
      (fun x : intervalDomainPoint =>
        intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1) = fun _ => 0 := by
    funext x
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_eq_zero_of_nonpos
      ht (intervalDomainLift u₀) x.1
  rw [hzero_slice]
  unfold ShenWork.PDE.intervalNeumannResolverSourceCoeff
  -- This should close by unfolding `unitIntervalNeumannCosineCoeff` /
  -- `unitIntervalCosineRawCoeff` and simplifying the zero source.
  -- If `simp` does not find the real-power lemma automatically, add:
  --   simp [intervalDomainLift, Real.zero_rpow (ne_of_gt p.hγ)]
  simp [intervalDomainLift, Real.zero_rpow (ne_of_gt p.hγ)]

/-- On `t < 0`, the level-0 source coefficient is locally zero. -/
lemma srcTimeCoeff_heat_seed_eventuallyEq_zero_of_neg
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (k : ℕ)
    {t : ℝ} (ht : t < 0) :
    (fun r => srcTimeCoeff p (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0) k r)
      =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds ht] with r hr
  exact srcTimeCoeff_heat_seed_eq_zero_of_nonpos p u₀ k (le_of_lt hr)

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

With the eventuallly-zero lemma, the derivative bound for `t < 0` is conceptually immediate: split `i = 0,1,2`, rewrite the function locally to the constant zero function using `EventuallyEq.deriv_eq` / the corresponding `fderiv` eventuallly-equal lemma, and finish with `builtEs_nonneg`.

Schematically:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalSemigroupAtZero
import ShenWork.Paper2.IntervalConjugatePicard

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalPhysicalResolverDataConcrete
open ShenWork.IntervalPhysicalSourceTimeC2Concrete

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Negative-time bound for the level-0 heat seed: all relevant time derivatives
vanish because the source coefficient is locally constant zero. -/
lemma srcTimeCoeff_heat_seed_bound_of_neg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p
      (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0) s₁ s₂)
    (i k : ℕ) {t : ℝ} (hi : i ≤ 2) (ht : t < 0) :
    ‖iteratedFDeriv ℝ i
        (srcTimeCoeff p (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0) k) t‖
      ≤ builtEs H i k := by
  -- Use `srcTimeCoeff_heat_seed_eventuallyEq_zero_of_neg p u₀ k ht`.
  -- Then split `i` by `interval_cases i`.
  -- Each case reduces to the corresponding derivative of `fun _ => 0`, hence norm `0`.
  -- Finish with:
  exact le_trans (by
    -- placeholder for the local-zero derivative calculation
    -- target: norm(...) ≤ 0
    sorry) (builtEs_nonneg H hi)

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

The only nontrivial bookkeeping in the last theorem is the Mathlib API for turning local equality into equality of `iteratedFDeriv` for `i = 0,1,2`.  Since `hi : i ≤ 2`, the robust route is simply:

```lean
interval_cases i
```

and handle the three cases directly.

## What happens at `t = 0`

Do **not** rely on “constant for `t ≤ 0`” to close global `ContDiff ℝ 2` at `0`.

The repo already documents the degeneracy in `IntervalSemigroupAtZero.lean`: the concrete kernel gives

```lean
intervalFullSemigroupOperator 0 f x = 0
```

for every `f`, while the genuine heat semigroup should satisfy only the one-sided approximate identity as `t → 0⁺`.  Therefore, unless the right-hand positive-time coefficient has matching zero value/first derivative/second derivative at `0`, the zero extension is not globally `C²` at `0`.

For `src_bound` alone:

* for `t < 0`, the bound is honestly `0 ≤ builtEs H i k`;
* for `t = 0`, the zeroth-order value is also zero for the heat seed, so the `i = 0` bound is again `0 ≤ builtEs H 0 k`;
* for `i = 1,2` at `t = 0`, a proof based only on Lean’s fallback value for derivatives at nondifferentiable points would be analytically misleading, and it would not solve `src_contDiff` anyway.

## Recommended fix

There are three honest options.

### Option A — positive-time physical source data

Change the consumer structure so that the source coefficient regularity/bounds are only required on `Ioi 0`, or on positive slabs.  This matches the actual `FlooredSourceTimeData` in the positive-time version of `IntervalPhysicalSourceTimeC2Concrete.lean`.

This is the cleanest if downstream PDE arguments only use `t > 0`.

### Option B — add a genuine global extension hypothesis

If `PhysicalSourceTimeC2` must remain global on all `ℝ`, add explicit hypotheses saying that the coefficient extension is globally `C²` and satisfies the global envelope.  Positive-time floor data plus semigroup zero at `t ≤ 0` is insufficient at `0`.

### Option C — prove a flat-at-zero extension, not the current semigroup value

Replace the raw concrete semigroup value at `t = 0` by a separately defined smooth cutoff/extension in time whose first two jets match at `0`.  This is a different object from the current `intervalFullSemigroupOperator`, whose definition gives `S 0 = 0`.

## Bottom line

For the level-0 heat seed and `t < 0`, the missing `src_bound` branch is trivial:

```text
srcTimeCoeff = 0 locally, so all derivatives through order 2 are 0,
and 0 ≤ builtEs H i k.
```

For `t = 0`, that same observation gives the zeroth-order bound, but it does **not** justify global `ContDiff ℝ 2` or the higher-order two-sided derivative story.  The global all-`ℝ` obligations need either a positive-time reformulation or an explicit flat/global extension hypothesis.
