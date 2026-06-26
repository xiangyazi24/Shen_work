# Q737 (cron2): smooth cutoff pattern for `contDiff_tsum`

Static repo inspection only; I did not run a Lean build.

## Executive verdict

The repo has a fully explicit smooth-cutoff infrastructure for the resolver restart-series `contDiff_tsum` route.

The cutoff is **not** built from `SmoothBumpFunction`.  It is built explicitly from Mathlib’s

```lean
Real.smoothTransition
```

via a one-sided cutoff:

```lean
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))
```

and then a compact two-sided bump

```lean
restartSmoothCutoff offset s t
```

as a product of two `smoothRightCutoff`s, one on the left and one applied to `-t` on the right.

I found **no existing heat-semigroup-specific** theorem of the form “heat semigroup + cutoff → `contDiff_tsum`.”  The closest existing code is the resolver restart homogeneous tail, which already uses the compact cutoff support to reduce global bounds to a positive compact restart-time slab and then bounds homogeneous factors by an exponential with the positive left edge `τmin`.

So for heat level 0, the recommended path is: copy/adapt the existing `restartSmoothCutoff` pattern and the `cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound` style, replacing `localRestartCoeff` by the homogeneous heat coefficient `Real.exp (-t * λ_n) * a₀ n`.

## 1. Smooth cutoff infrastructure

### File

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

This file imports:

```lean
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
```

and defines the one-sided cutoff:

```lean
/-- Smooth right cutoff equal to `0` on `(-∞, c']` and `1` on `[c, ∞)`. -/
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))
```

It proves:

```lean
smoothRightCutoff_contDiff
smoothRightCutoff_eq_zero_of_le
smoothRightCutoff_eq_one_of_ge
smoothRightCutoff_eventually_eq_one
```

So the primitive cutoff is explicit `Real.smoothTransition`, not a bundled `SmoothBumpFunction`.

## 2. `cutoffValueTerm`

### File

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

Definition:

```lean
/-- Cutoff-localized value term. -/
def cutoffValueTerm
    (φ : ℝ → ℝ) (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n *
    cosineMode n q.2
```

The same file also defines:

```lean
/-- Cutoff-localized gradient term. -/
def cutoffGradTerm (φ : ℝ → ℝ) (gradTerm : ℕ → ℝ × ℝ → ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * gradTerm n q
```

The generic `contDiff_tsum` wrapper is:

```lean
theorem resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
```

It takes:

* an arbitrary cutoff `φ : ℝ → ℝ`,
* `hφ_one : φ =ᶠ[𝓝 s] fun _ => 1`,
* termwise `ContDiff` for the cutoff value and gradient terms,
* summable majorants for `vValue` and `vGrad`,
* iterated derivative bounds for the cutoff terms,
* a gradient eventual-equality input.

Then it applies `contDiff_tsum` globally and transfers the result back to the original local series using `EventuallyEq` near `(s,x)`.

## 3. How the compact cutoff is constructed

### File

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

It first defines four edges around the target time `s` and `offset`:

```lean
def restartCutoffLeftOuter (offset s : ℝ) : ℝ :=
  offset + (s - offset) / 4

def restartCutoffLeft (offset s : ℝ) : ℝ :=
  offset + (s - offset) / 3

def restartCutoffRight (offset s : ℝ) : ℝ :=
  s + (s - offset) / 3

def restartCutoffRightOuter (offset s : ℝ) : ℝ :=
  s + (s - offset) / 2
```

Then the two-sided cutoff is:

```lean
/-- Concrete two-sided smooth cutoff supported in a compact slab around the
 target time and equal to one near the target time. -/
def restartSmoothCutoff (offset s : ℝ) : ℝ → ℝ :=
  fun t =>
    smoothRightCutoff (restartCutoffLeftOuter offset s)
        (restartCutoffLeft offset s) t *
      smoothRightCutoff (-(restartCutoffRightOuter offset s))
        (-(restartCutoffRight offset s)) (-t)
```

The file proves the ordering of those edges, plus:

```lean
restartSmoothCutoff_contDiff
restartSmoothCutoff_eventually_eq_one
restartSmoothCutoff_eq_zero_of_le_left
restartSmoothCutoff_eq_zero_of_right_le
restartSmoothCutoff_eq_one_of_mem_core
restartSmoothCutoff_hasCompactSupport
restartSmoothCutoff_iteratedFDeriv_bound_exists
restartCutoffDerivMajorant
restartCutoffDerivMajorant_spec
```

Key facts:

* `restartSmoothCutoff_eventually_eq_one hτ` gives `φ = 1` near the target `s`.
* `restartSmoothCutoff_eq_zero_of_le_left` and `_of_right_le` give zero outside the compact slab.
* `restartSmoothCutoff_hasCompactSupport` packages compact support.
* `restartCutoffDerivMajorant_spec` gives global bounds on the derivatives of the cutoff itself.

## 4. Concrete cutoff + `contDiff_tsum` instantiation

### Generic no-cutoff assembler

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Assemble.lean
```

This has the direct non-cutoff skeleton:

```lean
def resolverSpectralValueTerm ... :=
  fun q => localRestartCoeff a₀ a (q.1 - offset) n * cosineMode n q.2
```

and:

```lean
theorem resolverSpectralJointC2At_of_contDiff_tsum
```

It simply assumes termwise `ContDiff`, summability, and bounds, then calls `contDiff_tsum` for the value and gradient series.

### Cutoff wrapper

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

The cutoff wrapper:

```lean
resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
```

is the local version that inserts `φ`, proves the cutoff series is globally `ContDiff`, and transfers back to the original series near the target because `φ = 1` there.

### Concrete restart instantiation

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

This file instantiates the generic cutoff wrapper with:

```lean
φ := restartSmoothCutoff offset s
```

The final theorem is:

```lean
/-- Concrete cutoff instantiation of the generic producer. -/
theorem resolverSpectralJointC2At_of_restartSmoothCutoff
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ResolverSpectralJointC2At a₀ a offset s x :=
  resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    (φ := restartSmoothCutoff offset s)
    (gradTerm := resolverSpectralConcreteGradTerm a₀ a offset)
    (vValue := concreteRestartValueMajorant a₀ src offset s hτ)
    (vGrad := concreteRestartGradMajorant a₀ src offset s hτ)
    (restartSmoothCutoff_eventually_eq_one hτ)
    (cutoffValueTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartValueMajorant_summable hτ ha₀ src)
    (cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src)
    (cutoffGradTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartGradMajorant_summable hτ ha₀ src)
    (cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src)
    (resolverSpectralGradSeries_eventuallyEq_concreteGradTerm hτ ha₀ src)
```

This is the full “smooth cutoff + global `contDiff_tsum` + local equality” pattern.

## 5. How the bounds use compact support / positive slab

The concrete file defines:

```lean
def restartSlabMin (offset s : ℝ) : ℝ :=
  restartCutoffLeftOuter offset s - offset

def restartSlabMax (offset s : ℝ) : ℝ :=
  restartCutoffRightOuter offset s - offset
```

and proves:

```lean
restartSlabMin_pos
restartSlabMin_le_of_mem_support_slab
restartSlabMax_ge_of_mem_support_slab
```

This is the exact mechanism that prevents bad behavior outside the positive-time region: on the support of the cutoff, restart time `t - offset` is bounded below by `restartSlabMin offset s > 0`.  Outside that support, the cutoffed term has derivative zero by eventual equality to `0`.

For the homogeneous/restart heat tail, the relevant majorant is:

```lean
def restartHomogeneousCubeMajorant
    (a₀ : ℕ → ℝ) (τmin : ℝ) (n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n *
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (Real.exp (-τmin * unitIntervalCosineEigenvalue n) * |a₀ n|)))
```

and it is summable when `0 < τmin` and `|a₀ n| ≤ M`:

```lean
theorem restartHomogeneousCubeMajorant_summable
```

This is close to the heat-semigroup need: replace raw `Real.exp (-t λ_n)` by the uniform positive-slab bound `Real.exp (-τmin λ_n)`.

The global bound lemmas split into:

* zero outside the cutoff support:
  ```lean
  cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
  cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_right
  cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
  cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_right
  ```
* bounds inside the support slab:
  ```lean
  cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
  cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
  ```
* global bounds by case split on left/outside/right:
  ```lean
  cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
  cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound
  ```

## 6. Existing “heat semigroup + cutoff → contDiff_tsum” combination?

I searched for combinations involving heat terms and cutoff terms, including:

```text
unitIntervalCosineHeatValue restartSmoothCutoff
heatValue contDiff_tsum cutoff
smoothRightCutoff heat
```

I did **not** find a dedicated theorem that directly proves heat semigroup joint smoothness using this cutoff pattern.

The existing cutoff machinery is resolver/restart-specific:

* `cutoffValueTerm` uses `localRestartCoeff a₀ a (q.1 - offset) n`, not raw `Real.exp (-q.1 * λ_n) * a₀ n`.
* `restartCoeffCoreMajorant` combines homogeneous restart, Duhamel, source envelopes, and derivative envelopes.
* The homogeneous part already contains the exact exponential-positive-slab idea via `restartHomogeneousCubeMajorant`.

So for a heat-only proof, there is no ready-made final theorem, but there is a very close blueprint.

## 7. Suggested heat-level adaptation

For heat semigroup level 0, define a heat-specific cutoff term, something like:

```lean
def heatCutoffValueTerm
    (φ : ℝ → ℝ) (a₀ : ℕ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * (Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * a₀ n) *
    cosineMode n q.2
```

Then copy the resolver pattern:

1. Use `restartSmoothCutoff offset s` with `offset` chosen so the support slab has positive left edge.  For a target `s > 0`, `offset := 0` works if the left edge is positive; in the existing construction, `restartCutoffLeftOuter 0 s = s/4`, so the support stays in positive time.
2. Prove termwise `ContDiff` via:
   ```lean
   restartSmoothCutoff_contDiff.comp contDiff_fst
   ```
   plus `fun_prop` for the exponential and cosine factors.
3. Prove zero outside the cutoff support with the existing:
   ```lean
   restartSmoothCutoff_eq_zero_of_le_left
   restartSmoothCutoff_eq_zero_of_right_le
   ```
4. On the support, use the positive lower bound:
   ```lean
   restartSlabMin offset s ≤ q.1 - offset
   ```
   and hence, for heat time `q.1`, a bound like:
   ```lean
   Real.exp (-q.1 * λ_n) ≤ Real.exp (-(restartSlabMin offset s) * λ_n)
   ```
   when `λ_n ≥ 0`.
5. Use Mathlib/Shen_work product bounds (`norm_iteratedFDeriv_mul_le`) exactly as in the resolver cutoff proof.
6. Feed the resulting summable majorant into `resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum` if your target can be cast into that abstraction, or into a new heat-specific analogue of that wrapper.

## Bottom line

The smooth cutoff pattern is fully landed for resolver restart series.  The bump is explicit `Real.smoothTransition`-based, not `SmoothBumpFunction`.  `cutoffValueTerm` is defined in `IntervalResolverSpectralJointC2Cutoff.lean`.  The concrete compact cutoff `restartSmoothCutoff` is in `IntervalResolverSpectralJointC2Concrete.lean`, and the final concrete producer is `resolverSpectralJointC2At_of_restartSmoothCutoff`.

I found no existing heat-semigroup-specific cutoff+`contDiff_tsum` theorem, but the resolver code gives a direct implementation template, and its homogeneous restart majorant already encodes the key positive-slab exponential bound needed for heat semigroup terms.
