# Q1520 (cron3): `laplBound` for `i = 1` and the `t → 0+` obstruction

## Short answer

No: from the current heat-level-0 hypotheses, the bound

```lean
∀ t > 0, ∀ k ≥ 1,
  |cosineCoeffs (slice1 t) k| ≤ M / ((k : ℝ) * Real.pi)^2
```

cannot be proved with one finite `M` uniform over all `t > 0`.

The integration-by-parts idea is correct for each fixed positive time, and also uniformly on every positive slab `t ≥ τ > 0`.  But the constant obtained from

```text
|ĉ_k(f)| ≤ 2 * ∫₀¹ |f''(x)| dx / (kπ)^2
```

is controlled by `∫ |slice1_xx(t,x)| dx`.  For the heat semigroup this quantity is generally singular as `t → 0+`, unless the initial datum carries extra high spatial regularity.  Heat smoothing gives smoothness for every `t > 0`; it does not give a uniform-in-`t` high-derivative bound down to `0`.

So `laplBound i=1` is a genuine analytic obstruction if `FlooredSourceTimeData` keeps the current global-positive-time form.  It is not just a convolution bookkeeping problem.

## Relevant repo facts inspected

The searched tree for the relevant source files is the indexed/default tree at commit

```text
7db6d8e4b01d279823281613bb824200483faddd
```

The main heat-level-0 file is:

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
```

It defines

```lean
def heatDu (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
      t (cosineCoeffs (intervalDomainLift u₀)) x
  else 0
```

so for positive time `heatDu = Δ S(t)u₀`.

It also defines

```lean
def heatD2u (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    ∑' k : ℕ, unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) *
      ShenWork.CosineSpectrum.cosineMode k x
  else 0
```

so for positive time `heatD2u = Δ² S(t)u₀`.

The source derivative slice is imported from

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

where

```lean
def srcSlice1 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * du t x
```

Thus, for the heat base iterate,

```text
slice1(t,x) = p.ν * p.γ * v(t,x)^(p.γ - 1) * Δv(t,x),
where v(t,x) = S(t)u₀(x).
```

The current `heatSemigroup_flooredSourceTimeData` theorem still takes the global Laplacian coefficient envelope as an input:

```lean
(hlaplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧
  ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam ... i) t) k|
      ≤ M / ((k:ℝ) * Real.pi) ^ 2)
```

That is the problematic quantifier: `∃ M` comes before `∀ t > 0`.

The existing positive-time derivative proofs already use local positive-time majorants.  For example, `heatDu_hasDerivAt` sets `r := t / 2`; the summable majorant depends on this positive lower cutoff.  This is exactly the right local-in-time shape, but it is not uniform as `t ↓ 0`.

## Why the product is worse than “derivatives up to order 2”

Let

```text
v(t,x) = S(t)u₀(x),
α = γ - 1,
w(t,x) = heatDu(t,x) = Δv(t,x) = v_xx(t,x).
```

Ignoring the harmless constant `νγ`,

```text
slice1 = v^α * w = v^α * v_xx.
```

Then

```text
∂ₓ²(v^α w)
  = α(α-1) v^(α-2) (v_x)^2 w
    + α v^(α-1) v_xx w
    + 2α v^(α-1) v_x w_x
    + v^α w_xx.
```

Since `w = v_xx`, this is

```text
∂ₓ²(v^α v_xx)
  = α(α-1) v^(α-2) (v_x)^2 v_xx
    + α v^(α-1) (v_xx)^2
    + 2α v^(α-1) v_x v_xxx
    + v^α v_xxxx.
```

So the second spatial derivative of `slice1` needs spatial derivatives of `v` up to order `4`, not just order `2`.  In spectral terms, the last term contains

```text
Δ² S(t)u₀ = ∑ λ_n^2 e^{-λ_n t} a_n cos(nπx).
```

This is finite for each `t > 0`, but the bound obtained from spectral decay depends on a positive lower time cutoff.

## Why no uniform bound follows as `t → 0+`

Assume only the current kind of heat-level-0 data:

```lean
hu₀_cont  : Continuous u₀
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
hfloor    : ∀ t > 0, ... 0 < S(t)u₀
```

These give positive-time smoothing, but not a finite bound for

```text
sup_{t>0} ∫₀¹ |∂ₓ²(v^(γ-1) Δv)(t,x)| dx.
```

A model obstruction is an initial datum with a positive floor and a slowly decaying but absolutely summable cosine tail, for example schematically

```text
u₀(x) = c + ε ∑_{n≥1} n^{-2} cos(nπx),   c > 0, ε small.
```

This is continuous and positive for small `ε`; its cosine coefficients are uniformly bounded.  But

```text
Δ² S(t)u₀(0)
  ~ ε ∑_{n≥1} (nπ)^4 n^{-2} e^{-(nπ)^2 t}
  = ε π^4 ∑_{n≥1} n^2 e^{-π² n² t},
```

which diverges as `t → 0+`.  The product factor `v^(γ-1)` remains bounded below and above on the positive floor, so the `v^α v_xxxx` contribution cannot be controlled uniformly from the current assumptions.

Even with smoother-looking estimates, the heat-kernel constants have the same issue.  Bounds of the form

```text
||∂ₓ^m S(t)u₀|| ≤ C_m(t) * ||u₀||
```

have `C_m(t)` singular as `t ↓ 0`.  Spectral estimates with `|a_n| ≤ M₀` similarly use sums such as

```text
∑ n^m e^{-c n² t},
```

which are finite for `t > 0` but blow up as `t → 0+`.

Therefore the IBP proof gives

```text
∀ τ > 0, ∃ Mτ, ∀ t ≥ τ, ∀ k ≥ 1,
  |cosineCoeffs(slice1(t), k)| ≤ Mτ / (kπ)^2,
```

not the stronger

```text
∃ M, ∀ t > 0, ∀ k ≥ 1,
  |cosineCoeffs(slice1(t), k)| ≤ M / (kπ)^2.
```

## What would make the global bound true?

There are two honest options.

### Option A: weaken `laplBound` to a local positive-time/slab bound

This is the best match for the existing heat-semigroup proof architecture.  Replace the global field by something like:

```lean
laplBound_local :
  ∀ i : ℕ, i ≤ 2 → ∀ τ : ℝ, 0 < τ →
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, τ ≤ t → ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs ((sliceFam s₀ s₁ s₂ i) t) k| ≤
          M / ((k : ℝ) * Real.pi)^2
```

or, even closer to the `d0`/`d1` style:

```lean
laplBound_near :
  ∀ i : ℕ, i ≤ 2 → ∀ τ : ℝ, 0 < τ →
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧
      (∀ t ∈ Metric.ball τ δ, ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs ((sliceFam s₀ s₁ s₂ i) t) k| ≤
          M / ((k : ℝ) * Real.pi)^2)
```

Then the proof is feasible: choose a positive lower cutoff, say `r = τ / 2`, dominate all heat traces by sums with `e^{-r λ_n}`, and use the existing summability lemmas.  This mirrors what the current positive-time differentiability code already does with `r := t / 2`.

This also aligns with the cutoff resolver strategy: if a later proof only needs regularity near a fixed `s₀ > 0`, or on the support of a cutoff that vanishes near `0`, then local positive-time bounds are exactly enough.

### Option B: keep global `∀ t > 0`, but add initial spatial regularity

If the structure really needs one `M` for all positive time, then the theorem needs extra assumptions on `u₀` beyond continuity and bounded cosine coefficients.

A sufficient kind of assumption would be something like:

```text
u₀ has enough spatial regularity that
  ∂ₓ²(u₀^(γ-1) Δu₀) ∈ L¹(0,1),
with compatible Neumann boundary behavior,
and the heat-smoothed nonlinear expression converges/bounds to it as t → 0+.
```

A clean formal sufficient package would be stronger but easier to use:

```text
u₀ ∈ C⁴([0,1]),
Neumann/compatibility conditions as needed,
0 < c ≤ u₀(x),
and all derivatives up to order 4 are bounded.
```

Then `v = S(t)u₀` has derivatives up to order 4 uniformly down to `t = 0`, and the product formula above gives a uniform `L¹` bound for `slice1_xx`.

But that is a different theorem.  It is not derivable from the current heat-level-0 assumptions.

## Lean-facing recommendation

Do not try to prove the current global `hlaplBound` for `i = 1` from the existing hypotheses.

The minimal honest fix is to change the `FlooredSourceTimeData` Laplacian coefficient envelope from global-positive-time to local-positive-time.  Then prove the `i = 1` obligation on a slab by:

1. Fix `τ > 0` and choose `r = τ / 2`.
2. Establish bounds for `v`, `v_x`, `v_xx`, `v_xxx`, `v_xxxx` on `t ≥ τ` using spectral majorants with `e^{-r λ_n}`.
3. Use the product formula for `∂ₓ²(v^(γ-1) v_xx)` plus the positive floor for the `rpow` factors.
4. Conclude `∫ |slice1_xx| ≤ Mτ`.
5. Apply the Neumann IBP cosine-coefficient estimate to get the `(kπ)⁻²` envelope.

Classify this obligation as:

```text
genuine analytic obstruction for the current global statement;
mechanical/wirable after changing the field to local-positive-time, or after adding C⁴-type initial data.
```
