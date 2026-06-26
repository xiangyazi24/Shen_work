# Q733 (cron2): Mathlib / Shen_work search for `contDiff_tsum` mixed-product bounds

Static repo inspection only; I did not run a Lean build.  Mathlib files below were inspected at tag/ref `v4.29.1` where possible.

## Executive verdict

Yes: Mathlib v4.29.1 has exactly the kind of **norm bound** needed for products, though not phrased as a special “separate variables mixed partials factor” theorem.

The key theorem is:

```lean
norm_iteratedFDeriv_mul_le
```

from:

```text
Mathlib/Analysis/Calculus/ContDiff/Bounds.lean
```

It states, for scalar/normed-ring product:

```lean
theorem norm_iteratedFDeriv_mul_le
    {f : E → A} {g : E → A} {N : WithTop ℕ∞}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g)
    (x : E) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ *
          ‖iteratedFDeriv 𝕜 (n - i) g x‖
```

There is also the more general bilinear version:

```lean
ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear
```

and the within-set versions:

```lean
ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear
norm_iteratedFDerivWithin_mul_le
```

So for

```lean
f_n q = a n * Real.exp (-q.1 * λ n) * Real.cos ((n : ℝ) * Real.pi * q.2)
```

you do **not** need to prove a custom mixed-partial factorization theorem.  Use:

1. `norm_iteratedFDeriv_mul_le` for the product;
2. a first-coordinate projection bound for the time factor;
3. a second-coordinate projection bound for the spatial cosine factor;
4. explicit 1D bounds for `iteratedFDeriv` of `t ↦ a_n * exp(-t λ_n)` and `x ↦ cos(nπx)`.

Shen_work already has exactly this pattern for terms of the form

```lean
fun q : ℝ × ℝ => c n q.1 * cosineMode n q.2
```

in:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

The relevant theorem is:

```lean
theorem boundedWeightJointTerm_iteratedFDeriv_le
```

It calls `norm_iteratedFDeriv_mul_le`, then uses projection lemmas for `q.1` and `q.2`, then feeds the resulting majorant to `contDiff_tsum` in

```lean
theorem boundedWeightJointSeries_contDiff_two
```

This is probably the best template for your new heat-semigroup term.

## Mathlib results found

### 1. General bilinear product bound

File:

```text
Mathlib/Analysis/Calculus/ContDiff/Bounds.lean
```

Relevant theorem:

```lean
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear
    (B : E →L[𝕜] F →L[𝕜] G)
    {f : D → E} {g : D → F} {N : WithTop ℕ∞}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g)
    (x : D) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ *
          ‖iteratedFDeriv 𝕜 (n - i) g x‖
```

This is the direct abstract version of the desired Leibniz/mixed-order estimate.

### 2. Multiplication-specialized bound

Same file:

```lean
theorem norm_iteratedFDeriv_mul_le
    {f : E → A} {g : E → A} {N : WithTop ℕ∞}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g)
    (x : E) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ *
          ‖iteratedFDeriv 𝕜 (n - i) g x‖
```

This is usually the one to use for real-valued terms.

The theorem is derived from multiplication as a continuous bilinear map:

```lean
ContinuousLinearMap.mul 𝕜 A : A →L[𝕜] A →L[𝕜] A
```

with operator norm at most `1`.

### 3. Finite product bound

Same file also has:

```lean
norm_iteratedFDeriv_prod_le
```

for products over a finite set.  This is useful if the term is a product of more than two factors, but for your heat-cosine mode the binary product theorem is simpler.

### 4. `contDiff_tsum`

File:

```text
Mathlib/Analysis/Calculus/SmoothSeries.lean
```

Relevant theorem:

```lean
theorem contDiff_tsum
    (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), k ≤ N →
      ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x
```

There are also:

```lean
iteratedFDeriv_tsum
iteratedFDeriv_tsum_apply
contDiff_tsum_of_eventually
```

The important point: `contDiff_tsum` wants **summable uniform bounds** `v k i` for each derivative order `k ≤ N`, uniform in the base point `x`.  Merely proving `ContDiff` of each term is not enough.

## Shen_work examples found

### 1. Exact product-bound template: bounded-weight resolver joint term

File:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

Definitions:

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2
```

```lean
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

Key theorem:

```lean
theorem boundedWeightJointTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      boundedWeightJointMajorant Bt k n
```

Inside the proof, it does exactly this:

```lean
have hprod := norm_iteratedFDeriv_mul_le hcj hcos q hkTop
```

then bounds the time factor via `norm_iteratedFDeriv_comp_fst_le` and the spatial factor via `norm_iteratedFDeriv_comp_snd_le` plus `cosineMode_iteratedFDeriv_bound`.

The assembler is:

```lean
theorem boundedWeightJointSeries_contDiff_two ... :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q) :=
  contDiff_tsum ...
```

This is the exact pattern to copy.

### 2. Projection helper lemmas

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2CutoffBounds.lean
```

Useful lemmas:

```lean
theorem norm_iteratedFDeriv_comp_fst_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.1) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.1‖
```

```lean
theorem norm_iteratedFDeriv_comp_snd_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.2) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.2‖
```

These are not generic Mathlib names; they are Shen_work helper lemmas built from `ContinuousLinearMap.fst/snd` and `iteratedFDeriv_comp_right`.

### 3. Another direct product-bound example

Same file has:

```lean
theorem cutoffValueTerm_leibniz_bound
```

It rewrites a cutoff value term as a product and then does:

```lean
norm_iteratedFDeriv_mul_le hG hH q hk'
```

This is a compact small example of using the Mathlib product bound.

### 4. A simple fixed-time heat-series `contDiff_tsum` example

File:

```text
ShenWork/Paper2/IntervalCD6HeatSmoothness.lean
```

The theorem

```lean
theorem unitIntervalCosineHeatValue_contDiff_seven
```

uses `contDiff_tsum` for the fixed-time spatial heat series.  Since `t` is fixed there, it avoids mixed `(t,x)` derivatives and only bounds spatial derivatives:

```lean
let v : ℕ → ℕ → ℝ := fun k n =>
  |(n : ℝ) * Real.pi| ^ k *
    Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|
```

This is useful for the purely spatial heat-value route, but for joint `(t,x)` smoothness the `IntervalResolverJointC2Physical` pattern is closer.

## About the proposed “simpler approach”

> Since each `f_n` is `ContDiff ℝ ⊤`, can I just use `norm_iteratedFDeriv_le_of_bound` or similar?

Not by itself.

`ContDiff` gives smoothness of each term and continuity of each iterated derivative, but `contDiff_tsum` needs a **summable uniform majorant**:

```lean
∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i
```

with `Summable (v k)`.

For the full domain `ℝ × ℝ`, the heat factor

```lean
Real.exp (-t * λ_n)
```

is not uniformly bounded in `t`, because it blows up as `t → -∞` when `λ_n > 0`.  So a global-on-`ℝ×ℝ` summable majorant for the heat terms is generally false unless you insert a cutoff or restrict the time domain.

On a positive slab, e.g.

```lean
t ∈ Icc c T,  0 < c
```

you can use

```lean
Real.exp (-t * λ_n) ≤ Real.exp (-c * λ_n)
```

and get a summable majorant of the form, schematically,

```lean
|a_n| * ∑ i ∈ Finset.range (k+1),
  (k.choose i : ℝ) * λ_n^i * Real.exp (-c * λ_n) * |nπ|^(k-i)
```

or any cruder summable polynomial-times-exponential bound.

If the term is cutoff-supported in time, another route is compact-support/compactness: Shen_work uses this style for `restartSmoothCutoff_iteratedFDeriv_bound_exists`, deriving a bound on each cutoff derivative from `ContDiff.continuous_iteratedFDeriv` plus compact support.  But for the raw heat kernel on all `ℝ`, explicit positive-time exponential bounds are the right route.

## Recommended implementation route for your term

For each mode, define or rewrite into:

```lean
G n q := a n * Real.exp (-q.1 * λ n)
H n q := cosineMode n q.2
f n q := G n q * H n q
```

Then:

```lean
have hG : ContDiff ℝ N (G n) := by fun_prop
have hH : ContDiff ℝ N (H n) := by
  have hcos : ContDiff ℝ N (cosineMode n) := by
    unfold cosineMode; fun_prop
  exact hcos.comp contDiff_snd

have hprod := norm_iteratedFDeriv_mul_le hG hH q hk
```

For a cleaner bound, follow the repo’s existing abstraction:

```lean
norm_iteratedFDeriv_comp_fst_le
norm_iteratedFDeriv_comp_snd_le
cosineMode_iteratedFDeriv_bound
```

and build a majorant analogous to:

```lean
boundedWeightJointMajorant Bt k n
```

For the heat term on `t ≥ c`, take the time derivative bound roughly as:

```lean
Bt i n := |a n| * λ_n^i * Real.exp (-c * λ_n)
```

Then the joint majorant is:

```lean
∑ i ∈ Finset.range (k+1),
  (k.choose i : ℝ) * Bt i n * valueCosWeight (k-i) n
```

and `contDiff_tsum` consumes exactly this shape.

## Bottom line

Use `norm_iteratedFDeriv_mul_le`; do not try to prove a new mixed partial formula unless you need exact equality.  Shen_work already contains the needed blueprint in `IntervalResolverJointC2Physical.boundedWeightJointTerm_iteratedFDeriv_le` and `boundedWeightJointSeries_contDiff_two`.
