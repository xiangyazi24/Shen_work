# Q1038 (cron2/cron1) — coefficient decay of `ν·(S(t)u₀)^γ` at positive time

Static repo inspection only; I did **not** run Lean.

I read:

- `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`
- `ShenWork/PDE/IntervalSourceDecayQuantitative.lean`
- `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean`
- `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean`
- `ShenWork/PDE/IntervalDuhamelSourceTimeC2Coeff.lean`
- `ShenWork/PDE/IntervalResolverSpectralTimeC2.lean`
- `ShenWork/Paper2/IntervalResolverLevel0SpectralC2Coeff.lean`
- `ShenWork/Paper2/IntervalSpatialC6Certificate.lean`
- `ShenWork/Paper2/IntervalCD6HeatSmoothness.lean`

## Executive verdict

For the **linear heat profile**

```lean
u(t,x) = S(t)u₀ = ∑ k, exp(-t λ_k) û₀_k cos(kπx),
```

the repo has exponential heat-tail summability and finite high spatial regularity at positive time.

For the **nonlinear source**

```lean
srcSlice p u t x = p.ν * intervalDomainLift (u t) x ^ p.γ
```

where `u = conjugatePicardIter p u₀ 0`, the repo does **not** currently prove exponential coefficient decay.  Existing source-decay infrastructure is polynomial/IBP based:

- depth 1 weak-H² gives quadratic decay `(kπ)⁻²`;
- depth 2 weak-H² tower gives quartic decay `(kπ)⁻⁴`;
- there is no committed depth 3 / sextic coefficient-decay theorem that would give `(kπ)⁻⁶`.

So:

1. Mathematically, exponential decay of `ν·(S(t)u₀)^γ` is plausible/true under a positive floor and an analytic-strip argument, because heat smoothing makes `S(t)u₀` real analytic for `t>0` and `rpow` is analytic on a positive range.  But this is **not in the repo**.
2. From the existing Lean infrastructure, the safe route is finite-order Sobolev/IBP, not exponential.
3. For `DuhamelSourceTimeC2Coeff`, λ²-weighted source envelopes require at least **sextic** coefficient decay, i.e. depth-3 IBP / H⁶-type Neumann data for each relevant time-order slice.  Quadratic and quartic are insufficient for λ² summability.
4. However, note an important route distinction: `PhysicalSourceTimeC2Concrete` deliberately avoids `DuhamelSourceTimeC2Coeff`.  It needs only `(kπ)⁻²` source-side envelopes because the elliptic resolver weight `wₖ = 1/(μ+λₖ)` is folded in and cancels the spectral growth.  So the physical resolver lane may be fillable with existing-style H² data; the older/alternate `DuhamelSourceTimeC2Coeff` lane needs new stronger analysis.

## What the repo currently proves for the heat semigroup

`IntervalHeatSemigroupHighRegularity.lean` has:

```lean
theorem heatSemigroup_eigenvalueSq_summable
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 *
      |Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k|)
```

and:

```lean
theorem heatSemigroup_contDiff_four
    ... {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 4 (fun x => ∑' k,
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x)
```

It also exposes the general exponential tail summability:

```lean
theorem eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m *
        Real.exp (-τ * unitIntervalCosineEigenvalue n))
```

and the coefficient-weighted version:

```lean
theorem eigenvalue_pow_mul_coeff_exp_summable
    (m : ℕ) {M₀ c : ℝ} (hc : 0 < c) (_hM₀ : 0 ≤ M₀) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m * M₀ *
        Real.exp (-c * unitIntervalCosineEigenvalue n))
```

Those are statements about the **linear heat coefficients**.

The same file also proves cutoff-based joint `C²` of the heat semigroup series, but again for the linear heat terms.

`IntervalCD6HeatSmoothness.lean` and `IntervalSpatialC6Certificate.lean` push finite heat smoothness further:

```lean
theorem unitIntervalCosineHeatValue_contDiff_seven
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 7 (fun x => unitIntervalCosineHeatValue t a x)
```

and:

```lean
theorem cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable
    {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * |b n|)))) :
    ContDiff ℝ 6 (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x)
```

These are useful finite-regularity tools, but they still do not prove exponential decay of the nonlinear source coefficients.

## What `srcTimeCoeff` is

In `IntervalPhysicalResolverDataConcrete.lean`:

```lean
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re
```

The file comments identify this as the `k`-th cosine coefficient of the chemotaxis source

```lean
x ↦ p.ν * u(t,x)^p.γ
```

and `IntervalPhysicalSourceTimeC2Concrete.lean` makes the identity explicit:

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ

theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k
```

So all decay questions about `srcTimeCoeff p u k t` are exactly decay questions about cosine coefficients of the nonlinear spatial slice `x ↦ ν·u(t,x)^γ`.

## Existing source-decay infrastructure

`IntervalSourceDecayQuantitative.lean` has the weak-H² quantitative theorem:

```lean
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB : (∫ x in (0:ℝ)..1, |hf.secondDeriv x|) ≤ B) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2
```

and depth-2 / H⁴-style quartic decay:

```lean
theorem intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    {B₂ : ℝ} (hB₂ : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4
```

It also proves:

```lean
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|)
```

This is λ¹ summability, not λ² summability.

I did **not** find a committed sextic/depth-3 coefficient-decay theorem of the form:

```lean
|cosineCoeffs f k| ≤ C / ((k : ℝ) * Real.pi) ^ 6
```

or:

```lean
Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 * |cosineCoeffs f k|)
```

from an H⁶ Neumann tower.

## Route distinction: physical lane vs `DuhamelSourceTimeC2Coeff` lane

This is crucial.

### Physical resolver lane

`IntervalPhysicalSourceTimeC2Concrete.lean` explicitly says it builds source-side `C²`-in-time / `(kπ)⁻²`-spatial data and does **not** route through `DuhamelSourceTimeC2Coeff` or an eigen-cube ladder.

Its central structure is:

```lean
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  d0 : ...
  d1 : ...
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)
  sliceNeumann : ...
  zerothBound : ...
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

Then:

```lean
def builtEs ...
```

uses only the zeroth-mode bound and `(kπ)⁻²` bound, and:

```lean
theorem physicalSourceTimeC2_of_floored
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m ≤ 2, Summable (boundedWeightJointMajorant
      (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m ≤ 2, Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

This route can work with quadratic decay because the resolver weight is folded in:

```lean
wₖ = 1 / (μ + λₖ)
```

and the weighted majorants see `wₖ·Es` rather than `Es` alone.

### `DuhamelSourceTimeC2Coeff` lane

`IntervalResolverSpectralTimeC2.lean` defines:

```lean
structure DuhamelSourceTimeC2Coeff (a : ℝ → ℕ → ℝ) where
  toTimeC1 : DuhamelSourceTimeC1 a
  sourceEigenEnvelope : ℕ → ℝ
  sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |a s n| ≤ sourceEigenEnvelope n
  sourceEigenSqEnvelope : ℕ → ℝ
  sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |a s n|) ≤ sourceEigenSqEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |toTimeC1.adot s n| ≤ adotEigenEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |toTimeC1.adot s n|) ≤ adotEigenSqEnvelope n
```

So yes: this route requires λ²-summable envelopes for the source family `a` and its time derivative `adot`.

In `IntervalResolverLevel0SpectralC2Coeff.lean`, the Level0 spectral-C2 agreement theorem has a `srcC2` sorry:

```lean
have srcC2 : DuhamelSourceTimeC2Coeff a := by
  -- TODO: build the strengthened source package for
  --   a ρ k = c'_k(offset+ρ) + λ_k c_k(offset+ρ),
  -- where c_k(t) = resolverTimeCoeff p u k t.
  -- Required fields:
  --   * DuhamelSourceTimeC1 a: ...
  --   * λ-weighted and λ²-weighted envelopes for a;
  --   * λ-weighted and λ²-weighted envelopes for adot.
  -- For Level0 heat, these should come from positive-time exponential
  -- heat smoothing, resolver weight `1/(μ+λ_k)`, and the source-side
  -- `srcTimeCoeff_contDiff`/bounds.  This is not presently packaged in
  -- the repo; the committed physical resolver lane bypasses this structure.
  sorry
```

That comment is accurate.

## Q1. Does `ν·u(t)^γ` still have exponential coefficient decay?

Mathematically: likely yes, under a positive floor and analytic-strip control.

At positive time, `S(t)u₀` is real analytic in space.  If it is bounded below by a positive constant on the real interval, then in a sufficiently small complex strip it stays away from zero; the map `z ↦ z^γ` can be defined with a holomorphic branch there.  Therefore `ν·(S(t)u₀)^γ` is analytic in a strip, which implies exponential cosine coefficient decay.

But in the current repo: no, this is not available as a theorem.  The repo has:

```lean
heatSemigroup_eigenvalueSq_summable
heatSemigroup_contDiff_four
heatSemigroup_jointContDiffAt_two
unitIntervalCosineHeatValue_contDiff_seven
```

for the linear heat series, and polynomial IBP decay for nonlinear source slices.  It does not have a real/complex analytic composition theorem for `Real.rpow` under a positive floor, nor an exponential coefficient-decay theorem for `srcTimeCoeff p (conjugatePicardIter p u₀ 0)`.

So for Lean, answer: **not currently proved; only polynomial finite-order decay is available for the nonlinear source.**

## Q2. If nonlinear source only has polynomial decay, how get λ² summability?

Need higher spatial regularity than H²/H⁴.

Let `λ_k = (kπ)^2`.  Suppose

```lean
|a_k| ≤ C / (kπ)^(2j)
```

from depth-`j` integration by parts.  Then

```text
λ_k^2 |a_k| ~ (kπ)^4 · C/(kπ)^(2j)
              = C/(kπ)^(2j-4).
```

The series over `k` converges iff

```text
2j - 4 > 1,
```

so:

```text
j ≥ 3.
```

Therefore:

- quadratic decay (`j=1`, `(kπ)⁻²`) is not enough;
- quartic decay (`j=2`, `(kπ)⁻⁴`) is still not enough for λ², since `λ²·(kπ)⁻⁴ ~ constant`;
- sextic decay (`j=3`, `(kπ)⁻⁶`) is enough, since `λ²·(kπ)⁻⁶ ~ (kπ)⁻²`, summable.

So if avoiding analytic/exponential estimates, the minimal integer-depth IBP route is depth 3 / H⁶ Neumann data for every coefficient family that must satisfy a λ² envelope.

The repo currently has depth-1 and depth-2 source-decay results, but I did not find the depth-3 sextic theorem.  It would need a new lemma, e.g.

```lean
theorem intervalWeakH6Neumann_cosineCoeff_sextic_decay_of_bound
    {f : ℝ → ℝ}
    (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    (hf'''' : IntervalWeakH2Neumann hf''.secondDeriv)
    {B₃ : ℝ}
    (hB₃ : (∫ x in (0:ℝ)..1, |hf''''.secondDeriv x|) ≤ B₃) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₃ / ((k : ℝ) * Real.pi) ^ 6
```

and then:

```lean
theorem intervalWeakH6Neumann_eigenvalueSq_L1_summable ... :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (unitIntervalCosineEigenvalue k * |cosineCoeffs f k|))
```

## Q3. What about the derivative `∂ₜ(ν·u^γ)`?

For heat Level0:

```text
∂ₜ(ν·u^γ) = ν·γ·u^(γ-1)·∂ₜu
           = ν·γ·u^(γ-1)·Δu.
```

This is worse than the zero-th time source because `Δu` contains two spatial derivatives of heat.  However heat smoothing at positive time still gives arbitrary finite spatial regularity, and analytically it still has exponential coefficient decay if the same analytic-strip route is developed.

For the polynomial/IBP route, each time derivative costs heat regularity:

- `s₀ = ν·u^γ` requires enough spatial derivatives of `u` to show `s₀ ∈ H⁶_N` if λ² envelopes are needed.
- `s₁ = ν·γ·u^(γ-1)·Δu` requires enough spatial derivatives of both `u` and `Δu`; in practice this means `u` needs at least two more derivatives than the target regularity of `s₁`.
- `s₂ = ∂ₜ²(ν·u^γ)` contains terms like

```text
ν·γ·(γ-1)·u^(γ-2)·(Δu)^2 + ν·γ·u^(γ-1)·Δ²u,
```

so it needs still more heat regularity.

Because heat Level0 is smooth for `t ≥ c > 0`, this is mathematically fine for any finite order.  But the repo only has selected finite-order pieces wired.  Existing `FlooredSourceTimeData` in `IntervalPhysicalSourceTimeC2Concrete.lean` only asks for space `C²`/Neumann data for `s₀,s₁,s₂`, giving `(kπ)⁻²` envelopes, because that physical lane only needs those after the resolver weight.

For `DuhamelSourceTimeC2Coeff`, the analogous data would have to be upgraded to H⁶/depth-3 for `a` and `adot`, or to exponential estimates.

## Q4. Minimal regularity for λ²-summable envelopes

For cosine coefficients on `[0,1]` with Neumann IBP in even orders:

```text
H² depth 1  → |a_k| = O(k⁻²)
H⁴ depth 2  → |a_k| = O(k⁻⁴)
H⁶ depth 3  → |a_k| = O(k⁻⁶)
```

Since `λ_k² ~ k⁴`, λ² summability requires:

```text
∑ k⁴ |a_k| < ∞.
```

The minimal integer IBP depth is depth 3:

```text
k⁴ · k⁻⁶ = k⁻²,
```

and `∑ k⁻²` converges.

So yes: depth-`j` IBP giving `(kπ)^(-2j)` is sufficient for λ² at `j=3`.  It is also essentially the minimal finite-depth Neumann IBP route.

If the route needs λ³ envelopes, then depth 4 / H⁸ would be needed, since

```text
λ³ · k⁻⁸ ~ k⁶ · k⁻⁸ = k⁻².
```

The `DuhamelSourceTimeC2Coeff` structure itself asks λ² for `a` and `adot`, but downstream local restart coefficient cube summability can involve λ³ of restart coefficients.  The committed `IntervalSpatialC6Certificate.lean` consumes `DuhamelSourceTimeC2Coeff` to get C⁶ of Duhamel/restart series, rather than asking source coefficients directly for λ³.

## Does existing infrastructure fill `srcC2`?

For the `PhysicalSourceTimeC2`/physical resolver lane: maybe yes in spirit, with existing-style H² infrastructure, because it was designed to bypass the λ²/eigen-cube ladder.

For the `DuhamelSourceTimeC2Coeff` lane in Q1034 / `IntervalResolverLevel0SpectralC2Coeff.lean`: no, not from the currently committed source-decay infrastructure.

The `srcC2` sorry there requires a strengthened package for

```lean
a ρ k = deriv (resolverTimeCoeff p u k) (offset + ρ)
        + λ_k * resolverTimeCoeff p u k (offset + ρ)
```

with λ and λ² envelopes for `a` and its time derivative.  Since

```lean
resolverTimeCoeff p u k t = intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

and `intervalNeumannResolverWeight p k ~ 1/λ_k`, this source `a` is roughly a combination of

```text
srcTimeCoeff,  λ⁻¹·∂ₜ srcTimeCoeff,
```

and its derivative uses

```text
∂ₜ srcTimeCoeff,  λ⁻¹·∂ₜ² srcTimeCoeff.
```

Thus λ² envelopes for `a` still require, at minimum, strong λ²/λ-weighted control of the nonlinear source coefficient families and their time derivatives.  The existing quadratic `(kπ)⁻²` source bounds are not enough, and the quartic theorem gives only λ¹ summability.

## Recommended route

There are two viable routes.

### Route A — stay on the physical resolver lane

Use:

```lean
IntervalPhysicalSourceTimeC2Concrete.FlooredSourceTimeData
IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor
```

This avoids `DuhamelSourceTimeC2Coeff` and only needs the source-side `(kπ)⁻²` envelopes after the elliptic weight.  This is the route the repo comments currently recommend.

### Route B — complete the older `DuhamelSourceTimeC2Coeff` lane

Then add new analysis:

1. Either exponential coefficient decay of `srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t` and its first two time derivatives, uniformly on positive windows, via an analytic-strip argument for `ν·(S(t)u₀)^γ`.
2. Or depth-3 IBP/H⁶ Neumann source data for each relevant time-order slice, plus a sextic decay theorem and λ²-summability theorem.

Concrete missing theorem family for the polynomial route:

```lean
intervalWeakH6Neumann_cosineCoeff_sextic_decay_of_bound
intervalWeakH6Neumann_eigenvalueSq_L1_summable
level0_srcSlice_timeOrder_H6_neumann  -- for s₀, s₁, s₂ or for `a`, `adot`
```

For the exponential route, missing theorem family:

```lean
level0_srcTimeCoeff_exp_decay
level0_srcTimeCoeff_timeDeriv_exp_decay
level0_srcTimeCoeff_timeDeriv2_exp_decay
```

uniformly on `t ∈ Icc c T`.

## Direct answers

### 1. Is `ν·u^γ` exponential like `u`, or only polynomial?

Mathematically it should be exponential at positive time under a positive floor, but the repo does not prove that.  Existing committed source-decay infrastructure gives only polynomial IBP decay for the nonlinear source.

### 2. If only polynomial, how get λ²-summability?

Need depth-3 / H⁶ Neumann data giving sextic decay `(kπ)⁻⁶`, or stronger.  H²/quadratic is not enough; H⁴/quartic is not enough for λ².  H⁶/sextic is enough.

### 3. What about `∂ₜ(ν·u^γ)`?

It contains `u^{γ-1} Δu`, so it costs additional heat spatial derivatives.  Heat smoothing supplies arbitrary finite regularity at positive time mathematically, but the repo does not currently package H⁶/depth-3 coefficient decay for this time-derivative slice.  The second time derivative is worse again because it contains `(Δu)^2` and `Δ²u` terms.

### 4. Minimal spatial regularity?

For λ²-summable source coefficients, depth-3 IBP / H⁶ Neumann data is the minimal integer-depth route:

```text
|a_k| ≤ C/(kπ)^6  ⇒  λ_k² |a_k| ≤ C' / k²  ⇒ summable.
```

So yes, depth-`j` IBP giving `(kπ)^(-2j)` is sufficient for `j=3`.  The repo has depth 1 and depth 2, but not the required depth 3 theorem.

## Bottom line for Q1034

`srcC2` for the `DuhamelSourceTimeC2Coeff` route is **not fillable from existing infrastructure alone**.  It needs new analysis: either exponential nonlinear-source coefficient decay, or a new depth-3/H⁶ polynomial-decay chain for the nonlinear source and its time derivatives.

But if the goal is resolver joint C² for FAC/Level0, the repo already has a different intended route: `PhysicalSourceTimeC2` + elliptic resolver weight.  That route deliberately avoids `DuhamelSourceTimeC2Coeff` and may be the better route to finish.
