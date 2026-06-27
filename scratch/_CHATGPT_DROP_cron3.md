# Q1230 (cron3): time derivative of `heatDu` / termwise time differentiation APIs

## Short answer

Yes: `unitIntervalCosineHeatValue_hasDerivAt_time` exists.

It is in:

```lean
ShenWork.PDE.IntervalDuhamelClosedC2
```

with namespace-qualified name:

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
```

Its shape is:

```lean
theorem unitIntervalCosineHeatValue_hasDerivAt_time
    {r x : ℝ} (hr : 0 < r) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatValue s a x)
      (unitIntervalCosineHeatSecondValue r a x) r
```

It proves exactly the time derivative of the heat-value cosine series with bounded coefficient sequence `a`:

```text
∂ₜ ∑ₙ exp(-t λₙ) aₙ cos(nπx)
  = ∑ₙ -λₙ exp(-t λₙ) aₙ cos(nπx)
```

Internally it uses `hasDerivAt_tsum_of_isPreconnected` on the positive-time interval `Ioi (r/2)`.

For `heatDu`, however, **do not apply this theorem directly with coefficients**

```lean
fun n => -unitIntervalCosineEigenvalue n * heatCoeff u₀ n
```

because those coefficients are not bounded from the current assumptions. Instead use either:

1. the generic termwise-differentiation API directly on `heatDu`, with an exponential majorant on `Ioi (t/2)`; or
2. the half-time shift trick, absorbing `exp(-(t/2)λₙ)` into the coefficient sequence so the remaining heat-time is positive.

For the `d1` field, I recommend route 1. It matches `heatDu` and `heatD2u` as they are defined and avoids trying to make the unbounded coefficient sequence bounded.

## Search results / relevant APIs

### 1. Repo-local one-sided termwise differentiation

File:

```lean
ShenWork/PDE/HasDerivWithinAtTsum.lean
```

Namespace/theorem:

```lean
ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum
```

Shape:

```lean
theorem hasDerivWithinAt_tsum
    {F F' : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    {u : ℕ → ℝ} (hu : Summable u)
    (hF : ∀ n, ∀ x ∈ s, HasDerivWithinAt (F n) (F' n x) s x)
    (hbound : ∀ n, ∀ x ∈ s, |F' n x| ≤ u n)
    {xbase : ℝ} (hxbase : xbase ∈ s)
    (hF0 : Summable fun n => F n xbase)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    HasDerivWithinAt (fun y => ∑' n, F n y) (∑' n, F' n x₀) s x₀
```

This is the most directly usable API for `heatDu`: take `s = Ioi (t/2)`.

### 2. Mathlib termwise `HasDerivAt` APIs already used in the repo

Search found uses of:

```lean
hasDerivAt_tsum
hasDerivAt_tsum_of_isPreconnected
```

The repo uses them in:

```lean
ShenWork/PDE/RegularityBootstrap.lean
ShenWork/PDE/IntervalDuhamelClosedC2.lean
```

In `RegularityBootstrap.lean`, the theorem

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound
```

uses `hasDerivAt_tsum`.

Its local positive-time variant

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound_on_Ioi
```

uses `hasDerivAt_tsum_of_isPreconnected` on `Set.Ioi r`.

### 3. Heat-value derivative APIs

There are three useful levels.

#### Bounded coefficients

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
```

Requires:

```lean
∀ n, |a n| ≤ M
```

Returns:

```lean
HasDerivAt (fun s => unitIntervalCosineHeatValue s a x)
  (unitIntervalCosineHeatSecondValue r a x) r
```

This is good for ordinary heat series with bounded initial coefficients.

#### Explicit summable majorant

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound_on_Ioi
```

These are lower-level and more flexible. They return a `RegularityBootstrap.unitIntervalCosineHeatLaplacianValue` derivative.

#### L² coefficients

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
```

Shape:

```lean
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
    {t x : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t
```

This is sometimes better than the bounded-coefficient theorem if you absorb a positive heat time into the coefficients.

### 4. Duhamel product / moving-coefficient termwise derivative

For a product series with moving coefficients, the relevant API is already in:

```lean
ShenWork/PDE/IntervalDuhamelClosedC2.lean
```

The per-mode product rule is:

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatTerm_sub_hasDerivAt
```

and the assembled series theorem is:

```lean
ShenWork.IntervalDuhamelClosedC2.duhamelIntegrand_hasDerivAt
```

That theorem differentiates

```lean
fun s => unitIntervalCosineHeatValue (t - s) (a s) x
```

and proves the derivative

```lean
-(unitIntervalCosineHeatSecondValue (t - s₀) (a s₀) x)
  + unitIntervalCosineHeatValue (t - s₀) (adot s₀) x
```

using `hasDerivAt_tsum_of_isPreconnected`. This is not the exact `heatDu` target, but it is the repo’s existing “termwise derivative of a product/moving-coefficient heat series” pattern.

### 5. Negative search result

I did not find a repo theorem literally named:

```lean
tsum_hasDerivAt
```

The working names are `hasDerivAt_tsum`, `hasDerivAt_tsum_of_isPreconnected`, and the repo wrapper `ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum`.

I also did not find a theorem already named like:

```lean
heatDu_hasDerivAt_time
```

so for the `d1` field you should add that helper.

## Recommended helper for `d1`: prove `heatDu` has time derivative `heatD2u`

Target shape:

```lean
import ShenWork.PDE.HasDerivWithinAtTsum
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Positive-time time derivative of the heat Laplacian representative.

This is the missing local atom for the `d1` field: at positive time, differentiating
`heatDu` in time gives `heatD2u`.
-/
theorem heatDu_hasDerivAt_time
    {u₀ : intervalDomainPoint → ℝ} {M₀ t x : ℝ}
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (ht : 0 < t) :
    HasDerivAt (fun τ : ℝ => heatDu u₀ τ x) (heatD2u u₀ t x) t := by
  classical
  -- Proof route below.
  sorry

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

Fill the proof using the direct termwise-differentiation route below.

### Direct proof route

Let

```lean
F n τ  = (-λ_ n) * (Real.exp (-τ * λ_ n) * heatCoeff u₀ n) * cosineMode n x
F' n τ = (λ_ n)^2 * (Real.exp (-τ * λ_ n) * heatCoeff u₀ n) * cosineMode n x
```

Work on the open interval

```lean
S := Ioi (t / 2)
```

so every `τ ∈ S` has a uniform lower heat time `τ ≥ t/2`.

The per-mode derivative can reuse the existing lemma:

```lean
ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff_hasDerivAt
```

which proves:

```lean
HasDerivAt
  (fun r => Real.exp (-r * λ_ k) * heatCoeff u₀ k)
  (-(λ_ k) * (Real.exp (-σ * λ_ k) * heatCoeff u₀ k)) σ
```

After multiplying by `-(λ_ k) * cosineMode k x`, the derivative becomes exactly
`F' k σ`.

The derivative majorant on `S` is:

```lean
u n := (λ_ n)^2 * M₀ * Real.exp (-(t / 2) * λ_ n)
```

up to harmless reassociation. Summability comes from:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
  2 (by positivity : 0 < t / 2)
```

or the coefficient-weighted wrapper:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_coeff_exp_summable
  2 (by positivity : 0 < t / 2) hM₀nn
```

where:

```lean
have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
```

The base summability needed by `hasDerivWithinAt_tsum` is:

```lean
Summable fun n => F n t
```

and it is dominated by

```lean
fun n => λ_ n * M₀ * Real.exp (-t * λ_ n)
```

which is summable by the same `eigenvalue_pow_mul_exp_summable` theorem with `m = 1`.

Then apply:

```lean
ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum
  (s := Ioi (t / 2))
  (hs := convex_Ioi (t / 2))
  (F := F)
  (F' := F')
  (u := u)
```

This gives:

```lean
HasDerivWithinAt
  (fun τ => ∑' n, F n τ)
  (∑' n, F' n t)
  (Ioi (t / 2))
  t
```

Since `Ioi (t/2) ∈ 𝓝 t`, convert it to `HasDerivAt`.

Finally use eventual equality near `t` to replace the raw series by `heatDu` and the target sum by `heatD2u`:

```lean
-- near t, positive branch of heatDu is active
have hτpos : ∀ᶠ τ in 𝓝 t, 0 < τ := Ioi_mem_nhds ht

-- on that neighborhood:
-- heatDu u₀ τ x
--   = ∑' n, (-λ_n) * exp(-τ λ_n) * heatCoeff u₀ n * cosineMode n x
-- and, since ht : 0 < t:
-- heatD2u u₀ t x
--   = ∑' n, λ_n^2 * exp(-t λ_n) * heatCoeff u₀ n * cosineMode n x
```

Use `unfold heatDu heatD2u` plus `simp [ht]`, `tsum_congr`, and the definitions of
`RegularityBootstrap.unitIntervalCosineHeatLaplacianValue` /
`unitIntervalCosineHeatLaplacianPointWeight` to perform the identification.

## Alternative: half-time shift using the existing heat-value theorem

You can also avoid proving the termwise derivative directly by absorbing half the heat time into a new coefficient sequence.

Fix `t > 0`, set:

```lean
θ := t / 2
b n := -λ_ n * Real.exp (-θ * λ_ n) * heatCoeff u₀ n
```

Then near `t`, for `τ > θ`,

```lean
heatDu u₀ τ x
  = unitIntervalCosineHeatValue (τ - θ) b x
```

because

```text
exp(-(τ - θ)λₙ) * (-λₙ exp(-θλₙ) aₙ)
  = -λₙ exp(-τλₙ) aₙ.
```

Differentiate the right-hand side at `τ = t` by composing the heat-value theorem at heat time `θ` with `τ ↦ τ - θ`.

For this route, the bounded-coefficient theorem `unitIntervalCosineHeatValue_hasDerivAt_time` still requires a bound on `b`. It is often easier to use the L² theorem instead:

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
```

because

```lean
Summable fun n => (b n)^2
```

follows from exponential damping:

```text
(b n)^2 ≤ M₀^2 * (λ_n)^2 * exp(-t * λ_n)
```

and `∑ λ_n^2 exp(-t λ_n)` is summable by
`eigenvalue_pow_mul_exp_summable 2 ht`.

The derivative is then:

```lean
unitIntervalCosineHeatLaplacianValue θ b x
```

which unfolds to

```text
∑ λ_n^2 * exp(-t λ_n) * heatCoeff u₀ n * cos(nπx)
```

i.e. exactly `heatD2u u₀ t x`.

## Which route to use for `d1`?

For the `d1` field in `IntervalHeatSemigroupFlooredSourceTimeData.lean`, I would add the helper:

```lean
heatDu_hasDerivAt_time
```

and prove it by the **direct `HasDerivWithinAtTsum.hasDerivWithinAt_tsum` route** on `Ioi (t/2)`. It is the most local and avoids having to prove a separate boundedness lemma for the shifted coefficients.

The proof obligations line up exactly:

* per-mode derivative: `heatCoeff_hasDerivAt`, multiplied by `-λ_n*cos(nπx)`;
* derivative majorant: `M₀ * λ_n^2 * exp(-(t/2)λ_n)`;
* majorant summability: `eigenvalue_pow_mul_exp_summable 2`;
* base summability: `eigenvalue_pow_mul_exp_summable 1`;
* raw-series identification: unfold `heatDu`, `heatD2u`, and the Laplacian point-weight definitions.

Once this helper exists, the `d1` chain-rule proof can feed it as the `hd2u` input to:

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.hasDerivAt_srcSlice1
```

namely:

```lean
have hdu : HasDerivAt
    (fun r => intervalDomainLift (conjugatePicardIter p u₀ 0 r) x)
    (heatDu u₀ s x) s :=
  -- existing / d0 heat-time derivative atom
  ...

have hd2u : HasDerivAt
    (fun r => heatDu u₀ r x)
    (heatD2u u₀ s x) s :=
  heatDu_hasDerivAt_time _hu₀_bound hs_pos

exact ShenWork.IntervalFlooredSourceTimeDataIterate.hasDerivAt_srcSlice1
  (p := p) (u := conjugatePicardIter p u₀ 0)
  (du := heatDu u₀) (d2u := heatD2u u₀)
  hpos hdu hd2u
```

The only caveat is positivity: `hasDerivAt_srcSlice1` needs the floor/strict positivity hypothesis

```lean
0 < intervalDomainLift (conjugatePicardIter p u₀ 0 s) x
```

for the `rpow` chain rule. The `heatDu` derivative helper itself does not need positivity; it is purely spectral.
