# Q861 / cron1: direct resolver joint-C² shortcut?

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Refs inspected:

- `chatgpt-scratch` for the committed physical resolver/source files under `ShenWork/PDE`.
- `main` for `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`; the connector returned 404 for that path on `chatgpt-scratch`, but code search/fetch found it on `main`.

## Verdict

There is **no magic shortcut** that gets resolver joint `C²` from only

```lean
ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s, x)
```

by saying “the elliptic resolver is bounded linear.”

The bounded-linear idea is mathematically valid only after you have a **Banach-valued** statement of the form

```lean
ContDiffAt ℝ 2 (fun t => sourceSliceAsBanachElement t) s
```

and a continuous linear elliptic resolver

```lean
R : E →L[ℝ] F
```

plus an evaluation/uncurrying theorem turning a `C²` curve in `F` into joint `(t,x)` `C²`.  The current repo is not organized that way.  It is organized coefficient-by-coefficient / cosine-series-first.

So the direct resolver cutoff approach does **not** avoid source coefficient time-`C²`; it merely moves where that obligation appears.

The fastest route is:

```lean
source coefficient time-C² + bounded-weight summability
  → PhysicalSourceTimeC2
  → PhysicalResolverJointC2Data
  → coupledChemical_jointContDiffAt_two
```

or a **positive-window** variant of that route if global time data is blocked at `t = 0`.

## What the repo already has

### 1. The bounded-weight resolver series assembler already exists

`ShenWork/PDE/IntervalResolverJointC2Physical.lean` defines the generic bounded-weight joint series:

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2

 theorem boundedWeightJointSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q)
```

This is already the “resolver series directly by `contDiff_tsum`” approach.  It does not use the old spectral `λ²`/`λ³` ladder.

### 2. The physical resolver data structure already packages exactly the needed assumptions

`ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean` defines:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

Then:

```lean
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

So the direct resolver joint-`C²` theorem already exists.  The unresolved part is producing `PhysicalResolverJointC2Data` for the heat-semigroup iterate.

### 3. The constant elliptic weight transfer already exists

`ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean` proves the exact coefficient factorization:

```lean
theorem resolverTimeCoeff_eq_weight_smul
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    resolverTimeCoeff p u k t =
      intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

and packages the source-to-resolver transfer:

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

This is precisely the observation that `1/(μ+λ_k)` is a constant scalar in time, so all time derivatives transfer mechanically:

```lean
∂ₜⁱ resolverTimeCoeff = wₖ • ∂ₜⁱ srcTimeCoeff
```

### 4. The source-side data is the real work

`ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean` defines `FlooredSourceTimeData` and proves:

```lean
theorem srcTimeCoeff_contDiff
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)

 theorem srcTimeCoeff_bound
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) (t : ℝ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k

 theorem physicalSourceTimeC2_of_floored
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ...)
    (hgrad : ...) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

This is where the nonlinear source

```lean
g(t,x) = ν * u(t,x)^γ
```

is differentiated in time.  The resolver weight does not make this disappear.

## Why the proposed direct cutoff still loops back

Suppose you define

```lean
def cutoffResolverTerm ... k : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * resolverTimeCoeff p u k q.1 * cosineMode k q.2
```

and try to use `contDiff_tsum`.  You still need, for each mode and each `i ≤ 2`, a bound of the form

```lean
‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
```

on the cutoff support.

But

```lean
resolverTimeCoeff p u k t = wₖ * srcTimeCoeff p u k t
```

so this becomes exactly

```lean
‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
```

for the source coefficient.  That is precisely `PhysicalSourceTimeC2.src_contDiff` plus `PhysicalSourceTimeC2.src_bound`, or a windowed analogue of those fields.

So the cutoff helps with **localizing away from `t = 0`**, but it does not remove the source coefficient differentiability problem.

## Why `heatSemigroup_jointContDiffAt_two` is not enough by composition

`heatSemigroup_jointContDiffAt_two` proves scalar joint regularity of the uncurried heat series:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => ∑' k, exp(-q.1 * λ_k) * û₀_k * cos(kπq.2))
  (s₀, x₀)
```

That is not the same as a Banach-valued theorem:

```lean
ContDiffAt ℝ 2 (fun t => S(t)u₀) s₀
```

with codomain `C²`, `H^σ`, or some cosine-coefficient Banach space.

To use the bounded-linear resolver composition route, you would need all of the following infrastructure:

1. A Banach/function-space model `E` for the source slices.
2. A theorem that `t ↦ ν * (S(t)u₀)^γ` is `C²` as an `E`-valued map on a positive-time neighborhood.
3. A continuous linear map `R : E →L[ℝ] F` implementing the elliptic Neumann resolver.
4. A theorem that a `C²` curve into `F` gives joint `(t,x)` `C²` after uncurrying/evaluation.
5. For the flux lane, an analogous statement for `x ↦ deriv (R(source_t)) x`, or enough regularity in `F` so derivative evaluation is continuous.

None of that is currently the active infrastructure in this repo.  Proving it would likely be heavier than finishing the coefficient-route obligations.

Also, `R` is linear in the **source** `g`, not in `u`.  The actual map is

```lean
u ↦ R (ν * u^γ)
```

so even abstractly the nonlinear Nemytskii map `u ↦ ν*u^γ` under the positivity floor must still be proved `C²`.

## The useful shortcut that remains

The good shortcut is not “use bounded linearity from scalar `ContDiffAt`.”

The good shortcut is:

> Avoid the old spectral `DuhamelSourceTimeC2Coeff` / eigen-cube ladder.  Use the existing bounded-weight physical route, and only prove the source-side three-time-order data on the positive time window actually needed downstream.

Concretely, either:

### Option A: prove `PhysicalSourceTimeC2` directly

If you can produce source coefficient `ContDiff`/bounds directly for the heat semigroup, skip the explicit `FlooredSourceTimeData` wrapper and prove:

```lean
PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) Es
```

Then use:

```lean
physicalResolverJointC2Data_of_floor
coupledChemical_jointContDiffAt_two
```

This skips one packaging layer but not the mathematical source time-`C²` content.

### Option B: make a positive-window version

This is probably the better path if global `FlooredSourceTimeData` is blocked by the hard zero-extension at `t = 0`.

Define a local/windowed variant, for example:

```lean
PhysicalSourceTimeC2On p u Es c T
PhysicalResolverJointC2DataOn p u Bt c T
```

with all time-regularity and bounds only on a compact positive slab, say `t ∈ Icc c T`, with `0 < c`.

Then prove a windowed assembler using a cutoff whose support is contained in the positive slab.  This uses the same idea as `heatSemigroup_jointContDiffAt_two`: the cutoff makes the global `contDiff_tsum` proof possible, while the coefficients only need to be controlled on the positive support.

That avoids the `τ = 0` obstruction from global `FlooredSourceTimeData`, while still reusing the bounded-weight resolver majorant.

## Caveat: value vs gradient

For `coupledChemical_jointContDiffAt_two` itself, the value-series majorant is the important one.

For the FAC input package, the repo also needs the gradient lane:

```lean
coupledChemical_grad_jointContDiffAt_two
```

That uses `boundedWeightJointGradMajorant`, not just `boundedWeightJointMajorant`.  Do not assume the value majorant automatically gives the gradient majorant.  The gradient lane carries one extra spatial derivative of the cosine mode, so its summability must be checked separately.  On a positive heat window this should come from heat smoothing/exponential decay, but it is a distinct obligation.

## Bottom line

The bounded-linear resolver shortcut is mathematically reasonable in an abstract Banach-space development, but in this repo it is **not** the shortest Lean path.

The current code already has the right shortcut:

```lean
PhysicalSourceTimeC2
  → physicalResolverJointC2Data_of_floor
  → coupledChemical_jointContDiffAt_two
```

The remaining hard point is not the elliptic resolver.  The remaining hard point is proving, preferably on a positive time window, that the source coefficients of

```lean
ν * (S(t)u₀)^γ
```

are `C²` in `t` with the summable envelopes required by the bounded-weight value/gradient majorants.

So I would **not** start a new bounded-linear-map composition layer.  I would either:

1. directly prove `PhysicalSourceTimeC2` for the heat base iterate on the positive window, bypassing only the `FlooredSourceTimeData` packaging, or
2. introduce `PhysicalSourceTimeC2On` / `PhysicalResolverJointC2DataOn` and a cutoff-localized version of the existing bounded-weight assembler.

That is the real simplification.