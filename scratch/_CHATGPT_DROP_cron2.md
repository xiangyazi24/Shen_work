# Q1519 (cron2) — zeroth-mode bound for `srcSlice1 = νγ u^{γ-1} heatDu`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

The observation

```text
∫ heatDu = 0
```

is correct for the pure heat Laplacian: the zero mode is killed by `λ₀ = 0`.

But it does **not** prove the `i = 1` `zerothBound`, because the slice is not just `heatDu`; it is

```lean
srcSlice1 p u heatDu t x
  = p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * heatDu t x
```

so the zeroth coefficient is the integral of a **weighted** Laplacian:

```text
ν γ ∫₀¹ u(t,x)^(γ-1) · Δu(t,x) dx.
```

The factor `u^(γ-1)` destroys the zero-mode cancellation unless it is constant, for example when `γ = 1`.

For smooth Neumann heat slices, the correct identity is instead

```text
ν γ ∫ u^(γ-1) Δu
  = -ν γ (γ - 1) ∫ u^(γ-2) |u_x|²,
```

with the boundary term vanishing by the Neumann condition. Thus the zeroth mode is controlled by a weighted Dirichlet energy, not by the zero mode of `heatDu` alone.

Consequently, a uniform bound over **all** `t > 0` is not available from the current weak hypotheses `hu₀_cont` and `hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀`. Near `t = 0+`, heat smoothing can make `‖∂ₓS(t)u₀‖₂²` blow up unless the initial datum carries additional `H¹`/energy/variation regularity. On a fixed positive window `t ≥ c > 0`, it is bounded by smoothing estimates; globally over `t > 0`, it needs an extra assumption or a weakened API.

## What the repo currently has

In

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
```

`heatDu` is defined as the spectral Laplacian for positive time:

```lean
def heatDu (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplianValue
      t (cosineCoeffs (intervalDomainLift u₀)) x
  else 0
```

The actual file name is `unitIntervalCosineHeatLaplacianValue`; the important point is that `heatDu` is the spectral Laplacian.

The same file proves the bridge:

```lean
private theorem heatDu_eq_secondValue
    (u₀ : intervalDomainPoint → ℝ) {t x : ℝ} (ht : 0 < t) :
    heatDu u₀ t x =
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        t (cosineCoeffs (intervalDomainLift u₀)) x := by
  ...
```

So `heatDu` is also the second spatial derivative of the cosine heat value.

In

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

`srcSlice1` is exactly the nonlinear weighted expression:

```lean
def srcSlice1 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * du t x
```

Therefore `hzerothBound` for `i = 1` is asking for a uniform bound on

```lean
|cosineCoeffs (fun x => p.ν * p.γ * u(t,x)^(p.γ - 1) * heatDu u₀ t x) 0|.
```

Since the normalized Neumann zeroth coefficient is just the unscaled integral mode, this is morally

```text
|ν γ ∫₀¹ u(t,x)^(γ-1) heatDu(t,x) dx|.
```

## Why the zero-mode argument fails

The tempting argument is:

```text
heatDu(t,x) = ∑ₙ -λₙ e^{-tλₙ} aₙ cos(nπx).
∫ heatDu = -λ₀ e^{-tλ₀} a₀ = 0.
```

This is right for `∫ heatDu`, but the needed term is

```text
∫ u^(γ-1) heatDu.
```

The function `u^(γ-1)` has its own nontrivial cosine expansion. Multiplying by it convolves modes; the integral of the product is not the zero mode of `heatDu`, but an inner product:

```text
⟨u^(γ-1), Δu⟩.
```

Only if `u^(γ-1)` is constant does this reduce to a constant times `∫ Δu = 0`.

So:

```text
∫ heatDu = 0
```

but generally

```text
∫ u^(γ-1) heatDu ≠ 0.
```

## The correct identity

Let

```text
u(t,x) = S(t)u₀(x),      heatDu = u_t = u_xx.
```

For smooth positive Neumann slices, integration by parts gives:

```text
∫₀¹ u^(γ-1) u_xx dx
  = [u^(γ-1) u_x]₀¹ - (γ - 1)∫₀¹ u^(γ-2) (u_x)² dx.
```

The Neumann boundary term vanishes, so

```text
∫₀¹ u^(γ-1) u_xx dx
  = -(γ - 1)∫₀¹ u^(γ-2) (u_x)² dx.
```

Thus

```text
cosineCoeffs(srcSlice1 ...) 0
  = -ν γ (γ - 1) ∫₀¹ u^(γ-2) (u_x)² dx.
```

up to the exact repo normalization of `cosineCoeffs 0`, which is unscaled in this development.

This gives two useful special cases:

1. If `γ = 1`, the expression is exactly zero.
2. If `γ > 1` and `u` has a uniform positive floor and a uniform `H¹` energy bound, the expression is uniformly bounded by the energy.

But the repo’s current level-0 theorem only takes `hu₀_cont` and coefficient boundedness. That is not enough for a global `∀ t > 0` bound.

## Why global uniform-in-`t > 0` is too strong from bounded coefficients alone

From the coefficient bound alone,

```lean
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
```

the heat derivative has size like

```text
∂ₓS(t)u₀ : coefficients ~ |kπ| e^{-t(kπ)^2} a_k.
```

If only `|a_k| ≤ M₀`, then the crude energy bound is

```text
∑ k² e^{-2t(kπ)^2} M₀²,
```

which diverges as `t → 0+` like a negative power of `t`. This is a smoothing bound on each window `[c,∞)`, not a uniform bound on `(0,∞)`.

For a fixed datum with extra regularity, this may be finite; for merely continuous data, the Dirichlet energy of the heat trace can blow as `t → 0+`. Therefore `hzerothBound` as currently stated is analytically suspicious for `i = 1` and even more for `i = 2`.

## What to prove instead

There are three viable options.

### Option A: weaken `zerothBound` to positive windows

If downstream only needs bounds near a positive time `τ > 0`, the cleanest analytic API is local/windowed:

```lean
zerothBoundOn : ∀ i : ℕ, i ≤ 2 → ∀ c T : ℝ, 0 < c → c ≤ T →
  ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc c T,
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D
```

This is compatible with heat smoothing and compactness on `[c,T]`. It avoids false global-in-time uniformity at `t = 0+`.

### Option B: keep global `zerothBound`, but add stronger initial regularity

For `i = 1`, assume enough regularity to control the heat energy uniformly:

```lean
∃ E : ℝ, 0 ≤ E ∧ ∀ t > 0,
  ∫ x in (0:ℝ)..1, (deriv (fun y => intervalDomainLift (conjugatePicardIter p u₀ 0 t) y) x)^2 ≤ E
```

or a spectral form like:

```lean
Summable (fun k => unitIntervalCosineEigenvalue k *
  |cosineCoeffs (intervalDomainLift u₀) k| ^ 2)
```

Then the integration-by-parts route can bound `i = 1` globally, assuming the floor keeps `u^(γ-2)` controlled when needed.

For `i = 2`, more regularity is needed because `srcSlice2` contains both `(heatDu)^2` and `heatD2u`.

### Option C: handle only `γ = 1`

If the model ever specializes to `γ = 1`, then

```text
srcSlice1 = ν * heatDu
```

and the zeroth mode is exactly zero. But the current API has general `p.γ`, so this does not solve the general theorem.

## Lean proof skeleton for the useful identity

The right lemma to add is not “zeroth mode of `heatDu` is zero” alone, but the weighted integration-by-parts identity. A possible target shape:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceZeroth

/-- Zeroth coefficient is the integral mode.  This is just unfolding the repo's
normalization of `cosineCoeffs` at `0`. -/
theorem cosineCoeffs_zero_eq_integral (f : ℝ → ℝ) :
    cosineCoeffs f 0 = ∫ x in (0 : ℝ)..1, f x := by
  -- unfold cosineCoeffs
  -- unfold HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
  -- simp [HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  sorry

/-- Pure heat Laplacian has zero zeroth mode.  This is true, but it is not the
`srcSlice1` bound unless `γ = 1`. -/
theorem heatDu_zeroth_mode_zero
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    cosineCoeffs (fun x => heatDu u₀ t x) 0 = 0 := by
  -- Route 1: rewrite `heatDu` to `unitIntervalCosineHeatSecondValue`.
  -- Route 2: identify the zeroth cosine coefficient of the second-derivative series.
  -- The k = 0 term carries `unitIntervalCosineEigenvalue 0 = 0`.
  -- Alternatively prove by mass conservation of the Neumann heat semigroup.
  sorry

/-- The actual zeroth coefficient for `srcSlice1` is a weighted Laplacian inner
product, not the zeroth mode of `heatDu`.  Under sufficient smoothness and Neumann
BCs, integrate by parts to get the weighted energy identity. -/
theorem srcSlice1_zeroth_eq_weighted_energy
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {t : ℝ}
    (ht : 0 < t)
    -- hypotheses to be supplied from heat semigroup high regularity:
    (hC2 : ContDiffOn ℝ 2
      (fun x : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
      (Icc (0 : ℝ) 1))
    (hNeu0 : deriv (fun x : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) 0 = 0)
    (hNeu1 : deriv (fun x : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) 1 = 0) :
    cosineCoeffs
      (fun x => srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x) 0
      = -p.ν * p.γ * (p.γ - 1) *
          ∫ x in (0 : ℝ)..1,
            (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 2) *
              (deriv (fun y : ℝ => intervalDomainLift
                (conjugatePicardIter p u₀ 0 t) y) x) ^ 2 := by
  -- 1. rewrite zeroth coefficient as integral.
  -- 2. rewrite `heatDu` as second spatial derivative / Laplacian of the heat profile.
  -- 3. integrate by parts:
  --      ∫ u^(γ-1) u_xx = [u^(γ-1)u_x]_0^1
  --        - ∫ (γ-1)u^(γ-2)u_x^2.
  -- 4. boundary term vanishes by Neumann.
  sorry

end ShenWork.Paper2.HeatSemigroupFlooredSourceZeroth
```

The first lemma, `heatDu_zeroth_mode_zero`, is still useful as a sanity check and for the `γ = 1` specialization. But for general `γ`, the necessary lemma is `srcSlice1_zeroth_eq_weighted_energy` plus whatever energy bound you decide to assume/prove.

## Recommendation for the current `hzerothBound`

Do **not** discharge `i = 1` by claiming the integral is the zero mode of `heatDu`. That misses the nonlinear weight.

Either:

1. change `zerothBound` to a windowed positive-time bound, matching the local nature of the rest of `FlooredSourceTimeData`, or
2. add an explicit global energy/regularity assumption on the initial data strong enough to control `∫u^{γ-2}|u_x|²` uniformly over `t > 0`.

For the current theorem as stated, with only continuous initial data and bounded coefficients, the global uniform `t > 0` `zerothBound` for `i = 1` is not justified.
