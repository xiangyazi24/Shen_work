# Q1329 / cron1 — positivity hypothesis for `heatLevel0_srcTimeCoeff_contDiffAt_two`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

Do **not** try to prove `heatLevel0_srcTimeCoeff_contDiffAt_two` from only

```lean
hu₀_nonneg : ∀ x, 0 ≤ u₀ x
```

for the current general hypothesis `1 ≤ p.γ`.  It is too weak for the `Real.rpow` smoothness route.  If `u₀ = 0`, then `S(t)u₀ = 0`, and for a real exponent such as `γ = 3 / 2`, the map `x ↦ x^γ` is not `C²` at zero.  More generally, Mathlib’s robust `rpow` `ContDiff` lemmas want the base away from zero / nonzero at the point, and your proof of the slab continuity/chain rule needs that away from zero on a neighborhood.

The clean route is indeed a **strict positive floor**, but I would not put raw

```lean
hu₀_pos : ∀ x, 0 < u₀ x
```

deep in `IntervalHeatResolverJointC2.lean`.  Carry a **floor/profile-floor hypothesis** instead, and derive it once near the top from `hu₀_pos + hu₀_cont`.

Best low-level hypothesis:

```lean
hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

This is already the hypothesis used by the current source-data construction in

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
```

where `heatSemigroup_d0`, `heatSemigroup_d1`, and `heatSemigroup_flooredSourceTimeData` all take exactly this kind of positive-time heat-profile floor.

Even better, if you want a quantitative floor, carry:

```lean
∃ c : ℝ, 0 < c ∧ ∀ x : intervalDomainPoint, c ≤ u₀ x
```

or `PaperPositiveInitialDatum intervalDomain u₀`, and convert it to the `hfloor` above once.

## Why `hu₀_nonneg` is not enough

`hu₀_nonneg` only gives the nonnegative semigroup result:

```lean
0 ≤ S(t)u₀
```

via `intervalFullSemigroupOperator_nonneg_of_nonneg_on_Icc` or the nonnegative variant.  This is enough for value-level facts and for integer exponents, but not for `ContDiffAt ℝ 2` of

```lean
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

when the source is

```lean
ν * (S(t)u₀)^γ
```

and `γ : ℝ` is merely known to satisfy `1 ≤ γ`.  The problematic exponent range is `1 < γ < 2`: the second derivative of `x^γ` is singular at `0`.

A nonnegative-but-nontrivial route could work mathematically if you prove a **strong positivity** theorem for the Neumann heat kernel:

```lean
u₀ ≥ 0, u₀ not identically zero ⟹ 0 < S(t)u₀(x) for t > 0
```

and then use compactness to get a positive minimum on the spatial slab.  But that is a much heavier theorem than the current infrastructure.  It is also not what the existing `lower_bound` lemma gives: with `c = 0`, it only returns `0 ≤ S(t)u₀`.

## Do not compute an `inf` manually

You do not need to use the `inf` API.  The repo already has a compactness helper:

```lean
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_uniformFloor_of_continuous_pos
```

with signature:

```lean
{u₀ : intervalDomainPoint → ℝ} →
  Continuous u₀ →
  (∀ x, 0 < u₀ x) →
  ∃ c : ℝ, 0 < c ∧ ∀ x : intervalDomainPoint, c ≤ u₀ x
```

It also has:

```lean
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_paperPositiveInitialDatum_of_continuous_pos
```

which upgrades continuous strict positivity plus admissibility to:

```lean
PaperPositiveInitialDatum intervalDomain u₀
```

And `IntervalConjugatePicardInfThreshold.lean` has the already-proved semigroup floor:

```lean
ShenWork.IntervalConjugatePicard.intervalFullSemigroupOperator_ge_paperPositiveFloor
```

which proves:

```lean
paperPositiveFloor hu₀ ≤
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x
```

for `t > 0`.

So the bridge from top-level positivity to the positive heat-profile floor should use these existing helpers.

## Recommended bridge lemma

Add a bridge lemma near the `IntervalHeatResolverJointC2` / level-0 source-data bridge, importing `IntervalConjugatePicardInfThreshold` or an appropriate lighter file exposing the helper.

```lean
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold

open Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter paperPositiveFloor paperPositiveFloor_pos
   intervalFullSemigroupOperator_ge_paperPositiveFloor)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- A paper-positive initial datum gives strict positivity of the level-0 heat iterate
on the closed interval for every positive time. -/
theorem heatLevel0_positive_on_Icc_of_paperPositive
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
  intro t ht x hx
  have hS := intervalFullSemigroupOperator_ge_paperPositiveFloor hu₀ ht x
  have hpos := paperPositiveFloor_pos hu₀
  have hEq :
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x =
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x := by
    -- `conjugatePicardIter p u₀ 0 t y = S(t)u₀(y.1)` and `x ∈ [0,1]`.
    simp [intervalDomainLift, conjugatePicardIter, hx]
  rw [hEq]
  exact lt_of_lt_of_le hpos hS

end ShenWork.Paper2.HeatResolverJointC2Direct
```

If the caller only has `hu₀_cont` and `hu₀_pos`, derive `PaperPositiveInitialDatum` once:

```lean
have hpaper : PaperPositiveInitialDatum intervalDomain u₀ :=
  ShenWork.Paper2.IntervalMildExistenceAssembly
    .intervalDomain_paperPositiveInitialDatum_of_continuous_pos
      hu₀.admissible hu₀_cont hu₀_pos

have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
  heatLevel0_positive_on_Icc_of_paperPositive (p := p) hpaper
```

If the local stack does not carry `PositiveInitialDatum`, use the raw floor version instead:

```lean
hfloor₀ : ∃ c : ℝ, 0 < c ∧ ∀ x : intervalDomainPoint, c ≤ u₀ x
```

and prove the same `hfloor` with `intervalFullSemigroupOperator_lower_bound`.  But if `PaperPositiveInitialDatum` is already available, prefer it because the boundedness/measurability side conditions for `lower_bound` are already discharged there.

## Recommended theorem signatures

Change the direct stack in `IntervalHeatResolverJointC2.lean` to carry a positive-time heat-profile floor, not raw initial positivity.

```lean
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (_ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  -- prove via the same d0/d1 chain as `IntervalHeatSemigroupFlooredSourceTimeData`,
  -- or expose/reuse a smaller source-time-C2 package.
  sorry
```

Then thread **`hfloor`**, not `hu₀_pos`, through:

```lean
heatLevel0_resolverTimeCoeff_contDiffAt_two
cutoffResolverCoeff_contDiff_two
cutoffResolverTerm_contDiff_two
cutoffResolverSeries_contDiff_two
heatResolver_jointContDiffAt_two
heatResolver_grad_jointContDiffAt_two
```

The callers derive `hfloor` once from the initial floor / `PaperPositiveInitialDatum`.

This is better than threading `hu₀_pos` through six theorems because each low-level theorem only needs the positivity of the **actual heat profile on positive time slabs**.  It should not know how that floor was obtained from the initial datum.

## Existing better route: use `FlooredSourceTimeData`

There is already a source-side abstraction that encodes this correctly:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.FlooredSourceTimeData
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiffAt
```

The theorem

```lean
srcTimeCoeff_contDiffAt
```

has the target conclusion:

```lean
ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t
```

for `t > 0`, provided you have `FlooredSourceTimeData p u s₁ s₂`.

And the level-0 file already builds the relevant package:

```lean
ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
```

with the exact positivity hypothesis:

```lean
hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

So, architecturally, the cleanest proof of `heatLevel0_srcTimeCoeff_contDiffAt_two` is not to create another independent analytic proof in `IntervalHeatResolverJointC2.lean`.  Instead either:

1. make `heatLevel0_srcTimeCoeff_contDiffAt_two` consume the already-built `FlooredSourceTimeData` and close by one line:

```lean
exact ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiffAt H k ht
```

or

2. import/reuse the level-0 floored source-data builder, passing the same `hfloor` plus the remaining source-slice C2/Neumann/bound obligations.

If you only want the coefficient `ContDiffAt`, a smaller structure containing only the `d0`, `d1`, and `s₂`-continuity fields would avoid requiring the `sliceC2`, `sliceNeumann`, `zerothBound`, and `laplBound` fields.  But the current committed structure already exists and is consistent with the physical-source route.

## Minimal recommendation

- **Do not use `hu₀_nonneg`** for this theorem under `1 ≤ γ`; it is insufficient.
- **Do not thread raw `hu₀_pos`** through the deep direct stack if you can avoid it.
- Thread either:

```lean
hfloor : ∀ t > 0, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

or a quantitative initial floor / `PaperPositiveInitialDatum`.

- At the top, derive the floor from `hu₀_cont + hu₀_pos` using:

```lean
intervalDomain_uniformFloor_of_continuous_pos
intervalDomain_paperPositiveInitialDatum_of_continuous_pos
intervalFullSemigroupOperator_ge_paperPositiveFloor
```

This is mathematically clean, matches the existing `IntervalHeatSemigroupFlooredSourceTimeData.lean` design, and avoids making low-level time-coefficient theorems depend on how the positivity was obtained.

No local `lake build` was run; this drop was produced through the GitHub connector only.
