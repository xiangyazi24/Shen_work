# Q1122 / cron1 — `heatLevel0_srcTimeCoeff_contDiffAt_two`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

Files inspected for this answer:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean
ShenWork/Paper2/IntervalMildPicardRegularity.lean
ShenWork/Paper2/IntervalDomainPositiveWindowK1OnEndpoint.lean
ShenWork/Paper2/IntervalConjugatePicard.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

## Executive answer

For the concrete source used by `srcTimeCoeff`, do **not** hand-code the first derivative from scratch.  The repo already has the right formulas under the names

```lean
srcSlice1 p u du
srcSlice2 p u du d2u
```

from `ShenWork.PDE.IntervalFlooredSourceTimeDataIterate`.

For the level-0 heat semigroup, instantiate these with

```lean
u   := conjugatePicardIter p u₀ 0
du  := ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatDu u₀
d2u := ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatD2u u₀
```

Then the first source-time derivative slice is exactly

```lean
fun τ x =>
  p.ν * p.γ *
    (intervalDomainLift (conjugatePicardIter p u₀ 0 τ) x) ^ (p.γ - 1) *
    ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatDu u₀ τ x
```

Mathematically, on positive time this is

```text
f₁(τ,x) = ν · γ · (S(τ)u₀(x))^(γ-1) · ΔS(τ)u₀(x).
```

The second derivative slice is the repo’s `srcSlice2`:

```text
f₂(τ,x)
  = ν·γ·(γ-1)·(S(τ)u₀(x))^(γ-2)·(ΔS(τ)u₀(x))²
    + ν·γ·(S(τ)u₀(x))^(γ-1)·Δ²S(τ)u₀(x).
```

In Lean, prefer the exact existing spelling

```lean
srcSlice2 p (conjugatePicardIter p u₀ 0)
  (heatDu u₀) (heatD2u u₀)
```

because it uses `p.γ - 1 - 1` rather than asking `ring`/`linarith` to normalize `p.γ - 2`.

## The shortest replacement, if the `FlooredSourceTimeData` producer is acceptable

There is already a public assembly theorem in `IntervalPhysicalSourceTimeC2Concrete.lean`:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiffAt
```

and a level-0 heat producer in `IntervalHeatSemigroupFlooredSourceTimeData.lean`:

```lean
ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
```

If those are available in your branch, the target theorem can be closed by delegating to them:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (FlooredSourceTimeData srcTimeCoeff_contDiffAt)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu heatD2u heatSemigroup_flooredSourceTimeData)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Direct closure through the existing heat-level-0 `FlooredSourceTimeData` package. -/
theorem heatLevel0_srcTimeCoeff_contDiffAt_two_via_floored
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
  let s₁ : ℝ → ℝ → ℝ := srcSlice1 p u (heatDu u₀)
  let s₂ : ℝ → ℝ → ℝ := srcSlice2 p u (heatDu u₀) (heatD2u u₀)
  have H : FlooredSourceTimeData p u s₁ s₂ := by
    dsimp [u, s₁, s₂]
    exact heatSemigroup_flooredSourceTimeData
      (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont
  simpa [u] using srcTimeCoeff_contDiffAt H k ht

end ShenWork.Paper2.HeatResolverJointC2Direct
```

That is the cleanest proof if your branch treats `heatSemigroup_flooredSourceTimeData` and `srcTimeCoeff_contDiffAt` as trusted/filled infrastructure.  If you want the local proof to visibly apply `cosineCoeffs_hasDerivAt_of_smooth_param`, use the skeleton below.

## Explicit `HasDerivAt` proof for `srcTimeCoeff`

This is the exact application of

```lean
cosineCoeffs_hasDerivAt_of_smooth_param
```

to the source slice `f₀ = srcSlice p u` and derivative slice `f₁ = srcSlice1 p u (heatDu u₀)`.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (srcSlice FlooredSourceTimeData srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatD2u heatSemigroup_flooredSourceTimeData)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

private abbrev heatLevel0U (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  conjugatePicardIter p u₀ 0

private abbrev heatLevel0F₁ (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℝ → ℝ → ℝ :=
  srcSlice1 p (heatLevel0U p u₀) (heatDu u₀)

private abbrev heatLevel0F₂ (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℝ → ℝ → ℝ :=
  srcSlice2 p (heatLevel0U p u₀) (heatDu u₀) (heatD2u u₀)

/-- Source time-data package specialized to the heat semigroup base iterate. -/
private theorem heatLevel0_flooredSourceTimeData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    FlooredSourceTimeData p (heatLevel0U p u₀)
      (heatLevel0F₁ p u₀) (heatLevel0F₂ p u₀) := by
  simpa [heatLevel0U, heatLevel0F₁, heatLevel0F₂] using
    heatSemigroup_flooredSourceTimeData
      (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont

/-- First application of `cosineCoeffs_hasDerivAt_of_smooth_param`:
`d/dt srcTimeCoeff = cosineCoeffs f₁`. -/
private theorem heatLevel0_srcTimeCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt
      (srcTimeCoeff p (heatLevel0U p u₀) k)
      (cosineCoeffs (heatLevel0F₁ p u₀ t) k)
      t := by
  classical
  have H := heatLevel0_flooredSourceTimeData
    (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont
  obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.d0 t ht

  -- This is the `hf_int` argument requested in the question.
  -- It comes from eventual `ContinuousOn` of the source slice in `H.d0`.
  have hf_int : ∀ᶠ s in 𝓝 t,
      IntervalIntegrable (srcSlice p (heatLevel0U p u₀) s)
        volume (0 : ℝ) 1 := by
    filter_upwards [hcont] with s hs
    exact (hs.mono (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable

  -- `hdiff` is exactly the `h_diff` argument requested:
  --   ∀ x ∈ Ioo 0 1, ∀ s ∈ ball t δ,
  --     HasDerivAt (fun r => srcSlice p u r x) (f₁ s x) s.
  -- `hcd` is exactly the requested `h_cont_deriv`:
  --   ContinuousOn (uncurry f₁) ((t-δ,t+δ) × [0,1]).
  have hcoeff := cosineCoeffs_hasDerivAt_of_smooth_param
    (f := srcSlice p (heatLevel0U p u₀))
    (f' := heatLevel0F₁ p u₀)
    (τ := t) (δ := δ) (n := k)
    hδ hf_int hdiff hcd

  have heq :
      (fun s => cosineCoeffs (srcSlice p (heatLevel0U p u₀) s) k) =
        srcTimeCoeff p (heatLevel0U p u₀) k := by
    funext s
    exact (srcTimeCoeff_eq_cosineCoeffs p (heatLevel0U p u₀) k s).symm
  rw [heq] at hcoeff
  exact hcoeff

/-- Second application of `cosineCoeffs_hasDerivAt_of_smooth_param`:
`d/dt cosineCoeffs f₁ = cosineCoeffs f₂`. -/
private theorem heatLevel0_srcCoeff1_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt
      (fun s => cosineCoeffs (heatLevel0F₁ p u₀ s) k)
      (cosineCoeffs (heatLevel0F₂ p u₀ t) k)
      t := by
  classical
  have H := heatLevel0_flooredSourceTimeData
    (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont
  obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.d1 t ht

  have hf_int : ∀ᶠ s in 𝓝 t,
      IntervalIntegrable (heatLevel0F₁ p u₀ s) volume (0 : ℝ) 1 := by
    filter_upwards [hcont] with s hs
    exact (hs.mono (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable

  exact cosineCoeffs_hasDerivAt_of_smooth_param
    (f := heatLevel0F₁ p u₀)
    (f' := heatLevel0F₂ p u₀)
    (τ := t) (δ := δ) (n := k)
    hδ hf_int hdiff hcd

/-- Continuity of the second source-coefficient derivative. -/
private theorem heatLevel0_srcCoeff2_continuousAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContinuousAt (fun s => cosineCoeffs (heatLevel0F₂ p u₀ s) k) t := by
  classical
  have H := heatLevel0_flooredSourceTimeData
    (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont
  obtain ⟨δ, hδ, _hcont, _hdiff, hcd⟩ := H.d1 t ht

  have hcont_on :=
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
      (f := heatLevel0F₂ p u₀)
      (c := t - δ) (T := t + δ) k hcd
  have htmem : t ∈ Icc (t - δ) (t + δ) := by
    constructor <;> linarith
  have hsub : Icc (t - δ) (t + δ) ∈ 𝓝 t := by
    apply Icc_mem_nhds <;> linarith
  exact (hcont_on t htmem).continuousAt hsub

/-- Pure calculus assembly lemma.  This is not heat-specific.

Use `contDiffAt_succ_iff` / `ContDiffAt.deriv` style lemmas here.  I am leaving
this as a hard sublemma because the question was specifically about the
`cosineCoeffs_hasDerivAt_of_smooth_param` application. -/
private theorem contDiffAt_two_of_hasDerivAt_chain
    {f f₁ f₂ : ℝ → ℝ} {t : ℝ} {U : Set ℝ}
    (hUopen : IsOpen U) (htU : t ∈ U)
    (hf : ∀ s ∈ U, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ U, HasDerivAt f₁ (f₂ s) s)
    (hf₂ : ContinuousOn f₂ U) :
    ContDiffAt ℝ (2 : ℕ∞) f t := by
  -- Standard route:
  -- 1. Prove `ContDiffOn ℝ 1 f U` from `hf` and continuity of `f₁`.
  -- 2. Prove `ContDiffOn ℝ 1 f₁ U` from `hf₁` and `hf₂`.
  -- 3. Use `contDiffAt_succ_iff` twice, or a local `ContDiffOn` theorem.
  -- For `ℝ → ℝ`, `HasDerivAt` can be converted to `HasFDerivAt` by `.hasFDerivAt`.
  sorry

/-- Local direct proof skeleton for the target theorem.

The only hard sublemma left here is the generic calculus assembly lemma above.
The two coefficient differentiations and the second-derivative continuity are
shown explicitly. -/
theorem heatLevel0_srcTimeCoeff_contDiffAt_two_skeleton
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
  let f₁ : ℝ → ℝ := fun s => cosineCoeffs (srcSlice1 p u (heatDu u₀) s) k
  let f₂ : ℝ → ℝ := fun s => cosineCoeffs (srcSlice2 p u (heatDu u₀) (heatD2u u₀) s) k

  refine contDiffAt_two_of_hasDerivAt_chain
    (f := srcTimeCoeff p u k) (f₁ := f₁) (f₂ := f₂)
    (U := Ioi (0 : ℝ)) isOpen_Ioi ht ?_ ?_ ?_
  · intro s hs
    have hspos : 0 < s := hs
    simpa [u, f₁, heatLevel0U, heatLevel0F₁] using
      heatLevel0_srcTimeCoeff_hasDerivAt
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hspos k
  · intro s hs
    have hspos : 0 < s := hs
    simpa [u, f₁, f₂, heatLevel0U, heatLevel0F₁, heatLevel0F₂] using
      heatLevel0_srcCoeff1_hasDerivAt
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hspos k
  · intro s hs
    have hspos : 0 < s := hs
    exact (by
      simpa [u, f₂, heatLevel0U, heatLevel0F₂] using
        (heatLevel0_srcCoeff2_continuousAt
          (p := p) (u₀ := u₀) (M₀ := M₀)
          hu₀_bound hu₀_cont hspos k)).continuousWithinAt

end ShenWork.Paper2.HeatResolverJointC2Direct
```

## Where each requested hypothesis comes from

### `hf_int`

For the first coefficient differentiation, `H.d0 t ht` supplies

```lean
hcont : ∀ᶠ s in 𝓝 t,
  ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)
```

where

```lean
H : FlooredSourceTimeData p u s₁ s₂
```

Then convert `ContinuousOn` on `[0,1]` to interval integrability exactly as in `IntervalPhysicalSourceTimeC2Concrete.lean`:

```lean
have hf_int : ∀ᶠ s in 𝓝 t,
    IntervalIntegrable (srcSlice p u s) volume (0 : ℝ) 1 := by
  filter_upwards [hcont] with s hs
  exact (hs.mono (by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable
```

For the second differentiation, use `H.d1 t ht`, where the corresponding eventual continuity is for `s₁ s`, and the same conversion gives

```lean
IntervalIntegrable (s₁ s) volume 0 1.
```

### `h_diff`

For the first differentiation, `H.d0 t ht` gives exactly:

```lean
∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball t δ,
  HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s
```

For the second differentiation, `H.d1 t ht` gives exactly:

```lean
∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball t δ,
  HasDerivAt (fun r => s₁ r x) (s₂ s x) s
```

Under the hood, the relevant generic chain-rule lemmas are in `IntervalFlooredSourceTimeDataIterate.lean`:

```lean
srcSlice1
srcSlice2
hasDerivAt_srcSlice
hasDerivAt_srcSlice1
flooredSourceTimeData_of_iterate
```

For your heat-level-0 case, the missing analytic content is the heat PDE identity

```text
∂τ intervalDomainLift (conjugatePicardIter p u₀ 0 τ) x
  = heatDu u₀ τ x
  = ΔS(τ)u₀(x)
```

and similarly

```text
∂τ heatDu u₀ τ x = heatD2u u₀ τ x = Δ²S(τ)u₀(x).
```

The repo’s `IntervalHeatSemigroupFlooredSourceTimeData.lean` is exactly the intended location for those heat-specific obligations: its fields `d0` and `d1` are stated precisely in the shape consumed by `cosineCoeffs_hasDerivAt_of_smooth_param`.

The closest already-proved first-derivative analogue is in `IntervalPicardLevel0SourceTimeC1On.lean`:

```lean
heatSlice_field_hasDerivWithinAt
heatSourceDot_jointContinuousOn
heatSourceCoeff_hasDerivWithinAt
```

That file is for the logistic source, not the concrete `ν·u^γ` source, but the pattern is the same: prove the heat-slice time derivative first, chain through the nonlinear source, then apply the cosine-coefficient Leibniz lemma.

### `h_cont_deriv`

For the first differentiation, `H.d0 t ht` gives exactly:

```lean
ContinuousOn (Function.uncurry s₁)
  (Icc (t - δ) (t + δ) ×ˢ Icc (0:ℝ) 1)
```

For the second differentiation, `H.d1 t ht` gives exactly:

```lean
ContinuousOn (Function.uncurry s₂)
  (Icc (t - δ) (t + δ) ×ˢ Icc (0:ℝ) 1)
```

Then the continuity of the coefficient of `s₂` is supplied by

```lean
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

from `IntervalDomainPositiveWindowK1OnEndpoint.lean`, as shown in `heatLevel0_srcCoeff2_continuousAt` above.

## Notes on `intervalDomainLift` and level 0

`conjugatePicardIter` level 0 is definitionally the heat semigroup:

```lean
conjugatePicardIter p u₀ 0
  = fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

So when proving the heat PDE identity directly, the useful local rewrite on `x ∈ Icc 0 1` is essentially:

```lean
simp [intervalDomainLift, conjugatePicardIter, hx]
```

or, if you route through the older `picardIter` heat-slice lemmas, use the already-existing level-0 definitional equalities in `IntervalConjugateLevel0BFormSourceOn.lean` as the model.  The important point is that the time derivative should be proved for the heat representation and then transported through `srcSlice1`; do not try to make `fun_prop` discover this through `intervalDomainLift` and `intervalFullSemigroupOperator` automatically.

## Recommended implementation order

1. In `IntervalHeatSemigroupFlooredSourceTimeData.lean`, fill or expose the heat-specific `d0` field:
   - local positive-time slab, e.g. choose `δ ≤ t / 2`,
   - heat field derivative `HasDerivAt (fun r => intervalDomainLift (conjugatePicardIter p u₀ 0 r) x) (heatDu u₀ s x) s`,
   - chain through `hasDerivAt_srcSlice`,
   - prove joint continuity of `srcSlice1` from heat profile continuity, `heatDu` continuity, and positivity/floor.

2. Fill or expose the `d1` field similarly:
   - derivative of `heatDu` is `heatD2u`,
   - chain through `hasDerivAt_srcSlice1`,
   - prove joint continuity of `srcSlice2`.

3. Use the `heatLevel0_srcTimeCoeff_hasDerivAt` and `heatLevel0_srcCoeff1_hasDerivAt` snippets above.  These are direct, low-risk applications of the existing cosine coefficient Leibniz theorem.

4. Assemble `ContDiffAt ℝ 2` either by the public `srcTimeCoeff_contDiffAt H k ht` theorem or by a small generic calculus lemma like `contDiffAt_two_of_hasDerivAt_chain`.

## Bottom line

The formula for `f₁` is:

```text
ν·γ·(S(τ)u₀)^(γ-1)·ΔS(τ)u₀.
```

In Lean, use:

```lean
srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)
```

The exact proof that applies `cosineCoeffs_hasDerivAt_of_smooth_param` is `heatLevel0_srcTimeCoeff_hasDerivAt` above.  Its three supplied arguments are not mysterious:

```text
hf_int        ← H.d0 eventual ContinuousOn, converted to IntervalIntegrable
h_diff        ← H.d0 pointwise HasDerivAt field
h_cont_deriv  ← H.d0 joint ContinuousOn field
```

and the second derivative layer is identical with `H.d1` and `srcSlice2`.
