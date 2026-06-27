# Q1116 / cron1 — proof strategy for `cutoffResolverTerm_contDiff_two`

Repo inspected: `xiangyazi24/Shen_work`

Files inspected:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
ShenWork/Paper2/IntervalMildPicardRegularity.lean
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalUnderIntegralLeibniz.lean
```

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

The cleanest route is **not** to try to make `fun_prop` see through `resolverTimeCoeff` directly, and not to prove `ContDiff` of the full `(t,x)` term by expanding all integrals inline.

Instead, split the proof into a scalar coefficient lemma and then use the same product decomposition as the heat proof:

```lean
cutoffResolverTerm p u c k q
  = (smoothRightCutoff (c/2) c q.1 * resolverTimeCoeff p u k q.1)
      * cosineMode k q.2
```

Then prove:

```lean
ContDiff ℝ 2 (fun t => smoothRightCutoff (c/2) c t * resolverTimeCoeff p u k t)
```

as a **one-dimensional scalar lemma**, and the final `(t,x)` theorem becomes routine:

```lean
have hcoef_q : ContDiff ℝ 2
    (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1 * resolverTimeCoeff p u k q.1) :=
  hcoef.comp contDiff_fst

have hcos_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => cosineMode k q.2) := by
  have hcos : ContDiff ℝ 2 (cosineMode k) := by
    unfold cosineMode
    fun_prop
  exact hcos.comp contDiff_snd

simpa [cutoffResolverTerm, mul_assoc] using hcoef_q.mul hcos_q
```

The scalar coefficient lemma is where all analytic content lives. For that scalar lemma, use the repo’s existing `cosineCoeffs_hasDerivAt_of_smooth_param` twice, not a nonexistent one-shot `ContDiff` theorem for parameterized `cosineCoeffs`.

## Direct answers to the three questions

### 1. Is there a theorem that `cosineCoeffs` of a smooth function is smooth in parameters?

Not as a single ready-made theorem of the exact shape you need.

What exists in the repo is the correct **one-derivative Leibniz brick**:

```lean
import ShenWork.Paper2.IntervalMildPicardRegularity

open MeasureTheory Filter Topology
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

#check ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
```

It has the shape:

```lean
theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_int : ∀ᶠ s in 𝓝 τ, IntervalIntegrable (f s) volume (0 : ℝ) 1)
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ
```

There is also the continuity bridge:

```lean
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint

open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint

#check cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

So the intended stack is:

```text
f₀(t,x) = ν * heat(t,x)^γ
f₁(t,x) = ∂ₜ f₀(t,x)
f₂(t,x) = ∂ₜ f₁(t,x)

cosineCoeffs_hasDerivAt_of_smooth_param f₀ f₁  ==> derivative of coeff₀ is coeff₁
cosineCoeffs_hasDerivAt_of_smooth_param f₁ f₂  ==> derivative of coeff₁ is coeff₂
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc f₂ ==> coeff₂ continuous
assemble ContDiffAt ℝ 2 for srcTimeCoeff
multiply by constant resolver weight ==> ContDiffAt ℝ 2 for resolverTimeCoeff
multiply by cutoff ==> ContDiff ℝ 2 for cutoff resolver coefficient
multiply by cos(kπx) composed with snd ==> ContDiff ℝ 2 in (t,x)
```

This is exactly what `IntervalPhysicalSourceTimeC2Concrete.lean` started to do through `FlooredSourceTimeData`: it proves/uses `srcTimeCoeff_hasDerivAt`, `cosS1_hasDerivAt`, and `cosS2_continuousAt`, then has a still-sorry `srcTimeCoeff_contDiffAt`. For the direct resolver route, copy that logic but feed it direct heat positive-time data instead of `FlooredSourceTimeData`.

### 2. Should I bypass this and prove `ContDiff` of the cutoff resolver term as a function of `(t,x)` directly?

No, not inline.

You should bypass `FlooredSourceTimeData`, but **not** bypass the scalar coefficient layer. The full `(t,x)` term is a product of a time-only coefficient and a space-only cosine. Proving it directly makes every goal harder because you carry product projections and interval-integral differentiability through a two-variable term.

Use this factorization:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff smoothRightCutoff_contDiff)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- The scalar cutoff coefficient. -/
def cutoffResolverCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t

/-- This is the right analytic target. -/
theorem cutoffResolverCoeff_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2
      (cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k) := by
  -- prove this by local ContDiffAt cases in t:
  --   t < c/2: cutoff is locally zero;
  --   t ≥ c/2: t is positive, so resolverTimeCoeff is ContDiffAt ℝ 2;
  -- then assemble with ContDiffAt / ContDiff.
  sorry

/-- Once the scalar coefficient is known, the `(t,x)` term is mechanical. -/
theorem cutoffResolverTerm_contDiff_two_from_coeff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef : ContDiff ℝ 2
      (cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k) :=
    cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hc k
  have hcoef_q : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k q.1) :=
    hcoef.comp contDiff_fst
  have hcos : ContDiff ℝ 2 (cosineMode k) := by
    unfold cosineMode
    fun_prop
  have hcos_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => cosineMode k q.2) :=
    hcos.comp contDiff_snd
  simpa [cutoffResolverCoeff, cutoffResolverTerm, mul_assoc] using hcoef_q.mul hcos_q

end ShenWork.Paper2.HeatResolverJointC2Direct
```

This is the closest analogue of `cutoffHeatTerm_contDiff_two` that still respects the fact that the resolver coefficient is not elementary.

### 3. Can I decompose the resolver term like the heat term using `ContDiff.mul` and `fun_prop`?

Yes, but only **after** you prove the scalar resolver coefficient is `ContDiff`.

For the heat term, everything is elementary:

```lean
exp(-t * λ) * ahat * cosineMode k x
```

so `fun_prop` closes the term-level smoothness.

For the resolver term, this part is not elementary:

```lean
resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

Lean will not unfold through:

```text
intervalNeumannResolverCoeff
intervalNeumannResolverSourceCoeff
cosineCoeffs
interval integral
Real.rpow of heat profile
```

and discover smoothness automatically. You need a lemma of this shape:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.Paper2.IntervalMildPicardRegularity

open Filter Topology MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Direct positive-time C² of the source coefficient, avoiding FlooredSourceTimeData. -/
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  -- Define direct heat source slices:
  --   f₀ τ x = p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 τ) x ^ p.γ
  --   f₁ τ x = p.ν * p.γ * heat(t,x)^(p.γ-1) * heatDu τ x
  --   f₂ τ x = ... heatD2u ...
  -- Pick δ > 0 with Metric.ball t δ ⊆ Ioi 0.
  -- Prove:
  --   HasDerivAt (fun r => f₀ r x) (f₁ s x) s for x∈Ioo, s∈ball
  --   ContinuousOn (uncurry f₁) on slab
  -- and apply cosineCoeffs_hasDerivAt_of_smooth_param.
  -- Repeat f₁ -> f₂, then use coefficient continuity of f₂.
  -- Finally assemble ContDiffAt ℝ 2.
  sorry

/-- Resolver coefficient C² follows by constant elliptic weight. -/
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  have hsrc := heatLevel0_srcTimeCoeff_contDiffAt_two
    (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k =
      (fun t => ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t) := by
    funext t
    exact resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k t
  rw [hEq]
  exact contDiffAt_const.mul hsrc

end ShenWork.Paper2.HeatResolverJointC2Direct
```

Then `cutoffResolverCoeff_contDiff_two` is a localization wrapper around `heatLevel0_resolverTimeCoeff_contDiffAt_two`.

## Recommended lemma stack

Implement in this order.

### Lemma 1: direct source coefficient `ContDiffAt` at positive time

This is the real analytic core. It replaces the FSTD-dependent `srcTimeCoeff_contDiffAt`.

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  sorry

end ShenWork.Paper2.HeatResolverJointC2Direct
```

Inside this lemma, use:

```text
cosineCoeffs_hasDerivAt_of_smooth_param f₀ f₁
cosineCoeffs_hasDerivAt_of_smooth_param f₁ f₂
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc f₂
```

and assemble via `contDiffAt_succ_iff` / a local helper patterned after the still-sorry `srcTimeCoeff_contDiffAt` in `IntervalPhysicalSourceTimeC2Concrete.lean`.

### Lemma 2: resolver coefficient `ContDiffAt` from source coefficient `ContDiffAt`

This should be short.

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete

open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

theorem heatLevel0_resolverTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  have hsrc := heatLevel0_srcTimeCoeff_contDiffAt_two
    (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k =
      fun t => ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t := by
    funext t
    exact resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k t
  rw [hEq]
  exact contDiffAt_const.mul hsrc

end ShenWork.Paper2.HeatResolverJointC2Direct
```

### Lemma 3: cutoff scalar coefficient is global `ContDiff`

This is the clean localization wrapper.

```lean
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff

open Filter Topology
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff smoothRightCutoff_contDiff smoothRightCutoff_eventually_eq_one)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

def cutoffResolverCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t

theorem cutoffResolverCoeff_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2
      (cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k) := by
  -- Suggested proof structure:
  -- rw [contDiff_iff_contDiffAt]
  -- intro t
  -- by_cases htpos : 0 < t
  -- · product of smooth cutoff and heatLevel0_resolverTimeCoeff_contDiffAt_two htpos
  -- · if t < c/2, cutoff is locally zero; use eventuallyEq to const 0
  --   if t = c/2, then c/2 > 0, so use the positive-time coefficient lemma.
  -- A slightly cleaner split is by `t < c / 2`, `t = c / 2`, `c / 2 < t`.
  sorry

end ShenWork.Paper2.HeatResolverJointC2Direct
```

Important detail: because `c/2 > 0`, the boundary point `t = c/2` is still a positive time. So even though the cutoff begins to turn on there, the resolver coefficient is smooth in a neighborhood of that point. For `t < c/2`, the cutoff is locally zero, so no coefficient regularity is needed.

### Lemma 4: the existing term theorem becomes mechanical

Replace the current `cutoffResolverTerm_contDiff_two` body by a one-line product proof using the scalar lemma.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef : ContDiff ℝ 2
      (cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k) :=
    cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hc k
  have hcoef_q : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k q.1) :=
    hcoef.comp contDiff_fst
  have hcos : ContDiff ℝ 2 (cosineMode k) := by
    unfold cosineMode
    fun_prop
  have hcos_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => cosineMode k q.2) :=
    hcos.comp contDiff_snd
  simpa [cutoffResolverCoeff, cutoffResolverTerm, mul_assoc] using hcoef_q.mul hcos_q

end ShenWork.Paper2.HeatResolverJointC2Direct
```

This is exactly the heat proof’s product style, except the time coefficient smoothness is hidden behind `cutoffResolverCoeff_contDiff_two` instead of `fun_prop`.

## Why not expand `resolverTimeCoeff` in `cutoffResolverTerm_contDiff_two`?

Expanding it too early produces goals involving:

```text
intervalNeumannResolverCoeff
intervalNeumannResolverSourceCoeff
Complex.re
cosineCoeffs
intervalIntegral
Real.rpow
intervalDomainLift (conjugatePicardIter p u₀ 0 t)
```

all inside a two-variable product. That is the worst possible proof shape. The existing repo already separated the hard part into time-Leibniz lemmas for cosine coefficients; use that separation.

The correct abstraction boundary is:

```text
positive-time heat source coefficient is ContDiffAt ℝ 2 in t
        ↓ constant resolver weight
positive-time resolver coefficient is ContDiffAt ℝ 2 in t
        ↓ smooth cutoff localization
cutoff resolver scalar coefficient is global ContDiff ℝ 2 in t
        ↓ product with cosineMode ∘ snd
cutoff resolver term is global ContDiff ℝ 2 in (t,x)
```

## Concrete recommendation for `IntervalHeatResolverJointC2.lean`

Add these helpers before the current `cutoffResolverTerm_contDiff_two`:

```lean
-- 1. Direct positive-time source coefficient C².
theorem heatLevel0_srcTimeCoeff_contDiffAt_two ... :
  ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  sorry

-- 2. Direct positive-time resolver coefficient C².
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two ... :
  ContDiffAt ℝ (2 : ℕ∞) (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  -- weight * source coefficient
  ...

-- 3. Scalar cutoff resolver coefficient.
def cutoffResolverCoeff ... :=
  fun t => smoothRightCutoff (c/2) c t * resolverTimeCoeff p u k t

theorem cutoffResolverCoeff_contDiff_two ... :
  ContDiff ℝ 2 (cutoffResolverCoeff p (conjugatePicardIter p u₀ 0) c k) := by
  sorry
```

Then replace `cutoffResolverTerm_contDiff_two` with the product proof above.

## Bottom line

There is no magic `fun_prop` path through `resolverTimeCoeff`. The proof should be layered.

Use the existing repo theorem `cosineCoeffs_hasDerivAt_of_smooth_param` to prove a scalar positive-time `ContDiffAt` theorem for the source coefficient, transfer it to `resolverTimeCoeff` by the constant elliptic weight, localize it with the smooth cutoff, and only then use `ContDiff.mul`/`fun_prop` for the elementary `(t,x)` product.

That is the cleanest Lean route and the closest faithful analogue of `cutoffHeatTerm_contDiff_two`.
