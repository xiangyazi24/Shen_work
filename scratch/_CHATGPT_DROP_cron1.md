# Q1716 (cron1) -- Laplacian / `laplBound` obstruction

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt I received was only:

```text
Q1716 (cron1): cron1 /tmp/q_cron1_laplacian.txt
```

The local file `/tmp/q_cron1_laplacian.txt` is not accessible through the GitHub connector. I used the connector only and inferred the target from the current `cron1` source-side Laplacian/envelope thread in the repository. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

The relevant files are:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalCosineCoeffDecay.lean
ShenWork/PDE/IntervalMildSourceDecayHelper.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
ShenWork/Paper2/IntervalMildPicardRegularity.lean
```

## Short answer

The fixed-time Laplacian/IBP step is already essentially present. The current global `hlaplBound` obligation is the problem.

At fixed positive time, this route works:

```text
sliceC2 + sliceNeumann
→ IntervalWeakH2Neumann
→ intervalWeakH2Neumann_cosineCoeff_quadratic_decay
→ |cosineCoeffs slice_t k| ≤ C_t / (kπ)^2, k ≥ 1
```

But the `FlooredSourceTimeData.laplBound` field asks for one constant `M` that works for **all** positive times:

```lean
laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧
  ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤
      M / ((k:ℝ) * Real.pi) ^ 2
```

That is not a local Laplacian coefficient estimate. It is a uniform-in-`t>0` spatial `C²` envelope. For heat level 0 with only bounded/continuous positive initial data, that uniform envelope is generally false as `t ↓ 0`.

## Where the current sorry sits

In `IntervalHeatSemigroupHighRegularity.lean`, the construction of physical resolver data has:

```lean
have hFSTD :=
  ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
    hu₀_bound hu₀_cont (p := p)
    (hfloor := by
      intro t ht x hx
      exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hx)
    (hsliceC2 := by intro i hi t ht; sorry)
    (hsliceNeumann := by intro i hi t ht; sorry)
    (hzerothBound := by intro i hi; sorry)
    (hlaplBound := by intro i hi; sorry)
```

The `hlaplBound` subgoal after `intro i hi` is:

```lean
∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
  |cosineCoeffs ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
    (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
    (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t) k|
  ≤ M / ((k : ℝ) * Real.pi) ^ 2
```

That is a single global envelope over all `t > 0`.

## What the existing Laplacian API gives

`IntervalCosineCoeffDecay.lean` contains the raw fixed-function ingredients:

```lean
theorem exists_laplacianCoeff_bound
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      |∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * deriv (deriv f) x| ≤ M
```

and:

```lean
theorem cosineCoeff_decay
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv f) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv f 0 = 0) (hbc1 : deriv f 1 = 0)
    {M : ℝ} (hMnonneg : 0 ≤ M)
    (hMbound : ∀ n : ℕ,
      |∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * deriv (deriv f) x| ≤ M)
    {n : ℕ} (hn : 1 ≤ n) :
    |∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x| ≤
      M / ((n : ℝ) * Real.pi) ^ 2
```

However, this is for a fixed `f`. The constant `M` comes from the fixed slice's second derivative, so if `f = slice_i t`, this produces `M_t`, not a single `M` for all positive `t`.

There is also a more directly useful normalized-coefficient wrapper in `IntervalMildSourceDecayHelper.lean`:

```lean
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ C / ((k : ℝ) * Real.pi) ^ 2
```

This theorem already accounts for the normalization of `cosineCoeffs`; for `k ≥ 1`, normalized coefficients carry the factor `2` relative to the raw integral. So prefer this wrapper rather than manually using `cosineCoeff_decay` unless you specifically need the raw integral theorem.

## Fixed-time lemma that should compile with minor namespace adjustments

This is the right local bridge from the current `sliceC2` and `sliceNeumann` fields to fixed-time coefficient decay:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalMildSourceDecayHelper
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam)
open ShenWork.PDE.IntervalMildSourceDecayHelper
  (IntervalWeakH2Neumann intervalWeakH2Neumann_of_contDiffOn
   intervalWeakH2Neumann_cosineCoeff_quadratic_decay)

namespace ShenWork.Paper2.Cron1Laplacian

/-- Fixed-time `C²` + Neumann endpoint data gives normalized cosine coefficient
quadratic decay for that one slice.  The output constant depends on this fixed `t`. -/
theorem slice_laplBound_fixed_time
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    {i : ℕ} {t : ℝ} (hi : i ≤ 2)
    (hC2 : ContDiffOn ℝ 2
      ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0 : ℝ) 1))
    (hNeu :
      Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t))
        (𝓝[Ioi 0] 0) (𝓝 0) ∧
      Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t))
        (𝓝[Iio 1] 1) (𝓝 0) ∧
      deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0 = 0 ∧
      deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 1 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤
        C / ((k : ℝ) * Real.pi) ^ 2 := by
  let f : ℝ → ℝ := (sliceFam (srcSlice p u) s₁ s₂ i) t
  have Hweak : IntervalWeakH2Neumann f :=
    intervalWeakH2Neumann_of_contDiffOn
      (g := f)
      (by simpa [f] using hC2)
      (by simpa [f] using hNeu.1)
      (by simpa [f] using hNeu.2.1)
      (by simpa [f] using hNeu.2.2.1)
      (by simpa [f] using hNeu.2.2.2)
  simpa [f] using intervalWeakH2Neumann_cosineCoeff_quadratic_decay Hweak

end ShenWork.Paper2.Cron1Laplacian
```

Use this to confirm the local Laplacian/IBP wiring. It gives exactly the right fixed-time result, but it cannot be used directly to fill the current `hlaplBound`, because `hlaplBound` needs one `C` independent of `t`.

## Why current `hlaplBound` is too strong

For `i = 0`, the slice is:

```lean
srcSlice p (conjugatePicardIter p u₀ 0) t x
= p.ν * (S(t)u₀(x)) ^ p.γ
```

For each fixed `t > 0`, heat smoothing makes this spatially smooth, so fixed-time `1/k²` decay is plausible and follows from `C²` + Neumann endpoint data.

But as `t ↓ 0`, `S(t)u₀` tends back to `u₀`. Under the current hypotheses, `u₀` is only continuous and coefficient-bounded:

```lean
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
hu₀_cont  : Continuous u₀
hu₀_pos   : ∀ x, 0 < u₀ x
```

There is no `C²` or Neumann regularity assumption on `u₀`, and no `(kπ)⁻²` coefficient decay assumption on `p.ν * u₀^p.γ`. A single `M` satisfying the current `hlaplBound` for all `t > 0` would force a uniform `1/k²` decay all the way down to time zero. That is not a consequence of continuous initial data.

For `i = 1` and `i = 2`, the situation is even more singular: `heatDu` and `heatD2u` are spectral Laplacian / iterated Laplacian values. Their natural estimates contain factors like:

```text
λ_k * exp(-t λ_k)
λ_k^2 * exp(-t λ_k)
```

These are bounded for each fixed lower time `t ≥ a > 0`, but not uniformly as `a ↓ 0` from only bounded coefficients. The file already uses positive lower-time slabs such as `Ioi (t/2)` in the `heatDu_hasDerivAt` proof, which is the correct analytic shape.

So the present global-in-`t>0` `laplBound` field is not a mechanical missing proof. It is an overstrong specification.

## What would make `hlaplBound` true

Any one of the following structural changes would make the Laplacian envelope honest.

### Option A: lower-time-local envelope

Change the source data so the Laplacian envelope is allowed to depend on a positive lower time:

```lean
laplBoundOnIci : ∀ a : ℝ, 0 < a → ∀ i : ℕ, i ≤ 2 →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤
      M / ((k : ℝ) * Real.pi) ^ 2
```

For the cutoff resolver proof with cutoff `smoothRightCutoff (c/2) c`, use `a = c/2`. This matches the actual smoothing estimates: once time is bounded away from zero, all spectral factors are uniformly controlled by exponential damping.

### Option B: cutoff-source coefficients

Instead of putting global bounds on raw source coefficients, define a cutoff source coefficient:

```lean
def cutoffSrcTimeCoeff
    (c : ℝ) (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) :
    ℝ → ℝ :=
  fun t => smoothRightCutoff (c / 2) c t * srcTimeCoeff p u k t
```

Then global-in-time `ContDiff` and global derivative bounds are plausible because the coefficient is identically zero near `t ≤ c/2`, and all nonzero-time estimates happen at positive times bounded away from zero.

This is the same reason the direct cutoff resolver term is the right construction path.

### Option C: strengthen initial data

If the theorem is intended to be global from raw coefficients, then assume something like:

```lean
∀ k : ℕ, 1 ≤ k →
  |cosineCoeffs (fun x => p.ν * intervalDomainLift u₀ x ^ p.γ) k| ≤
    M / ((k : ℝ) * Real.pi) ^ 2
```

or a true `C²`/Neumann certificate for `u₀` and its source power. But that is a much stronger theorem than the current heat-level0 result from continuous positive data.

## Concrete patch recommendation

Do **not** try to close:

```lean
(hlaplBound := by intro i hi; sorry)
```

under the current signature by calling `exists_laplacianCoeff_bound` inside `intro t ht`. That gives the wrong quantifier order:

```lean
∀ t > 0, ∃ M_t, ...
```

but the goal is:

```lean
∃ M, ∀ t > 0, ...
```

The correct immediate patch is to add the fixed-time lemma above, then refactor the data structure or cutoff assembler so it asks for one of the true statements:

```lean
∀ t > 0, ∃ M_t, ...
```

or:

```lean
∀ a > 0, ∃ M_a, ∀ t ≥ a, ...
```

For the current resolver cutoff proof, the second form is the useful one.

## Bottom line

The Laplacian IBP theorem is already available; the problem is uniformity near `t = 0`. Fixed-time source coefficient decay is fine. Uniform-in-all-positive-time `laplBound` is not derivable from the current assumptions and should be replaced by a lower-time-local/cutoff version, or the initial-data assumptions must be strengthened.
