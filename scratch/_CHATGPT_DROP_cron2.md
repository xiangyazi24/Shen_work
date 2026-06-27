# Q1095 (cron2) — direct cutoff resolver joint C²: exact `contDiff_tsum` inputs

Static GitHub-connector inspection only; I did **not** run Lean locally.

## Bottom line

For a direct cutoff resolver proof, the `contDiff_tsum` input shape is exactly the same as in the heat proof:

1. a per-mode `ContDiff ℝ 2` theorem;
2. a summable majorant `v : ℕ → ℕ → ℝ`, one summable sequence `v k` for each derivative order `k ≤ 2`;
3. a uniform bound
   ```lean
   ‖iteratedFDeriv ℝ k (mode n) q‖ ≤ v k n
   ```
   for all `q : ℝ × ℝ`, all modes `n`, and all derivative orders `k ≤ 2`.

For the resolver, the best existing wrapper is not to call `contDiff_tsum` directly.  Use the committed physical/bounded-weight wrapper:

```text
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
```

This wrapper already packages the `contDiff_tsum` call for series of the form

```text
(t,x) ↦ ∑' n, c n t * cosineMode n x
```

It reduces the direct cutoff resolver proof to three coefficient-level inputs for

```lean
cCut n t := smoothRightCutoff (c / 2) c t *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) n t
```

namely:

```lean
∀ n, ContDiff ℝ (2 : ℕ∞) (cCut n)
∀ i n t, i ≤ 2 → ‖iteratedFDeriv ℝ i (cCut n) t‖ ≤ BtCut i n
∀ k, (k : ℕ∞) ≤ 2 → Summable (boundedWeightJointMajorant BtCut k)
```

Then `boundedWeightJointSeries_contDiff_two` supplies the joint `(t,x)` `ContDiff ℝ 2` of the cutoff resolver value series.

## 1. `contDiff_tsum` signature, as used here

The relevant Mathlib theorem is imported through:

```lean
import Mathlib.Analysis.Calculus.SmoothSeries
```

The instantiated signature used in `IntervalHeatSemigroupHighRegularity.lean` and `IntervalResolverJointC2Physical.lean` is:

```lean
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology

noncomputable section

/-- Instantiated shape of `contDiff_tsum` for this repo's uses.

In the heat and resolver applications:
* index type `ι = ℕ`,
* domain `E = ℝ × ℝ`,
* codomain `F = ℝ`,
* smoothness order `n = 2`,
* mode family `f : ℕ → ℝ × ℝ → ℝ`,
* majorant `v : ℕ → ℕ → ℝ`.
-/
example
    (f : ℕ → ℝ × ℝ → ℝ)
    (v : ℕ → ℕ → ℝ)
    (hTerm : ∀ n : ℕ, ContDiff ℝ (2 : ℕ∞) (f n))
    (hSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (v k))
    (hBound : ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k (f n) q‖ ≤ v k n) :
    ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => ∑' n : ℕ, f n q) := by
  exact contDiff_tsum
    (𝕜 := ℝ) (f := f) (v := v)
    hTerm hSumm hBound
```

The fully generic theorem has the same logical shape over a complete normed target:

```lean
-- schematic generic shape
contDiff_tsum :
  (∀ i, ContDiff 𝕜 N (f i)) →
  (∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k)) →
  (∀ (k : ℕ) (i : ι) (x : E), (k : ℕ∞) ≤ N →
    ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) →
  ContDiff 𝕜 N (fun x => ∑' i, f i x)
```

## 2. Exact heat inputs in `IntervalHeatSemigroupHighRegularity.lean`

The heat proof uses:

```lean
f := cutoffHeatTerm u₀ c
v := v
```

where the term is:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupJointRegularity

#check heatTerm
#check heatTerm_contDiff
#check cutoffHeatTerm
#check cutoffHeatTerm_contDiff_two
#check cutoffHeatTerm_iteratedFDeriv_bound
#check cutoffHeatSeries_contDiff_two
#check heatSeries_eventuallyEq_cutoff
#check heatSemigroup_jointContDiffAt_two

end ShenWork.Paper2.HeatSemigroupJointRegularity
```

### Heat per-term `ContDiff`

Exact theorem:

```text
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatTerm_contDiff_two
```

Shape:

```lean
cutoffHeatTerm_contDiff_two
  (u₀ : intervalDomainPoint → ℝ) {c : ℝ} (_hc : 0 < c) (n : ℕ) :
  ContDiff ℝ 2 (cutoffHeatTerm u₀ c n)
```

It is proved from:

```text
smoothRightCutoff_contDiff
heatTerm_contDiff
contDiff_fst
ContDiff.mul
```

The core proof pattern is:

```lean
have hφ : ContDiff ℝ 2 (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) :=
  (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).comp contDiff_fst
exact hφ.mul ((heatTerm_contDiff u₀ n).of_le le_top)
```

### Heat majorant definition

The private heat majorant is:

```lean
private noncomputable def cutoffHeatMajorant (c M₀ : ℝ) (hc : 0 < c) (k : ℕ)
    (_hk : (k : ℕ∞) ≤ 2) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) *
      if hi : (i : ℕ∞) ≤ 2
      then smoothRightCutoffDerivBound (c / 2) c (by linarith) i hi
      else 0) *
    (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
      Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)))
```

Inside `cutoffHeatSeries_contDiff_two`, the actual `v` passed to `contDiff_tsum` is proof-argument-free:

```lean
let v : ℕ → ℕ → ℝ := fun k n =>
  (∑ i ∈ Finset.range 3,
    (k.choose i : ℝ) *
      if hi : (i : ℕ∞) ≤ 2
      then smoothRightCutoffDerivBound (c / 2) c hc'c i hi
      else 0) *
    (4 * ((1 + unitIntervalCosineEigenvalue n) ^ k * M₀ *
      Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)))
```

### Heat summability input

Exact theorem used:

```text
ShenWork.Paper2.HeatSemigroupJointRegularity.one_add_eigenvalue_pow_mul_exp_summable
```

Shape:

```lean
private theorem one_add_eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ M₀ : ℝ} (hτ : 0 < τ) (hM₀ : 0 ≤ M₀) :
    Summable (fun n : ℕ =>
      (1 + unitIntervalCosineEigenvalue n) ^ m * M₀ *
        Real.exp (-τ * unitIntervalCosineEigenvalue n))
```

It is used in the `contDiff_tsum` summability slot as:

```lean
exact ((one_add_eigenvalue_pow_mul_exp_summable k (half_pos hc) hM₀nn).mul_left 4).mul_left _
```

There is also a private theorem:

```text
cutoffHeatMajorant_summable
```

but the final `contDiff_tsum` proof in `cutoffHeatSeries_contDiff_two` inlines the range-3 majorant summability rather than using `cutoffHeatMajorant_summable` directly.

### Heat derivative bound input

Exact theorem:

```text
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatTerm_iteratedFDeriv_bound
```

Shape:

```lean
theorem cutoffHeatTerm_iteratedFDeriv_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) (k n : ℕ) (q : ℝ × ℝ)
    (hk : (k : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤
      cutoffHeatMajorant c M₀ hc k hk n
```

It is then transferred to the proof-argument-free `v k n` by showing

```lean
cutoffHeatMajorant c M₀ hc k hk n ≤ v k n
```

The internal tools used by the heat bound are:

```text
norm_iteratedFDeriv_mul_le
norm_iteratedFDeriv_comp_fst_le
norm_iteratedFDeriv_comp_snd_le
smoothRightCutoffDerivBound_spec
smoothRightCutoffDerivBound_nonneg
heatTerm_iteratedFDeriv_global_bound
cosineMode_iteratedFDeriv_bound
```

The split is important:

* If `q.1 < c/2`, `smoothRightCutoff = 0` locally, so every derivative of the cutoff term is `0`.
* If `c/2 ≤ q.1`, the exponential factor gives the uniform summable bound
  ```text
  exp(-q.1 λ_n) ≤ exp(-(c/2) λ_n).
  ```

## 3. Resolver analogue: recommended exact input structure

For the resolver value series

```text
∑' n, resolverTimeCoeff p u n t * cosineMode n x
```

with

```text
resolverTimeCoeff p u n t = intervalNeumannResolverWeight p n * srcTimeCoeff p u n t,
w_n = intervalNeumannResolverWeight p n = 1/(μ + λ_n),
u = conjugatePicardIter p u₀ 0,
```

the direct cutoff coefficient should be:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalResolverJointC2Physical
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant boundedWeightJointSeries_contDiff_two)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff (smoothRightCutoff)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

/-- Coefficient-level cutoff for the direct resolver value series. -/
def cutoffResolverCoeff
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ) : ℕ → ℝ → ℝ :=
  fun n t => smoothRightCutoff (c / 2) c t *
    resolverTimeCoeff p (conjugatePicardIter p u₀ 0) n t

/-- Mode term for the cutoff resolver value series. -/
def cutoffResolverValueTerm
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ) (n : ℕ) :
    ℝ × ℝ → ℝ :=
  boundedWeightJointTerm (cutoffResolverCoeff p u₀ c) n

end ShenWork.Paper2.HeatResolverJointRegularity
```

Then there are two equivalent routes.

### Route 3A: call `contDiff_tsum` directly

You would need:

```lean
-- Term smoothness:
hTerm : ∀ n : ℕ,
  ContDiff ℝ (2 : ℕ∞) (cutoffResolverValueTerm p u₀ c n)

-- Summable majorant:
hSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (v k)

-- Iterated derivative bound:
hBound : ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
  ‖iteratedFDeriv ℝ k (cutoffResolverValueTerm p u₀ c n) q‖ ≤ v k n
```

and then:

```lean
example
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {c : ℝ}
    (v : ℕ → ℕ → ℝ)
    (hTerm : ∀ n : ℕ,
      ContDiff ℝ (2 : ℕ∞) (cutoffResolverValueTerm p u₀ c n))
    (hSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (v k))
    (hBound : ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k (cutoffResolverValueTerm p u₀ c n) q‖ ≤ v k n) :
    ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ =>
      ∑' n : ℕ, cutoffResolverValueTerm p u₀ c n q) := by
  exact contDiff_tsum
    (𝕜 := ℝ) (f := cutoffResolverValueTerm p u₀ c) (v := v)
    hTerm hSumm hBound
```

### Route 3B: use the existing bounded-weight wrapper

This is cleaner and should be preferred.

Use the existing theorem:

```text
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
```

Signature:

```lean
#check ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two

-- boundedWeightJointSeries_contDiff_two
--   {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
--   (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
--   (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 →
--      ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
--   (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
--      Summable (boundedWeightJointMajorant Bt k)) :
--   ContDiff ℝ (2 : ℕ∞)
--     (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q)
```

With `c := cutoffResolverCoeff p u₀ c`, the exact three inputs become:

```lean
hCoeffContDiff : ∀ n : ℕ,
  ContDiff ℝ (2 : ℕ∞) (cutoffResolverCoeff p u₀ c n)

hCoeffBound : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (cutoffResolverCoeff p u₀ c n) t‖ ≤ BtCut i n

hValueSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointMajorant BtCut k)
```

Then the proof is one line:

```lean
example
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {c : ℝ}
    (BtCut : ℕ → ℕ → ℝ)
    (hCoeffContDiff : ∀ n : ℕ,
      ContDiff ℝ (2 : ℕ∞) (cutoffResolverCoeff p u₀ c n))
    (hCoeffBound : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (cutoffResolverCoeff p u₀ c n) t‖ ≤ BtCut i n)
    (hValueSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant BtCut k)) :
    ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ =>
      ∑' n : ℕ, boundedWeightJointTerm (cutoffResolverCoeff p u₀ c) n q) := by
  exact boundedWeightJointSeries_contDiff_two
    hCoeffContDiff hCoeffBound hValueSumm
```

## 4. Resolver per-term `ContDiff`: what should prove it?

The direct coefficient-level theorem should have this shape:

```lean
/-- Needed new direct-cutoff coefficient smoothness lemma. -/
theorem cutoffResolverCoeff_contDiff_two
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (cutoffResolverCoeff p u₀ c n) := by
  -- needs positive-time C² of `resolverTimeCoeff` on the support/transition region
  sorry
```

If one already had global source coefficient smoothness:

```lean
hsrc : ContDiff ℝ (2 : ℕ∞)
  (srcTimeCoeff p (conjugatePicardIter p u₀ 0) n)
```

then the proof would be purely formal:

```lean
have hφ : ContDiff ℝ (2 : ℕ∞) (smoothRightCutoff (c / 2) c) :=
  smoothRightCutoff_contDiff
have hres : ContDiff ℝ (2 : ℕ∞)
    (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) n) := by
  rw [ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_smul]
  exact contDiff_const.smul hsrc
show ContDiff ℝ (2 : ℕ∞)
  (fun t => smoothRightCutoff (c / 2) c t *
    resolverTimeCoeff p (conjugatePicardIter p u₀ 0) n t)
exact hφ.mul hres
```

Existing theorem names relevant here:

```text
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_contDiff
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_weight_smul
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_smul
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_iteratedFDeriv_eq
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_bound
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_eq_cosineCoeffs
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiffAt
ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
```

Important caveat: `srcTimeCoeff_contDiffAt` and `physicalSourceTimeC2_of_floored` are not the clean direct heat cutoff route.  In the current repo they are part of the `FlooredSourceTimeData` lane, and they still contain `sorry`s.  A direct cutoff proof needs a heat-specific positive-time/windowed replacement, not the current all-global `PhysicalSourceTimeC2` bridge.

### The subtlety: global `ContDiff` vs positive-time `ContDiffAt`

`contDiff_tsum` and `boundedWeightJointSeries_contDiff_two` require **global** `ContDiff ℝ 2` of each cutoff mode.  Positive-time `ContDiffAt` of `srcTimeCoeff` is not literally enough unless you also prove a cutoff/gluing lemma.

For the one-sided heat cutoff this was automatic because `heatTerm` is globally smooth in `t`.  For the resolver source coefficient, the natural smoothness is only for `t > 0`.  Therefore the direct resolver cutoff proof needs one of these two additional pieces:

1. prove `cutoffResolverCoeff_contDiff_two` directly, using that `smoothRightCutoff (c/2) c` is identically zero on `(-∞, c/2]` and the resolver coefficient is `C²` on the open positive region; or
2. use a two-sided compactly supported cutoff already in the repo:
   ```text
   ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff
   ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_contDiff
   ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_eventually_eq_one
   ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_eq_zero_of_le_left
   ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_eq_zero_of_right_le
   ```
   and prove the coefficient is smooth only on the compact positive support.

The second option is often safer if only local-in-time source coefficient bounds are available.  The prompt's one-sided `smoothRightCutoff` route is fine only if the needed coefficient envelopes are uniform for all `t ≥ c/2`.

## 5. Resolver coefficient majorant: exact shape

Let `Es i n` be a source coefficient envelope on the positive cutoff support:

```lean
hSrcBound : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → c / 2 ≤ t →
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p (conjugatePicardIter p u₀ 0) n) t‖ ≤ Es i n
```

and let `Φ j` bound the cutoff derivatives:

```lean
hΦ : ∀ j : ℕ, (j : ℕ∞) ≤ 2 → ∀ t : ℝ,
  ‖iteratedFDeriv ℝ j (smoothRightCutoff (c / 2) c) t‖ ≤ Φ j
```

Then the coefficient-level cutoff envelope should be a finite Leibniz sum:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2Physical

open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalResolverJointC2Physical (boundedWeightJointMajorant)
open ShenWork.PDE (intervalNeumannResolverWeight)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

/-- Expected coefficient-level majorant for
`∂ₜʲ (φ · resolverTimeCoeff_n)`.

Here `Es l n` bounds `∂ₜˡ srcTimeCoeff_n` on the positive cutoff support and
`Φ i` bounds `∂ₜⁱ φ`.  The elliptic resolver weight is folded in by
`resolverTimeCoeff = w_n * srcTimeCoeff`.
-/
def cutoffResolverCoeffMajorant
    (p : CM2Params) (Φ : ℕ → ℝ) (Es : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun j n =>
    ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * Φ i *
        (intervalNeumannResolverWeight p n * Es (j - i) n)

end ShenWork.Paper2.HeatResolverJointRegularity
```

The coefficient derivative bound needed by `boundedWeightJointSeries_contDiff_two` is then:

```lean
theorem cutoffResolverCoeff_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {c : ℝ} (hc : 0 < c)
    (Φ : ℕ → ℝ) (Es : ℕ → ℕ → ℝ)
    (hSrcC2 : ∀ n, ContDiffOn ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) n) (Set.Ici (c / 2)))
    (hSrcBound : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → c / 2 ≤ t →
      ‖iteratedFDeriv ℝ i
        (srcTimeCoeff p (conjugatePicardIter p u₀ 0) n) t‖ ≤ Es i n)
    (hΦ : ∀ j : ℕ, (j : ℕ∞) ≤ 2 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (smoothRightCutoff (c / 2) c) t‖ ≤ Φ j)
    (j n : ℕ) (t : ℝ) (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (cutoffResolverCoeff p u₀ c n) t‖ ≤
      cutoffResolverCoeffMajorant p Φ Es j n := by
  -- proof pattern:
  -- * if t < c/2, the cutoff coefficient is locally zero;
  -- * if c/2 ≤ t, use `norm_iteratedFDeriv_mul_le` in one dimension;
  -- * use `resolverTimeCoeff_eq_smul` / `resolverTimeCoeff_iteratedFDeriv_eq`
  --   to move derivatives to `srcTimeCoeff` and multiply by `w_n`.
  sorry
```

The existing names for this proof are:

```text
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eq_zero_of_le
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eq_one_of_ge
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eventually_eq_one
ShenWork.IntervalResolverSpectralJointC2CutoffBounds.norm_iteratedFDeriv_comp_fst_le
ShenWork.IntervalResolverSpectralJointC2CutoffBounds.norm_iteratedFDeriv_comp_snd_le
norm_iteratedFDeriv_mul_le
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_smul
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_iteratedFDeriv_eq
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_bound
ShenWork.IntervalPhysicalResolverDataConcrete.resolverWeight_nonneg
```

## 6. Resolver summability input

For the value series, after defining `BtCut := cutoffResolverCoeffMajorant p Φ Es`, the exact summability goal is:

```lean
∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointMajorant BtCut k)
```

The relevant existing majorant machinery is:

```text
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointMajorant
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one
ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu
ShenWork.IntervalResolverJointC2PhysicalConcrete.valueCosWeight_one_mul_resolverWeight_le
```

The source-side decay/summability ingredients are:

```text
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_eq_cosineCoeffs
ShenWork.IntervalCosineCoeffDecay.exists_laplacianCoeff_bound
ShenWork.IntervalCosineCoeffDecay.cosineCoeff_decay
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
ShenWork.IntervalDomainPositiveWindowK1OnEndpoint.cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

The expected direct heat Level0 summability proof is finite-sum bookkeeping:

1. each `Es i n` has `n=0` bounded separately and `n≥1` decay like `C_i / ((n : ℝ) * π)^2`;
2. multiply by `w_n = 1/(μ+λ_n)`;
3. multiply by the spatial `valueCosWeight` from `boundedWeightJointMajorant`;
4. use `λ_n * w_n ≤ 1` and p-series summability.

This is exactly the bounded-weight mechanism already encoded abstractly by `PhysicalSourceTimeC2.value_summable`; the direct cutoff route needs the heat-specific, positive-window version of that proof rather than routing through `PhysicalSourceTimeC2`.

## 7. Gradient analogue, needed for resolver-gradient joint C²

For `3D` / resolver-gradient joint C², use the existing gradient wrapper:

```text
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradTerm
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradTerm_contDiff
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradTerm_iteratedFDeriv_le
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradSeries_contDiff_two
```

The coefficient inputs `hCoeffContDiff` and `hCoeffBound` are the same.  Only the summability target changes to:

```lean
∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointGradMajorant BtCut k)
```

This is exactly the analogue of `PhysicalSourceTimeC2.grad_summable`.

## 8. Existing theorem coverage vs missing direct-cutoff lemmas

### Already existing and directly reusable

```text
-- cutoff shape / eventual equality
smoothRightCutoff
smoothRightCutoff_contDiff
smoothRightCutoff_eq_zero_of_le
smoothRightCutoff_eq_one_of_ge
smoothRightCutoff_eventually_eq_one

-- two-sided local cutoff alternative
restartSmoothCutoff
restartSmoothCutoff_contDiff
restartSmoothCutoff_eventually_eq_one
restartSmoothCutoff_eq_zero_of_le_left
restartSmoothCutoff_eq_zero_of_right_le

-- heat template
heatTerm
heatTerm_contDiff
cutoffHeatTerm
cutoffHeatTerm_contDiff_two
cutoffHeatTerm_iteratedFDeriv_bound
cutoffHeatSeries_contDiff_two
heatSeries_eventuallyEq_cutoff
heatSemigroup_jointContDiffAt_two

-- resolver bounded-weight series wrapper
boundedWeightJointTerm
boundedWeightJointMajorant
boundedWeightJointTerm_contDiff
boundedWeightJointTerm_iteratedFDeriv_le
boundedWeightJointSeries_contDiff_two

-- resolver coefficient factorization
srcTimeCoeff
resolverTimeCoeff
resolverTimeCoeff_eq_weight_smul
resolverTimeCoeff_eq_smul
resolverTimeCoeff_iteratedFDeriv_eq
resolverTimeCoeff_bound
resolverWeight_nonneg

-- source coefficient / IBP ingredients
srcTimeCoeff_eq_cosineCoeffs
cosineCoeffs_hasDerivAt_of_smooth_param
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
exists_laplacianCoeff_bound
cosineCoeff_decay
```

### Still missing for the clean direct heat resolver cutoff proof

These are the exact new lemmas I would add:

```text
heatLevel0_srcTimeCoeff_contDiffOn_positive_window
  -- source coefficients for ν·(S(t)u₀)^γ are C² in t on a positive window

heatLevel0_srcTimeCoeff_window_bound
  -- uniform-in-t-on-window bounds for ∂ₜⁱ srcTimeCoeff, i ≤ 2, with (kπ)^-2 decay

cutoffResolverCoeff_contDiff_two
  -- global C² of φ(t) * resolverTimeCoeff_n(t), using cutoff/gluing

cutoffResolverCoeff_bound
  -- coefficient-level Leibniz envelope BtCut

cutoffResolverValueMajorant_summable
  -- ∀ k≤2, Summable (boundedWeightJointMajorant BtCut k)

cutoffResolverValueSeries_contDiff_two
  -- one-line application of boundedWeightJointSeries_contDiff_two

resolverSeries_eventuallyEq_cutoff
  -- φ=1 near target, so original resolver series equals cutoff series locally

heatResolverJointContDiffAt_two_direct
  -- eventual-equality transfer to the lifted coupled chemical concentration
```

For the gradient version, add:

```text
cutoffResolverGradMajorant_summable
cutoffResolverGradSeries_contDiff_two
heatResolverGradJointContDiffAt_two_direct
```

## Final assessment

The heat proof feeds `contDiff_tsum` with:

```text
cutoffHeatTerm_contDiff_two
one_add_eigenvalue_pow_mul_exp_summable / range-3 `v` summability
cutoffHeatTerm_iteratedFDeriv_bound
```

The resolver proof should feed the same three slots through the existing bounded-weight wrapper:

```text
boundedWeightJointSeries_contDiff_two
```

with:

```text
cutoffResolverCoeff_contDiff_two
cutoffResolverCoeff_bound
Summable (boundedWeightJointMajorant BtCut k)
```

The existing repo already has most of the generic machinery.  The missing work is not `contDiff_tsum` plumbing; it is the heat-specific positive-window source coefficient regularity/envelope package for `srcTimeCoeff`, plus the cutoff/gluing lemma that upgrades positive-time coefficient regularity into global `ContDiff ℝ 2` of the cutoff coefficient.
