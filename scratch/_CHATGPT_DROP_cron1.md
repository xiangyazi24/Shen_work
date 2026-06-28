# Q1731 (cron1) -- Laplacian helper theorem

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt I received was only:

```text
Q1731 (cron1): cron1 /tmp/q_cron1_helper.txt
```

The local file `/tmp/q_cron1_helper.txt` is not accessible through the GitHub connector. I used the connector only and inferred this as the requested helper after the Q1716 Laplacian-envelope diagnosis. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

The relevant existing API is in:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalMildSourceDecayHelper.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
```

## Short answer

The helper you want is the fixed-time bridge:

```text
ContDiffOn ℝ 2 of one source slice on [0,1]
+ Neumann endpoint/tendsto data for that slice
→ normalized cosine coefficient decay |cosineCoeffs slice k| ≤ C/(kπ)^2.
```

Use the already committed normalized-coefficient theorem:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_cosineCoeff_quadratic_decay
```

not the lower-level raw-integral theorem directly. The normalized theorem already accounts for the positive-mode factor `2` in `cosineCoeffs`.

This helper gives `∀ t > 0, ∃ C_t, ...`. It **does not** fill the current global `laplBound : ∃ M, ∀ t > 0, ...`, because that current field asks for a single constant uniform down to `t = 0`.

## Standalone helper code

This is the minimal helper file/code with imports.

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalMildSourceDecayHelper

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (srcSlice sliceFam FlooredSourceTimeData)
open ShenWork.PDE.IntervalMildSourceDecayHelper
  (IntervalWeakH2Neumann intervalWeakH2Neumann_of_contDiffOn
   intervalWeakH2Neumann_cosineCoeff_quadratic_decay)

noncomputable section

namespace ShenWork.Paper2.Cron1Helper

/-- Fixed-time helper: a single source slice with closed-interval `C²` regularity
and Neumann endpoint data has normalized cosine-coefficient `1/k²` decay.

The constant `C` depends on this fixed slice, hence on `t` if the slice is
`sliceFam ... i t`. -/
theorem sliceFam_laplBound_fixed_time
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    {i : ℕ} {t : ℝ}
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

/-- Same helper packaged for an existing `FlooredSourceTimeData` object. -/
theorem flooredSourceTimeData_laplBound_fixed_time
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (i : ℕ) (hi : i ≤ 2) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤
        C / ((k : ℝ) * Real.pi) ^ 2 := by
  exact sliceFam_laplBound_fixed_time
    (p := p) (u := u) (s₁ := s₁) (s₂ := s₂) (i := i) (t := t)
    (H.sliceC2 i hi t ht)
    (H.sliceNeumann i hi t ht)

end ShenWork.Paper2.Cron1Helper
```

## Where to put it

Best location options:

1. A small helper file, for example:

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceLaplacianHelper.lean
```

with the imports above.

2. Or directly in `IntervalPhysicalSourceTimeC2Concrete.lean`, after `FlooredSourceTimeData` and before `builtEs`. If you put it there, you can omit the self-import and add/keep access to:

```lean
import ShenWork.PDE.IntervalMildSourceDecayHelper
```

The file already has much of this transitively via `IntervalMildPicardRegularity`, but an explicit import is clearer and safer.

## How it relates to `hlaplBound`

This helper can prove the true fixed-time statement:

```lean
∀ t : ℝ, 0 < t → ∃ C_t : ℝ, 0 ≤ C_t ∧ ∀ k : ℕ, 1 ≤ k →
  |cosineCoeffs (slice_i t) k| ≤ C_t / ((k : ℝ) * Real.pi) ^ 2
```

It cannot prove the current constructor field:

```lean
∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → ∀ k : ℕ, 1 ≤ k →
  |cosineCoeffs (slice_i t) k| ≤ M / ((k : ℝ) * Real.pi) ^ 2
```

because the latter is a uniform-in-all-positive-time spatial `C²` envelope. For heat level 0 with only continuous bounded positive initial data, that uniform envelope is not available as `t ↓ 0`.

## If the goal has been refactored to lower-time-local bounds

If you change the data structure to the honest lower-time-local version:

```lean
laplBoundOnIci : ∀ a : ℝ, 0 < a → ∀ i : ℕ, i ≤ 2 →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤
      M / ((k : ℝ) * Real.pi) ^ 2
```

then the fixed-time helper above is still not by itself enough. You also need a **uniform slab** second-derivative envelope on `t ∈ [a, ∞)` or at least on the support used by the cutoff. That is where the heat spectral estimates with exponential damping enter:

```text
λ^r * exp(-a λ) is summable / bounded for a > 0.
```

For the cutoff resolver proof, it is usually enough to ask for the lower-time bound at `a = c/2`, because `smoothRightCutoff (c/2) c` kills the singular region near zero.

## Common elaboration fixes

If the `simpa [f]` lines in `sliceFam_laplBound_fixed_time` do not unfold the local `let f` as expected, use this more explicit version of the weak certificate block:

```lean
  have Hweak : IntervalWeakH2Neumann
      ((sliceFam (srcSlice p u) s₁ s₂ i) t) :=
    intervalWeakH2Neumann_of_contDiffOn
      (g := (sliceFam (srcSlice p u) s₁ s₂ i) t)
      hC2 hNeu.1 hNeu.2.1 hNeu.2.2.1 hNeu.2.2.2
  simpa using intervalWeakH2Neumann_cosineCoeff_quadratic_decay Hweak
```

This avoids relying on `let`-unfolding.

## Bottom line

The helper is a fixed-time `C² + Neumann ⇒ cosineCoeff 1/k²` bridge. It is correct and useful, but it should be used after refactoring the global `laplBound` field, not as a proof of the currently overstrong `∃ M, ∀ t > 0` obligation.
