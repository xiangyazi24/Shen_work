# Q1303 / cron1 — zero input for `intervalFullSemigroupOperator`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

Yes, there is a theorem named `intervalFullSemigroupOperator_zero`, but it is **not** the lemma you need for positive time.  It is the degenerate time-zero statement:

```lean
ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero
  (f : ℝ → ℝ) (x : ℝ) :
  intervalFullSemigroupOperator 0 f x = 0
```

from:

```text
ShenWork/PDE/IntervalSemigroupAtZero.lean
```

For your argument, where `c > 0` and `f` vanishes on `Icc 0 1`, you need a **zero-input-on-the-support** lemma:

```lean
∀ y ∈ Icc (0 : ℝ) 1, f y = 0
→ intervalFullSemigroupOperator c f x = 0
```

This is easier and more direct than using any spectral theorem.  `intervalFullSemigroupOperator` is defined as an integral against

```lean
intervalMeasure 1 = volume.restrict (Icc 0 1)
```

so values of `f` outside `[0,1]` are ignored.  Continuity is not needed for this lemma.

## Definitions found

From:

```text
ShenWork/PDE/IntervalNeumannFullKernel.lean
```

```lean
/-- The full periodised-image Neumann heat propagator on `[0,1]`. -/
def intervalFullSemigroupOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1
```

From:

```text
ShenWork/PDE/IntervalDomain.lean
```

```lean
def intervalSet (L : ℝ) : Set ℝ := Set.Icc 0 L

def intervalMeasure (L : ℝ) : Measure ℝ :=
  volume.restrict (intervalSet L)
```

From:

```text
ShenWork/PDE/IntervalSemigroupAtZero.lean
```

```lean
/-- **The actual value of the propagator at time `0`.**
`intervalFullSemigroupOperator 0 f x = 0` for every `f`, `x` — the kernel is
identically zero, so the defining integral is the integral of the zero
integrand. -/
theorem intervalFullSemigroupOperator_zero (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_zero]
```

Again: that theorem is about `t = 0`, not about `S(c) 0` for positive `c`.

## Lemma to add/use

Add this local lemma near the positivity-by-contradiction code in
`IntervalConjugateLevel0BFormSourceOn.lean`, or put it in a nearby support namespace.

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain (intervalMeasure intervalSet intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- If the input vanishes on `[0,1]`, then the full Neumann propagator vanishes.

No continuity assumption is needed: `intervalFullSemigroupOperator` integrates
against `intervalMeasure 1 = volume.restrict (Icc 0 1)`, so the integrand is
zero almost everywhere for that restricted measure. -/
theorem intervalFullSemigroupOperator_eq_zero_of_eq_zero_on_Icc
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hf_zero : ∀ y ∈ Icc (0 : ℝ) 1, f y = 0) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  have hae :
      (fun y : ℝ => intervalNeumannFullKernel t x y * f y)
        =ᵐ[intervalMeasure 1] (fun _ : ℝ => 0) := by
    unfold intervalMeasure intervalSet
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun y hy => by
        rw [hf_zero y hy, mul_zero])
  calc
    (∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1)
        = ∫ y, (0 : ℝ) ∂ intervalMeasure 1 := by
          exact integral_congr_ae hae
    _ = 0 := by simp

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

If namespace/import pressure is annoying, the same proof can be used fully-qualified:

```lean
have hS_zero : intervalFullSemigroupOperator c f x = 0 := by
  unfold intervalFullSemigroupOperator
  have hae :
      (fun y : ℝ => intervalNeumannFullKernel c x y * f y)
        =ᵐ[ShenWork.IntervalDomain.intervalMeasure 1] (fun _ : ℝ => 0) := by
    unfold ShenWork.IntervalDomain.intervalMeasure ShenWork.IntervalDomain.intervalSet
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun y hy => by
        rw [hf_zero y hy, mul_zero])
  calc
    (∫ y, intervalNeumannFullKernel c x y * f y
        ∂ ShenWork.IntervalDomain.intervalMeasure 1)
        = ∫ y, (0 : ℝ) ∂ ShenWork.IntervalDomain.intervalMeasure 1 := by
          exact integral_congr_ae hae
    _ = 0 := by simp
```

## How to use it in your contradiction

Suppose in the contradiction branch you have:

```lean
hzero_on : ∀ y ∈ Icc (0 : ℝ) 1, intervalDomainLift u₀ y = 0
```

Then for the known positive window time `s` and point `1/2`:

```lean
have hhalf : ((1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

have hS_zero :
    intervalFullSemigroupOperator s (intervalDomainLift u₀) ((1 : ℝ) / 2) = 0 :=
  intervalFullSemigroupOperator_eq_zero_of_eq_zero_on_Icc
    s (intervalDomainLift u₀) ((1 : ℝ) / 2) hzero_on

have hlift_zero :
    intervalDomainLift (conjugatePicardIter p u₀ 0 s) ((1 : ℝ) / 2) = 0 := by
  simp [conjugatePicardIter, intervalDomainLift, hhalf, hS_zero]

have hpos_half := _hpos s hs ((1 : ℝ) / 2) hhalf
rw [hlift_zero] at hpos_half
exact (lt_irrefl (0 : ℝ)) hpos_half
```

This avoids trying to rewrite the whole input function globally as zero.  You only need the on-`Icc` vanishing, which is exactly what the restricted measure sees.

## If the input is globally zero

There is also a route through scalar linearity if you truly have `f = fun _ => 0` globally.  The file

```text
ShenWork/PDE/IntervalSemigroupConeAtoms.lean
```

has:

```lean
theorem intervalFullSemigroupOperator_const_mul
    (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t (fun y => c * f y) x
      = c * intervalFullSemigroupOperator t f x
```

Then with `c = 0`:

```lean
have hS0_global : intervalFullSemigroupOperator t (fun _ : ℝ => 0) x = 0 := by
  simpa using
    ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_const_mul
      t 0 (fun _ : ℝ => 1) x
```

But for your actual `lift u₀`, the restricted-measure lemma above is the correct one.

## Minimal answer

There is `intervalFullSemigroupOperator_zero`, but it is only:

```lean
intervalFullSemigroupOperator 0 f x = 0
```

For `f = 0` on `[0,1]` and arbitrary time `c`, prove:

```lean
intervalFullSemigroupOperator c f x = 0
```

by unfolding the definition and using AE equality on

```lean
intervalMeasure 1 = volume.restrict (Icc 0 1)
```

as in `intervalFullSemigroupOperator_eq_zero_of_eq_zero_on_Icc` above.

No local `lake build` was run; this drop was produced through the GitHub connector only.
