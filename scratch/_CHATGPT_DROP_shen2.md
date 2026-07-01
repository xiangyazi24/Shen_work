# Q2733 shen2: first bridge lemmas for interval Agmon/rpow

Repo target: `xiangyazi24/Shen_work`, Lean 4. Default branch after commit `216cbc4f`.

Scope honored: non-Zinan files only. I did not touch or rely on `ShenWork/PDE/P3MoserHighExcursionProducer.lean` or `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

Files inspected:

```text
ShenWork/PDE/IntervalAgmonInterpolation.lean
ShenWork/PDE/IntervalDomain.lean
ShenWork/PDE/GagliardoNirenberg.lean
ShenWork/PDE/IntervalEllipticCharacterization.lean
ShenWork/Paper2/IntervalMildPicardRegularity.lean
ShenWork/Paper2/IntervalResolverPowerDecay.lean
```

## Main API facts to use

The newly proved endpoint is:

```lean
ShenWork.GagliardoNirenberg.agmon_inequality_interval_rightDeriv
```

with shape:

```lean
{L : ℝ} → 0 < L →
{f f' : ℝ → ℝ} →
ContinuousOn f (Icc 0 L) →
(∀ x ∈ Ioo 0 L, HasDerivWithinAt f (f' x) (Ioi x) x) →
IntervalIntegrable f' volume 0 L →
IntervalIntegrable (fun y => f y ^ 2) volume 0 L →
IntervalIntegrable (fun y => f' y ^ 2) volume 0 L →
IntervalIntegrable (fun y => f y * f' y) volume 0 L →
∀ x ∈ Icc 0 L, ...
```

For `IntervalAgmonInterpolation.lean`, the first bridge should set

```lean
F  y := (intervalDomainLift f y) ^ (q / 2)
F' y := (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y
```

and prove the positivity/continuity/right-derivative facts first.

Useful local theorem names already present elsewhere:

```lean
ContDiffOn.rpow_const_of_ne
HasDerivAt.rpow_const
ShenWork.IntervalEllipticCharacterization.hasDerivAt_of_contDiffOn_two_interior
ShenWork.IntervalEllipticCharacterization.intervalIntegrable_deriv_of_contDiffOn_two
ContinuousOn.intervalIntegrable
ContinuousOn.pow
ContinuousOn.mul
IntervalIntegrable.congr
IntervalIntegrable.congr_ae
```

The two `IntervalEllipticCharacterization` helpers are particularly relevant because they already encode the exact issue with closed-`Icc` `ContDiffOn`: two-sided `deriv` is available on the open interior, while endpoint facts about unrestricted `deriv` are not automatic.

## Import guidance

In `ShenWork/PDE/IntervalAgmonInterpolation.lean`, add these imports if you add the bridge lemmas in that file:

```lean
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.PDE.IntervalEllipticCharacterization
```

The current file already imports `ShenWork.PDE.IntervalDomain`, but `IntervalEllipticCharacterization` gives the clean interior derivative helper:

```lean
hasDerivAt_of_contDiffOn_two_interior
```

## Snippet 1: positivity and rpow continuity on `Icc 0 1`

This is the first lemma I would add. It is small and should be stable.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.IntervalEllipticCharacterization

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalEllipticCharacterization
open scoped Interval Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- If a subtype profile is positive, its zero-extension/lift is positive on
`[0,1]`. -/
theorem intervalDomainLift_pos_on_Icc
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x : intervalDomain.Point, 0 < f x) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift f y := by
  intro y hy
  rw [intervalDomainLift, dif_pos hy]
  exact hf_pos ⟨y, hy⟩

/-- Closed-interval continuity of `(lift f)^(q/2)` from closed-`Icc` `C²`
regularity and positivity.  This uses the same `ContDiffOn.rpow_const_of_ne`
API used in nearby files. -/
theorem intervalDomainLift_rpow_half_continuousOn_Icc
    {f : intervalDomain.Point → ℝ} {q : ℝ}
    (hf_pos : ∀ x : intervalDomain.Point, 0 < f x)
    (hf_c2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
      (fun y : ℝ => (intervalDomainLift f y) ^ (q / 2))
      (Set.Icc (0 : ℝ) 1) := by
  exact
    (hf_c2.rpow_const_of_ne
      (fun y hy => ne_of_gt (intervalDomainLift_pos_on_Icc hf_pos y hy))).continuousOn

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

Notes:

* The proof of positivity should use `rw [intervalDomainLift, dif_pos hy]`, not `simp`, because it keeps the subtype witness exactly visible.
* For continuity, `ContDiffOn.rpow_const_of_ne` is stronger than needed but matches local style. A fallback is `hf_c2.continuousOn.rpow continuousOn_const ...`, but the `ContDiffOn` route is cleaner if subsequent lemmas need regularity.

## Snippet 2: right-derivative bridge on `Ioi y`

This is the key derivative bridge for `agmon_inequality_interval_rightDeriv`. Use the existing interior derivative helper rather than re-proving the `ContDiffOn`/neighborhood conversion.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.IntervalEllipticCharacterization

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalEllipticCharacterization
open scoped Interval Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Interior right-derivative of `(lift f)^(q/2)`. -/
theorem intervalDomainLift_rpow_half_hasDerivWithinAt_Ioi
    {f : intervalDomain.Point → ℝ} {q y : ℝ}
    (hf_pos : ∀ x : intervalDomain.Point, 0 < f x)
    (hf_c2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun z : ℝ => (intervalDomainLift f z) ^ (q / 2))
      ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
        deriv (intervalDomainLift f) y)
      (Set.Ioi y) y := by
  have hbase :
      HasDerivAt (intervalDomainLift f)
        (deriv (intervalDomainLift f) y) y :=
    hasDerivAt_of_contDiffOn_two_interior hf_c2 hy
  have hpos_y : 0 < intervalDomainLift f y :=
    intervalDomainLift_pos_on_Icc hf_pos y (Set.Ioo_subset_Icc_self hy)
  have hpow :
      HasDerivAt
        (fun z : ℝ => (intervalDomainLift f z) ^ (q / 2))
        (deriv (intervalDomainLift f) y * (q / 2) *
          (intervalDomainLift f y) ^ (q / 2 - 1)) y :=
    hbase.rpow_const (Or.inl (ne_of_gt hpos_y))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hpow.hasDerivWithinAt

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

Important points:

* `HasDerivAt.rpow_const` gives derivative in the order
  `deriv lift y * (q/2) * lift y ^ (q/2 - 1)`.
* The requested derivative is the same expression commuted; `simpa [mul_assoc, mul_left_comm, mul_comm]` should normalize it.
* The conversion from full derivative to right derivative is `hpow.hasDerivWithinAt`.

## Snippet 3: use a named derivative function and the smallest integrability boundary

The integrability part is **not** as short from only

```lean
ContDiffOn ℝ 2 (intervalDomainLift f) (Icc 0 1)
```

because `agmon_inequality_interval_rightDeriv` uses the unrestricted endpoint-valued function

```lean
deriv (intervalDomainLift f)
```

inside `F'`. Existing code in `IntervalEllipticCharacterization.lean` explicitly notes that `ContinuousOn (deriv g) (uIcc 0 1)` is not automatic from closed-`Icc` `ContDiffOn`; it proves interval-integrability of `deriv g` by comparison with `derivWithin` a.e.

So the smallest honest first-bridge boundary is to package exactly the four interval-integrability inputs that Agmon asks for, after defining the explicit `F'`.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.IntervalEllipticCharacterization

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalEllipticCharacterization
open scoped Interval Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- The explicit derivative of `y ↦ (intervalDomainLift f y)^(q/2)` on the
interior. -/
def intervalDomainLiftRpowHalfDeriv
    (q : ℝ) (f : intervalDomain.Point → ℝ) : ℝ → ℝ :=
  fun y : ℝ =>
    (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      deriv (intervalDomainLift f) y

/-- Exactly the integrability inputs needed by
`agmon_inequality_interval_rightDeriv` for
`F = (lift f)^(q/2)` and the explicit derivative `F'`. -/
structure IntervalDomainLiftRpowHalfAgmonIntegrability
    (q : ℝ) (f : intervalDomain.Point → ℝ) : Prop where
  fprime_int :
    IntervalIntegrable (intervalDomainLiftRpowHalfDeriv q f) volume 0 1
  f_sq_int :
    IntervalIntegrable
      (fun y : ℝ => ((intervalDomainLift f y) ^ (q / 2)) ^ 2)
      volume 0 1
  fprime_sq_int :
    IntervalIntegrable
      (fun y : ℝ => (intervalDomainLiftRpowHalfDeriv q f y) ^ 2)
      volume 0 1
  ffprime_int :
    IntervalIntegrable
      (fun y : ℝ =>
        (intervalDomainLift f y) ^ (q / 2) *
          intervalDomainLiftRpowHalfDeriv q f y)
      volume 0 1

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

This is the smallest statement boundary if you want no detour into endpoint behavior of unrestricted `deriv`.

A short sufficient producer exists if you additionally carry:

```lean
hderiv_cont : ContinuousOn (deriv (intervalDomainLift f)) (Set.Icc (0 : ℝ) 1)
```

but that hypothesis is stronger than what closed-`Icc` `ContDiffOn` alone currently gives.

## Snippet 4: optional short producer under `hderiv_cont`, and Agmon application shell

This is a useful local test/snippet. It should be treated as a sufficient producer, not the final minimal analytic statement.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.GagliardoNirenberg

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalEllipticCharacterization
open scoped Interval Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

private theorem intervalIntegrable_of_continuousOn_Icc01
    {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable F volume 0 1 := by
  have hFu : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hF
  exact hFu.intervalIntegrable

/-- A short sufficient integrability producer if endpoint continuity of the
unrestricted derivative is supplied separately. -/
theorem intervalDomainLift_rpow_half_agmonIntegrability_of_deriv_continuous
    {f : intervalDomain.Point → ℝ} {q : ℝ}
    (hf_pos : ∀ x : intervalDomain.Point, 0 < f x)
    (hf_c2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    (hderiv_cont :
      ContinuousOn (deriv (intervalDomainLift f)) (Set.Icc (0 : ℝ) 1)) :
    IntervalDomainLiftRpowHalfAgmonIntegrability q f := by
  have hF_cont :
      ContinuousOn
        (fun y : ℝ => (intervalDomainLift f y) ^ (q / 2))
        (Set.Icc (0 : ℝ) 1) :=
    intervalDomainLift_rpow_half_continuousOn_Icc hf_pos hf_c2
  have hpowm_cont :
      ContinuousOn
        (fun y : ℝ => (intervalDomainLift f y) ^ (q / 2 - 1))
        (Set.Icc (0 : ℝ) 1) := by
    exact
      (hf_c2.rpow_const_of_ne
        (fun y hy => ne_of_gt (intervalDomainLift_pos_on_Icc hf_pos y hy))).continuousOn
  have hFp_cont :
      ContinuousOn (intervalDomainLiftRpowHalfDeriv q f)
        (Set.Icc (0 : ℝ) 1) := by
    unfold intervalDomainLiftRpowHalfDeriv
    simpa [mul_assoc] using (hpowm_cont.const_mul (q / 2)).mul hderiv_cont
  exact
    { fprime_int := intervalIntegrable_of_continuousOn_Icc01 hFp_cont
      f_sq_int := intervalIntegrable_of_continuousOn_Icc01 (hF_cont.pow 2)
      fprime_sq_int := intervalIntegrable_of_continuousOn_Icc01 (hFp_cont.pow 2)
      ffprime_int := intervalIntegrable_of_continuousOn_Icc01 (hF_cont.mul hFp_cont) }

/-- First application shell for the right-derivative Agmon theorem.  This is not
the whole interpolation theorem; it only packages the first bridge facts. -/
theorem intervalDomainLift_rpow_half_agmon_pointwise
    {f : intervalDomain.Point → ℝ} {q x : ℝ}
    (hf_pos : ∀ x : intervalDomain.Point, 0 < f x)
    (hf_c2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    (hint : IntervalDomainLiftRpowHalfAgmonIntegrability q f)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((intervalDomainLift f x) ^ (q / 2)) ^ 2 ≤
      (2 / 1) *
          (∫ y in (0 : ℝ)..1,
            ((intervalDomainLift f y) ^ (q / 2)) ^ 2) +
        2 * Real.sqrt
          (∫ y in (0 : ℝ)..1,
            ((intervalDomainLift f y) ^ (q / 2)) ^ 2) *
          Real.sqrt
          (∫ y in (0 : ℝ)..1,
            (intervalDomainLiftRpowHalfDeriv q f y) ^ 2) := by
  exact
    ShenWork.GagliardoNirenberg.agmon_inequality_interval_rightDeriv
      (L := 1) (hL := by norm_num)
      (f := fun y : ℝ => (intervalDomainLift f y) ^ (q / 2))
      (f' := intervalDomainLiftRpowHalfDeriv q f)
      (intervalDomainLift_rpow_half_continuousOn_Icc hf_pos hf_c2)
      (fun y hy =>
        intervalDomainLift_rpow_half_hasDerivWithinAt_Ioi
          (f := f) (q := q) hf_pos hf_c2 hy)
      hint.fprime_int
      hint.f_sq_int
      hint.fprime_sq_int
      hint.ffprime_int
      hx

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

## Recommended first bridge boundary

Add only these first in `IntervalAgmonInterpolation.lean`:

```lean
intervalDomainLift_pos_on_Icc
intervalDomainLift_rpow_half_continuousOn_Icc
intervalDomainLift_rpow_half_hasDerivWithinAt_Ioi
intervalDomainLiftRpowHalfDeriv
IntervalDomainLiftRpowHalfAgmonIntegrability
intervalDomainLift_rpow_half_agmon_pointwise
```

Do **not** try to prove the final mass-gradient interpolation theorem in the same move. The next separate bridge can decide whether to prove `IntervalDomainLiftRpowHalfAgmonIntegrability` from stronger closed endpoint derivative data or to keep it as an explicit local frontier while the endpoint behavior of unrestricted `deriv` is normalized.

## Why I would not start with a stronger integrability lemma

The tempting statement

```lean
ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
IntervalDomainLiftRpowHalfAgmonIntegrability q f
```

is probably too large for the first bridge. It has two nontrivial endpoint issues:

1. `ContDiffOn` on `Icc` naturally controls `derivWithin`; the Agmon derivative function uses unrestricted `deriv`.
2. The square/product terms for `F'` need more than `IntervalIntegrable (deriv lift)`: they need integrability of products involving `((lift f)^(q/2-1))` and `deriv lift`, and for `F'^2` this is a weighted derivative-square term.

There are likely routes using `derivWithin` continuity plus a.e. congruence, mirroring `intervalIntegrable_deriv_of_contDiffOn_two`, but that is a second bridge, not a first bridge.
