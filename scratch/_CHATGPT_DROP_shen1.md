# Q2720 (shen1) — C2 `UnitIntervalPositiveAgmonInterpolation` audit

Repo: `xiangyazi24/Shen_work`  
Branch for this drop: `chatgpt-scratch`  
Lean target: Lean 4 / Mathlib 4.29.1  
Scope: non-Zinan files only. I did **not** inspect, edit, rely on, or propose edits to
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

I inspected/search-audited the requested files:

- `ShenWork/PDE/SobolevEmbedding.lean`
- `ShenWork/PDE/GagliardoNirenberg.lean`
- `ShenWork/Paper2/IntervalDomainLemma41.lean`
- `ShenWork/PDE/IntervalDomain.lean`
- `ShenWork/PDE/IntervalAgmonInterpolation.lean`

I also checked adjacent non-forbidden consumer files only to identify exact names and whether the new raw-drop terminal-endpoint full-statement wrappers produce or merely consume the Agmon/mass-gradient frontier. The wrappers in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` lower the full-statement route to a `relativeMassGradient` field, but they do not prove the C2 `UnitIntervalPositiveAgmonInterpolation` producer.

## Verdict

The current repo has most of the **algebraic** and **classical Agmon** components, but I do **not** see an existing theorem composition that proves

```lean
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q → ∀ eps : ℝ, 0 < eps → ∃ Ceps > 0,
    ∀ f : intervalDomain.Point → ℝ,
      (∀ x, 0 < f x) →
      ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
        intervalDomain.integral (fun x => f x ^ q) ≤
          eps * intervalDomain.integral
            (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
          Ceps * (intervalDomain.integral f) ^ q
```

from the currently exported lemmas alone.

The smallest genuine missing analytic lemma is an **endpoint-safe Agmon/FTC lemma** compatible with `ContDiffOn ℝ 2 ... (Set.Icc 0 1)` / within-domain regularity of `intervalDomainLift`. The existing Agmon theorem requires ordinary `HasDerivAt` on the closed interval, which is the wrong interface for the zero-extension `intervalDomainLift`.

Once that endpoint-safe Agmon core is available, the rest is a finite amount of `intervalDomain.integral` / `intervalDomainLift` / `gradNorm` / `rpow` chain-rule conversion plus the already-proved algebraic absorption theorem in `IntervalDomainLemma41.lean`.

## 1. Existing theorem names/signatures that can be composed

### A. Current frontier and wiring in `IntervalAgmonInterpolation.lean`

The file has a proved single-slice sanity lemma, but it is **not** uniform in `f`:

```lean
namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

theorem intervalDomain_agmon_interpolation_slice
    {f : intervalDomain.Point → ℝ} {q eps : ℝ}
    (hmass : 0 < intervalDomain.integral f) :
    ∃ Ceps > 0,
      intervalDomain.integral (fun x => f x ^ q) ≤
        eps * intervalDomain.integral
          (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
        Ceps * (intervalDomain.integral f) ^ q
```

This lemma chooses `Ceps` after `f`, so it cannot discharge `UnitIntervalPositiveAgmonInterpolation`, where `Ceps` must be chosen from `q, eps` before the slice is supplied.

The file also has the correct downstream wiring theorem:

```lean
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolation) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params
```

The proof extracts closed-interval C2 regularity from the classical solution:

```lean
have hC2_closed :
    ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
  (hsol.regularity.2.2.2.2.1 t ht).1.1
```

This theorem is good and should be kept unchanged. The missing work is producing `UnitIntervalPositiveAgmonInterpolation`.

### B. Sobolev/Agmon infrastructure in `SobolevEmbedding.lean`

Exported theorem names/signatures:

```lean
namespace ShenWork.Sobolev

theorem lpNorm_one_le_rpow_measure_mul_lpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hf_mem : MemLp f (2 : ℝ≥0∞) μ) :
    lpNorm f (1 : ℝ≥0∞) μ ≤
      ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) *
        lpNorm f (2 : ℝ≥0∞) μ

theorem interval_integral_abs_le_length_rpow_mul_lpNorm_two
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) L)))
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) :
    (∫ y in (0 : ℝ)..L, |f y|) ≤
      (L ^ (1 / 2 : ℝ)) *
        lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))

theorem sobolev_pointwise_bound
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤ (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) +
      (∫ y in (0 : ℝ)..L, |f' y|)

theorem sobolev_H1_Linfty_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤
      (1 / L) *
          ((L ^ (1 / 2 : ℝ)) *
            lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) +
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))
```

These are not directly enough for the target because they also require ordinary closed-interval `HasDerivAt` for the chosen representative.

### C. GN/Agmon facts in `GagliardoNirenberg.lean`

Exported theorem names/signatures:

```lean
namespace ShenWork.Sobolev

theorem lpNorm_four_rpow_two_le_bound_mul_lpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hf_mem : MemLp f (2 : ℝ≥0∞) μ)
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    (lpNorm f (4 : ℝ≥0∞) μ) ^ (2 : ℝ) ≤
      B * lpNorm f (2 : ℝ≥0∞) μ

theorem gagliardoNirenberg_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) :
    (lpNorm f (4 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) ^ (2 : ℝ) ≤
      ((1 / L) *
          ((L ^ (1 / 2 : ℝ)) *
            lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) +
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) *
        lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))
```

The strongest directly relevant theorem is:

```lean
namespace ShenWork.GagliardoNirenberg

theorem agmon_inequality_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (_hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (_hf'_int : IntervalIntegrable f' volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun y => f' y ^ 2) volume 0 L)
    (hff'_int : IntervalIntegrable (fun y => f y * f' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    f x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, f y ^ 2) +
      2 * sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
        sqrt (∫ y in (0 : ℝ)..L, f' y ^ 2)
```

This is mathematically the right estimate. The problem is the derivative hypothesis. It requires ordinary `HasDerivAt` on **all** `x ∈ Icc 0 L`. Its proof uses

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

with derivative data over `uIcc y₀ x`, so endpoint ordinary derivatives are part of the interface.

### D. Algebraic absorption in `IntervalDomainLemma41.lean`

This file has the absorption step already proved:

```lean
namespace ShenWork.Paper2.IntervalDomainLemma41

theorem quadratic_absorption {a b c : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (h : a ≤ b * Real.sqrt a + c) :
    a ≤ b ^ 2 + 2 * c

theorem interpolation_absorption {Y G Mp δ pv C : ℝ}
    (hY : 0 ≤ Y) (hG : 0 ≤ G) (hMp : 0 ≤ Mp)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 4) (hp : 0 < pv)
    (hC : 0 ≤ C)
    (hineq : Y ≤ 2 * δ * Y + δ * pv * Real.sqrt (Y * G) + C * Mp) :
    Y ≤ δ ^ 2 * pv ^ 2 / (1 - 2 * δ) ^ 2 * G +
      2 * C / (1 - 2 * δ) * Mp
```

This should be reused. Do not reprove the quadratic absorption.

The same file defines a global interpolation frontier:

```lean
def IntervalDomainInterpolation : Prop :=
  ∀ (eps : ℝ), 0 < eps → ∀ (pExp : ℝ), 1 < pExp → ∃ Ceps > 0,
    ∀ (f : intervalDomainPoint → ℝ),
      (∀ x, x ∈ intervalDomain.inside → 0 < f x) →
        intervalDomain.integral (fun x => (f x) ^ pExp) ≤
          eps * intervalDomain.integral
              (fun x => (f x) ^ (pExp - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ pExp
```

But this is only a `Prop` frontier, not a proved theorem. It also has no `ContDiffOn` hypothesis, so it is not the right theorem to prove directly for arbitrary functions.

### E. Adjacent existing slice package in `IntervalDomainAPrioriGlobal.lean`

This theorem is useful for orientation because it packages an elementary power/sup step plus Agmon, but it still inherits the closed ordinary derivative requirement:

```lean
namespace ShenWork.IntervalDomainExistence

theorem integral_pow_le_sup_pow_mul
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (hf_int : IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1)
    (hfp_int :
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
      (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f

theorem intervalDomain_Lp_interpolation_classicalSlice
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (hf_int : IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1)
    (hfp_int :
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1)
    (hf_cont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    {f' : ℝ → ℝ}
    (hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (intervalDomainLift f) (f' x) x)
    (hf'_int : IntervalIntegrable f' MeasureTheory.volume 0 1)
    (hf_sq_int : IntervalIntegrable (fun y : ℝ => (intervalDomainLift f y) ^ 2)
      MeasureTheory.volume 0 1)
    (hf'_sq_int : IntervalIntegrable (fun y : ℝ => f' y ^ 2) MeasureTheory.volume 0 1)
    (hff'_int : IntervalIntegrable (fun y : ℝ => intervalDomainLift f y * f' y)
      MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
        (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift f x) ^ 2 ≤
          (2 / (1 : ℝ)) *
              (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) +
            2 * Real.sqrt
                (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) *
              Real.sqrt (∫ y in (0 : ℝ)..1, f' y ^ 2)
```

This does **not** prove `UnitIntervalPositiveAgmonInterpolation`. It is a slice package that still asks the caller to provide closed ordinary `HasDerivAt` of the chosen lift.

### F. Concrete interval-domain definitions

The relevant definitions in `IntervalDomain.lean` are:

```lean
def intervalDomainPoint : Type := Subtype (Set.Icc (0 : ℝ) 1)

def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

def intervalDomainIntegral (f : intervalDomainPoint → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, intervalDomainLift f x

def intervalDomainGradNorm (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  |deriv (intervalDomainLift f) x.1|

def intervalDomain : ShenWork.Paper2.BoundedDomainData where
  Point := intervalDomainPoint
  inside := {x : intervalDomainPoint | (x.1 : ℝ) ∈ Set.Ioo 0 1}
  boundary := {x : intervalDomainPoint | x.1 = 0 ∨ x.1 = 1}
  volume := 1
  integral := intervalDomainIntegral
  gradNorm := intervalDomainGradNorm
  classicalRegularity := intervalDomainClassicalRegularity
  -- other fields elided
```

The concrete definitions are good, but they force the proof to constantly move between subtype points and real interval variables.

## 2. Why the existing lemmas do not directly close the C2 frontier

The obstruction is not the final epsilon absorption. That is handled by `IntervalDomainLemma41.interpolation_absorption`.

The obstruction is the interface mismatch:

```lean
ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)
```

is a **within-set** regularity hypothesis. But `intervalDomainLift` is the zero extension. For a positive function on `[0,1]`, the zero extension usually has jumps at `0` and `1` from outside the interval. Hence it is not generally ordinary differentiable at the endpoints.

Existing `agmon_inequality_interval` requires:

```lean
∀ x ∈ Set.Icc 0 L, HasDerivAt g (g' x) x
```

for the real representative `g`. The C2 frontier only gives the right regularity on the closed interval in the `ContDiffOn`/within sense, not ordinary endpoint `HasDerivAt` of the zero extension.

This also blocks the apparently tempting route through:

```lean
ShenWork.IntervalDomainExistence.intervalDomain_Lp_interpolation_classicalSlice
```

because that theorem has the same explicit input:

```lean
(hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1,
  HasDerivAt (intervalDomainLift f) (f' x) x)
```

So the repo currently has the right pointwise Agmon theorem for ordinary closed-interval representatives, but it lacks an endpoint-safe theorem for zero-extended interval-domain representatives.

## 3. Smallest missing analytic lemma(s)

There are two viable ways to add the missing producer. The first is more reusable; the second is narrower and probably fastest.

### Option A — reusable endpoint-safe Agmon theorem

Add this near `agmon_inequality_interval` in `ShenWork/PDE/GagliardoNirenberg.lean`:

```lean
import ShenWork.PDE.GagliardoNirenberg

open MeasureTheory Set intervalIntegral
open scoped ENNReal Interval

noncomputable section

namespace ShenWork.GagliardoNirenberg

/-- Endpoint-safe Agmon inequality on `[0,L]`.

This is the same estimate as `agmon_inequality_interval`, but it only requires
ordinary derivative data on the open interval.  It is the right interface for
zero-extended interval-domain functions: endpoint ordinary differentiability of
the zero extension is not required, and endpoint values are irrelevant for the
integral estimates. -/
theorem agmon_inequality_interval_Ioo_ae
    {L : ℝ} (hL : 0 < L)
    {g g' : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.Icc 0 L))
    (hg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) L, HasDerivAt g (g' x) x)
    (hg'_int : IntervalIntegrable g' volume 0 L)
    (hg_sq_int : IntervalIntegrable (fun y => g y ^ 2) volume 0 L)
    (hg'_sq_int : IntervalIntegrable (fun y => g' y ^ 2) volume 0 L)
    (hgg'_int : IntervalIntegrable (fun y => g y * g' y) volume 0 L) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) L)),
      g x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, g y ^ 2) +
        2 * Real.sqrt (∫ y in (0 : ℝ)..L, g y ^ 2) *
          Real.sqrt (∫ y in (0 : ℝ)..L, g' y ^ 2) := by
  -- Proof plan: copy the existing `agmon_inequality_interval` proof, but prove
  -- the FTC step on interior subintervals and then conclude a.e.; endpoints are
  -- measure-zero under `volume.restrict (Icc 0 L)`.
  --
  -- The core replacement is the current call:
  --   intervalIntegral.integral_eq_sub_of_hasDerivAt
  -- which needs closed ordinary `HasDerivAt`.
  -- Replace it by an interior/within-interval FTC lemma, or prove that small
  -- interior truncations `(a,L-a)` satisfy the current theorem and let `a ↓ 0`.
  -- This is the only genuinely analytic missing step.
  --
  -- Do not try to obtain endpoint `HasDerivAt` for `intervalDomainLift`; it is
  -- false for positive zero-extensions.
  admit

end ShenWork.GagliardoNirenberg
```

The `admit` above marks the missing analytic theorem; do not commit it as-is. The theorem statement is the useful target. If Mathlib already has a suitable `integral_eq_sub_of_hasDerivWithinAt`/absolute-continuity interval FTC theorem, this proof should be short by adapting the existing proof.

A pointwise interior variant is also fine:

```lean
theorem agmon_inequality_interval_Ioo
    {L : ℝ} (hL : 0 < L)
    {g g' : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.Icc 0 L))
    (hg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) L, HasDerivAt g (g' x) x)
    (hg'_int : IntervalIntegrable g' volume 0 L)
    (hg_sq_int : IntervalIntegrable (fun y => g y ^ 2) volume 0 L)
    (hg'_sq_int : IntervalIntegrable (fun y => g' y ^ 2) volume 0 L)
    (hgg'_int : IntervalIntegrable (fun y => g y * g' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) L) :
    g x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, g y ^ 2) +
      2 * Real.sqrt (∫ y in (0 : ℝ)..L, g y ^ 2) *
        Real.sqrt (∫ y in (0 : ℝ)..L, g' y ^ 2)
```

For the final interpolation proof, the a.e. version is often easier because the endpoint values do not matter under the interval integral.

### Option B — narrower direct interval-domain Agmon core

If you want the smallest theorem tailored to this task, prove the following in `ShenWork/PDE/IntervalAgmonInterpolation.lean` or a small imported helper file:

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.Paper2.IntervalDomainLemma41

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLemma41

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Agmon applied to `g = f^(q/2)`, rewritten in interval-domain notation.

This is the narrow analytic producer needed before the already-proved algebraic
absorption step. -/
theorem intervalDomain_positive_C2_power_agmon_core
    {q : ℝ} (hq : 1 < q)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
    let G : ℝ := intervalDomain.integral
      (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
    ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (intervalDomainLift f y) ^ q ≤ 2 * Y + q * Real.sqrt (Y * G) := by
  -- Proof outline:
  --   g  y := (intervalDomainLift f y) ^ (q / 2)
  --   g' y := (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
  --             deriv (intervalDomainLift f) y
  --
  -- Use endpoint-safe Agmon on `g`, then rewrite:
  --   ∫ g^2  = intervalDomain.integral (fun x => f x^q)
  --   ∫ g'^2 = (q^2 / 4) * intervalDomain.integral
  --       (fun x => f x^(q-2) * gradNorm f x^2)
  --
  -- Required ingredients:
  --   * positivity of `intervalDomainLift f y` for `y ∈ Icc 0 1`;
  --   * rpow chain rule for positive base;
  --   * `intervalIntegral.integral_congr` conversions;
  --   * `sq_abs` for `gradNorm`.
  --
  -- This theorem is not currently derivable from the repo without the endpoint-
  -- safe Agmon/FTC step described above.
  admit

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

Again, the `admit` is only to mark the missing proof in this audit. The statement is the narrow producer target, not a residual wrapper.

## 4. Compile-oriented proof skeleton after the missing core

The following is the route I would implement after proving the endpoint-safe Agmon core. It is intentionally split so the hard analytic step is isolated from the algebraic absorption.

### 4.1 Small scalar and positivity support lemmas

These are not the hard analytic part, but they make the final proof clean.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLemma41

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLemma41

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Choose a small absorption parameter. -/
theorem exists_delta_for_interpolation_coeff
    {q eps : ℝ} (hq : 0 < q) (heps : 0 < eps) :
    ∃ δ : ℝ,
      0 < δ ∧ δ < 1 / 4 ∧
        δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 ≤ eps := by
  -- A conservative explicit choice such as
  --   δ = min (1/8) (Real.sqrt eps / (4 * q))
  -- should work.  This is scalar real algebra, not analytic.
  admit

/-- Nonnegativity of the `Y = ∫ f^q` term. -/
theorem intervalDomain_integral_rpow_nonneg
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    0 ≤ intervalDomain.integral (fun x => f x ^ q) := by
  unfold intervalDomain intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  simpa [intervalDomainLift, hyIcc, x] using
    Real.rpow_nonneg (hf_nonneg x) q

/-- Nonnegativity of the weighted gradient term. -/
theorem intervalDomain_weightedGradientIntegral_nonneg
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    0 ≤ intervalDomain.integral
      (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) := by
  unfold intervalDomain intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  have hpow : 0 ≤ f x ^ (q - 2) := Real.rpow_nonneg (hf_nonneg x) (q - 2)
  have hsq : 0 ≤ (intervalDomain.gradNorm f x) ^ 2 := sq_nonneg _
  simpa [intervalDomainLift, hyIcc, x] using mul_nonneg hpow hsq

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

The two nonnegativity proofs above are intended to be very close to compilable. Depending on local simp behavior, the final `simpa` in the gradient lemma may need:

```lean
simp [intervalDomainLift, hyIcc, x, intervalDomainGradNorm]
```

### 4.2 Pre-absorption producer

This is the next narrow target after `intervalDomain_positive_C2_power_agmon_core`:

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLemma41

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLemma41

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- The analytic + Young step before quadratic absorption.

This is narrower than the final `UnitIntervalPositiveAgmonInterpolation`: it
stops exactly at the hypothesis consumed by
`IntervalDomainLemma41.interpolation_absorption`. -/
theorem intervalDomain_positive_C2_pre_absorption
    {q δ : ℝ} (hq : 1 < q) (hδ_pos : 0 < δ)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
      let G : ℝ := intervalDomain.integral
        (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
      let Mp : ℝ := (intervalDomain.integral f) ^ q
      Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * Mp := by
  -- Route:
  -- 1. Get the a.e. bound from `intervalDomain_positive_C2_power_agmon_core`:
  --      f^q ≤ B := 2Y + q sqrt(YG).
  -- 2. Convert it to an a.e. bound for `f^(q-1)`:
  --      f^(q-1) ≤ B^((q-1)/q), using positivity and `Real.rpow_le_rpow`.
  -- 3. Integrate `f^q = f * f^(q-1)`:
  --      Y ≤ M * B^((q-1)/q).
  -- 4. Apply scaled Young with exponents `q` and `q/(q-1)`:
  --      M * B^((q-1)/q) ≤ δ * B + Cδ * M^q.
  -- 5. Expand `δ * B`.
  --
  -- This is still proof-producing, not a residual wrapper, because it isolates
  -- the exact analytic/Young obligation before the already-proved absorption.
  admit

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

This theorem is probably the best single theorem for a worker to attack after endpoint-safe Agmon is in place.

### 4.3 Final closure to `UnitIntervalPositiveAgmonInterpolation`

After `exists_delta_for_interpolation_coeff`, the two nonnegativity lemmas, and `intervalDomain_positive_C2_pre_absorption`, the final theorem is mostly algebraic:

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLemma41

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLemma41

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Final proof of the C2 unit-interval positive Agmon interpolation frontier,
once the endpoint-safe Agmon/Young pre-absorption producer is available. -/
theorem unitIntervalPositiveAgmonInterpolation_proved :
    UnitIntervalPositiveAgmonInterpolation := by
  intro q hq eps heps
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  rcases exists_delta_for_interpolation_coeff (q := q) (eps := eps) hq_pos heps with
    ⟨δ, hδ_pos, hδ_lt, hcoeff⟩
  -- `Cδ` comes from the pre-absorption theorem; `Ceps` is made strictly
  -- positive by adding `1`.
  classical
  obtain ⟨Cδ, hCδ_nonneg, hpre_all⟩ :=
    Classical.choice ?preChoice
  -- In a real proof, avoid `Classical.choice ?preChoice`: after introducing
  -- `f hf_pos hfC2`, call `intervalDomain_positive_C2_pre_absorption` for that
  -- slice.  If one wants a single `Ceps` independent of `f`, then the
  -- pre-absorption theorem must choose `Cδ` from `q,δ` only.  Prefer this
  -- stronger statement:
  --
  -- theorem intervalDomain_positive_C2_pre_absorption_uniform
  --   {q δ : ℝ} (hq : 1 < q) (hδ_pos : 0 < δ) :
  --   ∃ Cδ ≥ 0, ∀ f, ...
  --
  -- The current displayed `pre_absorption` statement above chooses `Cδ` after
  -- `f`; for the final theorem it must be strengthened to choose `Cδ` before
  -- `f`.  That is a critical quantifier-order detail.
  admit

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

Important correction: the final theorem requires the Young constant to be uniform in `f`. Therefore the actual pre-absorption producer should be stated as:

```lean
theorem intervalDomain_positive_C2_pre_absorption_uniform
    {q δ : ℝ} (hq : 1 < q) (hδ_pos : 0 < δ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
          let G : ℝ := intervalDomain.integral
            (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
          let Mp : ℝ := (intervalDomain.integral f) ^ q
          Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * Mp
```

Then the final closure has the right quantifier order:

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLemma41

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLemma41

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

theorem unitIntervalPositiveAgmonInterpolation_of_pre_absorption_uniform
    (hdelta : ∀ {q eps : ℝ}, 0 < q → 0 < eps →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
        δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 ≤ eps)
    (hpre : ∀ {q δ : ℝ}, 1 < q → 0 < δ →
      ∃ Cδ : ℝ, 0 ≤ Cδ ∧
        ∀ f : intervalDomain.Point → ℝ,
          (∀ x, 0 < f x) →
          ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
            let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
            let G : ℝ := intervalDomain.integral
              (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
            let Mp : ℝ := (intervalDomain.integral f) ^ q
            Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * Mp) :
    UnitIntervalPositiveAgmonInterpolation := by
  intro q hq eps heps
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  rcases hdelta (q := q) (eps := eps) hq_pos heps with
    ⟨δ, hδ_pos, hδ_lt, hcoeff⟩
  rcases hpre (q := q) (δ := δ) hq hδ_pos with
    ⟨Cδ, hCδ_nonneg, hpreδ⟩
  let Ceps : ℝ := 2 * Cδ / (1 - 2 * δ) + 1
  refine ⟨Ceps, ?_, ?_⟩
  · have hden : 0 < 1 - 2 * δ := by linarith
    dsimp [Ceps]
    positivity
  · intro f hf_pos hfC2
    let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
    let G : ℝ := intervalDomain.integral
      (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
    let Mp : ℝ := (intervalDomain.integral f) ^ q
    have hY : 0 ≤ Y := by
      dsimp [Y]
      exact intervalDomain_integral_rpow_nonneg (q := q) (f := f)
        (fun x => le_of_lt (hf_pos x))
    have hG : 0 ≤ G := by
      dsimp [G]
      exact intervalDomain_weightedGradientIntegral_nonneg (q := q) (f := f)
        (fun x => le_of_lt (hf_pos x))
    have hMp : 0 ≤ Mp := by
      dsimp [Mp]
      -- Enough to show `0 ≤ intervalDomain.integral f`; for strict positivity,
      -- prove/use `intervalDomain_integral_pos_of_pos_continuous`.
      have hM_nonneg : 0 ≤ intervalDomain.integral f := by
        exact intervalDomain_integral_rpow_nonneg (q := (1 : ℝ)) (f := f)
          (fun x => le_of_lt (hf_pos x))
      exact Real.rpow_nonneg hM_nonneg q
    have hpreY :
        Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * Mp := by
      simpa [Y, G, Mp] using hpreδ f hf_pos hfC2
    have habs :=
      interpolation_absorption
        (Y := Y) (G := G) (Mp := Mp) (δ := δ) (pv := q) (C := Cδ)
        hY hG hMp hδ_pos hδ_lt hq_pos hCδ_nonneg hpreY
    have hden : 0 < 1 - 2 * δ := by linarith
    have hmassCoeff_nonneg : 0 ≤ 2 * Cδ / (1 - 2 * δ) := by positivity
    have hCeps_ge : 2 * Cδ / (1 - 2 * δ) ≤ Ceps := by
      dsimp [Ceps]
      linarith
    have hGterm :
        δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 * G ≤ eps * G :=
      mul_le_mul_of_nonneg_right hcoeff hG
    have hMpterm :
        2 * Cδ / (1 - 2 * δ) * Mp ≤ Ceps * Mp :=
      mul_le_mul_of_nonneg_right hCeps_ge hMp
    -- Finish by unfolding Y/G/Mp and chaining the two coefficient comparisons.
    calc
      intervalDomain.integral (fun x => f x ^ q) = Y := rfl
      _ ≤ δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 * G +
            2 * Cδ / (1 - 2 * δ) * Mp := habs
      _ ≤ eps * G + Ceps * Mp := add_le_add hGterm hMpterm
      _ = eps * intervalDomain.integral
            (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
          Ceps * (intervalDomain.integral f) ^ q := rfl

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

This last closure is close to compile-plausible once the named support lemmas are present. The one subtle point is the nonnegativity of `intervalDomain.integral f`: the displayed use of `intervalDomain_integral_rpow_nonneg (q := 1)` proves nonnegativity of `∫ f^1`, so one may need `simpa [Real.rpow_one]` to rewrite it to `∫ f`.

## 5. Likely troublesome conversions

### A. `intervalDomain.integral`

Most goals need this unfolding:

```lean
unfold intervalDomain intervalDomainIntegral
```

or, if the expected head symbol is already known:

```lean
change intervalDomainIntegral (fun x : intervalDomainPoint => f x ^ q) ≤ _
unfold intervalDomainIntegral
```

After unfolding, target integrals have shape:

```lean
∫ y in (0 : ℝ)..1, intervalDomainLift (fun x : intervalDomain.Point => f x ^ q) y
```

### B. Subtype point from interval variable

Inside `intervalIntegral.integral_congr`, `integral_mono_on`, or nonnegativity proofs:

```lean
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
let x : intervalDomain.Point := ⟨y, hyIcc⟩
simp [intervalDomainLift, hyIcc, x]
```

If the local hypothesis is `Ioc`/`uIoc`, use:

```lean
have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hyIoc.1.le, hyIoc.2⟩
```

### C. Lift of a power vs power of a lift

On `[0,1]`:

```lean
have hpow_lift :
    intervalDomainLift (fun x : intervalDomain.Point => f x ^ q) y =
      (intervalDomainLift f y) ^ q := by
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  simp [intervalDomainLift, hyIcc, x]
```

Do not expect this rewrite to hold definitionally outside `[0,1]`; do it under the interval membership hypothesis.

### D. `gradNorm`

By definition:

```lean
intervalDomain.gradNorm f x = |deriv (intervalDomainLift f) x.1|
```

Typical rewrite after constructing `x : intervalDomain.Point := ⟨y, hyIcc⟩`:

```lean
simp [intervalDomain, intervalDomainGradNorm, intervalDomainLift, hyIcc, x, sq_abs]
```

The `sq_abs` rewrite is needed to turn `|deriv ...| ^ 2` into `(deriv ...)^2`.

### E. Endpoint ordinary derivative trap

Do not try to prove:

```lean
∀ x ∈ Set.Icc (0 : ℝ) 1,
  HasDerivAt (intervalDomainLift f) (deriv (intervalDomainLift f) x) x
```

from the C2 frontier. For a positive `f`, the zero extension `intervalDomainLift f` is generally discontinuous from outside at `0` and `1`. `ContDiffOn` on `Set.Icc 0 1` is within-domain smoothness, not ordinary differentiability of the zero extension at endpoints.

This is the core reason existing `agmon_inequality_interval` does not compose directly.

### F. `ContDiffOn` to interior derivative

Interior points should be fine. For `hy : y ∈ Set.Ioo 0 1`, use the neighborhood fact that `[0,1] ∈ 𝓝 y`:

```lean
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
have hIcc_mem : Set.Icc (0 : ℝ) 1 ∈ 𝓝 y :=
  Icc_mem_nhds hy.1 hy.2
```

Then extract differentiability/derivative data for `intervalDomainLift f` at interior points from `hfC2`. The exact API may require `hfC2.contDiffAt hIcc_mem` or a nearby `ContDiffOn` lemma, then `.differentiableAt` / `.hasDerivAt`. This is a standard API nuisance, not the analytic blocker.

### G. `rpow` chain rule

For interior `y`:

```lean
have hbase_pos : 0 < intervalDomainLift f y := by
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  simpa [intervalDomainLift, hyIcc, x] using hf_pos x
```

The derivative of `g y = (intervalDomainLift f y)^(q/2)` should be obtained from a positive-base `rpow` derivative theorem, with target:

```lean
HasDerivAt
  (fun z : ℝ => (intervalDomainLift f z) ^ (q / 2))
  ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
    deriv (intervalDomainLift f) y)
  y
```

Keep the base positivity explicit; it is the main side condition that keeps `rpow` manageable.

### H. Squared chain-rule integrand

The key pointwise rewrite is:

```lean
((q / 2) * a ^ (q / 2 - 1) * b) ^ 2 =
  (q ^ 2 / 4) * a ^ (q - 2) * b ^ 2
```

under `0 < a`. Useful scalar facts:

```lean
have hpow_exp : 2 * (q / 2 - 1) = q - 2 := by ring
have hqhalf_sq : (q / 2) ^ 2 = q ^ 2 / 4 := by ring
```

For `rpow`, use `Real.rpow_mul` / `Real.mul_rpow` with `le_of_lt hbase_pos`.

### I. Positivity of mass

For the final mass term, nonnegativity is enough for coefficient comparison, but strict positivity is useful for some Young rewrites:

```lean
theorem intervalDomain_integral_pos_of_pos_continuous
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hf_cont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    0 < intervalDomain.integral f
```

Proof route: unfold `intervalDomainIntegral`, prove `0 < intervalDomainLift f y` on `Icc 0 1`, then use an interval-integral positivity theorem. If using only nonnegativity in the final closure, the easier `intervalDomain_integral_rpow_nonneg (q := 1)` plus `Real.rpow_one` is enough.

## 6. Recommended implementation order

1. Add/prove `agmon_inequality_interval_Ioo` or `agmon_inequality_interval_Ioo_ae` in `ShenWork/PDE/GagliardoNirenberg.lean`.

2. Add/prove the interval-domain power Agmon core:

```lean
intervalDomain_positive_C2_power_agmon_core
```

3. Add/prove the uniform pre-absorption theorem:

```lean
intervalDomain_positive_C2_pre_absorption_uniform
```

Pay attention to quantifier order: `Cδ` must be chosen from `q, δ`, before `f`.

4. Add the small scalar and nonnegativity lemmas:

```lean
exists_delta_for_interpolation_coeff
intervalDomain_integral_rpow_nonneg
intervalDomain_weightedGradientIntegral_nonneg
```

5. Prove:

```lean
unitIntervalPositiveAgmonInterpolation_of_pre_absorption_uniform
```

or directly:

```lean
theorem unitIntervalPositiveAgmonInterpolation_proved :
    UnitIntervalPositiveAgmonInterpolation := ...
```

6. Keep the existing wiring theorem:

```lean
intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
```

That theorem already feeds `IntervalDomainClassicalSolutionPositiveInterpolation`, and the newer raw-drop terminal-endpoint wrappers can then consume the resulting mass-gradient frontier through their `relativeMassGradient` fields.

## Bottom line

Existing repo lemmas are close but do not currently prove the C2 `UnitIntervalPositiveAgmonInterpolation` frontier. The missing analytic core is endpoint-safe Agmon/FTC for closed-interval within-regular functions, followed by the `rpow` chain-rule conversion for `f^(q/2)`. The algebraic absorption is already present as `IntervalDomainLemma41.interpolation_absorption`; use it rather than adding a new wrapper or reproving the final quadratic step.
