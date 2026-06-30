# Q2702 (shen1) — `IntervalAgmonInterpolation.lean` sorry audit

Repo: `xiangyazi24/Shen_work`, Lean 4 / Mathlib 4.29.1.  
Scope: non-Zinan files only.  I did not inspect or rely on
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

## Executive verdict

Do **not** try to fill the four `sorry`s in the current statements as written.
There are two real API problems:

1. `sup_le_integral_add_integral_deriv` and
   `integral_abs_le_sqrt_integral_sq` are missing essential analytic hypotheses.
   They are not just hard Lean exercises.
2. `intervalDomain_classicalSolutionPositiveInterpolation_of_agmon` cannot use
   the current `hagmon` signature, because it needs one `Ceps` uniform for all
   time slices, while the current `hagmon` only gives a `Ceps` after a particular
   function `f` has been chosen.

There is a small compile-likely wiring replacement for (4), but only after
changing the Agmon input to a uniform-frontier shape.

## Source facts checked

`IntervalDomainClassicalSolutionPositiveInterpolation` is:

```lean
abbrev IntervalDomainClassicalSolutionPositiveInterpolation
    (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      ∀ eps, 0 < eps → ∀ q, 1 < q → ∃ Ceps > 0,
        LpMassGradientInterpolationEstimate intervalDomain q eps Ceps T u
```

So the `Ceps` is chosen once after `T,u,v,hsol,eps,q` and before the estimate is
used at arbitrary `t ∈ (0,T)`.  A per-slice `∃ Ceps` from
`hagmon (u t) ...` is too weak.

For classical slices, the regularity accessors available in the repo are enough
to provide positivity and spatial regularity:

```lean
have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
have hpos : ∀ x : intervalDomain.Point, 0 < u t x :=
  fun x => hsol.u_pos' ht0 htT
have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
  (hsol.regularity.2.2.2.2.1 t ht).1.1
```

The file also has the open-interval interior regularity field:

```lean
(hsol.regularity.1 t ht).1 :
  ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1)
```

Those are adequate for wiring to a correct slice inequality, but they do not
supply the missing analytic theorem itself.

## Sorry 1: `sup_le_integral_add_integral_deriv`

### Current statement is too weak

Current theorem:

```lean
theorem sup_le_integral_add_integral_deriv
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_diff : DifferentiableOn ℝ f (Ioo 0 1))
    (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      f x ≤ ∫ y in (0 : ℝ)..1, f y + ∫ y in (0 : ℝ)..1, |deriv f y|
```

The proof sketch needs a fundamental theorem of calculus / bounded variation
step:

```lean
f x - f y ≤ ∫ s in (0 : ℝ)..1, |deriv f s|
```

But `ContinuousOn` on `[0,1]` plus `DifferentiableOn` on `(0,1)` does **not**
encode absolute continuity or an integrable derivative / FTC identity.  In Lean
terms, there is no source for the desired
`f x - f y = ∫ s in y..x, deriv f s` bridge from those hypotheses alone.

A standard counterexample shape is a differentiable continuous function whose
derivative is not Lebesgue integrable, such as an oscillatory term near `0`
(e.g. a smooth bump plus a small `x^2 * sin (1 / x^2)`-type term, adjusted at
`0`).  The derivative has a nonintegrable absolute value near `0`, while the
function is continuous and differentiable on the open interval.  With Mathlib's
unconditional integral notation, nonintegrable terms do not give the FTC bound
for free, so the proposed inequality is not derivable.

### Thinnest honest replacement

Use either an explicit variation/FTC frontier, or strengthen to a genuine C¹ /
absolute-continuity input.

The smallest statement-surface replacement is to name the exact pointwise FTC
consequence the proof needs:

```lean
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Exact FTC/variation input needed for the elementary sup bound. -/
def UnitIntervalDerivativeVariationBound (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    f x - f y ≤ ∫ s in (0 : ℝ)..1, |deriv f s|

/-- Sup bound from the explicit variation input.  This is the honest algebraic
part of the current `sup_le_integral_add_integral_deriv` proof. -/
theorem sup_le_integral_add_integral_deriv_of_variationBound
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hvar : UnitIntervalDerivativeVariationBound f) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      f x ≤ ∫ y in (0 : ℝ)..1, f y + ∫ y in (0 : ℝ)..1, |deriv f y| := by
  intro x hx
  set C := ∫ s in (0 : ℝ)..1, |deriv f s|
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1, f x ≤ f y + C := by
    intro y hy
    have hxy := hvar x hx y hy
    dsimp [C]
    linarith
  have hle_integral : f x ≤ ∫ y in (0 : ℝ)..1, (f y + C) := by
    have hconst : f x = ∫ _y in (0 : ℝ)..1, f x := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    rw [hconst]
    exact intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      intervalIntegrable_const
      ((hf_cont.intervalIntegrable_of_Icc (by norm_num)).add intervalIntegrable_const)
      (fun y hy => hpoint y hy)
  have hsplit : ∫ y in (0 : ℝ)..1, (f y + C) =
      (∫ y in (0 : ℝ)..1, f y) + C := by
    rw [intervalIntegral.integral_add
      (hf_cont.intervalIntegrable_of_Icc (by norm_num))
      intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]
  linarith

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

If Codex wants to prove `UnitIntervalDerivativeVariationBound` later, use a
separate theorem with explicit hypotheses such as `ContDiffOn ℝ 1 f (Icc 0 1)`
or `AbsoluteContinuousOn f (Icc 0 1)` plus the appropriate derivative
integrability/FTC theorem.  Do not hide that in the current weak theorem.

## Sorry 2: `integral_abs_le_sqrt_integral_sq`

### Current statement is false / missing `L²`

Current theorem:

```lean
theorem integral_abs_le_sqrt_integral_sq
    {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) :
    ∫ y in (0 : ℝ)..1, |g y| ≤
      Real.sqrt (∫ y in (0 : ℝ)..1, g y ^ 2)
```

`IntervalIntegrable g` is only an `L¹` hypothesis.  It does not imply that
`g^2` is integrable.  A standard counterexample is `g y = 1 / sqrt y` on
`(0,1]` with any harmless value at `0`: it is `L¹` on the unit interval, but
`g^2 = 1/y` is not integrable.  In Lean, the RHS interval integral is not
justified by `hg`, so the Cauchy--Schwarz proof has no valid input.

### Thinnest honest replacement

Require square integrability.  The theorem then follows from Cauchy--Schwarz /
Hölder on the restricted unit interval.  A compile route is:

```lean
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain
import Mathlib.Analysis.InnerProductSpace.L2Space

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Honest `L¹ ≤ L²` on the unit interval: requires square integrability. -/
theorem integral_abs_le_sqrt_integral_sq_of_sq_integrable
    {g : ℝ → ℝ}
    (hg2 : IntervalIntegrable (fun y => g y ^ 2) volume 0 1) :
    ∫ y in (0 : ℝ)..1, |g y| ≤
      Real.sqrt (∫ y in (0 : ℝ)..1, g y ^ 2) := by
  -- Recommended proof route:
  -- 1. Rewrite interval integrals as integrals over `volume.restrict (Ioc 0 1)`
  --    or `volume.restrict (Icc 0 1)` using the interval-integral API.
  -- 2. Apply Cauchy--Schwarz to `|g| * 1`.
  -- 3. Use `∫ 1^2 = 1` on the unit interval.
  -- 4. Use nonnegativity of `∫ g^2` and `sq_le_sq` / `Real.le_sqrt`.
  --
  -- The key missing input in the old statement is exactly `hg2`; do not try to
  -- derive it from `IntervalIntegrable g`.
  admit

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

Replace the final `admit` with the local Mathlib Cauchy--Schwarz API available in
the working tree.  The important correction is the statement surface: `hg2`, not
`hg`, is the right input.

## Sorry 3: `intervalDomain_agmon_interpolation`

### Current statement is true only in a weak/non-useful sense, and the intended proof route is incomplete

Current theorem places `∃ Ceps` after `f`:

```lean
theorem intervalDomain_agmon_interpolation
    {f : intervalDomain.Point → ℝ}
    ... :
    ∃ Ceps > 0,
      intervalDomain.integral (fun x => f x ^ q) ≤
        eps * intervalDomain.integral
          (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
        Ceps * (intervalDomain.integral f) ^ q
```

With `Ceps` allowed to depend on `f`, this is much easier than the paper's
interpolation frontier and is not enough for `IntervalDomainClassicalSolutionPositiveInterpolation`.
For a fixed positive continuous `f`, `intervalDomain.integral f` is positive, so
one can often choose a huge `Ceps` after seeing `f`; this does not give a uniform
constant for all time slices.

The intended four-step proof also has a mathematical mismatch: Step 2 controls
an unweighted `∫ |f'|` or `∫ (f')²`, but the target gradient term is

```lean
∫ f^(q-2) * (f')²
```

To bridge that honestly you need a power-chain-rule/coercivity argument, usually
by applying the 1D estimate to a power of `f`, e.g. `f^(q/2)`, and proving

```lean
|∂x (f^(q/2))|² = (q / 2)^2 * f^(q-2) * |f'|²
```

on the interior, plus integrability.  The current hypotheses
`ContinuousOn` + `DifferentiableOn` do not package those analytic facts.

### Thinnest useful replacement

Define the useful theorem as a **uniform frontier**:

```lean
/-- Uniform positive 1D Agmon/GN frontier on the unit interval.

The constant is chosen from `q` and `eps` before the particular positive slice
`f` is supplied.  This is the shape needed for classical solution slices. -/
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContinuousOn (intervalDomainLift f) (Icc (0 : ℝ) 1) →
        DifferentiableOn ℝ (intervalDomainLift f) (Ioo (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q
```

If proving the actual inequality now, use stronger assumptions in the producer
lemma, not this weak C¹ shell.  For example, introduce a private analytic lemma
for `ContDiffOn ℝ 1 (intervalDomainLift f) (Icc 0 1)` or explicit
`UnitIntervalDerivativeVariationBound` / square-integrability / chain-rule
frontiers, then export the uniform frontier above only after those pieces are
proved.

## Sorry 4: `intervalDomain_classicalSolutionPositiveInterpolation_of_agmon`

### Current theorem cannot be proved from its current `hagmon`

Current input:

```lean
hagmon :
  ∀ (f : intervalDomain.Point → ℝ), ... →
    ∀ q : ℝ, 1 < q →
      ∀ eps : ℝ, 0 < eps →
        ∃ Ceps > 0, inequality f q eps Ceps
```

This gives `Ceps` after choosing `f`.  In the target, `Ceps` must work for every
time slice in `LpMassGradientInterpolationEstimate intervalDomain q eps Ceps T u`.
Therefore the theorem is not derivable from the current `hagmon` signature.

### Compile-shaped replacement wiring

Use the uniform frontier above.  This should be placed in
`ShenWork/PDE/IntervalAgmonInterpolation.lean` and then the old theorem should be
replaced or deprecated.

```lean
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Uniform positive 1D Agmon/GN frontier on the unit interval. -/
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContinuousOn (intervalDomainLift f) (Icc (0 : ℝ) 1) →
        DifferentiableOn ℝ (intervalDomainLift f) (Ioo (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q

/-- Produce the classical-solution positive interpolation frontier from a uniform
unit-interval Agmon/GN frontier. -/
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolation) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params := by
  intro T u v hsol eps heps q hq
  rcases hagmon q hq eps heps with ⟨Ceps, hCeps_pos, hCeps⟩
  refine ⟨Ceps, hCeps_pos, ?_⟩
  intro t ht0 htT
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hf_pos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hC2_closed :
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hf_cont : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    hC2_closed.continuousOn
  have hC2_open :
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).1
  have hf_diff : DifferentiableOn ℝ (intervalDomainLift (u t)) (Ioo (0 : ℝ) 1) := by
    -- Depending on the local Mathlib API, this line may be either exactly this
    -- or use `hC2_open.contDiffOn`/`contDiffOn_iff_contDiffAt` variants.
    exact hC2_open.differentiableOn (by norm_num : (1 : ℕ∞) ≤ 2)
  exact hCeps (u t) hf_pos hf_cont hf_diff

#print axioms intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

If `ContDiffOn.differentiableOn` expects a different numeric cast in Mathlib
4.29.1, the only fragile line is:

```lean
exact hC2_open.differentiableOn (by norm_num : (1 : ℕ∞) ≤ 2)
```

The rest of the wiring is the right route.  A common fallback is to derive
`DifferentiableOn` from the closed `ContDiffOn` field and then `.mono` to
`Ioo_subset_Icc_self`.

## Practical patch recommendation

For this file, I would make the following small, honest patch:

1. Rename or replace the current weak
   `intervalDomain_classicalSolutionPositiveInterpolation_of_agmon` with
   `intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon`.
2. Replace the current per-function `intervalDomain_agmon_interpolation` target
   by the uniform frontier `UnitIntervalPositiveAgmonInterpolation`, unless the
   per-function theorem is needed elsewhere.  The per-function theorem is not the
   one that closes Paper2/Paper3 callers.
3. Do not try to prove `sup_le_integral_add_integral_deriv` from only
   `ContinuousOn + DifferentiableOn`; introduce either
   `UnitIntervalDerivativeVariationBound` or a stronger `ContDiffOn`/absolute
   continuity theorem.
4. Do not try to prove `integral_abs_le_sqrt_integral_sq` from only
   `IntervalIntegrable g`; add square-integrability.

This leaves the true analytic Agmon/GN theorem as a named residual rather than a
hidden axiom.  The final solution-slice wiring can then be closed cleanly and
without touching statement surfaces outside this file, except for replacing the
bad `hagmon` signature with the uniform one.
