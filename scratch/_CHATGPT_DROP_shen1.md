# Q2709 (shen1) — Agmon producer route audit

Repo: `xiangyazi24/Shen_work`, Lean 4 / Mathlib 4.29.1.  
Scope: non-Zinan files only.  I did not inspect, rely on, or propose edits to
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

I inspected the current committed `ShenWork/PDE/IntervalAgmonInterpolation.lean`.
It now contains no `sorry`s, defines the uniform frontier
`UnitIntervalPositiveAgmonInterpolation`, and proves the wiring theorem

```lean
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolation) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params
```

The wiring theorem is the right quantifier-order fix: `Ceps` is chosen before the
slice `f`.  The remaining question is whether the frontier itself is a theorem
under its current weak slice assumptions.

## 1. Is `UnitIntervalPositiveAgmonInterpolation` true as stated?

Lean-oriented answer: **do not try to prove it from the current assumptions as
stated.**  It is still under-hypothesized for a direct analytic proof.

Current frontier:

```lean
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
        DifferentiableOn ℝ (intervalDomainLift f) (Set.Ioo (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q
```

The issue is the same one that killed the old FTC and `L¹ ≤ L²` sublemmas, but
now hidden inside the frontier: `ContinuousOn` on `[0,1]` plus
`DifferentiableOn` on `(0,1)` does not give the absolute-continuity / Sobolev
regularity needed to use the derivative integral.  In the repository,
`intervalDomain.gradNorm f x` is

```lean
|deriv (intervalDomainLift f) x.1|
```

so the gradient term is a Bochner interval integral of a derivative expression.
For a direct proof, one needs enough regularity to know that this derivative term
is the right derivative in an FTC sense and is square-integrable or at least
usable in the relevant chain-rule estimate.

Mathematical adversarial example shape: a positive continuous function on
`[0,1]` that is differentiable on `(0,1)` but has a non-square-integrable
oscillatory derivative near an endpoint.  The weak assumptions allow such
functions.  In ordinary analysis one cannot use a finite-energy Agmon/Sobolev
inequality on them.  In Lean this is worse: unprotected interval integrals of
nonintegrable functions are not a valid substitute for extended-real `∞` terms,
so the statement can behave like a false finite-integral claim rather than a
vacuously-true extended-integral claim.

The current proposition is acceptable **only as an explicit residual**.  It is
not the right theorem target for Codex to attack directly.

## 2. Thinnest corrected uniform frontier strong enough for classical slices

Use a `C¹`/Sobolev-strength slice assumption.  The cleanest minimal surface that
wires to existing `hsol.regularity` fields is:

```lean
ContDiffOn ℝ 1 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)
```

because every classical solution slice already provides the stronger field:

```lean
(hsol.regularity.2.2.2.2.1 t ht).1.1 :
  ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1)
```

So the corrected frontier should be:

```lean
def UnitIntervalPositiveAgmonInterpolationC1 : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 1 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q
```

This is still a genuine analytic theorem, not a trivial wrapper.  But it is now
the right statement shape: the quantifier order is uniform, and the regularity
surface is strong enough to justify the FTC / Cauchy--Schwarz / chain-rule route.

If the proof of the actual analytic inequality gets stuck on endpoint behavior
of `intervalDomainLift`, the next honest strengthening is:

```lean
ContDiffOn ℝ 1 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)
∧ IntervalIntegrable (fun x => deriv (intervalDomainLift f) x) volume 0 1
∧ IntervalIntegrable (fun x =>
    f ⟨x, _⟩ ^ (q - 2) * deriv (intervalDomainLift f) x ^ 2) volume 0 1
```

But I would not put the integrability fields into the public frontier first,
because `ContDiffOn ℝ 1` on compact `[0,1]` should be enough to derive the
ordinary derivative integrability facts locally.  Keep those as private lemmas
inside the future proof, not caller-facing fields, unless Mathlib friction forces
the explicit surface.

## 3. Search-oriented guidance for Codex

Start with the existing repo algebra and frontier files:

```bash
grep -R "UnitIntervalPositiveAgmonInterpolation\|intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon" -n ShenWork/PDE ShenWork/Paper2

grep -R "IntervalDomainInterpolation\|interpolation_absorption\|quadratic_absorption" -n ShenWork/Paper2/IntervalDomainLemma41.lean

grep -R "LpMassGradientInterpolationEstimate\|Lemma_4_1_intervalDomain_of_solution_interpolation_frontier\|IntervalDomainClassicalSolutionPositiveInterpolation" -n ShenWork/Paper2 ShenWork/PDE

grep -R "ContDiffOn ℝ 2 (intervalDomainLift (u t))\|solution_deriv_lift_continuousOn_Icc\|lift_hasDerivAt_interior" -n ShenWork/Paper2 ShenWork/PDE

grep -R "intervalIntegral.integral_deriv\|integral_deriv_eq\|integral_mul_deriv\|intervalFluxByParts_open\|intervalCosineLaplacianCoeff_eq" -n ShenWork/Paper2 ShenWork/PDE
```

Useful repo files to inspect first:

```lean
ShenWork/PDE/IntervalAgmonInterpolation.lean
ShenWork/Paper2/IntervalDomainLemma41.lean
ShenWork/Paper2/IntervalDomainTheorem11.lean
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
ShenWork/Paper2/IntervalDomainMass.lean
ShenWork/PDE/IntervalSolutionCoeffDeriv.lean
ShenWork/PDE/IntervalDomain.lean
```

Likely Mathlib theorem/API patterns to type-search:

```lean
#check intervalIntegral.integral_deriv_eq_sub
#check intervalIntegral.integral_deriv_eq_sub'
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_mono_on
#check intervalIntegral.integral_const
#check intervalIntegral.integral_add
#check intervalIntegral.integral_const_mul

#check ContDiffOn.continuousOn
#check ContDiffOn.differentiableOn
#check ContDiffOn.of_le
#check HasDerivAt.rpow_const
#check HasDerivWithinAt.rpow_const
#check DifferentiableOn.rpow

#check ContinuousOn.intervalIntegrable
#check IntervalIntegrable.norm
#check IntervalIntegrable.mul
#check IntervalIntegrable.pow
#check intervalIntegral.integral_nonneg

#check Real.rpow_pos_of_pos
#check Real.rpow_nonneg
#check Real.rpow_le_rpow
#check Real.rpow_add
#check Real.sqrt_mul
#check Real.sq_sqrt
```

For Cauchy--Schwarz/Hölder, search in Mathlib for these names/patterns rather
than guessing exact spelling:

```lean
#check MeasureTheory.integral_mul_le_Lp_mul_Lq
#check MeasureTheory.lintegral_mul_le_Lp_mul_Lq
#check MeasureTheory.memLp_const
#check MeasureTheory.MemLp
#check MeasureTheory.eLpNorm
```

If those are too heavy, avoid the `Lp` API and prove the unit-interval
`L¹ ≤ L²` lemma using a dedicated Cauchy--Schwarz lemma over
`volume.restrict (Set.Icc 0 1)` or `volume.restrict (Set.Ioc 0 1)`, then convert
back to interval integrals.

Likely imports for the analytic proof attempt:

```lean
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain
import ShenWork.Paper2.IntervalDomainLemma41
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSpace
```

Keep `Mathlib.MeasureTheory.Function.LpSpace` optional; it may be expensive, but
it is the likely source for Hölder/Cauchy--Schwarz if the local environment has
those theorem names.

## 4. Compile-likely corrected frontier and wiring theorem

This is the patch shape I recommend.  It does not prove Agmon; it records the
right residual and gives a finished wrapper from existing classical regularity.

```lean
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Uniform positive one-dimensional Agmon/Gagliardo-Nirenberg frontier on the
unit interval, with a `C¹` slice regularity surface.

This is the corrected theorem target.  The constant is chosen from `q` and
`eps`, before the particular positive slice `f` is supplied. -/
def UnitIntervalPositiveAgmonInterpolationC1 : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 1 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q

/-- A `C¹` uniform Agmon frontier implies the current weaker-looking uniform
frontier.  This is optional; keep it only if existing callers already expect
`UnitIntervalPositiveAgmonInterpolation`.

The proof uses the fact that callers supplying only `ContinuousOn` and
`DifferentiableOn` are not enough to produce `ContDiffOn`; therefore this
conversion should **not** be added in this direction.  Instead, change callers to
use `UnitIntervalPositiveAgmonInterpolationC1` directly.
-/- no theorem here on purpose -/

/-- Produce the classical-solution positive interpolation frontier from the
corrected `C¹` uniform unit-interval Agmon frontier. -/
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon_C1
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolationC1) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params := by
  intro T u v hsol eps heps q hq
  rcases hagmon q hq eps heps with ⟨Ceps, hCeps_pos, hCeps⟩
  refine ⟨Ceps, hCeps_pos, ?_⟩
  intro t ht0 htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hf_pos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hC2_closed :
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hC1_closed :
      ContDiffOn ℝ 1 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hC2_closed.of_le (by norm_num)
  exact hCeps (u t) hf_pos hC1_closed

#print axioms intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon_C1

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
```

If `hC2_closed.of_le (by norm_num)` is the only line that fails under the local
Mathlib spelling, replace it by the local pattern already known to compile in the
current file:

```lean
have hf_diff : DifferentiableOn ℝ (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) :=
  ((hsol.regularity.1 t ht).1).differentiableOn (by norm_num)
```

but then keep the analytic frontier as the existing weak one.  I prefer the C¹
frontier because it is the honest theorem target.

## 5. Realistic proof route for the analytic lemma

Do not attack the current weak frontier.  Attack this:

```lean
UnitIntervalPositiveAgmonInterpolationC1
```

A realistic proof route is:

```text
1. Prove a 1D Agmon/Sobolev bound for nonnegative C¹ `g` on `[0,1]`:
      sup_{x∈[0,1]} g x^2 ≤ A * ∫ g^2 + B * sqrt (∫ g^2) * sqrt (∫ (g')^2)
   or a variant sufficient for the mass-gradient interpolation.

2. Apply it to `g = (intervalDomainLift f) ^ (q / 2)`.

3. Use `HasDerivAt.rpow_const` / `ContDiffOn` chain-rule lemmas and positivity
   to identify
      deriv (fun x => (intervalDomainLift f x) ^ (q / 2))
   with
      (q / 2) * (intervalDomainLift f x) ^ (q / 2 - 1) * deriv (intervalDomainLift f) x.

4. Rewrite the squared derivative as
      (q / 2)^2 * f^(q-2) * (gradNorm f)^2.

5. Feed the algebra into the already-proved
      IntervalDomainLemma41.interpolation_absorption
   or copy that absorption pattern locally.

6. Convert `intervalDomain.integral` to `∫ x in 0..1, intervalDomainLift ...`
   using `intervalDomainIntegral` unfolding and `intervalIntegral.integral_congr`.
```

The hardest Lean work is not the final wiring; it is the chain-rule and interval
integral conversion around `intervalDomainLift`, especially at endpoints.  If
that becomes painful, first prove a real-line lemma for `g : ℝ → ℝ` on
`Set.Icc 0 1`, then add a small bridge from `f : intervalDomain.Point → ℝ` to
`intervalDomainLift f`.

## 6. What should remain as explicit residual now

For current Paper2/Paper3 purposes, keep a named residual; do not fake-prove it:

```lean
UnitIntervalPositiveAgmonInterpolationC1
```

Then export only the wiring theorem:

```lean
intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon_C1
```

This is strong enough for classical solution slices because `hsol.regularity`
already has closed-slab spatial `ContDiffOn ℝ 2` for every interior time slice.
It is also adversarially honest: it does not claim that arbitrary merely
continuous/differentiable functions have the Sobolev/Agmon regularity needed by
the derivative-energy term.
