# Q2847 (shen1) — producer-side route for coefficient dissipation wrapper

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Scope: proof audit only; no repository source edits.

Off-limits producer file:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`

Also do not edit `ShenWork/PDE/P3MoserThresholdPlanProducer.lean` for this task. The recommendation below stays in `P3MoserIntegratedClosure.lean` / nearby non-Zinan plumbing.

## Visibility note

The GitHub connector-visible default branch I inspected does **not** yet contain these new names:

```lean
IntegratedMoserDissipationDropBeforeCoeff
integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
scalar_absorb_higherPower_window
```

So I audited against the compiled signature in the prompt and the current surrounding source. The closest existing producer APIs are visible and stable enough to classify.

## Verdict

There is currently **no existing theorem** that produces the full `henergy` window hypothesis needed by

```lean
integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
```

from current `hsol + hcross + hboot` alone.

The closest existing source is still the pointwise differential theorem:

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

in

```text
ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
```

but it is not a window-integrated theorem and it does not expose the fixed-coefficient surplus needed for a target coefficient `theta`, especially not for `theta = 2`.

The minimal honest next wrapper is therefore a **packaging wrapper** that:

1. keeps `henergy` as an explicit full-window higher-power energy frontier;
2. keeps full-window integrated relative Moser as an explicit hypothesis;
3. supplies interval-domain gradient-window nonnegativity from existing `P3MoserIntegratedClosure` lemmas;
4. derives `hp_pos` from `AbstractLpBootstrapHypothesis`.

This wrapper is Lean-checkable once the compiled coefficient theorem is present.

## Closest existing sources for `henergy`

### 1. Pointwise Lp bootstrap energy inequality

File:

```text
ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
```

Key theorem:

```lean
theorem intervalDomain_LpBootstrapEnergyInequality_of_regularity
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequality intervalDomain u T rho p0
```

Internally it builds constants from:

```lean
intervalDomainLpMoserGradientControl_of_regularity
intervalDomainLpLowerOrderControl_of_regularity
intervalDomain_lp_energy_hCrossControl_of_regularity
intervalDomain_lp_energy_hPDEIntegral_of_regularity
intervalDomain_lp_energy_hIBP_of_regularity
intervalDomain_lp_energy_hDiffusionCoercive_of_regularity
intervalDomain_lp_logisticIntegral_le_a_energy_of_regularity
intervalDomain_lp_energy_gradient_inequality_of_frontiers
intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
intervalDomainLpEnergy_eventuallyEq_power_of_regularity
```

The final exposed shape is pointwise in time:

```lean
(1 / p) * deriv (fun τ => intervalDomain.integral (fun x => (u τ x)^p)) t
  + A * G_p(t) + B * Y_p(t)
≤ K * Y_{p+rho}(t) + L
```

This is close to `henergy`, but it is **not** the same as the window hypothesis.

### 2. Time derivative infrastructure

File:

```text
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
```

Closest names:

```lean
intervalDomainPowerEnergy_hasDerivAt
intervalDomain_lp_timeLeibniz
intervalDomain_lp_timeLeibniz_intervalIntegral
intervalDomainLpEnergy_eq_powerEnergy_of_pos
```

These prove pointwise derivative/Leibniz statements, but I did not find a theorem of the form:

```lean
∫ s in t1..t2, deriv (fun τ => intervalDomain.integral (fun x => (u τ x)^p)) s
  = intervalDomain.integral (fun x => (u t2 x)^p)
    - intervalDomain.integral (fun x => (u t1 x)^p)
```

for arbitrary closed windows `t1 ∈ Icc 0 T`, `t2 ∈ Icc t1 T`. That is a missing formal bridge for producing `henergy` from pointwise inequalities.

### 3. Existing integration/regularity plumbing

File:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Useful existing names:

```lean
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
Icc_subset_uIcc_zero_T_of_endpoint_memberships
intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
```

These help with integrability and `hG_nonneg`, but they do not integrate the pointwise derivative inequality into the full `henergy` window statement.

### 4. Relative-Moser time integration

Current visible integrated relative helper:

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

These are **strict interior-window** lemmas: they assume `0 < a` and `b < T`. They do not by themselves prove the full-window `hrelInt` needed by the coefficient wrapper when `t1 = 0` or `t2 = T` is allowed.

## Why `henergy` is not currently derivable from existing names

### Missing bridge A: pointwise-to-window integration

`intervalDomain_LpBootstrapEnergyInequality_of_regularity` is pointwise in `t`. To produce `henergy`, one must integrate over `[t1,t2]` and convert the derivative integral into an endpoint difference. The current source has pointwise derivative/Leibniz theorems, but not the closed-window FTC theorem needed at this exact shape.

### Missing bridge B: full-window endpoint treatment

The pointwise energy and relative-Moser statements are interior-time statements (`0 < t`, `t < T`). The target `henergy` quantifies closed windows:

```lean
t1 ∈ Set.Icc (0 : ℝ) T
 t2 ∈ Set.Icc t1 T
```

so endpoints are included. Endpoint-null/a.e. arguments should be possible, but the full closed-window theorem is not currently exposed.

### Missing bridge C: coefficient surplus

The current pointwise energy theorem gives some `A > 0`. For the coefficient wrapper, arbitrary `A > 0` is not enough. The wrapper needs the explicit surplus:

```lean
K * eps ≤ A - theta
```

or at least `theta < A` plus freedom to choose `eps` from `hrelInt`.

For the fixed coefficient route with `theta = 2`, the current `intervalDomain_LpBootstrapEnergyInequality_of_regularity` does **not** expose a proof that its produced `A` is greater than `2`. In fact the internal `Acoef` is built from absorbed diffusion/cross terms and a chain-rule constant; it is positive, but no lower bound by `2` is visible.

### Missing bridge D: nonnegative constant term

The coefficient wrapper’s `henergy` requires `0 ≤ L`. The exposed `LpBootstrapEnergyInequality` type has no nonnegativity field for its `L_const`. Internally, `intervalDomainLpLowerOrderControl_of_regularity` uses a nonnegative constant `params.a + 1`, but that nonnegativity is not retained in the final abstract `LpBootstrapEnergyInequality` package. A producer wrapper that only consumes `LpBootstrapEnergyInequality` cannot recover `0 ≤ L`.

## Minimal honest wrapper that should compile now

Put this kind of wrapper in:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Do not put it in `P3MoserDissipationShape.lean` if it calls closure-side lemmas; `P3MoserIntegratedClosure.lean` already imports `P3MoserDissipationShape.lean`, so the reverse import would risk a cycle.

The statement below keeps the true producer frontier as an explicit `henergy` field and proves the easy interval-domain plumbing around it.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Interval-domain packaging for the coefficient-form integrated Moser
dissipation theorem.  The hard producer input is the full-window higher-power
energy inequality `henergy`; this theorem only supplies `p > 0` from the bootstrap
hypothesis and gradient-window nonnegativity from the concrete interval domain.

This is intentionally not derived from `LpBootstrapEnergyInequality`: the
pointwise-to-window FTC bridge and coefficient-surplus lower bound are not
currently exposed. -/
theorem intervalDomain_integratedMoserDissipationDropBeforeCoeff_of_windowEnergy_and_relative
    {params : CM2Params} {T rho p0 theta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (henergy :
      ∀ p, p0 ≤ p →
        ∃ A K C0 L eps : ℝ,
          0 < eps ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
          (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            integratedMoserEnergy intervalDomain u p t2 -
                integratedMoserEnergy intervalDomain u p t1 +
              A * (∫ s in t1..t2,
                integratedMoserGradientEnergy intervalDomain u p s) ≤
            (C0 * p * (∫ s in t1..t2,
              max 1 (integratedMoserEnergy intervalDomain u p s)) +
              K * (∫ s in t1..t2,
                integratedMoserEnergy intervalDomain u (p + rho) s)) +
              L * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy intervalDomain u p s))) ∧
          K * eps ≤ A - theta)
    (hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps : ℝ, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            (∫ s in t1..t2,
              integratedMoserEnergy intervalDomain u (p + rho) s) ≤
            eps * (∫ s in t1..t2,
              integratedMoserGradientEnergy intervalDomain u p s) +
            Ceps * (∫ s in t1..t2,
              max 1 (integratedMoserEnergy intervalDomain u p s))) :
    IntegratedMoserDissipationDropBeforeCoeff
      theta intervalDomain u T rho p0 := by
  have hp_pos : ∀ p, p0 ≤ p → 0 < p := by
    intro p hp
    have hp0_gt_one : 1 < p0 := by
      have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
      have hone_le :
          (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
        le_max_left _ _
      linarith
    linarith
  have hG_nonneg :
      ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2,
          integratedMoserGradientEnergy intervalDomain u p s := by
    intro p _hp t1 _ht1 t2 ht2
    exact intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
      (u := u) (p := p) ht2.1
  exact
    integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
      hp_pos henergy hrelInt hG_nonneg

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Notes:

- If the compiled wrapper uses raw `D.integral` expressions instead of `integratedMoserEnergy` / `integratedMoserGradientEnergy`, keep the statement raw or add `simpa [integratedMoserEnergy, integratedMoserGradientEnergy]` before the final call.
- This wrapper does not need `hsol`; `hboot` is enough for `p > 0`, and `intervalDomain` supplies gradient nonnegativity for every `u`.
- If `IntegratedMoserDissipationDropBeforeCoeff` has argument order `(D u T rho p0 theta)` rather than `(theta D u T rho p0)`, adjust only the final target line.

## What would be needed to produce `henergy` from current pointwise APIs

A genuine producer theorem should be named something like:

```lean
theorem intervalDomain_windowHigherPowerEnergy_of_LpBootstrapEnergyInequality
```

but it is not currently available. A realistic missing statement is:

```lean
theorem intervalDomain_windowHigherPowerEnergy_of_regularity
    {params : CM2Params} {T rho p0 theta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    -- missing: full-window FTC/absolute-continuity for Y_p
    -- missing or explicit: coefficient surplus for theta
    (hsurplus :
      ∀ p, p0 ≤ p →
        -- whatever constants the pointwise producer chooses satisfy:
        -- K p * eps p ≤ A p - theta
        True) :
    ∀ p, p0 ≤ p →
      ∃ A K C0 L eps : ℝ,
        0 < eps ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
        (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          integratedMoserEnergy intervalDomain u p t2 -
              integratedMoserEnergy intervalDomain u p t1 +
            A * (∫ s in t1..t2,
              integratedMoserGradientEnergy intervalDomain u p s) ≤
          (C0 * p * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy intervalDomain u p s)) +
            K * (∫ s in t1..t2,
              integratedMoserEnergy intervalDomain u (p + rho) s)) +
            L * (∫ s in t1..t2,
              max 1 (integratedMoserEnergy intervalDomain u p s))) ∧
        K * eps ≤ A - theta
```

The current pointwise energy theorem is the right starting point, but it does not by itself provide the window theorem.

## Endpoint/window conditions

Be careful about the following mismatch:

- `RelativeMoserInterpolationBefore` is pointwise only for `0 < t` and `t < T`.
- The coefficient dissipation predicate quantifies windows with endpoints in closed intervals: `t1 = 0` and `t2 = T` are allowed.
- Existing integrated relative helpers in `P3MoserIntegratedClosure.lean` are strict-interior helpers (`0 < a`, `b < T`).

Therefore a full-window `hrelInt` should remain a separate hypothesis unless/until an endpoint-null/a.e. lemma is proved. The likely lemma would use interval integrability plus equality/inequality almost everywhere on `[t1,t2]` excluding `{0,T}`.

## `A > theta` versus explicit `K*eps ≤ A-theta`

For the compiled wrapper’s current henergy shape, keep the explicit condition:

```lean
K * eps ≤ A - theta
```

Do not replace it by `0 < A`.

A theorem with only `theta < A` is possible **only if** it also chooses `eps` itself using full-window `hrelInt`, for example:

```lean
eps := (A - theta) / (K + 1)
```

and proves `K * eps ≤ A - theta`. But the current pointwise producer does not expose `A > theta`, and for the fixed coefficient route `theta = 2` it only exposes a positive coefficient, not a coefficient above `2`. So the safest producer frontier should retain explicit surplus.

## Minimal honest frontier

Until the window FTC and surplus facts are proved, the honest producer frontier is:

```lean
IntervalDomainHigherPowerWindowEnergyCoeffFrontier params u T rho p0 theta
```

with body exactly the `henergy` hypothesis in the wrapper, plus a separate full-window integrated relative-Moser frontier. This is not empty: it isolates the remaining analytic work precisely and lets the coefficient dissipation wrapper be used without pretending that pointwise `LpBootstrapEnergyInequality` already supplies a closed-window absorbed estimate.

## Bottom line

Closest existing source for `henergy`:

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

and its internal proof ingredients in `IntervalDomainLpBootstrapEnergyInequality.lean` / `IntervalDomainLpEnergyFrontiers.lean`.

But the smallest Lean-checkable next wrapper should **not** claim derivation from that theorem. It should package explicit `henergy + hrelInt` into `IntegratedMoserDissipationDropBeforeCoeff` and supply only the easy interval-domain plumbing (`p > 0`, `∫G ≥ 0`). The missing analytic/formal theorem is the closed-window higher-power energy estimate with explicit coefficient surplus.
