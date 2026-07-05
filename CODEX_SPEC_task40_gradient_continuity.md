# Task 40: Gradient energy strict-window continuity → hG_int

## Context

We just proved (commit ba7ddc8a):
- `intervalDomain_dx_u_jointlyContinuous`: ContinuousOn (t,x) ↦ deriv(lift(u t)) x on (0,T)×[0,1]
- `intervalDomain_dx_v_jointlyContinuous`: ContinuousOn (t,x) ↦ deriv(lift(v t)) x on (0,T)×[0,1]

Both in `ShenWork/PDE/P3MoserDxJointContinuity.lean`.

The existing infrastructure in `ShenWork/PDE/P3MoserGradientIntegrability.lean` defines:
```lean
def IntervalDomainMoserGradientStrictWindowContinuity (u) (T p0) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
    ContinuousOn (intervalDomainMoserGradientEnergy u p) (Set.Icc a b)

def IntervalDomainMoserGradientStrictWindowIntegrability (u) (T p0) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
    IntervalIntegrable (intervalDomainMoserGradientEnergy u p) volume a b
```

And `intervalDomainMoserGradientEnergy u p t = intervalDomain.integral (fun x => (intervalDomain.gradNorm (fun y => (u t y) ^ (p/2)) x) ^ 2)`.

In 1D (intervalDomain): `gradNorm f x = |deriv (intervalDomainLift f) x.1|` (or similar — check the definition).

## Goal

Create a NEW file `ShenWork/PDE/P3MoserGradientContinuityFromDx.lean` that proves:

```lean
theorem intervalDomain_moserGradientStrictWindowContinuity_of_classical
    {params : CM2Params} {T : ℝ} {p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0 : 2 ≤ p0) :
    IntervalDomainMoserGradientStrictWindowContinuity u T p0

theorem intervalDomain_moserGradientStrictWindowIntegrability_of_classical
    {params : CM2Params} {T : ℝ} {p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0 : 2 ≤ p0) :
    IntervalDomainMoserGradientStrictWindowIntegrability u T p0

theorem intervalDomain_gradientIntegrability_of_classical
    {params : CM2Params} {T : ℝ} {p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0 : 2 ≤ p0) :
    ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy intervalDomain u p s)
        volume a b
```

The LAST theorem is exactly the `hG_int` shape from `P3MoserDissipationFromClassical.lean:143`.

## Proof route

### Step 1: Gradient energy integrand is jointly continuous

For fixed p ≥ 2, the integrand of `intervalDomainMoserGradientEnergy u p t` is:
```
(t,x) ↦ (gradNorm (y ↦ (u t y)^{p/2}) x)²
```

In 1D this is essentially `(deriv (x ↦ (lift(u t)(x))^{p/2}))²`.

By chain rule (for x in the interior where lift(u t) is differentiable):
```
deriv (x ↦ f(x)^{p/2}) = (p/2) · f(x)^{p/2-1} · deriv f x
```

where `f = lift(u t)`.

So the integrand = `((p/2) · (lift(u t)(x))^{p/2-1} · deriv(lift(u t))(x))²`
               = `(p/2)² · (lift(u t)(x))^{p-2} · (deriv(lift(u t))(x))²`

Each factor:
- `(lift(u t)(x))^{p-2}`: jointly continuous on [a,b]×[0,1] because u is ContinuousOn (field 9) and u > 0 (positivity), so u^{p-2} is ContinuousOn
- `(deriv(lift(u t))(x))²`: jointly continuous by `intervalDomain_dx_u_jointlyContinuous`

Product → jointly continuous on [a,b]×[0,1].

### Step 2: Integral of jointly continuous function → continuous in t

Standard result: if `f : ℝ × [0,1] → ℝ` is ContinuousOn on `[a,b] × [0,1]` (compact), then `t ↦ ∫₀¹ f(t,x) dx` is ContinuousOn on `[a,b]`.

In Mathlib: look for `ContinuousOn.integral_comp` or `continuousOn_integral_bilinear` or build from dominated convergence on compact (bounded + uniform continuity gives everything).

Alternatively: the repo may already have a parametric integral continuity result. Check `P3MoserDxJointContinuity.lean` for `continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc` — but that's for variable-limit integrals. For fixed-limit integrals (t ↦ ∫₀¹ f(t,x) dx), Mathlib has `continuousOn_integral_of_compact` or you can use `MeasureTheory.continuousOn_set_integral_of_continuousOn_of_compact`.

### Step 3: Integrability from continuity

Trivial: ContinuousOn on [a,b] → IntervalIntegrable.

### Step 4: Unfold to integratedMoserGradientEnergy

The function `integratedMoserGradientEnergy intervalDomain u p t` equals `intervalDomainMoserGradientEnergy u p t` by `intervalDomainMoserGradientEnergy_eq_integrated`. So the third theorem follows from the second by `rfl`-transport.

## Key challenges in Lean

1. **gradNorm unfolding in 1D**: Find what `intervalDomain.gradNorm f x` actually is. It's likely `‖fderiv ℝ (lift f) x.1‖` or `|deriv (lift f) x.1|` in 1D. Check `ShenWork/PDE/IntervalDomain.lean` for the definition.

2. **Chain rule for rpow**: `deriv (x ↦ f(x) ^ (p/2)) x = (p/2) * f(x)^(p/2-1) * deriv f x` when f(x) > 0 and f differentiable. Mathlib: `HasDerivAt.rpow_const` or `differentiableAt_rpow_const_of_ne`.

3. **Parametric integral continuity on fixed domain**: The clean way is to show the integrand is bounded by a constant on [a,b]×[0,1] (continuity on compact → bounded) and apply dominated convergence. Or use `MeasureTheory.continuousOn_set_integral_of_continuousOn_of_isCompact` if available.

4. **u > 0**: From `hsol.2.2.1 : ∀ t x, 0 < t → t < T → 0 < u t x`. On [a,b]⊂(0,T), u > 0.

## What to read first

1. `ShenWork/PDE/IntervalDomain.lean` — search for `gradNorm` definition
2. `ShenWork/PDE/P3MoserGradientIntegrability.lean` — the target predicates and existing bridges
3. `ShenWork/PDE/P3MoserDxJointContinuity.lean` — import for dx joint continuity
4. `ShenWork/PDE/P3MoserIntegratedClosure.lean:506-510` — integratedMoserGradientEnergy definition

## Imports

```lean
import ShenWork.PDE.P3MoserDxJointContinuity
import ShenWork.PDE.P3MoserGradientIntegrability
import ShenWork.PDE.P3MoserIntegratedClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.SetIntegral
```

## Constraints

- NO sorry, NO axiom
- `#print axioms` only `[propext, Classical.choice, Quot.sound]`
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3MoserGradientContinuityFromDx`
- NEW file: `ShenWork/PDE/P3MoserGradientContinuityFromDx.lean`
- Add to `ShenWork/PDE.lean` import list if needed
- If the full universal-p proof is too hard, deliver at least p=2 (where the chain rule simplifies to `deriv(u) = u_x`, no rpow needed)
