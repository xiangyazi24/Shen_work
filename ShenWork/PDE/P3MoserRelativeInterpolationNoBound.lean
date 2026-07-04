import ShenWork.PDE.P3MoserRelativeMassGradientProducer
import ShenWork.PDE.P3MoserLemmas

/-!
# Task 24 audit: relative interpolation without bounded-before

The requested target was to produce

```
RelativeMoserInterpolationBefore intervalDomain u T rho p0
```

from only `(hsol, hcross, hboot)`, avoiding
`IsPaper2BoundedBefore intervalDomain T u`.

## Outcome

The current codebase does not contain enough proved infrastructure to produce
that target from exactly `(hsol, hcross, hboot)`.

The obstruction is precise.  The mass-gradient route gives, for `q = p + rho`,

```
∫ u^q <= eta * ∫ u^(q-2) |grad u|^2 + Ceta * (∫ u)^q.
```

The lower-order mass conversion

```
Ceta * (∫ u)^(p+rho) <= Crel * ∫ u^p
```

is already available from classical positivity plus the seed `L^p0` bootstrap;
it does not require bounded-before.

The missing input is the weighted-gradient bridge

```
∫ u^(p+rho-2) |grad u|^2
  <= cGrad p * ∫ |grad (u^(p/2))|^2.
```

The existing proof of this bridge is exactly
`intervalDomain_weightedGradient_rho_le_of_boundedBefore`, which uses a
uniform-in-time pointwise bound `u^rho <= M^rho`.

The proposed 1D GN/Young estimate controls the left power integral directly by

```
eps * ∫ |grad (u^(p/2))|^2 + Ceps * (∫ u^p)^((p+rho)/p),
```

or, in the Agmon direct route already present in
`P3MoserAgmonDirectRoute.lean`, by a constant lower-order term under additional
exponent restrictions.  Neither statement matches the current
`RelativeMoserInterpolationBefore` interface, whose lower-order term is linear
in `∫ u^p` with a coefficient chosen before time.  Reducing the superlinear
current-Lp term to the linear one would itself require a current `L^p` bound,
which is only produced later by the Moser iteration consumer.

Thus the circularity is not broken at the current predicate boundary.  A
weaker substitute would suffice if one of the following is added:

* a uniform pointwise bound on `u` before `T` (the existing bounded-before
  hypothesis, or any equivalent local-in-time field with the same quantifier
  strength);
* a new Moser consumer whose interpolation predicate allows the superlinear
  current-Lp lower-order term and uses the induction's current `L^p` bound to
  close it;
* a direct constant-interpolation route, such as the Agmon route, with the
  extra exponent hypotheses and consumer shape it requires.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserRelativeInterpolationNoBound

noncomputable section

/-- The exact extra bridge missing from `(hsol, hcross, hboot)` for the
current mass-gradient route to produce `RelativeMoserInterpolationBefore`
without invoking `IsPaper2BoundedBefore`. -/
def WeightedGradientBridgeBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T rho p0 : ℝ) : Prop :=
  ∃ cGrad : ℝ → ℝ,
    (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
    (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
        (u t x) ^ (pExp + rho - 2) *
          (intervalDomain.gradNorm (u t) x) ^ 2) ≤
      cGrad pExp * intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2))

/-- What is already available from `(hsol, hcross, hboot)` without
bounded-before: the mass-gradient interpolation family and the lower-order
mass-to-current-Lp conversion. -/
theorem intervalDomain_relativeMoserInterpolationNoBound_components_of_classical
    {params : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain
        (pExp + rho) eta Ceta T u) ∧
      MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0 :=
  ShenWork.IntervalDomainExistence.P3MoserRelativeMassGradientProducer.intervalDomain_relativeMassGradient_components_BD_of_classical
    hsol hcross hboot

/-- Conditional no-bounded-before wiring: if the missing weighted-gradient
bridge is supplied by some future analytic argument, the current codebase can
produce the requested `RelativeMoserInterpolationBefore`. -/
theorem intervalDomain_relativeMoserInterpolationBefore_of_classical_noBound
    {params : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hgrad : WeightedGradientBridgeBefore u T rho p0) :
    RelativeMoserInterpolationBefore intervalDomain u T rho p0 := by
  rcases hgrad with ⟨cGrad, hcGrad, hgrad⟩
  rcases
    intervalDomain_relativeMoserInterpolationNoBound_components_of_classical
      hsol hcross hboot with
    ⟨hMG, hmassToLp⟩
  exact
    ShenWork.IntervalDomainExistence.P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient
      cGrad hcGrad hMG hgrad hmassToLp

#print axioms intervalDomain_relativeMoserInterpolationNoBound_components_of_classical
#print axioms intervalDomain_relativeMoserInterpolationBefore_of_classical_noBound

end

end ShenWork.IntervalDomainExistence.P3MoserRelativeInterpolationNoBound
