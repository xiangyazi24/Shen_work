# Q2667 (shen1) — gradient-energy continuity audit

Repo: `xiangyazi24/Shen_work`, Lean 4.  
Scope: non-Zinan files only.  Do **not** edit or rely on
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

## Answer first

No: the proposed

```lean
hgrad : ∀ p, p0 ≤ p → ContinuousOn gradientEnergy_p (Set.Icc 0 T)
```

is **not derivable** from the current
`IsPaper2ClassicalSolution intervalDomain params T u v` /
`intervalDomain.classicalRegularity T u v` fields.

The missing thing is not mere spatial `C²` of each fixed-time slice.  The Moser
gradient energy uses

```lean
intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x
```

and `intervalDomain.gradNorm` is definitionally

```lean
|deriv (intervalDomainLift f) x.1|
```

so continuity of `gradientEnergy_p t` requires control of a **spatial derivative
of a powered slice as `t` varies**, plus endpoint-in-time control.  Current
`intervalDomainClassicalRegularity` has joint continuity of the solution field
and of the time-derivative field, and it has fixed-time spatial `C²`; it does
not contain joint continuity of

```lean
(t, x) ↦ deriv (fun z => (intervalDomainLift (u t)) z) x
```

or of the powered derivative

```lean
(t, x) ↦ deriv (fun z => (intervalDomainLift (u t) z) ^ (p / 2)) x
```

on a closed time-space slab.  Also, the target `ContinuousOn ... (Set.Icc 0 T)`
includes `t = 0` and `t = T`; the classical-solution regularity surface is
interior in time except for per-fixed-time spatial closure.

## The small theorem is good, but it consumes a real new field

This theorem itself is a straightforward, compile-shaped wrapper and should be
added in `ShenWork/PDE/P3MoserRegularityProducer.lean` near the existing
`intervalDomain_powerTimeIntegrable_of_energyContinuous` theorem.

```lean
import ShenWork.PDE.P3MoserRegularityProducer

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Closed-time continuity of the Moser gradient energy implies time-integrability
on the finite interval.  This is the exact gradient analogue of
`intervalDomain_powerTimeIntegrable_of_energyContinuous`. -/
theorem intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.Icc (0 : ℝ) T)) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hIcc :
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.Icc (0 : ℝ) T) volume :=
    (hgrad p hp).integrableOn_Icc
  simpa [Set.uIcc_of_le hT] using hIcc

#print axioms intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

The theorem is pure wire-up.  It should not be advertised as produced by
`IsPaper2ClassicalSolution`; it is a way to replace a carried integrability field
by a carried continuity field.

## Why current classical regularity does not prove `hgrad`

The relevant concrete facts are:

```lean
structure BoundedDomainData where
  ...
  gradNorm : (Point → ℝ) → Point → ℝ
  classicalRegularity : ℝ → (ℝ → Point → ℝ) → (ℝ → Point → ℝ) → Prop
```

For `intervalDomain`, the definitions are:

```lean
def intervalDomainGradNorm (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  |deriv (intervalDomainLift f) x.1|

...

def intervalDomain : ShenWork.Paper2.BoundedDomainData where
  Point := intervalDomainPoint
  ...
  gradNorm := intervalDomainGradNorm
  classicalRegularity := intervalDomainClassicalRegularity
```

And `intervalDomainClassicalRegularity` currently gives, among other fields:

```lean
-- fixed-time spatial regularity on the open interval
∀ t ∈ Set.Ioo (0 : ℝ) T,
  ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) ∧ ...

-- fixed-time closed-boundary spatial C² plus endpoint derivative values
∀ t ∈ Set.Ioo (0 : ℝ) T,
  (ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) ∧
    deriv (intervalDomainLift (u t)) 0 = 0 ∧
    deriv (intervalDomainLift (u t)) 1 = 0) ∧ ...

-- joint continuity of the time derivative field
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
  (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)

-- joint continuity of the solution field
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
  (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

What is absent is the spatial-gradient analogue:

```lean
ContinuousOn
  (Function.uncurry
    (fun (t : ℝ) (x : ℝ) =>
      deriv (fun z : ℝ => intervalDomainLift (u t) z) x))
  (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

or, closer to the Moser expression, the powered version:

```lean
∀ p, p0 ≤ p →
  ContinuousOn
    (Function.uncurry
      (fun (t : ℝ) (x : ℝ) =>
        deriv (fun z : ℝ => (intervalDomainLift (u t) z) ^ (p / 2)) x))
    (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

Per-time `ContDiffOn` plus joint continuity of `u` does not imply joint
continuity of `∂ₓu`.  Joint continuity of `∂ₜu` also does not imply it.  Those
are different directions of differentiation.  A future analytic proof may use a
PDE/parabolic-regularity theorem to get this, but that theorem is not encoded in
`intervalDomainClassicalRegularity` right now.

Even a powered-gradient joint-continuity field would still need a compact-slab /
parametric-integral step to turn pointwise joint continuity into continuity of

```lean
fun t => ∫₀¹ |∂ₓ(u(t)^(p/2))|^2
```

and it would need honest endpoint handling at `t = 0` and `t = T`.  So the
current `hgrad` field is already the cleanest immediate interface surface.

## Best honest package name and placement

Place the following in `ShenWork/PDE/P3MoserRegularityProducer.lean`, not in the
high-excursion or threshold-plan files.

```lean
import ShenWork.PDE.P3MoserRegularityProducer

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Closed-time continuity of the Moser gradient energy, exponent by exponent.

This is the honest replacement for directly carrying gradient-energy
`IntegrableOn`: it is stronger, but still not a consequence of the current
classical-solution API. -/
structure IntervalDomainIntegratedMoserGradientEnergyContinuityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  gradientEnergyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.Icc (0 : ℝ) T)

/-- Convert gradient-energy continuity data into the gradient-time-integrability
field expected by `IntervalDomainIntegratedMoserClassicalRegularityData`. -/
theorem intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuityData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hdata : IntervalDomainIntegratedMoserGradientEnergyContinuityData u T p0) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume :=
  intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
    hT hdata.gradientEnergyContinuous

/-- A continuity-based variant of the classical regularity data package.

This is the best next interface-thinning package: callers may provide endpoint
power-energy continuity and gradient-energy continuity; the old gradient
integrability field is derived. -/
structure IntervalDomainIntegratedMoserClassicalContinuityRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientEnergy :
    IntervalDomainIntegratedMoserGradientEnergyContinuityData u T p0

/-- Convert the continuity-based classical regularity package to the existing
classical regularity data package. -/
theorem intervalDomain_classicalRegularityData_of_continuityRegularityData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hdata :
      IntervalDomainIntegratedMoserClassicalContinuityRegularityData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy := hdata.endpointEnergy
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuityData
      hT hdata.gradientEnergy

#print axioms intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuityData
#print axioms intervalDomain_classicalRegularityData_of_continuityRegularityData

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

This is the patch I would ask Codex to land first.  It is small, purely
interface-thinning, and exactly parallel to the already-proved power-energy
continuity-to-integrability bridge.

## If you want the lower-level analytic target instead

If the next Codex is not just thinning the interface, but naming the future
analytic producer target, put the lower-level frontier in
`ShenWork/PDE/P3MoserEnergyContinuity.lean` or a new small
`P3MoserGradientEnergyContinuity.lean` file:

```lean
structure IntervalDomainPowerGradientEnergyJointContinuity
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  poweredSpatialGradient_jointContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun z : ℝ => (intervalDomainLift (u t) z) ^ (p / 2)) x))
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

But do not pretend this is already enough to close `hgrad`; it still needs a
separate parametric-integral continuity lemma for the squared absolute derivative
and endpoint positivity/rpow-chain-rule handling.  For the current Moser
regularity producer, the more honest minimal field is directly
`IntervalDomainIntegratedMoserGradientEnergyContinuityData.gradientEnergyContinuous`.
