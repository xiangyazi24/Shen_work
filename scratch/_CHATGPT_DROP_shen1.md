# Q2662 (shen1) — next interface-thinning patch after global endpoint continuity

Repo: `xiangyazi24/Shen_work`  
Scope: Lean 4, current `main` with commits `e278b3fc` and `5c4583a5`.  
Do **not** edit `ShenWork/PDE/P3MoserHighExcursionProducer.lean` or `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

## 1. Yes: add an at-zero-only global-classical regularity data package

This is the smallest interface-thinning patch I see.  It belongs in
`ShenWork/PDE/P3MoserRegularityProducer.lean`, near the existing
`IntervalDomainIntegratedMoserClassicalRegularityData` section.

The point is to replace the carried

```lean
endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
```

by only the left endpoint residual, because
`intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`
already derives `atRight` from a global classical solution by viewing `T` as an
interior time of horizon `T + 1`.

A compile-test-style snippet with all imports:

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

/-- Global-classical-facing reduced regularity data for integrated Moser.

For a global classical solution, right-endpoint power-energy continuity on
`[0,T]` follows by applying the interior-time continuity theorem on the longer
horizon `T + 1`.  Therefore the only endpoint-energy residual that has to remain
explicit is continuity at `0`.  Gradient-energy time integrability is still a
separate analytic input. -/
structure IntervalDomainIntegratedMoserGlobalClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) 0
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- Convert the at-zero-only global-classical package to the existing classical
regularity-data package.

This is pure interface wiring: `atRight` is supplied by
`intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`,
and the gradient field is copied through. -/
theorem intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata : IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy :=
    intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hT hdata.atZero
  gradientTimeIntegrable := hdata.gradientTimeIntegrable

/-- Convenience reduced-frontier producer from the at-zero-only global-classical
package.  This is optional but useful, because most downstream code consumes the
`Lite` frontier or the existing first-crossing regularity producer. -/
theorem intervalDomain_regularityLite_of_globalClassicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata : IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0) :
    IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0 :=
  intervalDomain_regularityLite_of_classicalRegularityData
    (hglobal.classical hT)
    (intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
      hglobal hT hdata)

/-- Convenience first-crossing regularity producer from the at-zero-only
global-classical package.  This does not add analytic power; it only avoids
repeating the conversion at call sites. -/
theorem
    intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata : IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
    (intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
      hglobal hT hdata)
    (hglobal.classical hT)

#print axioms intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
#print axioms intervalDomain_regularityLite_of_globalClassicalRegularityData
#print axioms
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

For the actual patch inside `P3MoserRegularityProducer.lean`, do not duplicate
the import header; the current file already imports `P3MoserEnergyContinuity` and
opens `P3MoserEnergyContinuity`.  Insert the structure and theorem near the
existing `IntervalDomainIntegratedMoserClassicalRegularityData` block, then add
the three `#print axioms` lines to the existing `section AxiomAudit`.

The absolute smallest version is only the structure plus
`intervalDomain_classicalRegularityData_of_globalClassicalRegularityData`.  The
`Lite` and `IntegratedMoserFirstCrossingRegularity` convenience theorems are safe
pure wrappers, but can be skipped if you want the smallest possible diff.

## 2. `atZero` is not plausibly derivable from current `InitialTrace` alone

The likely current shape is:

```lean
def InitialTrace
    (D : BoundedDomainData) (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    D.supNorm (fun x => u t x - u₀ x) < ε
```

This is a right-limit statement toward `u₀` for strictly positive times.  It does
not state `u 0 = u₀`, and it does not directly state continuity of the energy
map at the actual value used by

```lean
ContinuousWithinAt
  (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
  (Set.Icc (0 : ℝ) T) 0
```

The target limit is the value at `t = 0`, namely
`intervalDomain.integral (fun x => (u 0 x) ^ p)`.  `InitialTrace` only controls
`u t` as `t ↓ 0`, relative to `u₀`; it leaves `u 0` unconstrained.  Semantically,
one can keep `u t = u₀` for all `t > 0` small and redefine `u 0` arbitrarily;
the trace statement still holds, while the energy continuity at `0` can fail.

So do **not** add an axiom or theorem claiming

```lean
InitialTrace intervalDomain u₀ u →
  IntervalDomainPowerEnergyEndpointContinuity u T p0
```

or even the `atZero` field, unless extra hypotheses are added.  Reasonable extra
hypotheses would include at least a pointwise/sup-norm identification `u 0 = u₀`
(or an energy identity at `0`) plus a theorem turning the sup-norm trace into
continuity of `∫ (u t)^p` for the relevant real exponents.  For arbitrary real
`p`, that second step is not just algebraic; it needs positivity/floor or a
controlled rpow-continuity argument.

## 3. Better non-high-excursion target among existing residuals

The best immediate non-Zinan target is still the endpoint-regularity residual
itself:

```lean
IntervalDomainIntegratedMoserClassicalRegularityData.endpointEnergy
```

The patch above thins it to the strictly smaller package

```lean
IntervalDomainIntegratedMoserGlobalClassicalRegularityData.atZero
IntervalDomainIntegratedMoserGlobalClassicalRegularityData.gradientTimeIntegrable
```

whenever the caller has

```lean
IsPaper2GlobalClassicalSolution intervalDomain params u v
0 < T
```

After that lands, the next repository-local, non-high-excursion consumer target
is:

```lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals.integratedStep
IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.lowerUpperFrontiers
```

But I would not patch that until a concrete caller actually has global classical
solutions available at the residual surface.  The existing
`IntervalDomainMassLpSmoothingIntegratedStepResiduals` field only receives a
finite-horizon

```lean
IsPaper2ClassicalSolution intervalDomain p T u v
```

not a global classical solution, so an at-zero-only endpoint package cannot be
used there without changing the caller surface.  If the caller only has finite
`hsol`, it still needs the full

```lean
IntervalDomainPowerEnergyEndpointContinuity u T p0
```

or an explicit `atRight` producer.

The remaining honest analytic residuals are still:

```lean
IntervalDomainIntegratedMoserClassicalRegularityData.gradientTimeIntegrable
IntegratedMoserDissipationDropBefore
RelativeMoserInterpolationBefore
IntegratedMoserHighExcursionLowerAverageWindowFrontier
IntegratedMoserWindowUpperDataGapFrontier
```

The last two are Zinan-adjacent high-excursion/threshold-plan territory; consume
them through the already-existing interfaces, but do not edit the owned producer
files.
