import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper2.Statements

/-!
# Regularity producer data for `IntegratedMoserFirstCrossingRegularity`

This file packages explicit regularity frontiers for
`IntegratedMoserFirstCrossingRegularity intervalDomain u T p0`.
Classical solutions are still used for the separate nonnegativity field, but
they are not claimed to prove the closed-time and gradient-integrability
regularity fields by themselves.

The four fields of `IntegratedMoserFirstCrossingRegularity` are:

1. `energyContinuous`: `t ↦ ∫₀¹ u(t,x)^p dx` is continuous on `[0,T]`.
   This remains an explicit frontier: joint space-time continuity plus a
   parametric-integral continuity lemma should eventually produce it.

2. `initialPowerBound`: `∫₀¹ u(0,x)^p dx ≤ C₀` for some `C₀ ≥ 0`.
   This is algebraic: use `max integral 0` as a nonnegative upper bound.

3. `powerTimeIntegrable`: `t ↦ ∫₀¹ u(t,x)^p dx` is integrable on `[0,T]`.
   The compatibility package below keeps this as an explicit field, but the
   reduced `Lite` package derives it from `energyContinuous` when `0 ≤ T`.

4. `gradientTimeIntegrable`: the gradient energy is integrable in time.
   This remains an explicit frontier.

The file provides no proof of these analytic frontier fields from the current
classical-solution interface.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-! ### Auxiliary lemmas for the interval domain -/

/-- Pointwise nonnegativity of `u(t,x)` at interior times, extracted from the
classical solution. -/
theorem intervalDomain_u_nonneg_of_classical
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T)
    (x : intervalDomain.Point) :
    0 ≤ u t x :=
  (hsol.u_pos' ht0 htT (x := x)).le

/-- The integral `∫₀¹ u(t,x)^p dx` is nonnegative for a positive classical
solution at interior times. -/
theorem intervalDomain_power_integral_nonneg_of_classical
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    0 ≤ intervalDomain.integral (fun x => (u t x) ^ p) :=
  intervalDomain_integral_nonneg _
    (fun x => Real.rpow_nonneg
      (intervalDomain_u_nonneg_of_classical hsol ht0 htT x) p)

/-! ### Regularity frontier data -/

/-- Explicit interval-domain regularity data for the integrated Moser
first-crossing argument.  The initial bound field is omitted because it is an
algebraic consequence for real-valued integrals. -/
structure IntervalDomainIntegratedMoserRegularityFrontierData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  powerTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- Reduced interval-domain regularity data for the integrated Moser
first-crossing argument.  The power-energy time-integrability field is omitted
because it follows from closed-time energy continuity on the compact interval
`[0,T]` when `0 ≤ T`. -/
structure IntervalDomainIntegratedMoserRegularityFrontierDataLite
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- Minimal classical-solution-facing data still needed to produce the reduced
integrated-Moser regularity frontier.

The endpoint energy field is separated because current classical regularity is
interior in time.  The gradient time-integrability field is a genuine analytic
frontier. -/
structure IntervalDomainIntegratedMoserClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- Classical-solution-facing regularity data with the gradient residual stated
as closed-time continuity rather than raw time integrability. -/
structure IntervalDomainIntegratedMoserClassicalGradientContinuityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientEnergyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.Icc (0 : ℝ) T)

/-- Global-classical-solution-facing regularity data.  Compared with
`IntervalDomainIntegratedMoserClassicalRegularityData`, this only asks for the
left endpoint of the power-energy continuity package; the right endpoint is an
interior time for a longer global classical branch. -/
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

/-- Convert global-classical-facing regularity data to the local
classical-branch package by deriving right-endpoint power-energy continuity
from the global branch. -/
theorem intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy :=
    intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
      hglobal hT hdata.atZero
  gradientTimeIntegrable := hdata.gradientTimeIntegrable

/-- Extract energy continuity from the explicit regularity frontier data. -/
theorem intervalDomain_energyContinuous_of_regularityFrontierData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0) :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) :=
  hreg.energyContinuous

/-! ### Initial power bound -/

/-- The initial power integral has a nonnegative real upper bound. -/
theorem intervalDomain_initialPowerBound
    {p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ} :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        intervalDomain.integral (fun x => (u 0 x) ^ p) ≤ C0 := by
  intro p _hp
  refine ⟨max (intervalDomain.integral (fun x => (u 0 x) ^ p)) 0, ?_, ?_⟩
  · exact le_max_right _ _
  · exact le_max_left _ _

/-! ### Power time integrability -/

/-- Closed-time energy continuity on `[0,T]` implies power-energy
time-integrability on `Set.uIcc 0 T`. -/
theorem intervalDomain_powerTimeIntegrable_of_energyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (henergy :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T)) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hIcc :
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) volume :=
    (henergy p hp).integrableOn_Icc
  simpa [Set.uIcc_of_le hT] using hIcc

/-! ### Gradient time integrability -/

/-- Closed-time continuity of the Moser gradient energy implies the
gradient-energy time-integrability field. -/
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

/-- Convert the closed-gradient-continuity package to the existing classical
regularity-data package. -/
theorem intervalDomain_classicalRegularityData_of_gradientContinuityData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hdata :
      IntervalDomainIntegratedMoserClassicalGradientContinuityData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy := hdata.endpointEnergy
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
      hT hdata.gradientEnergyContinuous

/-- Extract power-energy time integrability from the explicit regularity
frontier data. -/
theorem intervalDomain_powerTimeIntegrable_of_regularityFrontierData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume :=
  hreg.powerTimeIntegrable

/-- Extract gradient-energy time integrability from the explicit regularity
frontier data. -/
theorem intervalDomain_gradientTimeIntegrable_of_regularityFrontierData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume :=
  hreg.gradientTimeIntegrable

/-! ### Reduced frontier conversion -/

/-- Expand the reduced regularity frontier to the compatibility frontier by
deriving power-energy time-integrability from closed-time energy continuity. -/
theorem intervalDomain_regularFrontierData_of_lite
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0) :
    IntervalDomainIntegratedMoserRegularityFrontierData u T p0 where
  energyContinuous := hreg.energyContinuous
  powerTimeIntegrable :=
    intervalDomain_powerTimeIntegrable_of_energyContinuous
      hT hreg.energyContinuous
  gradientTimeIntegrable := hreg.gradientTimeIntegrable

/-! ### Main producer -/

/-- Produce `IntegratedMoserFirstCrossingRegularity` for `intervalDomain`
from explicit regularity frontier data. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 where
  energyContinuous :=
    intervalDomain_energyContinuous_of_regularityFrontierData hreg
  initialPowerBound :=
    intervalDomain_initialPowerBound
  powerTimeIntegrable :=
    intervalDomain_powerTimeIntegrable_of_regularityFrontierData hreg
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_of_regularityFrontierData hreg

/-- Instance-facing producer for
`IntegratedMoserFirstCrossingRegularity`. -/
theorem
    intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierDataFact
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    [hreg : Fact
      (IntervalDomainIntegratedMoserRegularityFrontierData u T p0)] :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
    hreg.out

/-- Produce `IntegratedMoserFirstCrossingRegularity` from the reduced
regularity frontier. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
    (intervalDomain_regularFrontierData_of_lite hT hreg)

/-- Classical-solution-facing reduced producer for
`IntegratedMoserFirstCrossingRegularity`; the classical solution supplies the
positive horizon `T > 0`. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
    (IsPaper2ClassicalSolution.T_pos hsol).le hreg

/-! ### Classical-solution-facing regularity data -/

/-- Build the reduced integrated-Moser regularity frontier from a classical
solution plus the two honest extra regularity inputs not supplied by the
current classical-solution API. -/
theorem intervalDomain_regularityLite_of_classicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0) :
    IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0 where
  energyContinuous :=
    intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
      hsol hdata.endpointEnergy
  gradientTimeIntegrable := hdata.gradientTimeIntegrable

/-- Produce `IntegratedMoserFirstCrossingRegularity` from a classical solution
plus endpoint-energy and gradient-integrability data. -/
theorem
    intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
    (intervalDomain_regularityLite_of_classicalRegularityData hsol hdata) hsol

/-- Build the reduced regularity frontier directly from the at-zero-only
global-classical package. -/
theorem intervalDomain_regularityLite_of_globalClassicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0) :
    IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0 :=
  intervalDomain_regularityLite_of_classicalRegularityData
    (hglobal.classical hT)
    (intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
      hglobal hT hdata)

/-- Produce `IntegratedMoserFirstCrossingRegularity` directly from the
at-zero-only global-classical package. -/
theorem
    intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
    (intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
      hglobal hT hdata)
    (hglobal.classical hT)

/-! ### Combined regularity + nonnegativity package -/

/-- Produce both `IntegratedMoserFirstCrossingRegularity` and
`IntegratedMoserEnergyNonnegativity` from explicit regularity data and a
classical solution.
This is the standard entry point for the Moser iteration route. -/
theorem intervalDomain_regularity_and_nonnegativity_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 ∧
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
  ⟨intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData hreg,
   intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol⟩

/-- Reduced regularity-data version of
`intervalDomain_regularity_and_nonnegativity_of_classical`. -/
theorem intervalDomain_regularity_and_nonnegativity_of_lite_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 ∧
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
  ⟨intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
      hreg hsol,
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol⟩

/-! ### Lower-average/epsilon-gap data assembly -/

/-- Assemble the full `IntegratedMoserFirstCrossingLowerAverageEpsilonData`
from explicit regularity data and a classical solution, given the dissipation,
interpolation, lower-average, and epsilon-gap frontiers as separate inputs.

This is the top-level interface that the actual Moser wiring file should call.
The regularity data gives closed-time and time-integrability facts; `hsol`
gives nonnegativity; the remaining hypotheses are the genuine PDE content. -/
theorem intervalDomain_lowerAverageEpsilonData_of_classical
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hgap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          IntegratedMoserWindowUpperGapEpsilonFrontier
            intervalDomain u T rho p0 p) :
    IntegratedMoserFirstCrossingLowerAverageEpsilonData
      intervalDomain u T rho p0 where
  regularity :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData hreg
  energyNonneg :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
  dissipation := hdiss
  relative := hrel
  rho_pos := hrho
  p0_nonneg := hp0_nonneg
  lowerAverage := hlower
  epsilonGap := hgap

/-- Reduced regularity-data version of
`intervalDomain_lowerAverageEpsilonData_of_classical`. -/
theorem intervalDomain_lowerAverageEpsilonData_of_lite_classical
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hgap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          IntegratedMoserWindowUpperGapEpsilonFrontier
            intervalDomain u T rho p0 p) :
    IntegratedMoserFirstCrossingLowerAverageEpsilonData
      intervalDomain u T rho p0 :=
  intervalDomain_lowerAverageEpsilonData_of_classical
    (intervalDomain_regularFrontierData_of_lite
      (IsPaper2ClassicalSolution.T_pos hsol).le hreg)
    hsol hdiss hrel hrho hp0_nonneg hlower hgap

/-! ### Lower-average/upper-data-gap data assembly -/

/-- Assemble the preferred
`IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` package from
explicit regularity data and a classical solution, given dissipation,
interpolation, lower-average, and upper-data-gap frontiers separately.

Unlike the older epsilon-gap route, the upper-gap chooser may inspect the
fixed-window upper-bound data witness selected by the routine Moser algebra. -/
theorem intervalDomain_lowerAverageUpperDataGapData_of_classical
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hupperDataGap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 p)) :
    IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
      intervalDomain u T rho p0 where
  regularity :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData hreg
  energyNonneg :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
  dissipation := hdiss
  relative := hrel
  rho_pos := hrho
  p0_nonneg := hp0_nonneg
  lowerAverage := hlower
  upperDataGap := hupperDataGap

/-- Reduced regularity-data version of
`intervalDomain_lowerAverageUpperDataGapData_of_classical`. -/
theorem intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hupperDataGap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 p)) :
    IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
      intervalDomain u T rho p0 :=
  intervalDomain_lowerAverageUpperDataGapData_of_classical
    (intervalDomain_regularFrontierData_of_lite
      (IsPaper2ClassicalSolution.T_pos hsol).le hreg)
    hsol hdiss hrel hrho hp0_nonneg hlower hupperDataGap

/-- Shortcut: produce `IntegratedMoserFirstCrossingStep` from explicit
regularity data, a classical solution, and the four PDE-content hypotheses via
the lower-average/epsilon-gap route. -/
theorem intervalDomain_firstCrossingStep_of_classical_and_frontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hgap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          IntegratedMoserWindowUpperGapEpsilonFrontier
            intervalDomain u T rho p0 p) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
    (intervalDomain_lowerAverageEpsilonData_of_classical
      hreg hsol hdiss hrel hrho hp0_nonneg hlower hgap)

/-- Reduced regularity-data shortcut for
`IntegratedMoserFirstCrossingStep`. -/
theorem intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hgap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          IntegratedMoserWindowUpperGapEpsilonFrontier
            intervalDomain u T rho p0 p) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
    (intervalDomain_lowerAverageEpsilonData_of_lite_classical
      hreg hsol hdiss hrel hrho hp0_nonneg hlower hgap)

/-- Shortcut: produce `IntegratedMoserFirstCrossingStep` from explicit
regularity data, a classical solution, and the preferred lower-average /
upper-data-gap frontiers. -/
theorem intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hupperDataGap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 p)) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
    (intervalDomain_lowerAverageUpperDataGapData_of_classical
      hreg hsol hdiss hrel hrho hp0_nonneg hlower hupperDataGap)

/-- Reduced regularity-data shortcut for the preferred lower-average /
upper-data-gap first-crossing route. -/
theorem intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hupperDataGap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 p)) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
    (intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
      hreg hsol hdiss hrel hrho hp0_nonneg hlower hupperDataGap)

section AxiomAudit

#print axioms intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
#print axioms intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
#print axioms intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
#print axioms intervalDomain_classicalRegularityData_of_gradientContinuityData
#print axioms intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
#print axioms intervalDomain_regularityLite_of_globalClassicalRegularityData
#print axioms
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData
#print axioms intervalDomain_regularityLite_of_classicalRegularityData
#print axioms intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
#print axioms intervalDomain_lowerAverageEpsilonData_of_classical
#print axioms intervalDomain_lowerAverageEpsilonData_of_lite_classical
#print axioms intervalDomain_lowerAverageUpperDataGapData_of_classical
#print axioms intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
#print axioms intervalDomain_firstCrossingStep_of_classical_and_frontiers
#print axioms intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
#print axioms intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
#print axioms intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers

end AxiomAudit

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
