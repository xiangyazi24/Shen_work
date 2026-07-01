import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserThresholdPlanProducer
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
open ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer
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

/-- Raw Moser-gradient time-integrability for the positive-time representative.

This is the remaining analytic input after the zero-time re-anchoring route:
anchoring can transport this property across the null singleton `{0}`, but it
does not produce the raw estimate. -/
def IntervalDomainRawMoserGradientTimeIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    IntegrableOn
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      (Set.uIcc (0 : ℝ) T) volume

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

/-- Closed-time continuity of the Moser gradient energy, exponent by exponent.

This is an honest replacement for directly carrying the gradient-energy
`IntegrableOn` field.  It is not currently produced by the classical-solution
API. -/
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

/-- Classical regularity data stated with endpoint power-energy continuity and a
separate gradient-energy continuity package. -/
structure IntervalDomainIntegratedMoserClassicalContinuityRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  gradientEnergy :
    IntervalDomainIntegratedMoserGradientEnergyContinuityData u T p0

/-- Global-classical-solution-facing regularity data.  Compared with
`IntervalDomainIntegratedMoserClassicalRegularityData`, this only asks for the
left endpoint of the power-energy continuity package; the right endpoint is an
interior time for a longer global classical branch. -/
structure IntervalDomainIntegratedMoserGlobalClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- Build the global-classical-facing regularity data from the deleted-right
initial trace theorem plus the honest zero-slice compatibility residual. -/
theorem intervalDomain_globalClassicalRegularityData_of_trace_compat
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0 where
  atZero :=
    intervalDomain_initialPowerEnergyContinuityAtZero_of_traceTendsto_compat
      (intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
        hT htrace hdatum hglobal)
      hcompat
  gradientTimeIntegrable := hgrad

/-- Build the global-classical-facing regularity data for the re-anchored
representative.  No zero-slice compatibility hypothesis is needed: the anchored
trajectory has the prescribed initial slice by construction. -/
theorem intervalDomain_globalClassicalRegularityData_of_trace_paperPositive_anchored
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntervalDomainIntegratedMoserGlobalClassicalRegularityData
      (intervalDomainWithInitialSlice u₀ u) T p0 where
  atZero :=
    intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
      hT htrace hdatum hglobal
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw hgrad

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
    intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
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

/-- Convert gradient-energy continuity data into the gradient-time-integrability
field expected by the classical regularity package. -/
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

/-- Convert the separated continuity-based regularity package to the existing
classical regularity-data package. -/
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

/-- Reduced regularity frontier from a global classical solution, initial trace,
paper-positive initial datum, zero-slice compatibility, and the gradient
time-integrability frontier. -/
theorem intervalDomain_regularityLite_of_globalClassicalTraceCompat
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0 :=
  intervalDomain_regularityLite_of_globalClassicalRegularityData
    hglobal hT
    (intervalDomain_globalClassicalRegularityData_of_trace_compat
      hT htrace hdatum hglobal hcompat hgrad)

/-- Produce the integrated-Moser regularity package from a global classical
solution, initial trace, paper-positive initial datum, zero-slice compatibility,
and the gradient time-integrability frontier. -/
theorem
    intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceCompat
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData
    hglobal hT
    (intervalDomain_globalClassicalRegularityData_of_trace_compat
      hT htrace hdatum hglobal hcompat hgrad)

/-- Reduced regularity frontier for the re-anchored global classical
representative.  The gradient input is stated for the raw trajectory; it is
transported across the zero-time re-anchoring by a.e. equality. -/
theorem intervalDomain_regularityLite_of_globalClassicalTraceAnchored
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntervalDomainIntegratedMoserRegularityFrontierDataLite
      (intervalDomainWithInitialSlice u₀ u) T p0 :=
  intervalDomain_regularityLite_of_globalClassicalRegularityData
    (intervalDomain_globalClassical_withInitialSlice hglobal)
    hT
    (intervalDomain_globalClassicalRegularityData_of_trace_paperPositive_anchored
      hT htrace hdatum hglobal hgrad)

/-- Integrated-Moser regularity for the re-anchored global classical
representative.  The remaining analytic input is raw gradient
time-integrability, transferred across the zero-time re-anchoring. -/
theorem
    intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntegratedMoserFirstCrossingRegularity intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData
    (intervalDomain_globalClassical_withInitialSlice hglobal)
    hT
    (intervalDomain_globalClassicalRegularityData_of_trace_paperPositive_anchored
      hT htrace hdatum hglobal hgrad)

/-- Named-frontier version of
`intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored`.
The `hgrad` input is the genuine raw Moser-gradient time-integrability
frontier. -/
theorem
    intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hgrad : IntervalDomainRawMoserGradientTimeIntegrability u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
    hglobal hT htrace hdatum hgrad

/-- Closed-time raw Moser-gradient energy continuity is a sufficient, stronger
source of the named raw-gradient frontier.  This is still an analytic input, not
a consequence of the current classical-solution API. -/
theorem
    intervalDomain_integratedMoserRegularityAnchored_of_gradientContinuous
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.Icc (0 : ℝ) T)) :
    IntegratedMoserFirstCrossingRegularity intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
    hglobal hT htrace hdatum
    (intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous hT.le hgrad)

/-! ### Positive-time transfer from the anchored representative -/

/-- Raw bootstrap data transfers to the anchored representative because
`AbstractLpBootstrapHypothesis` only depends on `u` through a positive-time
`LpPowerBoundedBefore` field. -/
theorem intervalDomain_abstractLpBootstrapHypothesis_anchored_of_raw
    {N T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0) :
    AbstractLpBootstrapHypothesis intervalDomain
      (intervalDomainWithInitialSlice u₀ u) N T rho p0 := by
  refine AbstractLpBootstrapHypothesis_congr_pos ?_ hboot
  intro t ht0 _htT x
  exact (intervalDomainWithInitialSlice_eq_raw_of_pos_apply
    (u₀ := u₀) (u := u) ht0 x).symm

/-- An anchored first-crossing step is a raw first-crossing step: the step only
maps positive-time `LpPowerBoundedBefore` predicates. -/
theorem intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
    {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hstep :
      IntegratedMoserFirstCrossingStep intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  refine IntegratedMoserFirstCrossingStep_congr_pos ?_ hstep
  intro t ht0 _htT x
  exact intervalDomainWithInitialSlice_eq_raw_of_pos_apply
    (u₀ := u₀) (u := u) ht0 x

/-- Produce a raw first-crossing step by running the direct threshold-plan route
on the re-anchored representative, then transferring the positive-time step
back to the raw trajectory.

All closed-time Moser inputs in this theorem are stated for
`intervalDomainWithInitialSlice u₀ u`; only the final first-crossing step is
exported back to raw `u`.  The lower-average / upper-data-gap frontiers are not
needed here because the threshold-plan producer consumes regularity, energy
nonnegativity, dissipation, and relative interpolation directly. -/
theorem
    intervalDomain_firstCrossingStep_raw_of_globalClassicalTraceAnchored_upperDataGapFrontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hgrad : IntervalDomainRawMoserGradientTimeIntegrability u T p0)
    (hdiss :
      IntegratedMoserDissipationDropBefore intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0)
    (hrel :
      RelativeMoserInterpolationBefore intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  let uA : ℝ → intervalDomain.Point → ℝ :=
    intervalDomainWithInitialSlice u₀ u
  have hglobalA :
      IsPaper2GlobalClassicalSolution intervalDomain params uA v := by
    simpa [uA] using
      (intervalDomain_globalClassical_withInitialSlice
        (u₀ := u₀) (u := u) (v := v) hglobal)
  have hsolA : IsPaper2ClassicalSolution intervalDomain params T uA v :=
    hglobalA.classical hT
  have hregA :
      IntegratedMoserFirstCrossingRegularity intervalDomain uA T p0 := by
    simpa [uA] using
      intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
        hglobal hT htrace hdatum hgrad
  have hnonnegA :
      IntegratedMoserEnergyNonnegativity intervalDomain uA T p0 :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical
      (p0 := p0) hsolA
  have hstepA : IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0 :=
    intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
      hregA hnonnegA (by simpa [uA] using hdiss)
      (by simpa [uA] using hrel) hrho hp0_nonneg
  exact intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
    (u₀ := u₀) (u := u) (T := T) (rho := rho) (p0 := p0)
    (by simpa [uA] using hstepA)

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

/-! ### Direct threshold-plan first-crossing producer -/

/-- Produce the integrated first-crossing step directly from regularity,
integrated dissipation, and relative Moser interpolation via the threshold-plan
route. -/
theorem intervalDomain_firstCrossingStep_of_classical_integratedData
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
    (intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData hreg)
    (intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol)
    hdiss hrel hrho hp0_nonneg

/-- Produce the integrated first-crossing step directly from reduced regularity,
integrated dissipation, and relative Moser interpolation via the threshold-plan
route. -/
theorem intervalDomain_firstCrossingStep_of_lite_classical_integratedData
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
    (intervalDomain_integratedMoserFirstCrossingRegularity_of_lite_classical
      hreg hsol)
    (intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol)
    hdiss hrel hrho hp0_nonneg

/-- Classical-regularity-data version of
`intervalDomain_firstCrossingStep_of_lite_classical_integratedData`. -/
theorem intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  intervalDomain_firstCrossingStep_of_lite_classical_integratedData
    (intervalDomain_regularityLite_of_classicalRegularityData hsol hdata)
    hsol hdiss hrel hrho hp0_nonneg

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

section AxiomAudit

#print axioms intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
#print axioms intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
#print axioms intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
#print axioms intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuityData
#print axioms intervalDomain_classicalRegularityData_of_gradientContinuityData
#print axioms intervalDomain_classicalRegularityData_of_continuityRegularityData
#print axioms intervalDomain_globalClassicalRegularityData_of_trace_compat
#print axioms intervalDomain_globalClassicalRegularityData_of_trace_paperPositive_anchored
#print axioms intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
#print axioms intervalDomain_regularityLite_of_globalClassicalRegularityData
#print axioms
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData
#print axioms intervalDomain_regularityLite_of_globalClassicalTraceCompat
#print axioms
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceCompat
#print axioms intervalDomain_regularityLite_of_globalClassicalTraceAnchored
#print axioms
  intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
#print axioms
  intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
#print axioms
  intervalDomain_integratedMoserRegularityAnchored_of_gradientContinuous
#print axioms intervalDomain_abstractLpBootstrapHypothesis_anchored_of_raw
#print axioms intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
#print axioms
  intervalDomain_firstCrossingStep_raw_of_globalClassicalTraceAnchored_upperDataGapFrontiers
#print axioms intervalDomain_regularityLite_of_classicalRegularityData
#print axioms intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
#print axioms intervalDomain_lowerAverageEpsilonData_of_classical
#print axioms intervalDomain_lowerAverageEpsilonData_of_lite_classical
#print axioms intervalDomain_lowerAverageUpperDataGapData_of_classical
#print axioms intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
#print axioms intervalDomain_firstCrossingStep_of_classical_integratedData
#print axioms intervalDomain_firstCrossingStep_of_lite_classical_integratedData
#print axioms intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData

end AxiomAudit

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
