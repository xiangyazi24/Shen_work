import ShenWork.PDE.P3MoserRegularityProducer

/-!
# Gradient time-integrability frontier for integrated Moser data

This file records what the current infrastructure proves about the field

```
∀ p ≥ p0, IntegrableOn
  (fun t => ∫_Ω |∇(u(t, ·)^(p/2))|^2)
  (Set.uIcc 0 T) volume
```

The audit result is negative for a proof from `IsPaper2ClassicalSolution` alone.
For the interval domain, `intervalDomainClassicalRegularity` supplies interior
spatial `C^2`, closed-boundary spatial `C^2` at each positive time, time `C^1`,
and joint continuity of the solution/time-derivative fields. It does not supply
closed-time continuity or a closed-time bound for the spatial-gradient energy,
especially at `t = 0`. Existing integrated-Moser code therefore keeps this as a
frontier, or derives it from the stronger closed-time gradient-energy
continuity package.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

/-- The concrete interval-domain Moser gradient-energy profile. -/
def intervalDomainMoserGradientEnergy
    (u : ℝ → intervalDomain.Point → ℝ) (p : ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)

theorem intervalDomainMoserGradientEnergy_eq_integrated
    (u : ℝ → intervalDomain.Point → ℝ) (p t : ℝ) :
    intervalDomainMoserGradientEnergy u p t =
      integratedMoserGradientEnergy intervalDomain u p t := by
  rfl

/-- The target field, named locally for this audit file. -/
def IntervalDomainMoserGradientTimeIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    IntegrableOn (intervalDomainMoserGradientEnergy u p)
      (Set.uIcc (0 : ℝ) T) volume

/-- Compact strict-window continuity of the Moser gradient-energy profile.

This is the natural weaker version suggested by the mathematics: it avoids both
time endpoints. The current `IsPaper2ClassicalSolution` API still does not prove
this automatically, because it lacks joint continuity of the spatial derivative
of `u(t, ·)^(p/2)` in `(t, x)`. -/
def IntervalDomainMoserGradientStrictWindowContinuity
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
    ContinuousOn (intervalDomainMoserGradientEnergy u p) (Set.Icc a b)

/-- Strict-window integrability of the Moser gradient-energy profile. -/
def IntervalDomainMoserGradientStrictWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
    IntervalIntegrable (intervalDomainMoserGradientEnergy u p) volume a b

/-- Positive-start window integrability, allowing the right endpoint to be `T`. -/
def IntervalDomainMoserGradientPositiveStartWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b ≤ T →
    IntervalIntegrable (intervalDomainMoserGradientEnergy u p) volume a b

/-- Closed-time gradient-energy continuity implies the target
gradient-time-integrability field. This is the strongest currently available
honest producer. -/
theorem intervalDomain_moserGradientTimeIntegrable_of_gradientEnergyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn (intervalDomainMoserGradientEnergy u p)
          (Set.Icc (0 : ℝ) T)) :
    IntervalDomainMoserGradientTimeIntegrability u T p0 := by
  intro p hp
  simpa [IntervalDomainMoserGradientTimeIntegrability,
    intervalDomainMoserGradientEnergy]
    using
      intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
        (T := T) (p0 := p0) (u := u) hT (by
          intro q hq
          simpa [intervalDomainMoserGradientEnergy] using hgrad q hq) p hp

/-- Classical-solution-facing version of
`intervalDomain_moserGradientTimeIntegrable_of_gradientEnergyContinuous`.

The classical solution is used only for `0 ≤ T`; the gradient-energy continuity
is the missing analytic input. -/
theorem intervalDomain_moserGradientTimeIntegrable_of_classical_gradientEnergyContinuous
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn (intervalDomainMoserGradientEnergy u p)
          (Set.Icc (0 : ℝ) T)) :
    IntervalDomainMoserGradientTimeIntegrability u T p0 :=
  intervalDomain_moserGradientTimeIntegrable_of_gradientEnergyContinuous
    (IsPaper2ClassicalSolution.T_pos hsol).le hgrad

/-- Closed-gradient-continuity data fills the `gradientTimeIntegrable` field of
the existing classical regularity package, provided endpoint power-energy
continuity is supplied separately. -/
theorem intervalDomain_classicalRegularityData_of_classical_endpoint_gradientContinuous
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn (intervalDomainMoserGradientEnergy u p)
          (Set.Icc (0 : ℝ) T)) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy := hend
  gradientTimeIntegrable := by
    intro p hp
    simpa [intervalDomainMoserGradientEnergy]
      using
        intervalDomain_moserGradientTimeIntegrable_of_classical_gradientEnergyContinuous
          hsol hgrad p hp

/-- Version using the pre-existing gradient-continuity data structure. -/
theorem intervalDomain_classicalRegularityData_of_classical_gradientContinuityData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdata :
      IntervalDomainIntegratedMoserClassicalGradientContinuityData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 :=
  intervalDomain_classicalRegularityData_of_gradientContinuityData
    (IsPaper2ClassicalSolution.T_pos hsol).le hdata

/-- Global-classical-facing version: the right endpoint causes no extra problem
once closed-time gradient-energy continuity and the left-endpoint power-energy
continuity package are supplied. -/
theorem intervalDomain_globalClassicalRegularityData_of_atZero_gradientContinuous
    {T p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn (intervalDomainMoserGradientEnergy u p)
          (Set.Icc (0 : ℝ) T)) :
    IntervalDomainIntegratedMoserGlobalClassicalRegularityData u T p0 where
  atZero := hzero
  gradientTimeIntegrable := by
    intro p hp
    simpa [intervalDomainMoserGradientEnergy]
      using
        intervalDomain_moserGradientTimeIntegrable_of_gradientEnergyContinuous
          hT.le hgrad p hp

/-- Convert the previous global-classical-facing package into the local
classical regularity data expected by the first-crossing Moser route. -/
theorem intervalDomain_classicalRegularityData_of_global_atZero_gradientContinuous
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn (intervalDomainMoserGradientEnergy u p)
          (Set.Icc (0 : ℝ) T)) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 :=
  intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
    hglobal hT
    (intervalDomain_globalClassicalRegularityData_of_atZero_gradientContinuous
      hT hzero hgrad)

/-- Strict-window continuity gives strict-window integrability. -/
theorem intervalDomain_moserGradientStrictWindowIntegrable_of_continuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hcont : IntervalDomainMoserGradientStrictWindowContinuity u T p0) :
    IntervalDomainMoserGradientStrictWindowIntegrability u T p0 := by
  intro p hp a b ha hab hb
  exact ContinuousOn.intervalIntegrable_of_Icc hab
    (hcont p hp a b ha hab hb)

/-- If strict-window continuity is available on every longer horizon, then all
positive-start windows inside `[0,T]` are integrable. This mirrors the existing
positive-start derivative-window strategy. -/
theorem intervalDomain_moserGradientPositiveStartWindowIntegrable_of_global_strictContinuity
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hcont :
      ∀ S, 0 < S →
        IntervalDomainMoserGradientStrictWindowContinuity u S p0) :
    IntervalDomainMoserGradientPositiveStartWindowIntegrability u T p0 := by
  intro p hp a b ha hab hbT
  have hT_pos : 0 < T := lt_of_lt_of_le ha (le_trans hab hbT)
  have hT1_pos : 0 < T + 1 := by linarith
  have hb_lt : b < T + 1 := by linarith
  exact intervalDomain_moserGradientStrictWindowIntegrable_of_continuous
    (T := T + 1) (p0 := p0) (u := u)
    (hcont (T + 1) hT1_pos) p hp a b ha hab hb_lt

/-- A full raw gradient-integrability hypothesis restricts to every closed
sub-window of `Set.uIcc 0 T`. -/
theorem intervalDomain_moserGradient_intervalIntegrable_of_raw_uIcc_subset
    {T p0 p a b : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hraw : IntervalDomainRawMoserGradientTimeIntegrability u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable (intervalDomainMoserGradientEnergy u p) volume a b := by
  simpa [intervalDomainMoserGradientEnergy,
    IntervalDomainRawMoserGradientTimeIntegrability]
    using
      intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
        (T := T) (a := a) (b := b)
        (f := intervalDomainMoserGradientEnergy u p)
        hab
        (by
          simpa [intervalDomainMoserGradientEnergy,
            IntervalDomainRawMoserGradientTimeIntegrability] using hraw p hp)
        hsub

/-- The existing classical regularity data package exposes exactly the target
field. This theorem is mainly a named extraction for downstream files. -/
theorem intervalDomain_moserGradientTimeIntegrable_of_classicalRegularityData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0) :
    IntervalDomainMoserGradientTimeIntegrability u T p0 := by
  intro p hp
  simpa [IntervalDomainMoserGradientTimeIntegrability,
    intervalDomainMoserGradientEnergy]
    using hdata.gradientTimeIntegrable p hp

#print axioms intervalDomain_moserGradientTimeIntegrable_of_gradientEnergyContinuous
#print axioms intervalDomain_moserGradientTimeIntegrable_of_classical_gradientEnergyContinuous
#print axioms intervalDomain_classicalRegularityData_of_classical_endpoint_gradientContinuous
#print axioms intervalDomain_moserGradientStrictWindowIntegrable_of_continuous

end ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

end
