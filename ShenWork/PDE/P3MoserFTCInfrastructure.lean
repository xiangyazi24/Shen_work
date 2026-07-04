import ShenWork.PDE.P3MoserClosedEnergyProducer
import ShenWork.PDE.P3MoserEnergyContinuity

/-!
# FTC infrastructure for the closed L² energy trace

This file records the executable connection found by the FTC survey:
`IntegratedMoserEnergyWindowFTC` already contains the closed-window fundamental
theorem of calculus needed for the L² closed-energy trace, after specializing
to exponent `2` and rewriting
`intervalDomainLpAbsEnergy 2 = integratedMoserEnergy intervalDomain _ 2`.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

/-- Convert interval-integrability on a non-reversed interval into the
closed-set `IntegrableOn` shape used by `ClosedEnergyIdentityTraceData`. -/
theorem integrableOn_uIcc_of_intervalIntegrable_of_le
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    IntegrableOn f (Set.uIcc a b) volume := by
  rw [Set.uIcc_of_le hab]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf

/-- The closed L² energy is the exponent-`2` integrated Moser energy. -/
theorem intervalDomainLpAbsEnergy_two_eq_integratedMoserEnergy
    (u : ℝ → intervalDomain.Point → ℝ) :
    (fun t : ℝ => intervalDomainLpAbsEnergy 2 u t) =
      fun t : ℝ => integratedMoserEnergy intervalDomain u 2 t := by
  funext t
  exact
    (intervalDomainLpAbsEnergy_two_eq_powerEnergy u t).trans
      ((congrFun (intervalDomain_integratedMoserEnergy_eq_powerEnergy 2 u) t).symm)

/-- Specialize an integrated-Moser window FTC at exponent `2` to the remaining
closed-energy trace data.

This discharges `g`, `g_integrable`, and `energy_eq` from the existing window
FTC package.  The zero-time right derivative remains the separate endpoint
input identified by the survey. -/
def closedEnergyIdentityTraceRemainingData_of_integratedMoserEnergyWindowFTC
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T 2)
    (hzero : IntervalDomainL2SeedZeroRightDerivative u) :
    ClosedEnergyIdentityTraceRemainingData T u where
  g := fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u 2 τ) s
  g_integrable := by
    have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hTT : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    exact integrableOn_uIcc_of_intervalIntegrable_of_le hT
      (hftc.deriv_intervalIntegrable 2 le_rfl 0 h0T T hTT)
  energy_eq := by
    intro t ht
    have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hEt :=
      congrFun (intervalDomainLpAbsEnergy_two_eq_integratedMoserEnergy u) t
    have hE0 :=
      congrFun (intervalDomainLpAbsEnergy_two_eq_integratedMoserEnergy u) 0
    have hFTC :=
      hftc.window_ftc 2 le_rfl 0 h0T t ht
    calc
      intervalDomainLpAbsEnergy 2 u t =
          integratedMoserEnergy intervalDomain u 2 t := hEt
      _ = integratedMoserEnergy intervalDomain u 2 0 +
            ∫ s in (0 : ℝ)..t,
              deriv (fun τ => integratedMoserEnergy intervalDomain u 2 τ) s := by
        linarith
      _ = intervalDomainLpAbsEnergy 2 u 0 +
            ∫ s in (0 : ℝ)..t,
              deriv (fun τ => integratedMoserEnergy intervalDomain u 2 τ) s := by
        rw [hE0]
  zeroRightDerivative := hzero

/-- Global-classical PDE initial-window data gives the closed-energy remaining
data, except for the irreducible zero-time right derivative. -/
def closedEnergyIdentityTraceRemainingData_of_globalPDEInitialData
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params u v T 2)
    (hzero : IntervalDomainL2SeedZeroRightDerivative u) :
    ClosedEnergyIdentityTraceRemainingData T u :=
  closedEnergyIdentityTraceRemainingData_of_integratedMoserEnergyWindowFTC
    hT.le
    (intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
      (params := params) (T := T) (p0 := (2 : ℝ)) (u := u) (v := v)
      hglobal hT hdata)
    hzero

/-- Full closed-energy trace for the re-anchored representative from global
classical data plus the remaining initial-window PDE FTC data and the zero-time
right derivative. -/
def closedEnergyIdentityTraceData_withInitialSlice_of_globalPDEInitialData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params (intervalDomainWithInitialSlice u₀ u) v T 2)
    (hzero :
      IntervalDomainL2SeedZeroRightDerivative
        (intervalDomainWithInitialSlice u₀ u)) :
    ClosedEnergyIdentityTraceData T u₀
      (intervalDomainWithInitialSlice u₀ u) :=
  closedEnergyIdentityTraceData_withInitialSlice_of_classical
    (params := params) (T := T) (u₀ := u₀) (u := u) (v := v)
    (hglobal.classical hT) htrace hdatum
    (closedEnergyIdentityTraceRemainingData_of_globalPDEInitialData
      (params := params) (T := T)
      (u := intervalDomainWithInitialSlice u₀ u) (v := v)
      (intervalDomain_globalClassical_withInitialSlice
        (params := params) (u₀ := u₀) (u := u) (v := v) hglobal)
      hT hdata hzero)

#print axioms integrableOn_uIcc_of_intervalIntegrable_of_le
#print axioms intervalDomainLpAbsEnergy_two_eq_integratedMoserEnergy
#print axioms closedEnergyIdentityTraceRemainingData_of_integratedMoserEnergyWindowFTC
#print axioms closedEnergyIdentityTraceRemainingData_of_globalPDEInitialData
#print axioms closedEnergyIdentityTraceData_withInitialSlice_of_globalPDEInitialData

end ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

end
