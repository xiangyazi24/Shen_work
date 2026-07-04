import ShenWork.PDE.P3MoserEnergyContinuity

/-!
# Initial-window combined PDE integrability producer

This file closes the Lean wiring from initial-window Moser-derivative
integrability back to the thinner combined PDE scalar used by
`IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData`.
-/

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Initial-window integrability of the Moser-energy derivative gives
initial-window integrability of the weighted Lp time term.

The equality is used only on `Ioc 0 b`, so the endpoint value at `0` is
irrelevant. -/
theorem
    intervalDomain_lpWeightedTimeTermInitialWindowIntegrability_of_moserDerivativeInitial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hinit :
      IntegratedMoserEnergyDerivativeInitialWindowIntegrability
        intervalDomain u T p0) :
    IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0 := by
  intro q hq b hb
  have hDeriv :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
        volume 0 b :=
    hinit q hq b hb
  refine hDeriv.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  have hpos : ∀ x : intervalDomain.Point, 0 < u s x := by
    intro x
    have hTpos : 0 < s + 1 := by
      linarith [hs.1]
    have hsol :
        IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
      hglobal.classical hTpos
    exact hsol.u_pos' (x := x) hs.1 (by linarith)
  have hDerivEq :
      deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s =
        intervalDomainPowerEnergyDerivIntegral q u s :=
    intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral_of_global_pos
      (params := params) (q := q) (s := s) (u := u) (v := v)
      hglobal hs.1
  have hPowerEq :
      intervalDomainPowerEnergyDerivIntegral q u s =
        q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s) :=
    intervalDomainPowerEnergyDerivIntegral_eq_scaled_weighted_of_pos
      q s u hpos
  exact hDerivEq.trans hPowerEq

/-- Initial-window Moser-derivative integrability produces the combined PDE
scalar initial-window residual. -/
theorem
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeInitial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hinit :
      IntegratedMoserEnergyDerivativeInitialWindowIntegrability
        intervalDomain u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0 :=
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_weightedTimeTerm_initial
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal
    (intervalDomain_lpWeightedTimeTermInitialWindowIntegrability_of_moserDerivativeInitial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hinit)

/-- Full closed-window Moser-derivative integrability gives the initial-window
combined PDE residual by restricting to windows of the form `[0,b]`. -/
theorem
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeWindow
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hderiv :
      IntegratedMoserEnergyDerivativeWindowIntegrability
        intervalDomain u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0 := by
  refine
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeInitial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal ?_
  intro q hq b hb
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_rfl, le_trans hb.1 hb.2⟩
  exact hderiv q hq 0 h0T b hb

/-- An already available Moser-energy window FTC package contains enough
derivative-window integrability to recover the initial-window combined PDE
residual. -/
theorem
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_windowFTC
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0 :=
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeWindow
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal hftc.deriv_intervalIntegrable

/-- Package the already-proved zero-endpoint continuity together with the
combined PDE initial-window integrability produced from Moser-derivative
initial-window integrability. -/
theorem
    intervalDomain_globalPDEInitialData_of_atZero_moserDerivativeInitial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hinit :
      IntegratedMoserEnergyDerivativeInitialWindowIntegrability
        intervalDomain u T p0) :
    IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
      params u v T p0 where
  atZero := hzero
  pdeCombinedInitial :=
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeInitial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hinit

/-- Re-anchored global-classical initial-window PDE data from initial trace,
positive datum, and Moser-derivative initial-window integrability for the
re-anchored representative. -/
set_option linter.style.longLine false
theorem
    intervalDomain_globalPDEInitialData_withInitialSlice_of_trace_moserDerivativeInitial
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hp0 : 1 ≤ p0)
    (hinit :
      IntegratedMoserEnergyDerivativeInitialWindowIntegrability
        intervalDomain (intervalDomainWithInitialSlice u₀ u) T p0) :
    IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
      params (intervalDomainWithInitialSlice u₀ u) v T p0 :=
  intervalDomain_globalPDEInitialData_of_atZero_moserDerivativeInitial
    (params := params) (T := T) (p0 := p0)
    (u := intervalDomainWithInitialSlice u₀ u) (v := v)
    (intervalDomain_globalClassical_withInitialSlice
      (u₀ := u₀) (u := u) (v := v) hglobal)
    (intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_classical_withInitialSlice
      (p := params) (T := T) (p0 := p0) (u₀ := u₀) (u := u) (v := v)
      hT (hglobal.classical hT) htrace hdatum hp0)
    hinit

set_option linter.style.longLine true

#print axioms
  intervalDomain_lpWeightedTimeTermInitialWindowIntegrability_of_moserDerivativeInitial
#print axioms
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeInitial
#print axioms
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_moserDerivativeWindow
#print axioms
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_windowFTC
#print axioms
  intervalDomain_globalPDEInitialData_of_atZero_moserDerivativeInitial
#print axioms
  intervalDomain_globalPDEInitialData_withInitialSlice_of_trace_moserDerivativeInitial

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
