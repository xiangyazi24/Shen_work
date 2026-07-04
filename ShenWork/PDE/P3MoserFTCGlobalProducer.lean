import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserPDECombinedInitialProducer
import ShenWork.Paper3.IntervalDomainGlobalChain

/-!
# FTC producer from global re-anchoring inputs

`IntervalDomainGlobalClassicalRegularityInputs` supplies the re-anchored global
classical branch, initial trace data, positivity of the initial datum, the
lower exponent bound, and closed-time Moser-gradient continuity.  It does not
by itself contain the initial-window derivative integrability needed to build
the combined PDE initial-window residual for the FTC package, so that residual
is carried explicitly below.
-/

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper3

namespace ShenWork.Paper3

noncomputable section

/-- Produce the assembly filler's FTC supplier from the global re-anchoring
input surface, plus the remaining initial-window Moser-derivative integrability
residual. -/
theorem intervalDomain_assemblyFTC_of_globalInputs
    {p : CM2Params}
    (hinputs : IntervalDomainGlobalClassicalRegularityInputs p)
    (hderivInitial :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyDerivativeInitialWindowIntegrability
          intervalDomain u T p0) :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0 := by
  intro T rho p0 u v hsol hcross hboot
  rcases hinputs hsol hcross hboot with
    ⟨u₀, uRaw, rfl, hglobal, htrace, hdatum, hp0, _hgrad⟩
  have hT : 0 < T := IsPaper2ClassicalSolution.T_pos hsol
  have hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        p (intervalDomainWithInitialSlice u₀ uRaw) v T p0 :=
    intervalDomain_globalPDEInitialData_withInitialSlice_of_trace_moserDerivativeInitial
      (params := p) (T := T) (p0 := p0) (u₀ := u₀) (u := uRaw) (v := v)
      hglobal hT htrace hdatum hp0
      (hderivInitial hsol hcross hboot)
  exact
    intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
      (params := p) (T := T) (p0 := p0)
      (u := intervalDomainWithInitialSlice u₀ uRaw) (v := v)
      (intervalDomain_globalClassical_withInitialSlice
        (params := p) (u₀ := u₀) (u := uRaw) (v := v) hglobal)
      hT hdata

#print axioms intervalDomain_assemblyFTC_of_globalInputs

end

end ShenWork.Paper3
