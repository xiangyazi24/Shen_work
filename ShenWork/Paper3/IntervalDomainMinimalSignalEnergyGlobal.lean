import ShenWork.Paper3.IntervalDomainMinimalSignalEnergy
import ShenWork.Paper3.IntervalDomainMinimalSignalFloor
import ShenWork.Paper3.IntervalDomainMinimalThresholdOrdering
import ShenWork.Paper3.IntervalDomainMinimalEventualConvergenceUpgrade

/-! # Second minimal-model formula branch on the unit interval -/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- The second minimal formula branch, evaluated at the canonical constants
produced by the interval estimates, supplies one basin-entry slice and then
the mass-constrained Stage B exponential bound. -/
theorem intervalDomain_minimal2_eventualC1
    (p : CM2Params) (hN : p.N = 1)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hgamma : p.γ = 1) (hbeta : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p
      (intervalDomainMinimalEventualBoxConstants p uStar).1
      (intervalDomainMinimalEventualBoxConstants p uStar).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith intervalDomain
        intervalDomainSectorialStabilityNorms u v
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 C rate t₀ := by
  let eq := minimalEquilibrium p uStar
  let constants := intervalDomainMinimalEventualBoxConstants p uStar
  let uBar := constants.1
  let vLower := constants.2
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal
      p ha0 hb0 uStar huStar
  have hcond : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower :=
    Or.inr ⟨hgamma, hchi,
      by simpa [uBar, vLower, constants] using hthreshold⟩
  have hchiBeta : p.χ₀ < chiBeta p :=
    hcond.chi_lt_chiBeta hbeta
  have hbox := intervalDomainMinimalEventualBoxConstants_spec
    p hm ha0 hb0 hbeta hchi hchiBeta huStar
  change IntervalDomainMinimalEventualBox p uStar uBar vLower at hbox
  rcases hbox with ⟨huBar, hvLower, hboxes⟩
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval
      p hN hm hbeta huStar
  obtain ⟨gap, _hgapPos, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  obtain ⟨hupper, hfloor⟩ := hboxes u v huv hmass
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by
    norm_num [sigma]
  have hsigma1 : sigma < 1 := by
    norm_num [sigma]
  let witness := intervalDomainMassSupToStrongBasinEntry_proved
    p hsigmaStrong hsigma1 hm ha0 hb0 heq hgap
  let delta : ℝ := Classical.choose witness
  have hdelta : 0 < delta := (Classical.choose_spec witness).1
  obtain ⟨tau, htauOne, hclose⟩ :=
    intervalDomain_minimal2_exists_late_supClose
      p hm ha0 hb0 hgamma hbeta heq huBar hvLower.le hchi
        (by simpa [uBar, vLower, constants] using hthreshold)
          huv hmass hupper hfloor (T := (1 : ℝ)) hdelta
  have htau : 0 < tau := lt_of_lt_of_le zero_lt_one htauOne
  simpa [eq] using
    (intervalDomain_minimal_eventualC1_of_supCloseSlice_of_massGap
      p hm ha0 hb0 heq hgap huv hmass htau
        (by simpa [sigma, witness, delta] using hclose))

/-- Unconditional second formula branch of faithful eventual Theorem 2.5 on
the concrete one-dimensional `m = 1`, `γ = 1` minimal equation. -/
theorem
    intervalDomain_eventuallyGloballyExponentiallyStableMinimal_minimal2
    (p : CM2Params) (hN : p.N = 1)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hgamma : p.γ = 1) (hbeta : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p
      (intervalDomainMinimalEventualBoxConstants p uStar).1
      (intervalDomainMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomain p
      intervalDomainSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
      HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith intervalDomain
          intervalDomainSectorialStabilityNorms u v
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 C rate t₀ := by
    intro u v huv hmass
    exact intervalDomain_minimal2_eventualC1
      p hN hm ha0 hb0 hgamma hbeta huStar hchi hthreshold huv hmass
  refine ⟨?_, hproduce⟩
  intro u v huv hmass
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ :=
    hproduce u v huv hmass
  exact intervalDomain_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

#print axioms intervalDomain_minimal2_eventualC1
#print axioms
  intervalDomain_eventuallyGloballyExponentiallyStableMinimal_minimal2

end

end ShenWork.Paper3
