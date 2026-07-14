import ShenWork.Paper3.IntervalDomainMLinearFluxTransfer
import ShenWork.Paper3.IntervalDomainMinimalSignalFloor
import ShenWork.Paper3.IntervalDomainPersistenceFaithfulUV
import ShenWork.Paper3.IntervalDomainPersistenceVCobounds
import ShenWork.Paper3.IntervalDomainStabilityChain

/-!
# Faithful minimal persistence on the interval

The stored value `u 0` is not tied to the positive-time orbit by the classical
solution API.  The minimal-model persistence theorem is therefore stated with
the physical mass on every positive time slice, which is the invariant used by
the analytic upper-bound and resolver-floor proofs.
-/

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Corrected form of Paper 3, Theorem 2.1(4): the prescribed mass belongs to
the positive-time orbit rather than to the freely stored zero-time slice. -/
def Theorem_2_1_part4_physicalMass
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ →
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ uStar > 0, ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasEquilibriumMassOnPositiveTimes D u uStar →
            minimalVLowerFormula C.gaussianLowerConst p.γ uStar
                (C.eventualMinimalUBound uStar) ≤
              liminfInfValue D v

/-- Concrete constants whose two Part-4 fields are exactly the proved
orbit-independent upper bound and the quantitative resolver mass gap. -/
def intervalDomainMPhysicalPart4Constants
    (p : CM2Params) : Paper3Constants intervalDomainM p where
  chiCritical := fun uStar =>
    paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
      (p.ν / p.μ * uStar ^ p.γ)
  chiStrong1 := fun uStar =>
    chiStrong1Formula p uStar (p.ν / p.μ * uStar ^ p.γ)
  chiStrong2 := fun uStar => chiStrong2Formula p uStar
  chiStrong3 := fun uStar =>
    chiStrong3Formula p 0 uStar (p.ν / p.μ * uStar ^ p.γ)
  chiStrong4 := fun uStar => chiStrong4Formula p 0 uStar
  chiMinimal1 := fun uStar =>
    chiMinimal1Formula p 1 uStar
      (intervalDomainMinimalEventualBoxConstants p uStar).1
      (intervalDomainMinimalEventualBoxConstants p uStar).2
  chiMinimal2 := fun uStar =>
    chiMinimal2Formula p
      (intervalDomainMinimalEventualBoxConstants p uStar).1
      (intervalDomainMinimalEventualBoxConstants p uStar).2
  eventualMinimalUBound := fun uStar =>
    (intervalDomainMinimalEventualBoxConstants p uStar).1
  gaussianLowerConst := unitIntervalResolverMassGapConstant p * p.ν
  gaussianLowerConst_pos :=
    mul_pos (unitIntervalResolverMassGapConstant_pos p) p.hν

/-- Paper 3, Theorem 2.1(4), on the paper-faithful interval model and with the
physical positive-time mass interface. -/
theorem Theorem_2_1_part4_intervalDomainM_physicalMass_proven
    (p : CM2Params) :
    Theorem_2_1_part4_physicalMass intervalDomainM p
      (intervalDomainMPhysicalPart4Constants p) := by
  intro ha hb hm hβ hχ₀ hχ uStar huStar u v hsolM hmassM
  have hχβpos : 0 < chiBeta p := chiBeta_pos_of_one_le_beta p hβ
  have hχβ : p.χ₀ < chiBeta p := by
    have hhalf : p.χ₀ < chiBeta p / 2 :=
      lt_of_lt_of_le hχ (min_le_left _ _)
    linarith
  have hsol : PositiveGlobalBoundedSolution intervalDomain p u v :=
    positiveGlobalBoundedSolution_intervalDomain_of_M_m_one hm hsolM
  have hmass :
      HasEquilibriumMassOnPositiveTimes intervalDomain u uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomain, intervalDomainM]
      using hmassM
  let uBar : ℝ := (intervalDomainMinimalEventualBoxConstants p uStar).1
  have hbox := intervalDomainMinimalEventualBoxConstants_spec
    p hm ha hb hβ hχ₀ hχβ huStar
  have huBar : 0 < uBar := by
    simpa [uBar] using hbox.1
  have hupper :
      ∀ᶠ t : ℝ in atTop, intervalDomain.supNorm (u t) ≤ uBar := by
    simpa [uBar] using (hbox.2.2 u v hsol hmass).1
  have hpoint :
      ∀ᶠ t : ℝ in atTop,
        ∀ x : intervalDomain.Point,
          intervalMinimalSignalLower p uStar uBar ≤ v t x := by
    filter_upwards [hupper, eventually_gt_atTop (0 : ℝ)] with t hupperT ht
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    have hclass : IsPaper2ClassicalSolution intervalDomain p T u v :=
      hsol.1.classical hT
    have htmem : t ∈ Ioo (0 : ℝ) T := ⟨ht, htT⟩
    have hpointUpper : ∀ z : intervalDomainPoint, u t z ≤ uBar := by
      intro z
      have hz :=
        ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer.intervalDomainLift_le_supNorm_of_classical
          hclass htmem z.property
      have hz' : u t z ≤ intervalDomain.supNorm (u t) := by
        simpa [intervalDomainLift, z.property] using hz
      exact hz'.trans hupperT
    have hmassT : intervalDomain.integral (u t) = uStar := by
      simpa [HasEquilibriumMassOnPositiveTimes, intervalDomain] using hmass t ht
    have hsignal := intervalDomain_solution_signal_lower_of_mass_upper
      p hclass htmem huBar hmassT hpointUpper
    intro x
    have hx := hsignal x.1 x.property
    simpa [intervalDomainLift, x.property] using hx
  have hdelta : 0 < intervalMinimalSignalLower p uStar uBar :=
    intervalMinimalSignalLower_pos p huStar huBar
  have heventual :
      EventuallyLowerBound intervalDomain v
        (intervalMinimalSignalLower p uStar uBar) :=
    intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hdelta hpoint
  have hliminf :
      intervalMinimalSignalLower p uStar uBar ≤
        liminfInfValue intervalDomain v := by
    simpa [liminfInfValue] using
      liminf_ge_of_eventuallyLowerBound
        (intervalDomain_infValue_v_isCoboundedUnder_of_positiveGlobalBoundedSolution
          hsol)
        heventual
  have hliminfM :
      intervalMinimalSignalLower p uStar uBar ≤
        liminfInfValue intervalDomainM v := by
    simpa [liminfInfValue, intervalDomain, intervalDomainM] using hliminf
  simpa [intervalDomainMPhysicalPart4Constants, uBar,
    intervalMinimalSignalLower, intervalMinimalPowerMassLower,
    minimalVLowerFormula, mul_assoc] using hliminfM

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.Theorem_2_1_part4_physicalMass
#print axioms ShenWork.Paper3.intervalDomainMPhysicalPart4Constants
#print axioms
  ShenWork.Paper3.Theorem_2_1_part4_intervalDomainM_physicalMass_proven
