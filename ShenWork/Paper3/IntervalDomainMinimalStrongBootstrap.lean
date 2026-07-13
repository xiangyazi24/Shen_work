/- Restarted scalar bootstrap on the mass-constrained minimal-model orbit. -/
import ShenWork.Paper3.IntervalDomainMinimalStrongDuhamel
import ShenWork.Paper3.IntervalDomainStrongBootstrap

namespace ShenWork.Paper3

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Restarted strong decay for the minimal model.  Physical mass removes the
neutral zero mode; all remaining modes are treated by the same weighted
quadratic bootstrap as in the positive-logistic branch. -/
theorem intervalDomainMassX2SigmaDistance_restart_exponential_bound_of_small
    {p : CM2Params} {sigma uStar vStar gap a radius : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0) (ha : 0 < a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hradius : 0 < radius)
    (hradiusPositivity :
      radius ≤ intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar)
    (hquadratic :
      (unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma *
        intervalDomainX2SigmaUniformNemytskiiConstant
          p sigma uStar vStar heq) * radius ^ 2 *
          reservedSingularKernelMass sigma (gap / 2 - gap / 4) ≤
        radius / 4)
    (hrestart :
      intervalDomainX2SigmaDistance sigma uStar (u a) ≤ radius / 2) :
    ∀ tau, 0 ≤ tau →
      intervalDomainX2SigmaDistance sigma uStar (u (a + tau)) ≤
        radius * Real.exp (-(gap / 4) * tau) := by
  let size : ℝ → ℝ := fun tau =>
    intervalDomainX2SigmaDistance sigma uStar (u (a + tau))
  let C : ℝ := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  let K : ℝ := intervalDomainX2SigmaUniformNemytskiiConstant
    p sigma uStar vStar heq
  let positivityRadius : ℝ :=
    intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar
  have hsigma0 : 0 < sigma := by linarith
  have hgap0 : 0 < gap := hgap.1
  have hC0 : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap0 hsigma0
  have hK0 : 0 < K := by
    simpa [K] using
      intervalDomainX2SigmaUniformNemytskiiConstant_pos
        p sigma uStar vStar heq
  have hposRadius0 : 0 < positivityRadius := by
    simpa [positivityRadius] using
      intervalDomainX2SigmaLocalNemytskiiRadius_pos heq.u_pos
  have hsizeCont : ContinuousOn size (Set.Ici (0 : ℝ)) := by
    simpa [size] using
      intervalDomainX2SigmaDistance_shift_continuousOn_Ici
        (uStar := uStar) hglobal hsigma1 ha
  let H : WeightedQuadraticDuhamelData size :=
    { theta := sigma
      smoothingRate := gap / 2
      delta := gap
      rate := gap / 4
      linearConst := 1
      nonlinearConst := C * K
      datum := size 0
      radius := radius
      positivityRadius := positivityRadius
      theta_pos := hsigma0
      theta_lt_one := hsigma1
      rate_pos := by linarith
      rate_lt_smoothingRate := by linarith
      rate_le_delta := by linarith
      linearConst_nonneg := by norm_num
      nonlinearConst_nonneg := mul_nonneg hC0.le hK0.le
      datum_nonneg := by
        dsimp [size]
        exact Real.sqrt_nonneg _
      radius_pos := hradius
      positivityRadius_pos := hposRadius0
      radius_le_positivityRadius := by
        simpa [positivityRadius] using hradiusPositivity
      size_nonneg := by
        intro tau _htau
        dsimp [size]
        exact Real.sqrt_nonneg _
      size_continuous := hsizeCont
      source_integrable := by
        intro tau htau
        exact singularQuadraticSource_intervalIntegrable_of_continuous
          hsigma1 htau hsizeCont
      size_zero_le := by simp
      duhamel_bound := by
        intro tau htau hlocal
        let T : ℝ := a + tau + 1
        have hT : 0 < T := by dsimp [T]; linarith
        have haTerminal : a ≤ a + tau := by linarith
        have hterminalT : a + tau < T := by dsimp [T]; linarith
        have hsol := hglobal T hT
        have hmem : ∀ s ∈ Set.Icc a (a + tau),
            IntervalDomainX2SigmaPerturbation sigma uStar (u s) := by
          intro s hs
          apply intervalDomainX2SigmaPerturbation_of_classical_positive
            hsol ⟨by linarith [ha, hs.1], by linarith [hs.2, hterminalT]⟩
            hsigma1.le
        have hsmall : ∀ s ∈ Set.Ioo a (a + tau),
            intervalDomainX2SigmaDistance sigma uStar (u s) ≤
              intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar := by
          intro s hs
          let q : ℝ := s - a
          have hq : q ∈ Set.Icc (0 : ℝ) tau := by
            dsimp [q]
            constructor <;> linarith [hs.1, hs.2]
          have hqBound := hlocal q hq
          simpa [size, q, positivityRadius] using hqBound
        have hduh := paper3MassStrongDuhamel_restart_actual_local_norm_le
          hsol hm ha0 hb0 ha haTerminal hterminalT heq hgap
          hsigmaStrong hsigma1 hmass hmem hsmall
        let physicalIntegrand : ℝ → ℝ := fun s =>
          C * ((a + tau) - s) ^ (-sigma) *
            Real.exp (-(gap / 2) * ((a + tau) - s)) *
              (K * intervalDomainX2SigmaDistance sigma uStar (u s) ^ 2)
        let shiftedIntegrand : ℝ → ℝ := fun q =>
          (tau - q) ^ (-sigma) *
            Real.exp (-(gap / 2) * (tau - q)) * size q ^ 2
        have hintegralShift :
            (∫ s in a..a + tau, physicalIntegrand s) =
              C * K * (∫ q in (0 : ℝ)..tau, shiftedIntegrand q) := by
          calc
            (∫ s in a..a + tau, physicalIntegrand s) =
                ∫ q in (0 : ℝ)..tau, physicalIntegrand (q + a) := by
              symm
              simpa only [zero_add, add_zero, add_comm] using
                intervalIntegral.integral_comp_add_right
                  (a := (0 : ℝ)) (b := tau) physicalIntegrand a
            _ = ∫ q in (0 : ℝ)..tau, (C * K) * shiftedIntegrand q := by
              refine intervalIntegral.integral_congr (fun q _hq => ?_)
              dsimp [physicalIntegrand, shiftedIntegrand, size]
              rw [show a + tau - (q + a) = tau - q by ring,
                show q + a = a + q by ring]
              ring
            _ = C * K * (∫ q in (0 : ℝ)..tau, shiftedIntegrand q) := by
              rw [intervalIntegral.integral_const_mul]
        change size tau ≤
          1 * Real.exp (-gap * tau) * size 0 +
            C * K * (∫ q in (0 : ℝ)..tau,
              (tau - q) ^ (-sigma) *
                Real.exp (-(gap / 2) * (tau - q)) * size q ^ 2)
        have hduh' : size tau ≤
            Real.exp (-gap * tau) * size 0 +
              ∫ s in a..a + tau, physicalIntegrand s := by
          simpa [size, C, K, physicalIntegrand] using hduh
        rw [hintegralShift] at hduh'
        simpa [shiftedIntegrand] using hduh'
      datum_small := by
        simpa [size] using hrestart
      quadratic_small := by
        simpa [C, K] using hquadratic }
  simpa [size] using H.exponential_bound

/-- Minimal-model restart decay on any smaller bootstrap radius. -/
theorem intervalDomainMassX2SigmaDistance_restart_exponential_bound_of_radius_le
    {p : CM2Params} {sigma uStar vStar gap a radius : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0) (ha : 0 < a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hradius : 0 < radius)
    (hradius_le : radius ≤
      intervalDomainStrongBootstrapRadius p sigma uStar vStar gap heq)
    (hrestart : intervalDomainX2SigmaDistance sigma uStar (u a) ≤ radius / 2) :
    ∀ tau, 0 ≤ tau →
      intervalDomainX2SigmaDistance sigma uStar (u (a + tau)) ≤
        radius * Real.exp (-(gap / 4) * tau) := by
  apply intervalDomainMassX2SigmaDistance_restart_exponential_bound_of_small
    hglobal hm ha0 hb0 ha heq hgap hsigmaStrong hsigma1 hmass hradius
  · exact hradius_le.trans
      (intervalDomainStrongBootstrapRadius_le_positivity
        p sigma uStar vStar gap heq)
  · exact intervalDomainStrongBootstrap_quadratic_small_of_radius_le
      p heq hgap.1 (by linarith) hsigma1 hradius.le hradius_le
  · exact hrestart

/-- Public restarted Stage-A estimate for the mass-constrained minimal model. -/
theorem intervalDomainMassX2SigmaDistance_restart_exponential_bound
    {p : CM2Params} {sigma uStar vStar gap a : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0) (ha : 0 < a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hrestart : intervalDomainX2SigmaDistance sigma uStar (u a) ≤
      intervalDomainStrongBootstrapRadius
        p sigma uStar vStar gap heq / 2) :
    ∀ tau, 0 ≤ tau →
      intervalDomainX2SigmaDistance sigma uStar (u (a + tau)) ≤
        intervalDomainStrongBootstrapRadius
            p sigma uStar vStar gap heq *
          Real.exp (-(gap / 4) * tau) := by
  apply intervalDomainMassX2SigmaDistance_restart_exponential_bound_of_small
    hglobal hm ha0 hb0 ha heq hgap hsigmaStrong hsigma1 hmass
    (intervalDomainStrongBootstrapRadius_pos p heq hgap.1
      (by linarith) hsigma1)
    (intervalDomainStrongBootstrapRadius_le_positivity
      p sigma uStar vStar gap heq)
    (intervalDomainStrongBootstrapRadius_quadratic_small
      p heq hgap.1 (by linarith) hsigma1)
    hrestart

#print axioms
  intervalDomainMassX2SigmaDistance_restart_exponential_bound_of_small
#print axioms
  intervalDomainMassX2SigmaDistance_restart_exponential_bound_of_radius_le
#print axioms intervalDomainMassX2SigmaDistance_restart_exponential_bound

end

end ShenWork.Paper3
