/- Restarted scalar bootstrap for the positive-time strong Paper3 orbit. -/
import ShenWork.Paper3.IntervalDomainStrongTimeContinuity
import ShenWork.Paper3.WeightedDuhamelStability
import ShenWork.Paper3.IntervalDomainUniformSpectralGap

namespace ShenWork.Paper3

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- A global classical orbit has continuous `X_2^sigma` size at every
strictly positive time. -/
theorem intervalDomainX2SigmaDistance_continuousOn_global_positive
    {p : CM2Params} {sigma uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hsigma1 : sigma < 1) :
    ContinuousOn
      (fun t => intervalDomainX2SigmaDistance sigma uStar (u t))
      (Set.Ioi (0 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := by simpa only [Set.mem_Ioi] using ht
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hlocal := intervalDomainX2SigmaDistance_continuousOn_positive
    (uStar := uStar) (hglobal T hT) hsigma1
  exact (hlocal.continuousAt (isOpen_Ioo.mem_nhds htmem)).continuousWithinAt

/-- Translating a global positive-time orbit to a positive restart produces a
continuous scalar trajectory on the closed half-line. -/
theorem intervalDomainX2SigmaDistance_shift_continuousOn_Ici
    {p : CM2Params} {sigma uStar a : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hsigma1 : sigma < 1) (ha : 0 < a) :
    ContinuousOn
      (fun tau => intervalDomainX2SigmaDistance sigma uStar (u (a + tau)))
      (Set.Ici (0 : ℝ)) := by
  have hpositive := intervalDomainX2SigmaDistance_continuousOn_global_positive
    (uStar := uStar) hglobal hsigma1
  exact hpositive.comp
    (continuousOn_const.add continuousOn_id)
    (fun tau htau => by
      change 0 < a + tau
      have htau0 : 0 ≤ tau := by simpa only [Set.mem_Ici] using htau
      linarith)

/-- A continuous scalar orbit can be multiplied into the integrable
`(t-s)^(-theta)` Duhamel singularity.  No a priori global bound is needed:
continuity on each compact time interval supplies the bounded multiplier. -/
theorem singularQuadraticSource_intervalIntegrable_of_continuous
    {size : ℝ → ℝ} {theta omega t : ℝ}
    (htheta1 : theta < 1) (ht : 0 ≤ t)
    (hcont : ContinuousOn size (Set.Ici (0 : ℝ))) :
    IntervalIntegrable
      (fun s : ℝ =>
        (t - s) ^ (-theta) * Real.exp (-omega * (t - s)) * size s ^ 2)
      volume 0 t := by
  have hpow : IntervalIntegrable (fun r : ℝ => r ^ (-theta)) volume 0 t :=
    rpow_neg_intervalIntegrable htheta1
  have hpowComp : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-theta))
      volume 0 t := by
    simpa using (hpow.comp_sub_left t).symm
  have hexp : ContinuousOn (fun s : ℝ => Real.exp (-omega * (t - s)))
      (Set.uIcc (0 : ℝ) t) := by
    fun_prop
  have hkernel := hpowComp.mul_continuousOn hexp
  have hsize : ContinuousOn (fun s : ℝ => size s ^ 2)
      (Set.uIcc (0 : ℝ) t) := by
    rw [Set.uIcc_of_le ht]
    exact (hcont.mono (fun s hs => hs.1)).pow 2
  simpa [mul_assoc] using hkernel.mul_continuousOn hsize

/-- Restarted strong decay once a positive classical slice is sufficiently
small.  The positivity radius is explicit in the hypotheses: it is precisely
the ball on which the route-(a) Nemytskii and polarized Lipschitz estimates are
valid. -/
theorem intervalDomainX2SigmaDistance_restart_exponential_bound_of_small
    {p : CM2Params} {sigma uStar vStar gap a radius : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hm : p.m = 1) (ha : 0 < a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
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
        have hduh := paper3StrongDuhamel_restart_actual_local_norm_le
          hsol hm ha haTerminal hterminalT heq hgap
          hsigmaStrong hsigma1 hmem hsmall
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

/-- A uniform radius on which both physical positivity and the quadratic
weighted convolution close.  The extra `+1` in the denominator makes the
smallness proof denominator-safe without case splits. -/
def intervalDomainStrongBootstrapRadius
    (p : CM2Params) (sigma uStar vStar gap : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let A :=
    unitIntervalLinearizedStrongSmoothingConstant
        p uStar vStar gap sigma *
      intervalDomainX2SigmaUniformNemytskiiConstant
        p sigma uStar vStar heq *
      reservedSingularKernelMass sigma (gap / 2 - gap / 4)
  min (intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar)
    (1 / (8 * A + 1))

theorem intervalDomainStrongBootstrapRadius_pos
    (p : CM2Params) {sigma uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : 0 < gap) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    0 < intervalDomainStrongBootstrapRadius
      p sigma uStar vStar gap heq := by
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  let K := intervalDomainX2SigmaUniformNemytskiiConstant
    p sigma uStar vStar heq
  let M := reservedSingularKernelMass sigma (gap / 2 - gap / 4)
  let A := C * K * M
  have hC : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap hsigma
  have hK : 0 < K := by
    simpa [K] using intervalDomainX2SigmaUniformNemytskiiConstant_pos
      p sigma uStar vStar heq
  have hd : 0 < gap / 2 - gap / 4 := by linarith
  have hM : 0 < M := by
    dsimp [M, reservedSingularKernelMass]
    exact mul_pos (Real.rpow_pos_of_pos hd _)
      (Real.Gamma_pos_of_pos (by linarith))
  have hA : 0 < A := mul_pos (mul_pos hC hK) hM
  unfold intervalDomainStrongBootstrapRadius
  dsimp only
  exact lt_min
    (intervalDomainX2SigmaLocalNemytskiiRadius_pos heq.u_pos)
    (one_div_pos.mpr (by nlinarith [hA]))

theorem intervalDomainStrongBootstrapRadius_le_positivity
    (p : CM2Params) (sigma uStar vStar gap : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    intervalDomainStrongBootstrapRadius p sigma uStar vStar gap heq ≤
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar := by
  unfold intervalDomainStrongBootstrapRadius
  exact min_le_left _ _

theorem intervalDomainStrongBootstrapRadius_quadratic_small
    (p : CM2Params) {sigma uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : 0 < gap) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    (unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma *
        intervalDomainX2SigmaUniformNemytskiiConstant
          p sigma uStar vStar heq) *
        intervalDomainStrongBootstrapRadius
            p sigma uStar vStar gap heq ^ 2 *
          reservedSingularKernelMass sigma (gap / 2 - gap / 4) ≤
      intervalDomainStrongBootstrapRadius p sigma uStar vStar gap heq / 4 := by
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  let K := intervalDomainX2SigmaUniformNemytskiiConstant
    p sigma uStar vStar heq
  let M := reservedSingularKernelMass sigma (gap / 2 - gap / 4)
  let A := C * K * M
  let r := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  have hC : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap hsigma
  have hK : 0 < K := by
    simpa [K] using intervalDomainX2SigmaUniformNemytskiiConstant_pos
      p sigma uStar vStar heq
  have hd : 0 < gap / 2 - gap / 4 := by linarith
  have hM : 0 < M := by
    dsimp [M, reservedSingularKernelMass]
    exact mul_pos (Real.rpow_pos_of_pos hd _)
      (Real.Gamma_pos_of_pos (by linarith))
  have hA : 0 < A := mul_pos (mul_pos hC hK) hM
  have hr : 0 < r := by
    simpa [r] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap hsigma hsigma1
  have hrDen : r ≤ 1 / (8 * A + 1) := by
    dsimp [r, intervalDomainStrongBootstrapRadius]
    exact min_le_right _ _
  have hden : 0 < 8 * A + 1 := by positivity
  have hmul : (8 * A + 1) * r ≤ 1 := by
    have hraw : r * (8 * A + 1) ≤ 1 :=
      (le_div_iff₀ hden).mp hrDen
    nlinarith
  have hAr : 8 * A * r ≤ 1 := by nlinarith [hr.le]
  have hquad := mul_le_mul_of_nonneg_right hAr hr.le
  change C * K * r ^ 2 * M ≤ r / 4
  dsimp [A] at hquad
  nlinarith

/-- Public restarted Stage-A estimate with the radius chosen internally. -/
theorem intervalDomainX2SigmaDistance_restart_exponential_bound
    {p : CM2Params} {sigma uStar vStar gap a : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hm : p.m = 1) (ha : 0 < a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hrestart : intervalDomainX2SigmaDistance sigma uStar (u a) ≤
      intervalDomainStrongBootstrapRadius
        p sigma uStar vStar gap heq / 2) :
    ∀ tau, 0 ≤ tau →
      intervalDomainX2SigmaDistance sigma uStar (u (a + tau)) ≤
        intervalDomainStrongBootstrapRadius
            p sigma uStar vStar gap heq *
          Real.exp (-(gap / 4) * tau) := by
  apply intervalDomainX2SigmaDistance_restart_exponential_bound_of_small
    hglobal hm ha heq hgap hsigmaStrong hsigma1
    (intervalDomainStrongBootstrapRadius_pos p heq hgap.1
      (by linarith) hsigma1)
    (intervalDomainStrongBootstrapRadius_le_positivity
      p sigma uStar vStar gap heq)
    (intervalDomainStrongBootstrapRadius_quadratic_small
      p heq hgap.1 (by linarith) hsigma1)
    hrestart

#print axioms intervalDomainX2SigmaDistance_continuousOn_global_positive
#print axioms intervalDomainX2SigmaDistance_shift_continuousOn_Ici
#print axioms singularQuadraticSource_intervalIntegrable_of_continuous
#print axioms intervalDomainX2SigmaDistance_restart_exponential_bound_of_small
#print axioms intervalDomainStrongBootstrapRadius_pos
#print axioms intervalDomainStrongBootstrapRadius_le_positivity
#print axioms intervalDomainStrongBootstrapRadius_quadratic_small
#print axioms intervalDomainX2SigmaDistance_restart_exponential_bound

end

end ShenWork.Paper3
