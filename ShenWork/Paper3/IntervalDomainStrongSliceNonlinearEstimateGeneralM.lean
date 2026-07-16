/- Strong-ball production of the faithful general-`m` Route-A estimate. -/
import ShenWork.Paper3.IntervalDomainRouteANonlinearSnapshotGeneralM
import ShenWork.Paper3.IntervalDomainSignalRegularityProducerGeneralM
import ShenWork.Paper3.IntervalDomainStrongEmbedding
import ShenWork.Paper3.IntervalDomainStrongRealizationProducer
import ShenWork.Paper3.IntervalDomainUniformNemytskiiConstants
import ShenWork.Paper2.IntervalDomainMMass
import ShenWork.Paper2.IntervalDomainMPhysicalRestart

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

/-- The faithful general-`m` local radius: the old positivity/trace radius is
retained, and the second factor enforces `P * M ≤ 1` for the power-scaled
Route-A strong radius. -/
def intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM
    (p : CM2Params) (sigma uStar : ℝ) : ℝ :=
  min (intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar)
    (1 / (paper3RouteAPowerFactor p uStar *
      intervalDomainX2SigmaC1Envelope sigma))

theorem intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM_pos
    (p : CM2Params) (sigma : ℝ) {uStar : ℝ} (huStar : 0 < uStar) :
    0 < intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar := by
  unfold intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM
  apply lt_min
  · exact intervalDomainX2SigmaLocalNemytskiiRadius_pos huStar
  · apply one_div_pos.mpr
    exact mul_pos
      (lt_of_lt_of_le zero_lt_one
        (paper3RouteAPowerFactor_one_le p uStar))
      (intervalDomainX2SigmaC1Envelope_pos sigma)

/-- Strong fractional smallness produces the full faithful general-`m`
Route-A package with one fixed signal and logistic constant. -/
theorem exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform_generalM
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar) :
    ∃ H : FullNonlinearRemainderRouteAData
        (paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t),
      H.flux.bounds.M =
          paper3RouteAPowerFactor p uStar *
            (intervalDomainX2SigmaC1Envelope sigma *
              intervalDomainX2SigmaDistance sigma uStar (u t)) ∧
        H.flux.bounds.L =
          intervalDomainX2SigmaC1Envelope sigma *
            intervalDomainX2SigmaDistance sigma uStar (u t) ∧
        H.toL2Data.quadraticConstant =
          paper3RouteAFullQuadraticConstantGeneralM p uStar vStar
            (paper3UniformSignalStrongConstant p uStar heq.u_pos)
            (paper3UniformLogisticTaylorConstant p heq) := by
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  let Cenv := intervalDomainX2SigmaC1Envelope sigma
  let P := paper3RouteAPowerFactor p uStar
  let M := Cenv * d
  have hsmallOld : d ≤ intervalDomainX2SigmaLocalNemytskiiRadius
      sigma uStar := by
    exact hsmall.trans (min_le_left _ _)
  have henv := Hreal.local_envelope_bounds hsmallOld
  have hM0 : 0 ≤ M := by simpa [M, Cenv, d] using henv.1
  have hM1 : M ≤ 1 := by simpa [M, Cenv, d] using henv.2.1
  have hvalue : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ M := by
    simpa [M, Cenv, d] using henv.2.2.1
  have hgrad : ∀ x : intervalDomainPoint,
      intervalDomain.gradNorm (fun y => u t y - uStar) x ≤ M := by
    simpa [M, Cenv, d] using henv.2.2.2
  have hscaledM1 : P * M ≤ 1 := by
    have hdsmall : d ≤ 1 / (P * Cenv) := by
      exact hsmall.trans (min_le_right _ _)
    have hP : 0 < P := lt_of_lt_of_le zero_lt_one (by
      simpa [P] using paper3RouteAPowerFactor_one_le p uStar)
    have hCenv : 0 < Cenv := by
      simpa [Cenv] using intervalDomainX2SigmaC1Envelope_pos sigma
    calc
      P * M = (P * Cenv) * d := by simp [M, mul_assoc]
      _ ≤ (P * Cenv) * (1 / (P * Cenv)) :=
        mul_le_mul_of_nonneg_left hdsmall (mul_pos hP hCenv).le
      _ = 1 := by field_simp [(mul_pos hP hCenv).ne']
  have hdistPos : d ≤ intervalDomainX2SigmaPositivityRadius sigma uStar :=
    hsmallOld.trans (min_le_left _ _)
  have hnearAbs : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ uStar / 2 := by
    intro x
    let Cinf := intervalDomainX2SigmaValueTrace sigma
    have hCinf : 0 ≤ Cinf := intervalDomainX2SigmaValueTrace_nonneg sigma
    have hden : 0 < 1 + Cinf := by linarith
    calc
      |u t x - uStar| ≤ Cinf * d := Hreal.value_bound x
      _ ≤ Cinf * intervalDomainX2SigmaPositivityRadius sigma uStar :=
        mul_le_mul_of_nonneg_left hdistPos hCinf
      _ = (uStar / 2) * (Cinf / (1 + Cinf)) := by
        dsimp [Cinf, intervalDomainX2SigmaPositivityRadius]
        field_simp [hden.ne']
      _ ≤ uStar / 2 := by
        have hfrac : Cinf / (1 + Cinf) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        simpa using mul_le_mul_of_nonneg_left hfrac (by linarith [heq.u_pos])
  have hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    have ha := hnearAbs xp
    have hlift : intervalDomainLift (u t) x = u t xp := by
      simp [intervalDomainLift, xp, hx]
    rw [hlift]
    constructor
    · linarith [neg_le_of_abs_le ha]
    · linarith [le_of_abs_le ha]
  have hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u t) x| ≤ M := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    simpa [paper3IntervalPerturbationProfile, intervalDomainLift, xp, hx]
      using hvalue xp
  have hphiCont : ContinuousOn
      (paper3IntervalPerturbationProfile uStar (u t))
      (Set.Icc (0 : ℝ) 1) := by
    have huCont : ContinuousOn (intervalDomainLift (u t))
        (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
    exact huCont.sub continuousOn_const
  have hphi : MemLp (paper3IntervalPerturbationProfile uStar (u t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont
  have hphi_l2 : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u t)) ≤ M :=
    intervalL2Size_le_of_pointwise_abs_bound hM0 hphi
      (fun x hx => hphi_sup x (Set.Ioo_subset_Icc_self hx))
  have hphiInt : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hphiCont
  have hreactCont : ContinuousOn
      (fun x => paper3LogisticReaction p (intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) 1) := by
    have huC2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
    have huCont := huC2.continuousOn
    have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (u t) x ≠ 0 := by
      intro x hx
      simpa [intervalDomainLift, hx] using
        (hsol.u_pos' (x := (⟨x, hx⟩ : intervalDomainPoint)) ht.1 ht.2).ne'
    unfold paper3LogisticReaction
    exact huCont.mul (continuousOn_const.sub
      (continuousOn_const.mul
        (huCont.rpow_const (fun x hx => Or.inl (hpos x hx)))))
  have hreact : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u t) x))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hreactCont
  have hlogCont : ContinuousOn
      (paper3IntervalLogisticRemainderProfile p uStar (u t))
      (Set.Icc (0 : ℝ) 1) := by
    unfold paper3IntervalLogisticRemainderProfile paper3LogisticRemainder
    exact hreactCont.add (continuousOn_const.mul hphiCont)
  have hlogLp : MemLp
      (paper3IntervalLogisticRemainderProfile p uStar (u t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hlogCont
  have hlog_meas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderProfile p uStar (u t))
      (intervalMeasure 1) := hlogLp.1
  have hwx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u t)) x| ≤ M := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
    have hg := hgrad xp
    change |deriv (intervalDomainLift (fun y => u t y - uStar)) x| ≤ M at hg
    have hevent : Filter.EventuallyEq (nhds x)
        (intervalDomainLift (fun y => u t y - uStar))
        (fun y => intervalDomainLift (u t) y - uStar) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx) ?_
      intro y hy
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hevent.deriv_eq, deriv_sub_const] at hg
    exact hg
  rcases paper3SignalSourceRegularity_of_classical_slice_generalM
      hsol ht heq with ⟨⟨Hlin, Hquad⟩⟩
  let Hsplit := intervalSolutionSignalSplitData_of_classical_slice_generalM
    (p := p) (uStar := uStar) hsol ht
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Klog := paper3UniformLogisticTaylorConstant p heq
  have hCsignal : 0 < Csignal := by
    simpa [Csignal] using
      paper3UniformSignalStrongConstant_pos p uStar heq.u_pos
  have hKlog : 0 < Klog := by
    simpa [Klog] using paper3UniformLogisticTaylorConstant_pos p heq
  have hsignal := paper3SignalComponents_strong_bounds_uniform
    p heq.u_pos hM0 (u t) hu_near hphi
      Hlin.profile_aestronglyMeasurable
      Hquad.profile_aestronglyMeasurable hphi_sup hphi_l2
  rcases
      exists_fullNonlinearRemainderRouteAData_of_strong_slice_with_constants_generalM
        hsol ht heq Hsplit Hlin Hquad Csignal Klog hCsignal hKlog
          hsignal (paper3UniformLogisticTaylorConstant_bound p heq)
          hM0 (by simpa [P, M] using hscaledM1) hu_near hphi hphi_sup
          hphi_l2 hphiInt hreact hlog_meas hwx with
    ⟨H, hHM, hHL, hconst⟩
  exact ⟨H, by simpa [P, M, Cenv, d] using hHM,
    by simpa [M, Cenv, d] using hHL,
    by simpa [Csignal, Klog] using hconst⟩

/-- One fixed effective general-`m` self-bound constant. -/
def intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
    (p : CM2Params) (sigma uStar vStar : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Klog := paper3UniformLogisticTaylorConstant p heq
  let Q := paper3RouteAFullQuadraticConstantGeneralM
    p uStar vStar Csignal Klog
  (Q + 1) * paper3RouteAPowerFactor p uStar *
    intervalDomainX2SigmaC1Envelope sigma ^ 2

theorem intervalDomainX2SigmaUniformNemytskiiConstantGeneralM_pos
    (p : CM2Params) (sigma uStar vStar : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    0 < intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
      p sigma uStar vStar heq := by
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Klog := paper3UniformLogisticTaylorConstant p heq
  have hC : 0 < Csignal := by
    simpa [Csignal] using
      paper3UniformSignalStrongConstant_pos p uStar heq.u_pos
  have hKlog : 0 < Klog := by
    simpa [Klog] using paper3UniformLogisticTaylorConstant_pos p heq
  have hU : 0 ≤ paper3RouteAPowerCeiling p uStar := by
    exact (paper3RouteAPowerCeiling_pos p heq.u_pos).le
  have hflux : 0 ≤ paper3RouteAFluxL2ConstantGeneralM
      p uStar vStar Csignal := by
    unfold paper3RouteAFluxL2ConstantGeneralM
    dsimp only
    have hCq : 0 ≤ 2 * p.β * Csignal :=
      mul_nonneg (mul_nonneg (by norm_num) p.hβ) hC.le
    have hK0 : 0 ≤
        |paper3SensitivityFactor p.β vStar| * Csignal +
          |paper3SensitivityFactor p.β vStar| * Csignal +
          (2 * p.β * Csignal) * (2 * Csignal) +
          paper3RouteAPowerCeiling p uStar * (2 * p.β * Csignal) *
            (2 * Csignal) := by
      positivity
    positivity
  have hQ : 0 ≤ paper3RouteAFullQuadraticConstantGeneralM
      p uStar vStar Csignal Klog := by
    unfold paper3RouteAFullQuadraticConstantGeneralM
    positivity
  unfold intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
  dsimp only
  exact mul_pos
    (mul_pos (by linarith)
      (lt_of_lt_of_le zero_lt_one
        (paper3RouteAPowerFactor_one_le p uStar)))
    (sq_pos_of_pos (intervalDomainX2SigmaC1Envelope_pos sigma))

theorem paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_generalM
    {p : CM2Params} {sigma uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomainM p T u v →
      t ∈ Set.Ioo (0 : ℝ) T →
      IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) →
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar →
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v t n : ℝ) : ℂ)) ≤
        intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
          p sigma uStar vStar heq *
            intervalDomainX2SigmaDistance sigma uStar (u t) ^ 2 := by
  intro T t u v hsol ht Hreal hsmall
  rcases exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform_generalM
      hsol ht heq Hreal hsmall with ⟨H, hM, hL, hconst⟩
  have hcoeff := H.coeffL2Norm_le
  have hQ0 := H.toL2Data.quadraticConstant_nonneg
  let P := paper3RouteAPowerFactor p uStar
  let Cenv := intervalDomainX2SigmaC1Envelope sigma
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  rw [hM, hL, hconst] at hcoeff
  refine ⟨hcoeff.1, ?_⟩
  calc
    _ ≤ paper3RouteAFullQuadraticConstantGeneralM p uStar vStar
          (paper3UniformSignalStrongConstant p uStar heq.u_pos)
          (paper3UniformLogisticTaylorConstant p heq) *
        (P * (Cenv * d)) * (Cenv * d) := by
      simpa [P, Cenv, d] using hcoeff.2
    _ ≤ intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
          p sigma uStar vStar heq * d ^ 2 := by
      dsimp [intervalDomainX2SigmaUniformNemytskiiConstantGeneralM, P, Cenv]
      have hP : 0 ≤ paper3RouteAPowerFactor p uStar :=
        paper3RouteAPowerFactor_nonneg p uStar
      have hC : 0 ≤ intervalDomainX2SigmaC1Envelope sigma :=
        (intervalDomainX2SigmaC1Envelope_pos sigma).le
      have hd : 0 ≤ d := by dsimp [d]; exact Real.sqrt_nonneg _
      have hfac : 0 ≤ paper3RouteAPowerFactor p uStar *
          intervalDomainX2SigmaC1Envelope sigma ^ 2 * d ^ 2 := by positivity
      nlinarith [hQ0, hfac]

/-- Strong membership and classical continuity construct the realization
record required by the faithful general-`m` quadratic estimate. -/
theorem paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_of_mem_generalM
    {p : CM2Params} {sigma uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomainM p T u v →
      t ∈ Set.Ioo (0 : ℝ) T →
      3 / 4 < sigma →
      IntervalDomainX2SigmaPerturbation sigma uStar (u t) →
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar →
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v t n : ℝ) : ℂ)) ≤
        intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
          p sigma uStar vStar heq *
            intervalDomainX2SigmaDistance sigma uStar (u t) ^ 2 := by
  intro T t u v hsol ht hsigma hmem hsmall
  have hcont : Continuous (u t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol ht
  have Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous
      hsigma hcont hmem
  exact paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_generalM
    heq hsol ht Hreal hsmall

#print axioms intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM_pos
#print axioms
  exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform_generalM
#print axioms intervalDomainX2SigmaUniformNemytskiiConstantGeneralM_pos
#print axioms paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_generalM
#print axioms
  paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_of_mem_generalM

end

end ShenWork.Paper3
