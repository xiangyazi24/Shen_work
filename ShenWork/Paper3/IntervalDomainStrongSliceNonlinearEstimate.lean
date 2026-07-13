/- Strong-ball production of the actual route-(a) nonlinear slice estimate. -/
import ShenWork.Paper3.IntervalDomainRouteANonlinearSnapshot
import ShenWork.Paper3.IntervalDomainSignalRegularityProducer
import ShenWork.Paper3.IntervalDomainFluxDerivativeIntegrability
import ShenWork.Paper3.IntervalDomainStrongEmbedding
import ShenWork.Paper3.IntervalDomainStrongRealizationProducer
import ShenWork.Paper3.IntervalDomainUniformNemytskiiConstants
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper2.IntervalDomainMPhysicalRestart

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

/-- Strong fractional smallness produces every local Nemytskii hypothesis,
including the load-bearing positive lower bound and the qualitative
integrability of the already-identified physical flux derivative. -/
theorem exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar) :
    ∃ H : FullNonlinearRemainderRouteAData
        (paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t),
      H.flux.bounds.M =
          intervalDomainX2SigmaC1Envelope sigma *
            intervalDomainX2SigmaDistance sigma uStar (u t) ∧
        H.flux.bounds.L =
          intervalDomainX2SigmaC1Envelope sigma *
            intervalDomainX2SigmaDistance sigma uStar (u t) ∧
        H.toL2Data.quadraticConstant =
          paper3RouteAFullQuadraticConstant p uStar vStar
            (paper3UniformSignalStrongConstant p uStar heq.u_pos)
            (paper3UniformLogisticTaylorConstant p heq) := by
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  let M := intervalDomainX2SigmaC1Envelope sigma * d
  have henv := Hreal.local_envelope_bounds hsmall
  have hM0 : 0 ≤ M := by simpa [M, d] using henv.1
  have hM1 : M ≤ 1 := by simpa [M, d] using henv.2.1
  have hvalue : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ M := by
    simpa [M, d] using henv.2.2.1
  have hgrad : ∀ x : intervalDomainPoint,
      intervalDomain.gradNorm (fun y => u t y - uStar) x ≤ M := by
    simpa [M, d] using henv.2.2.2
  have hdistPos : d ≤ intervalDomainX2SigmaPositivityRadius sigma uStar :=
    hsmall.trans (min_le_left _ _)
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
        <;> ring
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
      simp [intervalDomainLift, hx, (hsol.u_pos' ht.1 ht.2).ne']
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
      refine Filter.eventuallyEq_of_mem
        (IsOpen.mem_nhds isOpen_Ioo hx) ?_
      intro y hy
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hevent.deriv_eq, deriv_sub_const] at hg
    exact hg
  rcases paper3SignalSourceRegularity_of_classical_slice hsol ht heq with
    ⟨⟨Hlin, Hquad⟩⟩
  let Hsplit := intervalSolutionSignalSplitData_of_classical_slice
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
  have hz1xxMem : MemLp (paper3LinearSignalLaplacian p uStar (u t)) 2
      (intervalMeasure 1) := by
    apply memLp_two_of_hasDerivAt_Ioo_and_abs_bound_Icc
      (mul_nonneg hCsignal.le hM0)
    · intro x hx
      exact paper3LinearSignalGradient_hasDerivAt_laplacian
        p uStar (u t) Hlin hx
    · intro x hx
      exact (hsignal x hx).2.2.1
  have hfluxDerivInt := paper3ChemFluxRemainder_deriv_intervalIntegrable
    (vStar := vStar) hsol ht hm Hlin hz1xxMem
  rcases exists_fullNonlinearRemainderRouteAData_of_strong_slice_with_constants
      hsol ht hm heq Hsplit Hlin Hquad Csignal Klog hCsignal hKlog
        hsignal (paper3UniformLogisticTaylorConstant_bound p heq)
        hM0 hM1 hu_near hphi hphi_sup hphi_l2 hphiInt hreact hlog_meas
        hwx hfluxDerivInt with
    ⟨H, hHM, hHL, hconst⟩
  exact ⟨H, by simpa [M, d] using hHM,
    by simpa [M, d] using hHL, by simpa [Csignal, Klog] using hconst⟩

#print axioms exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform

/-- Compatibility form of the strong-ball producer. -/
theorem exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar) :
    ∃ H : FullNonlinearRemainderRouteAData
        (paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t),
      H.flux.bounds.M =
          intervalDomainX2SigmaC1Envelope sigma *
            intervalDomainX2SigmaDistance sigma uStar (u t) ∧
        H.flux.bounds.L =
          intervalDomainX2SigmaC1Envelope sigma *
            intervalDomainX2SigmaDistance sigma uStar (u t) := by
  rcases exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform
      hsol ht hm heq Hreal hsmall with ⟨H, hM, hL, _⟩
  exact ⟨H, hM, hL⟩

#print axioms exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball

/-- One trajectory-independent quadratic constant for the actual modal
nonlinearity on the strong positivity ball. -/
def intervalDomainX2SigmaUniformNemytskiiConstant
    (p : CM2Params) (sigma uStar vStar : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Klog := paper3UniformLogisticTaylorConstant p heq
  let Q := paper3RouteAFullQuadraticConstant
    p uStar vStar Csignal Klog
  (Q + 1) * intervalDomainX2SigmaC1Envelope sigma ^ 2

theorem intervalDomainX2SigmaUniformNemytskiiConstant_pos
    (p : CM2Params) (sigma uStar vStar : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    0 < intervalDomainX2SigmaUniformNemytskiiConstant
      p sigma uStar vStar heq := by
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Klog := paper3UniformLogisticTaylorConstant p heq
  have hC : 0 < Csignal := by
    simpa [Csignal] using
      paper3UniformSignalStrongConstant_pos p uStar heq.u_pos
  have hKlog : 0 < Klog := by
    simpa [Klog] using paper3UniformLogisticTaylorConstant_pos p heq
  have hflux : 0 ≤ paper3RouteAFluxL2Constant
      p uStar vStar Csignal := by
    unfold paper3RouteAFluxL2Constant
    dsimp only
    have hU : 0 ≤ uStar + 1 := by linarith [heq.u_pos]
    have hCq : 0 ≤ 2 * p.β * Csignal :=
      mul_nonneg (mul_nonneg (by norm_num) p.hβ) hC.le
    have hK0 : 0 ≤
        |paper3SensitivityFactor p.β vStar| * Csignal +
          |paper3SensitivityFactor p.β vStar| * Csignal +
          (2 * p.β * Csignal) * (2 * Csignal) +
          (uStar + 1) * (2 * p.β * Csignal) * (2 * Csignal) := by
      positivity
    positivity
  have hQ : 0 ≤ paper3RouteAFullQuadraticConstant
      p uStar vStar Csignal Klog := by
    unfold paper3RouteAFullQuadraticConstant
    positivity
  unfold intervalDomainX2SigmaUniformNemytskiiConstant
  dsimp only
  exact mul_pos (by linarith)
    (sq_pos_of_pos (intervalDomainX2SigmaC1Envelope_pos sigma))

/-- Uniform L12 self estimate.  The constant is fixed before the trajectory,
time slice, and local strong datum are quantified. -/
theorem paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound
    {p : CM2Params} {sigma uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      t ∈ Set.Ioo (0 : ℝ) T →
      p.m = 1 →
      IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) →
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar →
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v t n : ℝ) : ℂ)) ≤
        intervalDomainX2SigmaUniformNemytskiiConstant
          p sigma uStar vStar heq *
            intervalDomainX2SigmaDistance sigma uStar (u t) ^ 2 := by
  intro T t u v hsol ht hm Hreal hsmall
  rcases exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball_uniform
      hsol ht hm heq Hreal hsmall with ⟨H, hM, hL, hconst⟩
  have hcoeff := H.coeffL2Norm_le
  have hQ0 := H.toL2Data.quadraticConstant_nonneg
  let Cenv := intervalDomainX2SigmaC1Envelope sigma
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  rw [hM, hL, hconst] at hcoeff
  refine ⟨hcoeff.1, ?_⟩
  calc
    _ ≤ paper3RouteAFullQuadraticConstant p uStar vStar
          (paper3UniformSignalStrongConstant p uStar heq.u_pos)
          (paper3UniformLogisticTaylorConstant p heq) *
        (Cenv * d) * (Cenv * d) := by
      simpa [Cenv, d] using hcoeff.2
    _ ≤ intervalDomainX2SigmaUniformNemytskiiConstant
          p sigma uStar vStar heq * d ^ 2 := by
      dsimp [intervalDomainX2SigmaUniformNemytskiiConstant, Cenv]
      have hd : 0 ≤ d := by dsimp [d]; exact Real.sqrt_nonneg _
      nlinarith [sq_nonneg (intervalDomainX2SigmaC1Envelope sigma),
        sq_nonneg d, hQ0]

#print axioms paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound
#print axioms intervalDomainX2SigmaUniformNemytskiiConstant_pos

/-- L12 in the exact strong norm: on the local positivity ball the complete
physical modal nonlinearity is quadratic in the `X_2^sigma` distance. -/
theorem paper3FullModeNonlinearRemainderCoeffM_coeffL2Norm_le_X2Sigma_sq
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar) :
    ∃ K > 0,
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v t n : ℝ) : ℂ)) ≤
        K * intervalDomainX2SigmaDistance sigma uStar (u t) ^ 2 := by
  rcases exists_fullNonlinearRemainderRouteAData_of_X2Sigma_ball
      hsol ht hm heq Hreal hsmall with ⟨H, hM, hL⟩
  have hcoeff := H.coeffL2Norm_le
  have hK0 := H.toL2Data.quadraticConstant_nonneg
  let Cenv := intervalDomainX2SigmaC1Envelope sigma
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  let K := (H.toL2Data.quadraticConstant + 1) * Cenv ^ 2
  have hCenv : 0 < Cenv := intervalDomainX2SigmaC1Envelope_pos sigma
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (by linarith) (sq_pos_of_pos hCenv)
  refine ⟨K, hK, hcoeff.1, ?_⟩
  rw [hM, hL] at hcoeff
  calc
    _ ≤ H.toL2Data.quadraticConstant * (Cenv * d) * (Cenv * d) := by
      simpa [Cenv, d] using hcoeff.2
    _ ≤ K * d ^ 2 := by
      dsimp [K]
      have hd : 0 ≤ d := by dsimp [d]; exact Real.sqrt_nonneg _
      nlinarith [sq_nonneg Cenv, sq_nonneg d,
        mul_nonneg hK0 (mul_nonneg hCenv.le hd)]

#print axioms
      paper3FullModeNonlinearRemainderCoeffM_coeffL2Norm_le_X2Sigma_sq

/-- The actual quadratic Nemytskii estimate with no externally carried
physical-realization record.  In the strong range `sigma>3/4`, fractional
membership and the classical slice continuity produce that record
automatically. -/
theorem paper3FullModeNonlinearRemainderCoeffM_coeffL2Norm_le_X2Sigma_sq_of_mem
    {p : CM2Params} {T t sigma uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsigma : 3 / 4 < sigma)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hmem : IntervalDomainX2SigmaPerturbation sigma uStar (u t))
    (hsmall : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar) :
    ∃ K > 0,
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v t n : ℝ) : ℂ)) ≤
        K * intervalDomainX2SigmaDistance sigma uStar (u t) ^ 2 := by
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hcont : Continuous (u t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM ht
  have Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous
      hsigma hcont hmem
  exact paper3FullModeNonlinearRemainderCoeffM_coeffL2Norm_le_X2Sigma_sq
    hsol ht hm heq Hreal hsmall

/-- Uniform-constant version of the actual L12 estimate with the physical
realization record produced from strong membership and classical continuity. -/
theorem paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_of_mem
    {p : CM2Params} {sigma uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      t ∈ Set.Ioo (0 : ℝ) T →
      3 / 4 < sigma →
      p.m = 1 →
      IntervalDomainX2SigmaPerturbation sigma uStar (u t) →
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar →
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v t n : ℝ) : ℂ)) ≤
        intervalDomainX2SigmaUniformNemytskiiConstant
          p sigma uStar vStar heq *
            intervalDomainX2SigmaDistance sigma uStar (u t) ^ 2 := by
  intro T t u v hsol ht hsigma hm hmem hsmall
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hcont : Continuous (u t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM ht
  have Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous
      hsigma hcont hmem
  exact paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound
    heq hsol ht hm Hreal hsmall

#print axioms
  paper3FullModeNonlinearRemainderCoeffM_coeffL2Norm_le_X2Sigma_sq_of_mem
#print axioms
  paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_of_mem

end

end ShenWork.Paper3
