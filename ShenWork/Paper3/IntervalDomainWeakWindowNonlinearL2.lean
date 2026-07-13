/- Uniform route-(a) source bounds on the weak positive restart window. -/
import ShenWork.Paper3.IntervalDomainWeakSupBootstrap
import ShenWork.Paper3.IntervalDomainExplicitPositiveTimeC1
import ShenWork.Paper3.IntervalDomainStrongSliceNonlinearEstimate

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.SectorialOperator

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Fixed coefficient bound for the full nonlinear remainder on the last half
of a weak restart window. -/
def paper3WeakWindowNonlinearL2Constant
    (p : CM2Params) (uStar vStar T : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let M := intervalDomainWeakSupConeCeiling uStar
  let Cflux := paper3ChemFluxDerivPositiveTimeConstant p M T (T / 2)
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let qlin := uStar * paper3SensitivityFactor p.β vStar
  let Kchem := |p.χ₀| * (Cflux + |qlin| * Csignal)
  let Klog := paper3UniformLogisticTaylorConstant p heq
  2 * Real.sqrt 2 * (Kchem + Klog)

theorem paper3WeakWindowNonlinearL2Constant_nonneg
    (p : CM2Params) {uStar vStar T : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) (hT : 0 < T) :
    0 ≤ paper3WeakWindowNonlinearL2Constant p uStar vStar T heq := by
  let M := intervalDomainWeakSupConeCeiling uStar
  let Cflux := paper3ChemFluxDerivPositiveTimeConstant p M T (T / 2)
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let qlin := uStar * paper3SensitivityFactor p.β vStar
  let Kchem := |p.χ₀| * (Cflux + |qlin| * Csignal)
  let Klog := paper3UniformLogisticTaylorConstant p heq
  have hM : 0 ≤ M := by
    dsimp [M, intervalDomainWeakSupConeCeiling]
    linarith [heq.u_pos]
  have hCflux : 0 ≤ Cflux := by
    simpa [Cflux, M] using paper3ChemFluxDerivPositiveTimeConstant_nonneg
      p hM hT.le (by linarith : 0 < T / 2)
  have hCsignal : 0 ≤ Csignal := by
    simpa [Csignal] using
      (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le
  have hKchem : 0 ≤ Kchem := by
    dsimp [Kchem]
    positivity
  have hKlog : 0 ≤ Klog := by
    simpa [Klog] using
      (paper3UniformLogisticTaylorConstant_pos p heq).le
  unfold paper3WeakWindowNonlinearL2Constant
  dsimp only
  positivity

/-- The restarted initial slice is bounded by the fixed cone ceiling. -/
theorem IntervalDomainWeakSupRestartWindowData.initial_lift_bound
    {p : CM2Params} {uStar T delta : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (huStar : 0 < uStar) (hdeltaStar : delta ≤ uStar / 16) :
    ∀ y, |intervalDomainLift (u D.a) y| ≤ D.mild.M := by
  intro y
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · let x : intervalDomainPoint := ⟨y, hy⟩
    have hclose := D.close 0 le_rfl hT.le x
    have hzero : D.mild.u 0 x = u D.a x := by
      rw [D.mild_u]
      simpa using congrFun (intervalDomainRestartTrajectory_eq
        (a := D.a) (h := T) (u := u) ⟨le_rfl, hT.le⟩) x
    rw [hzero] at hclose
    have huabs : |u D.a x| ≤ 3 * uStar / 2 := by
      have htri : |u D.a x| ≤ |u D.a x - uStar| + |uStar| := by
        calc
          |u D.a x| = |(u D.a x - uStar) + uStar| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_of_pos huStar] at htri
      exact htri.trans (by linarith)
    rw [D.mild_M]
    simpa [intervalDomainLift, hy, intervalDomainWeakSupConeCeiling] using huabs
  · rw [D.mild_M]
    simp [intervalDomainLift, hy,
      (show 0 ≤ intervalDomainWeakSupConeCeiling uStar by
        dsimp [intervalDomainWeakSupConeCeiling]; linarith)]

/-- The restarted initial lift is measurable because the restart occurs at a
strictly positive classical time. -/
theorem IntervalDomainWeakSupRestartWindowData.initial_lift_measurable_of_solution
    {p : CM2Params} {uStar T delta H : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (haH : D.a < H) :
    AEStronglyMeasurable (intervalDomainLift (u D.a))
      (intervalMeasure 1) := by
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hcont : Continuous (u D.a) :=
    solutionSlice_continuous hsolM ⟨D.a_pos, haH⟩
  exact (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
    hcont).aestronglyMeasurable

/-- Global-orbit wrapper for measurability of the restarted initial lift. -/
theorem IntervalDomainWeakSupRestartWindowData.initial_lift_measurable
    {p : CM2Params} {uStar T delta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    AEStronglyMeasurable (intervalDomainLift (u D.a))
      (intervalMeasure 1) := by
  let H := D.a + T + 1
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hH : 0 < H := by dsimp [H]; linarith [D.a_pos, hT]
  have haH : D.a < H := by dsimp [H]; linarith [hT]
  exact D.initial_lift_measurable_of_solution hm (hglobal H hH) haH

/-- On the physical restart strip the derivative of the faithful flux agrees
with the derivative of the eliminated weak-map flux. -/
theorem weakRestart_actualFlux_deriv_eq_chemFlux_deriv_of_solution
    {p : CM2Params} {uStar T delta r x H : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (haTH : D.a + T < H)
    (hr : r ∈ Set.Icc (0 : ℝ) T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalFluxM p (u (D.a + r)) (v (D.a + r))) x =
      deriv (chemFluxLifted p (D.mild.u r)) x := by
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have heqOn : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalFluxM p (u (D.a + r)) (v (D.a + r)) y =
        chemFluxLifted p (D.mild.u r) y := by
    intro y hy
    have hphys := restartFluxM_eq_physical
      (isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol)
      D.a_pos hT.le haTH hr (Set.Ioo_subset_Icc_self hy)
    have helim := restartFluxM_eq_chemFluxLifted_restartTrajectory
      hsol hm D.a_pos hT.le haTH hr (Set.Ioo_subset_Icc_self hy)
    rw [← D.mild_u] at helim
    exact hphys.symm.trans helim
  have hev : intervalFluxM p (u (D.a + r)) (v (D.a + r)) =ᶠ[𝓝 x]
      chemFluxLifted p (D.mild.u r) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) heqOn
  exact hev.deriv_eq

/-- Global-orbit wrapper for the restarted flux identity. -/
theorem weakRestart_actualFlux_deriv_eq_chemFlux_deriv
    {p : CM2Params} {uStar T delta r x : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hr : r ∈ Set.Icc (0 : ℝ) T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalFluxM p (u (D.a + r)) (v (D.a + r))) x =
      deriv (chemFluxLifted p (D.mild.u r)) x := by
  let H := D.a + T + 1
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hH : 0 < H := by dsimp [H]; linarith [D.a_pos, hT]
  have haTH : D.a + T < H := by dsimp [H]; linarith
  exact weakRestart_actualFlux_deriv_eq_chemFlux_deriv_of_solution
    D hm (hglobal H hH) haTH hr hx

/-- Uniform coefficient-`ell2` estimate for the true full nonlinear remainder
on the last half of the weak restart window.  Route (a) is used: the spatial
derivative stays on the physical flux profile. -/
theorem weakRestart_fullNonlinearRemainderCoeff_uniform_L2_of_solution
    {p : CM2Params} {uStar vStar T delta r H : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (haTH : D.a + T < H)
    (hdelta : 0 ≤ delta) (hdeltaStar : delta ≤ uStar / 16)
    (hdeltaOne : 4 * delta ≤ 1)
    (hr : r ∈ Set.Ioo (T / 2) T) :
    Summable (fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v (D.a + r) n : ℝ) : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v (D.a + r) n : ℝ) : ℂ)) ≤
        paper3WeakWindowNonlinearL2Constant p uStar vStar T heq := by
  let Mcone := intervalDomainWeakSupConeCeiling uStar
  let Cflux := paper3ChemFluxDerivPositiveTimeConstant
    p Mcone T (T / 2)
  let Csignal := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let qlin := uStar * paper3SensitivityFactor p.β vStar
  let Kchem := |p.χ₀| * (Cflux + |qlin| * Csignal)
  let Klog := paper3UniformLogisticTaylorConstant p heq
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hrIcc : r ∈ Set.Icc (0 : ℝ) T :=
    ⟨(by linarith [hr.1]), hr.2.le⟩
  have ht : D.a + r ∈ Set.Ioo (0 : ℝ) H := by
    constructor
    · linarith [D.a_pos, hr.1]
    · exact lt_of_le_of_lt (by linarith [hr.2]) haTH
  have hu0Bound := D.initial_lift_bound heq.u_pos hdeltaStar
  have hu0Meas := D.initial_lift_measurable_of_solution hm hsol
    (by linarith [haTH, hT])
  have hfluxBound : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalFluxM p (u (D.a + r)) (v (D.a + r))) x| ≤
        Cflux := by
    intro x hx
    rw [weakRestart_actualFlux_deriv_eq_chemFlux_deriv_of_solution
      D hm hsol haTH hrIcc hx]
    have h := conjugateMild_chemFlux_deriv_positiveTime_explicit
      D.mild hu0Bound hu0Meas (by linarith : 0 < T / 2)
        r hr.1.le (by rw [D.mild_T]; exact hr.2.le) x hx
    simpa [Cflux, D.mild_M, D.mild_T, Mcone] using h
  have hclose : ∀ x : intervalDomainPoint,
      |u (D.a + r) x - uStar| ≤ 4 * delta := by
    have hmildEq := congrFun (D.mild_u) r
    have htrajEq := intervalDomainRestartTrajectory_eq
      (a := D.a) (h := T) (u := u) hrIcc
    intro x
    have hc := D.close r (by linarith [hr.1]) hr.2.le x
    rw [hmildEq, htrajEq] at hc
    exact hc
  have huNear : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u (D.a + r)) x ∈
        Set.Icc (uStar / 2) (3 * uStar / 2) := by
    intro x hx
    have hc := hclose ⟨x, hx⟩
    have hsmall : |u (D.a + r) ⟨x, hx⟩ - uStar| ≤ uStar / 4 :=
      hc.trans (by linarith)
    simp only [intervalDomainLift, hx, dif_pos]
    exact ⟨by linarith [neg_le_of_abs_le hsmall],
      by linarith [le_of_abs_le hsmall]⟩
  have hphiSup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u (D.a + r)) x| ≤ 1 := by
    intro x hx
    simpa [paper3IntervalPerturbationProfile, intervalDomainLift, hx] using
      (hclose ⟨x, hx⟩).trans hdeltaOne
  have hphiCont : ContinuousOn
      (paper3IntervalPerturbationProfile uStar (u (D.a + r)))
      (Set.Icc (0 : ℝ) 1) := by
    exact ((hsol.regularity.2.2.2.2.1 (D.a + r) ht).1.1.continuousOn).sub
      continuousOn_const
  have hphi : MemLp
      (paper3IntervalPerturbationProfile uStar (u (D.a + r))) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont
  have hphiL2 : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u (D.a + r))) ≤ 1 :=
    intervalL2Size_le_of_pointwise_abs_bound (by norm_num) hphi
      (fun x hx => hphiSup x (Set.Ioo_subset_Icc_self hx))
  have hphiInt : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u (D.a + r))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hphiCont
  rcases paper3SignalSourceRegularity_of_classical_slice hsol ht heq with
    ⟨⟨Hlin, Hquad⟩⟩
  let Hsplit := intervalSolutionSignalSplitData_of_classical_slice
    (p := p) (uStar := uStar) hsol ht
  have hsignal := paper3SignalComponents_strong_bounds_uniform
    p heq.u_pos (by norm_num : (0 : ℝ) ≤ 1) (u (D.a + r)) huNear hphi
      Hlin.profile_aestronglyMeasurable Hquad.profile_aestronglyMeasurable
      hphiSup hphiL2
  have hz1xxMem : MemLp
      (paper3LinearSignalLaplacian p uStar (u (D.a + r))) 2
      (intervalMeasure 1) := by
    apply memLp_two_of_hasDerivAt_Ioo_and_abs_bound_Icc
      (by simpa [Csignal] using
        (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le)
    · intro x hx
      exact paper3LinearSignalGradient_hasDerivAt_laplacian
        p uStar (u (D.a + r)) Hlin hx
    · intro x hx
      simpa [Csignal] using (hsignal x hx).2.2.1
  have hfluxRemInt := paper3ChemFluxRemainder_deriv_intervalIntegrable
    (vStar := vStar) hsol ht hm Hlin hz1xxMem
  have hreactCont : ContinuousOn
      (fun x => paper3LogisticReaction p
        (intervalDomainLift (u (D.a + r)) x))
      (Set.Icc (0 : ℝ) 1) := by
    have huCont := (hsol.regularity.2.2.2.2.1 (D.a + r) ht).1.1.continuousOn
    have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (u (D.a + r)) x ≠ 0 := by
      intro x hx
      simp [intervalDomainLift, hx, (hsol.u_pos' ht.1 ht.2).ne']
    unfold paper3LogisticReaction
    exact huCont.mul (continuousOn_const.sub
      (continuousOn_const.mul
        (huCont.rpow_const (fun x hx => Or.inl (hpos x hx)))))
  have hreactInt : IntervalIntegrable
      (fun x => paper3LogisticReaction p
        (intervalDomainLift (u (D.a + r)) x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hreactCont
  have hlogCont : ContinuousOn
      (paper3IntervalLogisticRemainderProfile p uStar (u (D.a + r)))
      (Set.Icc (0 : ℝ) 1) := by
    unfold paper3IntervalLogisticRemainderProfile paper3LogisticRemainder
    exact hreactCont.add (continuousOn_const.mul hphiCont)
  have hlogMeas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderProfile p uStar (u (D.a + r)))
      (intervalMeasure 1) :=
    (BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hlogCont).1
  have hremDeriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (paper3ChemFluxRemainderProfileM p uStar vStar
        (u (D.a + r)) (v (D.a + r))) x =
      deriv (intervalFluxM p (u (D.a + r)) (v (D.a + r))) x -
        qlin * paper3LinearSignalLaplacian p uStar (u (D.a + r)) x := by
    intro x hx
    have hactual : HasDerivAt
        (intervalFluxM p (u (D.a + r)) (v (D.a + r)))
        (deriv (intervalFluxM p (u (D.a + r)) (v (D.a + r))) x) x :=
      ((fluxM_contDiffOn_Ioo hsolM ht.1 ht.2).differentiableOn
        (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
    have hlinBase := paper3LinearSignalGradient_hasDerivAt_laplacian
      p uStar (u (D.a + r)) Hlin hx
    have hlin : HasDerivAt
        (paper3LinearChemFluxProfile p uStar vStar (u (D.a + r)))
        (qlin * paper3LinearSignalLaplacian p uStar (u (D.a + r)) x) x := by
      convert hlinBase.const_mul
        (uStar * paper3SensitivityFactor p.β vStar) using 1
      · funext y
        dsimp [paper3LinearChemFluxProfile, qlin]
        rw [hm, Real.rpow_one]
    unfold paper3ChemFluxRemainderProfileM
    exact (hactual.sub hlin).deriv
  have hchemPoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |-p.χ₀ * deriv (paper3ChemFluxRemainderProfileM p uStar vStar
        (u (D.a + r)) (v (D.a + r))) x| ≤ Kchem := by
    intro x hx
    rw [abs_mul, abs_neg]
    have hlap : |paper3LinearSignalLaplacian p uStar
        (u (D.a + r)) x| ≤ Csignal := by
      simpa [Csignal] using
        (hsignal x (Set.Ioo_subset_Icc_self hx)).2.2.1
    have hrem : |deriv (paper3ChemFluxRemainderProfileM p uStar vStar
        (u (D.a + r)) (v (D.a + r))) x| ≤
        Cflux + |qlin| * Csignal := by
      rw [hremDeriv x hx]
      calc
        _ ≤ |deriv (intervalFluxM p (u (D.a + r))
            (v (D.a + r))) x| +
            |qlin * paper3LinearSignalLaplacian p uStar
              (u (D.a + r)) x| := abs_sub _ _
        _ ≤ Cflux + |qlin| * Csignal := by
          rw [abs_mul]
          exact add_le_add (hfluxBound x hx)
            (mul_le_mul_of_nonneg_left hlap (abs_nonneg _))
    exact mul_le_mul_of_nonneg_left hrem (abs_nonneg _)
  have hlogPoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalLogisticRemainderProfile p uStar
        (u (D.a + r)) x| ≤ Klog := by
    intro x hx
    have hquad := paper3UniformLogisticTaylorConstant_bound p heq
      (intervalDomainLift (u (D.a + r)) x) (huNear x hx)
    have hphi := hphiSup x hx
    dsimp [paper3IntervalLogisticRemainderProfile,
      paper3IntervalPerturbationProfile, paper3LogisticRemainder] at hquad hphi ⊢
    calc
      _ ≤ Klog * |intervalDomainLift (u (D.a + r)) x - uStar| ^ 2 := by
        simpa [Klog] using hquad
      _ ≤ Klog * 1 ^ 2 :=
        mul_le_mul_of_nonneg_left
          (sq_le_sq₀ (abs_nonneg _) (by norm_num) |>.2 hphi)
          (by simpa [Klog] using
            (paper3UniformLogisticTaylorConstant_pos p heq).le)
      _ = Klog := by ring
  let chemProfile : ℝ → ℝ := fun x => -p.χ₀ *
    deriv (paper3ChemFluxRemainderProfileM p uStar vStar
      (u (D.a + r)) (v (D.a + r))) x
  let logProfile : ℝ → ℝ :=
    paper3IntervalLogisticRemainderProfile p uStar (u (D.a + r))
  have hKchem : 0 ≤ Kchem := by
    dsimp [Kchem]
    exact mul_nonneg (abs_nonneg _)
      (add_nonneg
        (paper3ChemFluxDerivPositiveTimeConstant_nonneg
          p (by
            dsimp [Mcone, intervalDomainWeakSupConeCeiling]
            linarith [heq.u_pos]) hT.le (by linarith : 0 < T / 2))
        (mul_nonneg (abs_nonneg _)
          (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le))
  have hKlog : 0 ≤ Klog := by
    simpa [Klog] using
      (paper3UniformLogisticTaylorConstant_pos p heq).le
  have hchemMeas : AEStronglyMeasurable chemProfile (intervalMeasure 1) :=
    (measurable_const.mul (measurable_deriv _)).aestronglyMeasurable
  have hchemMem : MemLp chemProfile 2 (intervalMeasure 1) := by
    apply memLp_two_of_pointwise_mul_Ioo hKchem hchemMeas (memLp_const 1)
    intro x hx
    simpa [chemProfile] using hchemPoint x hx
  have hchemL2 : intervalL2Size chemProfile ≤ Kchem :=
    intervalL2Size_le_of_pointwise_abs_bound hKchem hchemMem
      (fun x hx => by simpa [chemProfile] using hchemPoint x hx)
  have hlogMem : MemLp logProfile 2 (intervalMeasure 1) := by
    simpa [logProfile] using
      BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hlogCont
  have hlogL2 : intervalL2Size logProfile ≤ Klog :=
    intervalL2Size_le_of_pointwise_abs_bound hKlog hlogMem
      (fun x hx => by
        simpa [logProfile] using hlogPoint x (Set.Ioo_subset_Icc_self hx))
  let Hphys : FullNonlinearRemainderL2Data
      (paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v (D.a + r)) :=
    { M := 1
      L := 1
      Kchem := Kchem
      Klog := Klog
      chemProfile := chemProfile
      logProfile := logProfile
      M_nonneg := by norm_num
      L_nonneg := by norm_num
      Kchem_nonneg := hKchem
      Klog_nonneg := hKlog
      chem_memLp := hchemMem
      log_memLp := hlogMem
      chem_l2 := by simpa using hchemL2
      log_l2 := by simpa using hlogL2
      coeff_eq := by
        intro n
        rw [paper3FullModeNonlinearRemainderCoeffM_eq_parts,
          paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine
            hsol ht hm heq Hsplit Hlin Hquad hfluxRemInt n,
          paper3LogisticRemainderCoeffM_eq_cosine
            p uStar u (D.a + r) n hreactInt hphiInt]
    }
  have hcoeff := Hphys.coeffL2Norm_le
  simpa [Hphys, FullNonlinearRemainderL2Data.quadraticConstant,
    paper3WeakWindowNonlinearL2Constant, Kchem, Klog, Cflux, Csignal,
    qlin, Mcone, chemProfile, logProfile] using hcoeff

/-- Global-orbit wrapper for the finite-window nonlinear source estimate. -/
theorem weakRestart_fullNonlinearRemainderCoeff_uniform_L2
    {p : CM2Params} {uStar vStar T delta r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hdelta : 0 ≤ delta) (hdeltaStar : delta ≤ uStar / 16)
    (hdeltaOne : 4 * delta ≤ 1)
    (hr : r ∈ Set.Ioo (T / 2) T) :
    Summable (fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v (D.a + r) n : ℝ) : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v (D.a + r) n : ℝ) : ℂ)) ≤
        paper3WeakWindowNonlinearL2Constant p uStar vStar T heq := by
  let H := D.a + T + 1
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hH : 0 < H := by dsimp [H]; linarith [D.a_pos, hT]
  have haTH : D.a + T < H := by dsimp [H]; linarith
  exact weakRestart_fullNonlinearRemainderCoeff_uniform_L2_of_solution
    D hm heq (hglobal H hH) haTH hdelta hdeltaStar hdeltaOne hr

#print axioms paper3WeakWindowNonlinearL2Constant_nonneg
#print axioms IntervalDomainWeakSupRestartWindowData.initial_lift_bound
#print axioms IntervalDomainWeakSupRestartWindowData.initial_lift_measurable
#print axioms IntervalDomainWeakSupRestartWindowData.initial_lift_measurable_of_solution
#print axioms weakRestart_actualFlux_deriv_eq_chemFlux_deriv
#print axioms weakRestart_actualFlux_deriv_eq_chemFlux_deriv_of_solution
#print axioms weakRestart_fullNonlinearRemainderCoeff_uniform_L2
#print axioms weakRestart_fullNonlinearRemainderCoeff_uniform_L2_of_solution

end

end ShenWork.Paper3
