/- Uniform strong smoothing at the end of the faithful general-`m` weak
restart window. -/
import ShenWork.Paper3.IntervalDomainMWeakWindowNonlinearL2
import ShenWork.Paper3.IntervalDomainStrongDuhamelL2StartGeneralM

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

local instance intervalDomainMWeakWindowStrongTopologicalSpace :
    TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Every faithful general-`m` weak-window slice has unweighted coefficient
norm controlled by its physical sup distance from equilibrium. -/
theorem weakRestartM_perturbationCoeff_L2_of_solution
    {p : CM2Params} {uStar T delta r H : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainMWeakSupRestartWindowData p uStar T delta u)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p H u v)
    (haTH : D.a + T < H)
    (hdelta : 0 ≤ delta) (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Summable (fun n : ℕ =>
      ‖intervalDomainPerturbationCosineCoeff
        uStar (u (D.a + r)) n‖ ^ 2) ∧
      coeffL2Norm (intervalDomainPerturbationCosineCoeff
        uStar (u (D.a + r))) ≤ 8 * delta := by
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have ht : D.a + r ∈ Set.Ioo (0 : ℝ) H := by
    constructor
    · linarith [D.a_pos, hr.1]
    · exact lt_of_le_of_lt (by linarith [hr.2]) haTH
  have hclose : ∀ x : intervalDomainPoint,
      |u (D.a + r) x - uStar| ≤ 4 * delta := by
    have hmildEq := congrFun D.mild_u r
    have htrajEq := classicalRestartTrajectoryM_eq
      (a := D.a) (h := T) (u := u) hr
    intro x
    have hc := D.close r hr.1 hr.2 x
    rw [hmildEq, htrajEq] at hc
    exact hc
  let phi : ℝ → ℝ := fun x => intervalDomainLift (u (D.a + r)) x - uStar
  have hphiCont : ContinuousOn phi (Set.Icc (0 : ℝ) 1) := by
    dsimp [phi]
    exact ((hsol.regularity.2.2.2.2.1 (D.a + r) ht).1.1.continuousOn).sub
      continuousOn_const
  have hphiMeas : AEStronglyMeasurable phi (intervalMeasure 1) :=
    (BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont).1
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1, |phi x| ≤ 4 * delta := by
    intro x hx
    dsimp [phi]
    rw [show intervalDomainLift (u (D.a + r)) x =
        u (D.a + r) ⟨x, hx⟩ by simp [intervalDomainLift, hx]]
    exact hclose ⟨x, hx⟩
  rcases cosineCoeffs_l2_norm_le_of_pointwise_abs_bound
      (mul_nonneg (by norm_num) hdelta) hphiMeas hpoint with
    ⟨hsum, hnorm⟩
  constructor
  · simpa [intervalDomainPerturbationCosineCoeff, phi,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using hsum
  · unfold coeffL2Norm coeffL2Energy
    have hnorm' := hnorm.trans_eq (by ring : 2 * (4 * delta) = 8 * delta)
    simpa [intervalDomainPerturbationCosineCoeff, phi,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using hnorm'

/-- Global-orbit wrapper for the faithful finite-horizon coefficient
estimate. -/
theorem weakRestartM_perturbationCoeff_L2
    {p : CM2Params} {uStar T delta r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainMWeakSupRestartWindowData p uStar T delta u)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hdelta : 0 ≤ delta) (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Summable (fun n : ℕ =>
      ‖intervalDomainPerturbationCosineCoeff
        uStar (u (D.a + r)) n‖ ^ 2) ∧
      coeffL2Norm (intervalDomainPerturbationCosineCoeff
        uStar (u (D.a + r))) ≤ 8 * delta := by
  let H : ℝ := D.a + T + 1
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hH : 0 < H := by dsimp [H]; linarith [D.a_pos, hT]
  have haTH : D.a + T < H := by dsimp [H]; linarith
  exact weakRestartM_perturbationCoeff_L2_of_solution D
    (hglobal H hH) haTH hdelta hr

/-- A fixed high-strong-norm ceiling at the faithful general-`m` weak-window
target. -/
def paper3WeakWindowStrongSmoothingBoundGeneralM
    (p : CM2Params) (uStar vStar T gap rho : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap rho
  let B := paper3WeakWindowNonlinearL2ConstantGeneralM p uStar vStar T heq
  1 + 2 * C * (T / 4) ^ (-rho) +
    B * restartedKernelMassPositive C rho (gap / 2)

theorem paper3WeakWindowStrongSmoothingBoundGeneralM_pos
    (p : CM2Params) {uStar vStar T gap rho : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hT : 0 < T) (hgap : 0 < gap) (hrho : 0 < rho)
    (hrho1 : rho < 1) :
    0 < paper3WeakWindowStrongSmoothingBoundGeneralM
      p uStar vStar T gap rho heq := by
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap rho
  let B := paper3WeakWindowNonlinearL2ConstantGeneralM p uStar vStar T heq
  have hC : 0 ≤ C := by
    simpa [C] using
      (unitIntervalLinearizedStrongSmoothingConstant_pos p hgap hrho).le
  have hB : 0 ≤ B := by
    simpa [B] using
      paper3WeakWindowNonlinearL2ConstantGeneralM_nonneg p heq hT
  have hmass : 0 ≤ restartedKernelMassPositive C rho (gap / 2) := by
    unfold restartedKernelMassPositive
    exact mul_nonneg hC (add_nonneg
      (one_div_nonneg.mpr (by linarith))
      (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ gap / 2) _)
        (Real.Gamma_pos_of_pos (by linarith)).le))
  have hterm1 : 0 ≤ 2 * C * (T / 4) ^ (-rho) :=
    mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.rpow_nonneg (by linarith : 0 ≤ T / 4) _)
  have hterm2 : 0 ≤ B * restartedKernelMassPositive C rho (gap / 2) :=
    mul_nonneg hB hmass
  unfold paper3WeakWindowStrongSmoothingBoundGeneralM
  dsimp only
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg zero_lt_one hterm1) hterm2

/-- Uniform faithful `X_2^rho` regularization at the fixed absolute target
time `T`.  The smoothing subwindow has length at least `T/4`, because the
weak restart begins no later than `T/4`. -/
theorem weakRestartM_target_uniform_X2Rho_of_solution
    {p : CM2Params} {uStar vStar T delta gap rho H : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainMWeakSupRestartWindowData p uStar T delta u)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p H u v)
    (haTH : D.a + T < H)
    (hdelta : 0 ≤ delta) (hdeltaStar : delta ≤ uStar / 16)
    (hdeltaOne : 4 * delta ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    IntervalDomainX2SigmaPerturbation rho uStar (u T) ∧
      intervalDomainX2SigmaDistance rho uStar (u T) ≤
        paper3WeakWindowStrongSmoothingBoundGeneralM
          p uStar vStar T gap rho heq := by
  let s0 := D.a + T / 2
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap rho
  let B := paper3WeakWindowNonlinearL2ConstantGeneralM p uStar vStar T heq
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hs0 : 0 < s0 := by dsimp [s0]; linarith [D.a_pos, hT]
  have hs0T : s0 < T := by
    dsimp [s0]
    linarith [D.a_le_quarter, hT]
  have hTH : T < H := by linarith [D.a_pos, haTH]
  have hgapTime : T / 4 ≤ T - s0 := by
    dsimp [s0]
    linarith [D.a_le_quarter]
  have hstart := weakRestartM_perturbationCoeff_L2_of_solution
    D hsol haTH hdelta
      (show T / 2 ∈ Set.Icc (0 : ℝ) T by constructor <;> linarith)
  have hNdata : ∀ s ∈ Set.Ioo s0 T,
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B := by
    intro s hs
    let rr := s - D.a
    have hrr : rr ∈ Set.Ioo (T / 2) T := by
      dsimp [rr, s0] at hs ⊢
      constructor
      · linarith [hs.1]
      · linarith [hs.2, D.a_pos]
    have hsource := weakRestartM_fullNonlinearRemainderCoeff_uniform_L2_of_solution
      D heq hsol haTH hdelta hdeltaStar hdeltaOne hrr
    have htime : D.a + rr = s := by dsimp [rr]; ring
    simpa [B, htime] using hsource
  have hstrong :=
    intervalDomainX2SigmaPerturbation_and_norm_le_of_L2_restart_generalM
      hsol hs0 hs0T hTH heq hgap hrho hrho1
        hstart.1 (fun s hs => (hNdata s hs).1)
        (paper3WeakWindowNonlinearL2ConstantGeneralM_nonneg p heq hT)
        (fun s hs => by simpa [B] using (hNdata s hs).2)
  refine ⟨hstrong.1, hstrong.2.trans ?_⟩
  have hC : 0 ≤ C := by
    simpa [C] using
      (unitIntervalLinearizedStrongSmoothingConstant_pos
        p hgap.1 hrho).le
  have hB : 0 ≤ B := by
    simpa [B] using
      paper3WeakWindowNonlinearL2ConstantGeneralM_nonneg p heq hT
  have hpow : (T - s0) ^ (-rho) ≤ (T / 4) ^ (-rho) :=
    Real.rpow_le_rpow_of_nonpos (by linarith : 0 < T / 4)
      hgapTime (by linarith)
  have hexp : Real.exp (-(gap / 2) * (T - s0)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by
      nlinarith [hgap.1, sub_nonneg.mpr hs0T.le])
  have hcoeff : coeffL2Norm
      (intervalDomainPerturbationCosineCoeff uStar (u s0)) ≤ 2 := by
    have h := hstart.2
    dsimp [s0] at h ⊢
    exact h.trans (by linarith [hdeltaOne])
  have hlinear :
      C * (T - s0) ^ (-rho) *
          Real.exp (-(gap / 2) * (T - s0)) *
            coeffL2Norm
              (intervalDomainPerturbationCosineCoeff uStar (u s0)) ≤
        2 * C * (T / 4) ^ (-rho) := by
    have hp0 : 0 ≤ (T - s0) ^ (-rho) :=
      Real.rpow_nonneg (sub_nonneg.mpr hs0T.le) _
    have hpT : 0 ≤ (T / 4) ^ (-rho) :=
      Real.rpow_nonneg (by linarith : 0 ≤ T / 4) _
    have he0 := Real.exp_nonneg (-(gap / 2) * (T - s0))
    have hc0 := coeffL2Norm_nonneg
      (intervalDomainPerturbationCosineCoeff uStar (u s0))
    calc
      _ ≤ C * (T / 4) ^ (-rho) *
          Real.exp (-(gap / 2) * (T - s0)) *
            coeffL2Norm
              (intervalDomainPerturbationCosineCoeff uStar (u s0)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hC) he0) hc0
      _ ≤ C * (T / 4) ^ (-rho) * 1 *
            coeffL2Norm
              (intervalDomainPerturbationCosineCoeff uStar (u s0)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (mul_nonneg hC hpT)) hc0
      _ ≤ C * (T / 4) ^ (-rho) * 1 * 2 := by
        exact mul_le_mul_of_nonneg_left hcoeff
          (mul_nonneg (mul_nonneg hC hpT) zero_le_one)
      _ = 2 * C * (T / 4) ^ (-rho) := by ring
  unfold paper3WeakWindowStrongSmoothingBoundGeneralM
  dsimp only
  change
    C * (T - s0) ^ (-rho) * Real.exp (-(gap / 2) * (T - s0)) *
          coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u s0)) +
        B * restartedKernelMassPositive C rho (gap / 2) ≤
      1 + 2 * C * (T / 4) ^ (-rho) +
        B * restartedKernelMassPositive C rho (gap / 2)
  calc
    _ ≤ 2 * C * (T / 4) ^ (-rho) +
        B * restartedKernelMassPositive C rho (gap / 2) :=
      add_le_add hlinear le_rfl
    _ ≤ 1 + 2 * C * (T / 4) ^ (-rho) +
        B * restartedKernelMassPositive C rho (gap / 2) := by linarith

/-- Global-orbit wrapper for faithful finite-window strong smoothing. -/
theorem weakRestartM_target_uniform_X2Rho
    {p : CM2Params} {uStar vStar T delta gap rho : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainMWeakSupRestartWindowData p uStar T delta u)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hdelta : 0 ≤ delta) (hdeltaStar : delta ≤ uStar / 16)
    (hdeltaOne : 4 * delta ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    IntervalDomainX2SigmaPerturbation rho uStar (u T) ∧
      intervalDomainX2SigmaDistance rho uStar (u T) ≤
        paper3WeakWindowStrongSmoothingBoundGeneralM
          p uStar vStar T gap rho heq := by
  let H : ℝ := D.a + T + 1
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hH : 0 < H := by dsimp [H]; linarith [D.a_pos, hT]
  have haTH : D.a + T < H := by dsimp [H]; linarith
  exact weakRestartM_target_uniform_X2Rho_of_solution
    D heq hgap (hglobal H hH) haTH hdelta hdeltaStar hdeltaOne hrho hrho1

#print axioms weakRestartM_perturbationCoeff_L2
#print axioms weakRestartM_perturbationCoeff_L2_of_solution
#print axioms paper3WeakWindowStrongSmoothingBoundGeneralM_pos
#print axioms weakRestartM_target_uniform_X2Rho
#print axioms weakRestartM_target_uniform_X2Rho_of_solution

end

end ShenWork.Paper3
