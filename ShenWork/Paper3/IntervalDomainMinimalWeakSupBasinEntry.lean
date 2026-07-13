/- Weak-sup basin entry on the physical-mass hyperplane of the minimal model. -/
import ShenWork.Paper3.IntervalDomainWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainMinimalStrongDuhamelL2Start

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Uniform strong regularization at the end of a weak restart window on the
physical-mass hyperplane.  The zeroth Fourier coefficient is absent from both
the datum and the source, so the nonzero-mode spectral gap is sufficient. -/
theorem weakRestart_target_uniform_mass_X2Rho_of_solution
    {p : CM2Params} {uStar vStar T delta gap rho H : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (haTH : D.a + T < H)
    (hdelta : 0 ≤ delta) (hdeltaStar : delta ≤ uStar / 16)
    (hdeltaOne : 4 * delta ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    IntervalDomainX2SigmaPerturbation rho uStar (u T) ∧
      intervalDomainX2SigmaDistance rho uStar (u T) ≤
        paper3WeakWindowStrongSmoothingBound
          p uStar vStar T gap rho heq := by
  let s0 := D.a + T / 2
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap rho
  let B := paper3WeakWindowNonlinearL2Constant p uStar vStar T heq
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hs0 : 0 < s0 := by dsimp [s0]; linarith [D.a_pos, hT]
  have hs0T : s0 < T := by
    dsimp [s0]
    linarith [D.a_le_quarter, hT]
  have hTH : T < H := by linarith [D.a_pos, haTH]
  have hgapTime : T / 4 ≤ T - s0 := by
    dsimp [s0]
    linarith [D.a_le_quarter]
  have hstart := weakRestart_perturbationCoeff_L2_of_solution
    D hm hsol haTH hdelta
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
    have hsource := weakRestart_fullNonlinearRemainderCoeff_uniform_L2_of_solution
      D hm heq hsol haTH hdelta hdeltaStar hdeltaOne hrr
    have htime : D.a + rr = s := by dsimp [rr]; ring
    simpa [B, htime] using hsource
  have hstrong :=
    intervalDomainMassX2SigmaPerturbation_and_norm_le_of_L2_restart
      hsol hm ha0 hb0 hs0 hs0T hTH heq hgap hrho hrho1 hmass
        hstart.1 (fun s hs => (hNdata s hs).1)
        (paper3WeakWindowNonlinearL2Constant_nonneg p heq hT)
        (fun s hs => by simpa [B] using (hNdata s hs).2)
  refine ⟨hstrong.1, hstrong.2.trans ?_⟩
  have hC : 0 ≤ C := by
    simpa [C] using
      (unitIntervalLinearizedStrongSmoothingConstant_pos
        p hgap.1 hrho).le
  have hB : 0 ≤ B := by
    simpa [B] using paper3WeakWindowNonlinearL2Constant_nonneg p heq hT
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
  unfold paper3WeakWindowStrongSmoothingBound
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

/-- Global-orbit wrapper for mass-constrained finite-window smoothing. -/
theorem weakRestart_target_uniform_mass_X2Rho
    {p : CM2Params} {uStar vStar T delta gap rho : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hdelta : 0 ≤ delta) (hdeltaStar : delta ≤ uStar / 16)
    (hdeltaOne : 4 * delta ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    IntervalDomainX2SigmaPerturbation rho uStar (u T) ∧
      intervalDomainX2SigmaDistance rho uStar (u T) ≤
        paper3WeakWindowStrongSmoothingBound
          p uStar vStar T gap rho heq := by
  let H : ℝ := D.a + T + 1
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hH : 0 < H := by dsimp [H]; linarith [D.a_pos, hT]
  have haTH : D.a + T < H := by dsimp [H]; linarith
  exact weakRestart_target_uniform_mass_X2Rho_of_solution
    D hm ha0 hb0 heq hgap hmass (hglobal H hH) haTH
      hdelta hdeltaStar hdeltaOne hrho hrho1

/-- Positivity of the shared explicit basin radius requires only positivity
of the relevant (full or mass-constrained) spectral gap. -/
theorem paper3WeakSupBasinDelta_pos_of_gap_pos
    (p : CM2Params) {sigma uStar vStar T gap : ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : 0 < gap) (hT : 0 < T) :
    0 < paper3WeakSupBasinDelta p sigma uStar vStar T gap heq := by
  let rho := (sigma + 1) / 2
  let theta := sigma / rho
  let q := 1 - theta
  let H := paper3WeakWindowStrongSmoothingBound
    p uStar vStar T gap rho heq
  let R := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  have hsigma : 0 < sigma := by linarith
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hsigmaRho : sigma < rho := by dsimp [rho]; linarith
  have hrho1 : rho < 1 := by dsimp [rho]; linarith
  have htheta : 0 < theta := div_pos hsigma hrho
  have htheta1 : theta < 1 := (div_lt_one hrho).2 hsigmaRho
  have hq : 0 < q := by dsimp [q]; linarith
  have hH : 0 < H := by
    simpa [H] using paper3WeakWindowStrongSmoothingBound_pos
      p heq hT hgap hrho hrho1
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap hsigma hsigma1
  have hHpow : 0 ≤ H ^ theta := Real.rpow_nonneg hH.le _
  have hratio : 0 < (R / 2) / (1 + H ^ theta) := by positivity
  have hroot : 0 < ((R / 2) / (1 + H ^ theta)) ^ (1 / q) :=
    Real.rpow_pos_of_pos hratio _
  unfold paper3WeakSupBasinDelta
  dsimp only
  exact lt_min (div_pos heq.u_pos (by norm_num))
    (lt_min (by norm_num) (div_pos hroot (by norm_num)))

/-- The shared explicit radius satisfies the interpolation inequality for any
positive spectral gap, including the nonzero-mode gap of the minimal model. -/
theorem paper3WeakSupBasinDelta_interpolation_bound_of_gap_pos
    (p : CM2Params) {sigma uStar vStar T gap : ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : 0 < gap) (hT : 0 < T) :
    let rho := (sigma + 1) / 2
    let theta := sigma / rho
    let q := 1 - theta
    let H := paper3WeakWindowStrongSmoothingBound
      p uStar vStar T gap rho heq
    let R := intervalDomainStrongBootstrapRadius
      p sigma uStar vStar gap heq
    (8 * paper3WeakSupBasinDelta p sigma uStar vStar T gap heq) ^ q *
        H ^ theta ≤ R / 2 := by
  dsimp only
  let rho := (sigma + 1) / 2
  let theta := sigma / rho
  let q := 1 - theta
  let H := paper3WeakWindowStrongSmoothingBound
    p uStar vStar T gap rho heq
  let R := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let delta := paper3WeakSupBasinDelta p sigma uStar vStar T gap heq
  have hsigma : 0 < sigma := by linarith
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hsigmaRho : sigma < rho := by dsimp [rho]; linarith
  have hrho1 : rho < 1 := by dsimp [rho]; linarith
  have htheta : 0 < theta := div_pos hsigma hrho
  have htheta1 : theta < 1 := (div_lt_one hrho).2 hsigmaRho
  have hq : 0 < q := by dsimp [q]; linarith
  have hH : 0 < H := by
    simpa [H] using paper3WeakWindowStrongSmoothingBound_pos
      p heq hT hgap hrho hrho1
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap hsigma hsigma1
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDelta_pos_of_gap_pos
      p hsigmaStrong hsigma1 heq hgap hT
  let E := H ^ theta
  have hE : 0 ≤ E := Real.rpow_nonneg hH.le _
  let ratio := (R / 2) / (1 + E)
  have hratio : 0 < ratio := by dsimp [ratio]; positivity
  let root := ratio ^ (1 / q)
  have hroot : 0 < root := Real.rpow_pos_of_pos hratio _
  have hdeltaRoot : 8 * delta ≤ root := by
    have hle : delta ≤ root / 8 := by
      dsimp [delta, paper3WeakSupBasinDelta]
      exact (min_le_right _ _).trans (min_le_right _ _)
    nlinarith
  have hpow : (8 * delta) ^ q ≤ root ^ q :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) hdelta.le)
      hdeltaRoot hq.le
  have hrootPow : root ^ q = ratio := by
    dsimp [root]
    rw [← Real.rpow_mul hratio.le]
    have hmul : (1 / q) * q = 1 := by field_simp [hq.ne']
    rw [hmul, Real.rpow_one]
  calc
    (8 * delta) ^ q * H ^ theta = (8 * delta) ^ q * E := by rfl
    _ ≤ root ^ q * E := mul_le_mul_of_nonneg_right hpow hE
    _ = ratio * E := by rw [hrootPow]
    _ ≤ ratio * (1 + E) :=
      mul_le_mul_of_nonneg_left (by linarith) hratio.le
    _ = R / 2 := by
      dsimp [ratio]
      field_simp [show (1 + E) ≠ 0 by positivity]

/-- Weak-sup entry into the strong bootstrap ball for the minimal model on
the physical-mass hyperplane. -/
theorem intervalDomainMassSupToStrongBasinEntry_proved
    (p : CM2Params) {sigma uStar vStar gap : ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap) :
    ∃ delta > 0, ∃ T > 0,
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        SupCloseToConstant intervalDomain u₀ uStar delta →
        ∀ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v →
          InitialTrace intervalDomain u₀ u →
          HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
            IntervalDomainX2SigmaPerturbation sigma uStar (u T) ∧
            intervalDomainX2SigmaDistance sigma uStar (u T) ≤
              intervalDomainStrongBootstrapRadius
                p sigma uStar vStar gap heq / 2 := by
  obtain ⟨T, hT, hwindow⟩ :=
    exists_intervalDomainWeakSupRestartWindow p hm heq
  let rho := (sigma + 1) / 2
  let theta := sigma / rho
  let q := 1 - theta
  let Hbound := paper3WeakWindowStrongSmoothingBound
    p uStar vStar T gap rho heq
  let R := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let delta := paper3WeakSupBasinDelta p sigma uStar vStar T gap heq
  have hsigma : 0 < sigma := by linarith
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hsigmaRho : sigma < rho := by dsimp [rho]; linarith
  have hrho1 : rho < 1 := by dsimp [rho]; linarith
  have htheta : 0 < theta := div_pos hsigma hrho
  have htheta1 : theta < 1 := (div_lt_one hrho).2 hsigmaRho
  have hq : 0 < q := by dsimp [q]; linarith
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDelta_pos_of_gap_pos
      p hsigmaStrong hsigma1 heq hgap.1 hT
  have hdeltaStar : delta ≤ uStar / 16 := by
    simpa [delta] using paper3WeakSupBasinDelta_le_equilibrium
      p sigma uStar vStar T gap heq
  have hdeltaQuarter : delta ≤ 1 / 4 := by
    simpa [delta] using paper3WeakSupBasinDelta_le_quarter
      p sigma uStar vStar T gap heq
  have hdeltaOne : 4 * delta ≤ 1 := by linarith
  have hHbound : 0 < Hbound := by
    simpa [Hbound] using paper3WeakWindowStrongSmoothingBound_pos
      p heq hT hgap.1 hrho hrho1
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap.1 hsigma hsigma1
  refine ⟨delta, hdelta, T, hT, ?_⟩
  intro u₀ hu₀ hclose u v hglobal htrace hmass
  rcases hwindow delta hdelta hdeltaStar u₀ hu₀ hclose
      u v hglobal htrace with ⟨D⟩
  have hhigh := weakRestart_target_uniform_mass_X2Rho
    D hm ha0 hb0 heq hgap hmass hglobal hdelta.le hdeltaStar
      hdeltaOne hrho hrho1
  let rtarget := T - D.a
  have htargetMem : rtarget ∈ Set.Icc (0 : ℝ) T := by
    dsimp [rtarget]
    constructor
    · linarith [D.a_le_quarter, hT]
    · linarith [D.a_pos]
  have htarget0Raw := weakRestart_perturbationCoeff_L2
    D hm hglobal hdelta.le htargetMem
  have htarget0 :
      Summable (fun n : ℕ =>
        ‖intervalDomainPerturbationCosineCoeff uStar (u T) n‖ ^ 2) ∧
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ≤
        8 * delta := by
    simpa [rtarget] using htarget0Raw
  have hinterpEnergy := fractionalPowerEnergy_interpolation
    hsigma hsigmaRho htarget0.1 hhigh.1
  have hmem : IntervalDomainX2SigmaPerturbation sigma uStar (u T) := by
    simpa [IntervalDomainX2SigmaPerturbation] using hinterpEnergy.1
  have hinterp := fractionalPowerNorm_interpolation
    hsigma hsigmaRho htarget0.1 hhigh.1
  have hcoeffPow :
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q ≤
        (8 * delta) ^ q :=
    Real.rpow_le_rpow (coeffL2Norm_nonneg _) htarget0.2 hq.le
  have hhighPow :
      intervalDomainX2SigmaDistance rho uStar (u T) ^ theta ≤
        Hbound ^ theta :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _)
      (by simpa [Hbound] using hhigh.2) htheta.le
  have hproduct :
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q *
          intervalDomainX2SigmaDistance rho uStar (u T) ^ theta ≤
        (8 * delta) ^ q * Hbound ^ theta :=
    mul_le_mul hcoeffPow hhighPow
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) hdelta.le) _)
  have hchosen : (8 * delta) ^ q * Hbound ^ theta ≤ R / 2 := by
    simpa [delta, rho, theta, q, Hbound, R] using
      paper3WeakSupBasinDelta_interpolation_bound_of_gap_pos
        p hsigmaStrong hsigma1 heq hgap.1 hT
  refine ⟨hmem, ?_⟩
  calc
    intervalDomainX2SigmaDistance sigma uStar (u T) ≤
        coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q *
          intervalDomainX2SigmaDistance rho uStar (u T) ^ theta := by
      simpa [intervalDomainX2SigmaDistance, q, theta] using hinterp
    _ ≤ (8 * delta) ^ q * Hbound ^ theta := hproduct
    _ ≤ R / 2 := hchosen
    _ = intervalDomainStrongBootstrapRadius
        p sigma uStar vStar gap heq / 2 := by rfl

#print axioms weakRestart_target_uniform_mass_X2Rho_of_solution
#print axioms weakRestart_target_uniform_mass_X2Rho
#print axioms paper3WeakSupBasinDelta_pos_of_gap_pos
#print axioms paper3WeakSupBasinDelta_interpolation_bound_of_gap_pos
#print axioms intervalDomainMassSupToStrongBasinEntry_proved

end

end ShenWork.Paper3
