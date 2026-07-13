/- Weak-sup basin entry into the strong Stage-A neighborhood. -/
import ShenWork.PDE.FractionalPowerInterpolation
import ShenWork.Paper3.IntervalDomainWeakWindowStrongSmoothing
import ShenWork.Paper3.IntervalDomainStrongStageB

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

/-- Explicit weak-data radius which enters half of the strong bootstrap ball
after the fixed smoothing time. -/
def paper3WeakSupBasinDelta
    (p : CM2Params) (sigma uStar vStar T gap : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let rho := (sigma + 1) / 2
  let theta := sigma / rho
  let q := 1 - theta
  let H := paper3WeakWindowStrongSmoothingBound
    p uStar vStar T gap rho heq
  let R := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  min (uStar / 16) (min (1 / 4)
    (((R / 2) / (1 + H ^ theta)) ^ (1 / q) / 8))

theorem paper3WeakSupBasinDelta_pos
    (p : CM2Params) {sigma uStar vStar T gap : ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hT : 0 < T) :
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
      p heq hT hgap.1 hrho hrho1
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap.1 hsigma hsigma1
  have hHpow : 0 ≤ H ^ theta := Real.rpow_nonneg hH.le _
  have hratio : 0 < (R / 2) / (1 + H ^ theta) := by positivity
  have hroot : 0 < ((R / 2) / (1 + H ^ theta)) ^ (1 / q) :=
    Real.rpow_pos_of_pos hratio _
  unfold paper3WeakSupBasinDelta
  dsimp only
  exact lt_min (div_pos heq.u_pos (by norm_num))
    (lt_min (by norm_num) (div_pos hroot (by norm_num)))

theorem paper3WeakSupBasinDelta_le_equilibrium
    (p : CM2Params) (sigma uStar vStar T gap : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    paper3WeakSupBasinDelta p sigma uStar vStar T gap heq ≤ uStar / 16 :=
  min_le_left _ _

theorem paper3WeakSupBasinDelta_le_quarter
    (p : CM2Params) (sigma uStar vStar T gap : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    paper3WeakSupBasinDelta p sigma uStar vStar T gap heq ≤ 1 / 4 :=
  (min_le_right _ _).trans (min_le_left _ _)

/-- The explicit radius makes the interpolation product no larger than half
of the strong bootstrap radius. -/
theorem paper3WeakSupBasinDelta_interpolation_bound
    (p : CM2Params) {sigma uStar vStar T gap : ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hT : 0 < T) :
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
      p heq hT hgap.1 hrho hrho1
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap.1 hsigma hsigma1
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDelta_pos
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

/-- Stage B basin entry is fully discharged from the weak restart window,
uniform positive-time smoothing, and Hilbert-scale interpolation. -/
theorem intervalDomainSupToStrongBasinEntry_proved
    (p : CM2Params) : IntervalDomainSupToStrongBasinEntry p := by
  intro sigma uStar vStar gap hsigmaStrong hsigma1 hm heq hgap
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
    simpa [delta] using paper3WeakSupBasinDelta_pos
      p hsigmaStrong hsigma1 heq hgap hT
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
  intro u₀ hu₀ hclose u v hglobal htrace
  rcases hwindow delta hdelta hdeltaStar u₀ hu₀ hclose
      u v hglobal htrace with ⟨D⟩
  have hhigh := weakRestart_target_uniform_X2Rho
    D hm heq hgap hglobal hdelta.le hdeltaStar hdeltaOne hrho hrho1
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
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (by simpa [Hbound] using hhigh.2)
      htheta.le
  have hproduct :
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q *
          intervalDomainX2SigmaDistance rho uStar (u T) ^ theta ≤
        (8 * delta) ^ q * Hbound ^ theta :=
    mul_le_mul hcoeffPow hhighPow
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) hdelta.le) _)
  have hchosen : (8 * delta) ^ q * Hbound ^ theta ≤ R / 2 := by
    simpa [delta, rho, theta, q, Hbound, R] using
      paper3WeakSupBasinDelta_interpolation_bound
        p hsigmaStrong hsigma1 heq hgap hT
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

#print axioms paper3WeakSupBasinDelta_pos
#print axioms paper3WeakSupBasinDelta_interpolation_bound
#print axioms intervalDomainSupToStrongBasinEntry_proved

end

end ShenWork.Paper3
