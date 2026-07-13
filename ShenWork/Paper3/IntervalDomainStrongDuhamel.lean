/- Strong-space Bochner realization of the full-mode Paper3 Duhamel formula. -/
import ShenWork.PDE.WeightedCoefficientDuhamel
import ShenWork.PDE.RestartedMildSmoothing
import ShenWork.Paper3.IntervalDomainFullModeDuhamel
import ShenWork.Paper3.IntervalDomainLinearizedNormSmoothing
import ShenWork.Paper3.IntervalDomainStrongSliceNonlinearEstimate

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The physical perturbation coefficient agrees with the modal coefficient
used in the faithful PDE restart formula. -/
theorem paper3PerturbationCoeffM_eq_cosineCoeff_sub_const
    {u : ℝ → intervalDomainPoint → ℝ} {t uStar : ℝ} (n : ℕ)
    (hphi : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x - uStar) volume 0 1) :
    paper3PerturbationCoeffM u uStar t n =
      cosineCoeffs (fun x => intervalDomainLift (u t) x - uStar) n := by
  let phi : ℝ → ℝ := fun x => intervalDomainLift (u t) x - uStar
  have hconst : IntervalIntegrable (fun _ : ℝ => uStar) volume 0 1 :=
    intervalIntegrable_const
  have hadd := cosineCoeffs_add_of_intervalIntegrable n hphi hconst
  have hpoint : ∀ x, phi x + uStar = intervalDomainLift (u t) x := by
    intro x
    simp [phi]
  rw [paper3PerturbationCoeffM]
  change cosineCoeffs (intervalDomainLift (u t)) n -
      paper3EquilibriumCosineCoeff uStar n = cosineCoeffs phi n
  have heq : cosineCoeffs (intervalDomainLift (u t)) n =
      cosineCoeffs (fun x => phi x + uStar) n := by
    apply congrArg (fun f : ℝ → ℝ => cosineCoeffs f n)
    funext x
    exact (hpoint x).symm
  rw [heq, hadd]
  have hc := ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const
    uStar n
  unfold paper3EquilibriumCosineCoeff
  rw [← hc]
  ring

/-- Full nonlinear coefficient, viewed in the complex coefficient space and
cut off outside the open restart window.  Endpoint replacement is essential:
the `L² -> X^sigma` smoothing factor is singular at `s=t`, while a single
endpoint has no effect on the interval integral. -/
def paper3WindowedNonlinearCoeff
    (p : CM2Params) (uStar vStar a t : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (n : ℕ) : ℂ :=
  if s ∈ Set.Ioo a t then
    ((paper3FullModeNonlinearRemainderCoeffM
      p uStar vStar u v s n : ℝ) : ℂ)
  else 0

/-- The windowed full nonlinear source is in `X_2^sigma` after propagation
for every time argument.  Inside the window this is the full-mode
`L² -> X^sigma` estimate; outside it the source is zero. -/
noncomputable def paper3WindowedNonlinearCoeff_X2SigmaSummable
    (p : CM2Params) {uStar vStar gap sigma a t : ℝ}
    (u v : ℝ → intervalDomainPoint → ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (s : ℝ) :
    Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma
      (diagonalSemigroupCoeff
        (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
        (paper3WindowedNonlinearCoeff p uStar vStar a t u v s)) n := by
  by_cases hs : s ∈ Set.Ioo a t
  · have hsource :
        paper3WindowedNonlinearCoeff p uStar vStar a t u v s =
          fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v s n : ℝ) : ℂ) := by
      funext n
      simp [paper3WindowedNonlinearCoeff, hs]
    rw [hsource]
    exact unitIntervalLinearized_fractionalPower_summable_full
      p heq hgap hsigma (sub_pos.mpr hs.2) (hN s hs)
  · have hsource :
        paper3WindowedNonlinearCoeff p uStar vStar a t u v s = 0 := by
      funext n
      simp [paper3WindowedNonlinearCoeff, hs]
    rw [hsource]
    simp [diagonalSemigroupCoeff, fractionalPowerEnergyTerm]

/-- The complete weighted coefficient-space Duhamel integrand on a positive
restart window. -/
def paper3StrongDuhamelIntegrand
    (p : CM2Params) {uStar vStar gap sigma a t : ℝ}
    (u v : ℝ → intervalDomainPoint → ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (s : ℝ) : CoeffL2 :=
  weightedCoeffToLp 1 sigma
    (diagonalSemigroupCoeff
      (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
      (paper3WindowedNonlinearCoeff p uStar vStar a t u v s))
    (paper3WindowedNonlinearCoeff_X2SigmaSummable
      p u v heq hgap hsigma hN s)

/-- On a compact positive restart window, an `L²` bound for the physical
nonlinearity makes the singular strong-space Duhamel integrand Bochner
integrable.  The singularity is exactly `(t-s)^(-sigma)` and is integrable
because `sigma<1`. -/
theorem paper3StrongDuhamelIntegrand_intervalIntegrable
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hB : 0 ≤ B)
    (hNnorm : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B) :
    IntervalIntegrable
      (paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN)
      volume a t := by
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  let major : ℝ → ℝ := fun s =>
    B * ShenWork.PDE.restartedSmoothingKernel C sigma (gap / 2) (t - s)
  have hC : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap.1 hsigma
  have hkernel : IntervalIntegrable
      (ShenWork.PDE.restartedSmoothingKernel C sigma (gap / 2))
      volume 0 (t - a) :=
    ShenWork.PDE.restartedSmoothingKernel_intervalIntegrable_positive
      hsigma hsigma1 (by linarith [hgap.1]) (sub_nonneg.mpr hat)
  have hkernelComp : IntervalIntegrable
      (fun s => ShenWork.PDE.restartedSmoothingKernel
        C sigma (gap / 2) (t - s)) volume a t := by
    simpa using (hkernel.comp_sub_left t).symm
  have hmajor : IntervalIntegrable major volume a t := by
    simpa [major] using hkernelComp.const_mul B
  have hcoordAE : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => weightedCoeffSequence 1 sigma
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
          (paper3WindowedNonlinearCoeff p uStar vStar a t u v s)) n)
      (volume.restrict (Set.Ioo a t)) := by
    intro n
    let actual : ℝ → ℂ := fun s => weightedCoeffSequence 1 sigma
      (diagonalSemigroupCoeff
        (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
        (fun k => ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s k : ℝ) : ℂ))) n
    have hrem := paper3FullModeNonlinearRemainderCoeffM_continuousOn
      (uStar := uStar) (vStar := vStar) hsolM ha hat htT n
    have hremC : ContinuousOn
        (fun s => ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) (Set.Icc a t) :=
      Complex.continuous_ofReal.comp_continuousOn hrem
    have hactual : ContinuousOn actual (Set.Icc a t) := by
      unfold actual weightedCoeffSequence diagonalSemigroupCoeff
      exact continuousOn_const.mul ((by fun_prop : Continuous
        (fun s : ℝ =>
          ((Real.exp ((t - s) *
            unitIntervalLinearizedGrowth p uStar vStar n) : ℝ) : ℂ))).continuousOn.mul
          hremC)
    have haeActual : AEStronglyMeasurable actual
        (volume.restrict (Set.Ioo a t)) :=
      (hactual.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioo
    refine haeActual.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp [actual, weightedCoeffSequence, diagonalSemigroupCoeff,
      paper3WindowedNonlinearCoeff, hs]
  have hAE : AEStronglyMeasurable
      (paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN)
      (volume.restrict (Set.Ioo a t)) := by
    exact aestronglyMeasurable_weightedCoeffToLp_of_ae
      1 sigma
      (fun s => diagonalSemigroupCoeff
        (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
        (paper3WindowedNonlinearCoeff p uStar vStar a t u v s))
      (paper3WindowedNonlinearCoeff_X2SigmaSummable
        p u v heq hgap hsigma hN) hcoordAE
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hat]
  apply Integrable.mono'
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hat).mp hmajor) hAE
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hst : 0 < t - s := sub_pos.mpr hs.2
  have hsmooth := unitIntervalLinearized_fractionalPowerNorm_le_full
    p heq hgap hsigma hst (hN s hs)
  have hsourceEq :
      paper3WindowedNonlinearCoeff p uStar vStar a t u v s =
        fun n => ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ) := by
    funext n
    simp [paper3WindowedNonlinearCoeff, hs]
  have hnorm : ‖paper3StrongDuhamelIntegrand
      p u v heq hgap hsigma hN s‖ ≤
      C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) * B := by
    rw [show ‖paper3StrongDuhamelIntegrand
          p u v heq hgap hsigma hN s‖ =
        Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
            (paper3WindowedNonlinearCoeff
              p uStar vStar a t u v s)) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    rw [hsourceEq]
    exact hsmooth.trans (mul_le_mul_of_nonneg_left (hNnorm s hs)
      (mul_nonneg
        (mul_nonneg hC.le (Real.rpow_nonneg hst.le _))
        (Real.exp_nonneg _)))
  calc
    ‖paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN s‖ ≤
        C * (t - s) ^ (-sigma) *
          Real.exp (-(gap / 2) * (t - s)) * B := hnorm
    _ ≤ major s := by
      dsimp [major, ShenWork.PDE.restartedSmoothingKernel]
      have hrpow : 0 ≤ (t - s) ^ (-sigma) := Real.rpow_nonneg hst.le _
      have hexp : 0 ≤ Real.exp (-(gap / 2) * (t - s)) := Real.exp_nonneg _
      nlinarith [mul_nonneg hC.le hexp,
        mul_nonneg (add_nonneg zero_le_one hrpow) hexp,
        mul_nonneg hB (mul_nonneg hC.le hexp)]

/-- Pointwise strong-space smoothing bound for the exact Duhamel integrand.
At the terminal endpoint the windowed integrand is zero; on the open window
this is the full-mode `L² -> X^sigma` estimate. -/
theorem paper3StrongDuhamelIntegrand_norm_le
    (p : CM2Params) {a t sigma uStar vStar gap s : ℝ}
    (u v : ℝ → intervalDomainPoint → ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hN : ∀ r ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v r n : ℝ) : ℂ)‖ ^ 2)
    (hs : s ∈ Set.Ioc a t) :
    ‖paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN s‖ ≤
      unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma *
        (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
          coeffL2Norm (fun n =>
            ((paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s n : ℝ) : ℂ)) := by
  by_cases hst : s = t
  · subst s
    have hnot : t ∉ Set.Ioo a t := by simp
    have hintegrand : paper3StrongDuhamelIntegrand
        p u v heq hgap hsigma hN t = 0 := by
      ext n
      change paper3StrongDuhamelIntegrand
        p u v heq hgap hsigma hN t n = (0 : ℂ)
      simp [paper3StrongDuhamelIntegrand, weightedCoeffSequence,
        diagonalSemigroupCoeff, paper3WindowedNonlinearCoeff, hnot]
    rw [hintegrand, norm_zero]
    simp only [sub_self]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (unitIntervalLinearizedStrongSmoothingConstant_pos
            p hgap.1 hsigma).le
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) _))
        (Real.exp_nonneg _))
      (coeffL2Norm_nonneg _)
  · have hsopen : s ∈ Set.Ioo a t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hsmooth := unitIntervalLinearized_fractionalPowerNorm_le_full
      p heq hgap hsigma (sub_pos.mpr hsopen.2) (hN s hsopen)
    have hsourceEq :
        paper3WindowedNonlinearCoeff p uStar vStar a t u v s =
          fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v s n : ℝ) : ℂ) := by
      funext n
      simp [paper3WindowedNonlinearCoeff, hsopen]
    rw [show ‖paper3StrongDuhamelIntegrand
          p u v heq hgap hsigma hN s‖ =
        Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
            (paper3WindowedNonlinearCoeff
              p uStar vStar a t u v s)) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    rw [hsourceEq]
    exact hsmooth

/-- Exact positive-time restart formula in the complete strong coefficient
space.  The only remaining Bochner premise is interval integrability of the
explicit integrand; it is discharged quantitatively below. -/
theorem paper3StrongDuhamel_restart_eq
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hma : IntervalDomainX2SigmaPerturbation sigma uStar (u a))
    (hmt : IntervalDomainX2SigmaPerturbation sigma uStar (u t))
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hint : IntervalIntegrable
      (paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN)
      volume a t) :
    weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) hmt =
      weightedCoeffToLp 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
            (intervalDomainPerturbationCosineCoeff uStar (u a)))
          (unitIntervalLinearized_fractionalPower_summable_exp
            p hgap (sub_nonneg.mpr hat) hma) +
        ∫ s in a..t,
          paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN s := by
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have haT : a < T := lt_of_le_of_lt hat htT
  have ht0 : 0 < t := lt_of_lt_of_le ha hat
  have hphiA : IntervalIntegrable
      (fun x => intervalDomainLift (u a) x - uStar) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hsol.regularity.2.2.2.2.1 a ⟨ha, haT⟩).1.1.continuousOn).sub
      continuousOn_const
  have hphiT : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x - uStar) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1.continuousOn).sub
      continuousOn_const
  apply weightedCoeffToLp_mild_eq
    (hsource := paper3WindowedNonlinearCoeff_X2SigmaSummable
      p u v heq hgap hsigma hN)
    (hint := hint)
  intro n
  have hmodal := paper3PerturbationCoeffM_full_restart
    (uStar := uStar) (vStar := vStar) hsolM ha hat htT n
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hmodal
  push_cast at hcast
  rw [← intervalIntegral.integral_ofReal] at hcast
  have hwindow :
      (∫ s in a..t,
        diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
          (paper3WindowedNonlinearCoeff p uStar vStar a t u v s) n) =
      ∫ s in a..t,
        ((Real.exp ((t - s) *
              unitIntervalLinearizedGrowth p uStar vStar n) *
            paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s n : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne t] with s hst hs
    rw [Set.uIoc_of_le hat] at hs
    have hsopen : s ∈ Set.Ioo a t := ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    simp [diagonalSemigroupCoeff, paper3WindowedNonlinearCoeff, hsopen]
  rw [hwindow]
  unfold intervalDomainPerturbationCosineCoeff
  unfold diagonalSemigroupCoeff
  simp only
  rw [← paper3PerturbationCoeffM_eq_cosineCoeff_sub_const n hphiT,
    ← paper3PerturbationCoeffM_eq_cosineCoeff_sub_const n hphiA]
  simpa [diagonalSemigroupCoeff] using hcast

/-- The exact restart identity yields the singular quadratic strong-norm
Duhamel inequality used by the weighted bootstrap.  `B` is only a qualitative
local bound needed to establish Bochner integrability; the displayed estimate
uses the sharper trajectory-dependent quadratic bound. -/
theorem paper3StrongDuhamel_restart_quadratic_norm_le
    {p : CM2Params} {T a t sigma uStar vStar gap B K : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {size : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hma : IntervalDomainX2SigmaPerturbation sigma uStar (u a))
    (hmt : IntervalDomainX2SigmaPerturbation sigma uStar (u t))
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hB : 0 ≤ B)
    (hNnormB : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B)
    (hK : 0 ≤ K)
    (hNquad : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ K * size s ^ 2)
    (hquadInt : IntervalIntegrable
      (fun s =>
        unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma *
          (t - s) ^ (-sigma) *
          Real.exp (-(gap / 2) * (t - s)) * (K * size s ^ 2))
      volume a t) :
    intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      Real.exp (-gap * (t - a)) *
          intervalDomainX2SigmaDistance sigma uStar (u a) +
        ∫ s in a..t,
          unitIntervalLinearizedStrongSmoothingConstant
              p uStar vStar gap sigma *
            (t - s) ^ (-sigma) *
            Real.exp (-(gap / 2) * (t - s)) * (K * size s ^ 2) := by
  have hint := paper3StrongDuhamelIntegrand_intervalIntegrable
    hsol hm ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  have hmild := paper3StrongDuhamel_restart_eq
    hsol hm ha hat htT heq hgap hsigma hma hmt hN hint
  let linear : CoeffL2 := weightedCoeffToLp 1 sigma
    (diagonalSemigroupCoeff
      (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
      (intervalDomainPerturbationCosineCoeff uStar (u a)))
    (unitIntervalLinearized_fractionalPower_summable_exp
      p hgap (sub_nonneg.mpr hat) hma)
  have hlinear : ‖linear‖ ≤ Real.exp (-gap * (t - a)) *
      intervalDomainX2SigmaDistance sigma uStar (u a) := by
    rw [show ‖linear‖ = Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
            (intervalDomainPerturbationCosineCoeff uStar (u a))) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    simpa [intervalDomainX2SigmaDistance] using
      unitIntervalLinearized_fractionalPowerNorm_le_exp
        p hgap (sub_nonneg.mpr hat) hma
  have hintegral :
      ‖∫ s in a..t,
          paper3StrongDuhamelIntegrand p u v heq hgap hsigma hN s‖ ≤
        ∫ s in a..t,
          unitIntervalLinearizedStrongSmoothingConstant
              p uStar vStar gap sigma *
            (t - s) ^ (-sigma) *
            Real.exp (-(gap / 2) * (t - s)) * (K * size s ^ 2) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hat
      (Filter.Eventually.of_forall fun s hs => ?_) hquadInt
    by_cases hst : s = t
    · subst s
      have hnot : t ∉ Set.Ioo a t := by simp
      have hintegrand : paper3StrongDuhamelIntegrand
          p u v heq hgap hsigma hN t = 0 := by
        ext n
        change paper3StrongDuhamelIntegrand
          p u v heq hgap hsigma hN t n = (0 : ℂ)
        simp [paper3StrongDuhamelIntegrand, weightedCoeffSequence,
          diagonalSemigroupCoeff, paper3WindowedNonlinearCoeff, hnot]
      rw [hintegrand, norm_zero]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (unitIntervalLinearizedStrongSmoothingConstant_pos
              p hgap.1 hsigma).le
            (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
          (Real.exp_nonneg _))
        (mul_nonneg hK (sq_nonneg _))
    · have hsopen : s ∈ Set.Ioo a t :=
        ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
      have hsmooth := paper3StrongDuhamelIntegrand_norm_le
        p u v heq hgap hsigma hN hs
      exact hsmooth.trans (mul_le_mul_of_nonneg_left
        (hNquad s hsopen)
        (mul_nonneg
          (mul_nonneg
            (unitIntervalLinearizedStrongSmoothingConstant_pos
              p hgap.1 hsigma).le
            (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
          (Real.exp_nonneg _)))
  rw [show intervalDomainX2SigmaDistance sigma uStar (u t) =
      ‖weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) hmt‖ by
    symm
    simpa [intervalDomainX2SigmaDistance] using
      norm_weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) hmt]
  rw [hmild]
  exact (norm_add_le _ _).trans (add_le_add hlinear hintegral)

#print axioms paper3PerturbationCoeffM_eq_cosineCoeff_sub_const
#print axioms paper3WindowedNonlinearCoeff_X2SigmaSummable
#print axioms paper3StrongDuhamelIntegrand_intervalIntegrable
#print axioms paper3StrongDuhamelIntegrand_norm_le
#print axioms paper3StrongDuhamel_restart_eq
#print axioms paper3StrongDuhamel_restart_quadratic_norm_le

end

end ShenWork.Paper3
