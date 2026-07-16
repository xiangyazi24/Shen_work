/- Strong-space Duhamel realization for the faithful general-`m` interval model. -/
import ShenWork.Paper3.IntervalDomainStrongDuhamel
import ShenWork.Paper3.IntervalDomainStrongSliceNonlinearEstimateGeneralM

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Each physical strong perturbation coefficient is continuous on compact
positive-time windows. -/
theorem intervalDomainPerturbationCosineCoeff_continuousOn_generalM
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (n : ℕ) :
    ContinuousOn
      (fun s => intervalDomainPerturbationCosineCoeff uStar (u s) n)
      (Set.Icc a b) := by
  have hmodal : ContinuousOn
      (fun s => paper3PerturbationCoeffM u uStar s n) (Set.Icc a b) :=
    (solutionCoeffM_continuousOn hsol ha hab hbT n).sub
      continuousOn_const
  have hcast : ContinuousOn
      (fun s => ((paper3PerturbationCoeffM u uStar s n : ℝ) : ℂ))
      (Set.Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hmodal
  refine hcast.congr ?_
  intro s hs
  have hsT : s < T := lt_of_le_of_lt hs.2 hbT
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have hphi : IntervalIntegrable
      (fun x => intervalDomainLift (u s) x - uStar) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hsol.regularity.2.2.2.2.1 s ⟨hs0, hsT⟩).1.1.continuousOn).sub
      continuousOn_const
  unfold intervalDomainPerturbationCosineCoeff
  exact congrArg (fun r : ℝ => (r : ℂ))
    (paper3PerturbationCoeffM_eq_cosineCoeff_sub_const n hphi).symm

/-- Strong distance is measurable on a positive-time window as soon as every
slice belongs to the fractional space.  This uses finite-mode approximation
in `CoeffL2`; no unproved product-Borel principle is invoked. -/
theorem intervalDomainX2SigmaDistance_aestronglyMeasurable_restrict_Ioo_generalM
    {p : CM2Params} {T a b sigma uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hmem : ∀ s ∈ Set.Ioo a b,
      IntervalDomainX2SigmaPerturbation sigma uStar (u s)) :
    AEStronglyMeasurable
      (fun s => intervalDomainX2SigmaDistance sigma uStar (u s))
      (volume.restrict (Set.Ioo a b)) := by
  let c : ℝ → ℕ → ℂ := fun s =>
    if s ∈ Set.Ioo a b then
      intervalDomainPerturbationCosineCoeff uStar (u s)
    else 0
  have hcmem : ∀ s, Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma (c s) n := by
    intro s
    by_cases hs : s ∈ Set.Ioo a b
    · have hceq : c s =
          intervalDomainPerturbationCosineCoeff uStar (u s) := by
        dsimp [c]
        rw [if_pos hs]
      rw [hceq]
      exact hmem s hs
    · have hceq : c s = 0 := by
        dsimp [c]
        rw [if_neg hs]
      rw [hceq]
      simp [fractionalPowerEnergyTerm]
  have hcoordAE : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => weightedCoeffSequence 1 sigma (c s) n)
      (volume.restrict (Set.Ioo a b)) := by
    intro n
    let actual : ℝ → ℂ := fun s => weightedCoeffSequence 1 sigma
      (intervalDomainPerturbationCosineCoeff uStar (u s)) n
    have hcoeff := intervalDomainPerturbationCosineCoeff_continuousOn_generalM
      (uStar := uStar) hsol ha hab hbT n
    have hactual : ContinuousOn actual (Set.Icc a b) := by
      unfold actual weightedCoeffSequence
      exact continuousOn_const.mul hcoeff
    have haeActual : AEStronglyMeasurable actual
        (volume.restrict (Set.Ioo a b)) :=
      (hactual.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioo
    refine haeActual.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hceq : c s =
        intervalDomainPerturbationCosineCoeff uStar (u s) := by
      dsimp [c]
      rw [if_pos hs]
    rw [hceq]
  have hvec : AEStronglyMeasurable
      (fun s => weightedCoeffToLp 1 sigma (c s) (hcmem s))
      (volume.restrict (Set.Ioo a b)) :=
    aestronglyMeasurable_weightedCoeffToLp_of_ae
      1 sigma c hcmem hcoordAE
  have hnorm := continuous_norm.comp_aestronglyMeasurable hvec
  refine hnorm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hceq : c s =
      intervalDomainPerturbationCosineCoeff uStar (u s) := by
    dsimp [c]
    rw [if_pos hs]
  rw [norm_weightedCoeffToLp]
  rw [hceq]
  rfl

/-- The scalar quadratic convolution appearing in the strong Duhamel bound is
integrable on every positive window on which the trajectory stays in a fixed
strong ball. -/
theorem paper3StrongQuadraticKernel_intervalIntegrable_of_local_ball_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap K R : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hmem : ∀ s ∈ Set.Ioo a t,
      IntervalDomainX2SigmaPerturbation sigma uStar (u s))
    (hsmall : ∀ s ∈ Set.Ioo a t,
      intervalDomainX2SigmaDistance sigma uStar (u s) ≤ R) :
    IntervalIntegrable
      (fun s =>
        unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma *
          (t - s) ^ (-sigma) *
          Real.exp (-(gap / 2) * (t - s)) *
            (K * intervalDomainX2SigmaDistance sigma uStar (u s) ^ 2))
      volume a t := by
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  let size : ℝ → ℝ := fun s =>
    intervalDomainX2SigmaDistance sigma uStar (u s)
  let source : ℝ → ℝ := fun s =>
    C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
      (K * size s ^ 2)
  let major : ℝ → ℝ := fun s =>
    (K * R ^ 2) *
      ShenWork.PDE.restartedSmoothingKernel C sigma (gap / 2) (t - s)
  have hC : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap.1 hsigma
  have hsizeAE : AEStronglyMeasurable size
      (volume.restrict (Set.Ioo a t)) := by
    simpa [size] using
      intervalDomainX2SigmaDistance_aestronglyMeasurable_restrict_Ioo_generalM
        hsol ha hat htT hmem
  have hkernelCont : ContinuousOn
      (fun s => C * (t - s) ^ (-sigma) *
        Real.exp (-(gap / 2) * (t - s))) (Set.Ioo a t) := by
    have hbase : ContinuousOn (fun s : ℝ => t - s) (Set.Ioo a t) :=
      (continuous_const.sub continuous_id).continuousOn
    have hrpow : ContinuousOn (fun s : ℝ => (t - s) ^ (-sigma))
        (Set.Ioo a t) :=
      hbase.rpow_const (fun s hs => Or.inl (sub_ne_zero.mpr (ne_of_gt hs.2)))
    exact (continuousOn_const.mul hrpow).mul (by fun_prop)
  have hkernelAE : AEStronglyMeasurable
      (fun s => C * (t - s) ^ (-sigma) *
        Real.exp (-(gap / 2) * (t - s)))
      (volume.restrict (Set.Ioo a t)) :=
    hkernelCont.aestronglyMeasurable measurableSet_Ioo
  have hsourceAE : AEStronglyMeasurable source
      (volume.restrict (Set.Ioo a t)) := by
    have hprod := hkernelAE.mul ((hsizeAE.pow 2).const_mul K)
    refine hprod.congr ?_
    filter_upwards [] with s
    dsimp [source, size]
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
    simpa [major] using hkernelComp.const_mul (K * R ^ 2)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hat]
  apply Integrable.mono'
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hat).mp hmajor)
    hsourceAE
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsize0 : 0 ≤ size s := by
    dsimp [size, intervalDomainX2SigmaDistance]
    exact Real.sqrt_nonneg _
  have hsq : size s ^ 2 ≤ R ^ 2 := by
    nlinarith [hsmall s hs]
  have hsource0 : 0 ≤ source s := by
    dsimp [source]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC.le
          (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _))
        (Real.exp_nonneg _))
      (mul_nonneg hK (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg hsource0]
  dsimp [source, major, ShenWork.PDE.restartedSmoothingKernel]
  have hrpow : 0 ≤ (t - s) ^ (-sigma) :=
    Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _
  have hexp : 0 ≤ Real.exp (-(gap / 2) * (t - s)) := Real.exp_nonneg _
  have hfactor : 0 ≤ C * (t - s) ^ (-sigma) *
      Real.exp (-(gap / 2) * (t - s)) := by positivity
  calc
    C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
        (K * size s ^ 2) ≤
      C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
        (K * R ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq hK) hfactor
    _ ≤ (K * R ^ 2) *
        (C * (1 + (t - s) ^ (-sigma)) *
          Real.exp (-(gap / 2) * (t - s))) := by
      have hone : (t - s) ^ (-sigma) ≤ 1 + (t - s) ^ (-sigma) := by
        linarith
      nlinarith [mul_nonneg hK (sq_nonneg R),
        mul_nonneg hC.le hexp,
        mul_nonneg (add_nonneg zero_le_one hrpow) hexp]

/-- On a compact positive restart window, an `L²` bound for the physical
nonlinearity makes the singular strong-space Duhamel integrand Bochner
integrable.  The singularity is exactly `(t-s)^(-sigma)` and is integrable
because `sigma<1`. -/
theorem paper3StrongDuhamelIntegrand_intervalIntegrable_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
      (uStar := uStar) (vStar := vStar) hsol ha hat htT n
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

/-- Coordinate form of the physical restart formula with the endpoint-safe
windowed nonlinear source. -/
theorem intervalDomainPerturbationCosineCoeff_full_restart_windowed_generalM
    {p : CM2Params} {T a t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (n : ℕ) :
    intervalDomainPerturbationCosineCoeff uStar (u t) n =
      diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
          (intervalDomainPerturbationCosineCoeff uStar (u a)) n +
        ∫ s in a..t,
          diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
            (paper3WindowedNonlinearCoeff
              p uStar vStar a t u v s) n := by
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
  have hmodal := paper3PerturbationCoeffM_full_restart
    (uStar := uStar) (vStar := vStar) hsol ha hat htT n
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

/-- Strong membership propagates from the restart slice to the terminal slice
under a qualitative local `L²` bound for the nonlinear source. -/
theorem intervalDomainX2SigmaPerturbation_of_strongDuhamel_restart_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hma : IntervalDomainX2SigmaPerturbation sigma uStar (u a))
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hB : 0 ≤ B)
    (hNnormB : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B) :
    IntervalDomainX2SigmaPerturbation sigma uStar (u t) := by
  have hint := paper3StrongDuhamelIntegrand_intervalIntegrable_generalM
    hsol ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  exact fractionalPowerEnergy_summable_of_mild
    (L := 1) (sigma := sigma) (a := a) (t := t)
    (growth := unitIntervalLinearizedGrowth p uStar vStar)
    (c := fun r => intervalDomainPerturbationCosineCoeff uStar (u r))
    (source := fun r =>
      paper3WindowedNonlinearCoeff p uStar vStar a t u v r)
    (unitIntervalLinearized_fractionalPower_summable_exp
      p hgap (sub_nonneg.mpr hat) hma)
    (paper3WindowedNonlinearCoeff_X2SigmaSummable
      p u v heq hgap hsigma hN)
    hint
    (intervalDomainPerturbationCosineCoeff_full_restart_windowed_generalM
      hsol ha hat htT)

/-- Exact positive-time restart formula in the complete strong coefficient
space.  The only remaining Bochner premise is interval integrability of the
explicit integrand; it is discharged quantitatively below. -/
theorem paper3StrongDuhamel_restart_eq_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
    (uStar := uStar) (vStar := vStar) hsol ha hat htT n
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
theorem paper3StrongDuhamel_restart_quadratic_norm_le_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B K : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {size : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
  have hint := paper3StrongDuhamelIntegrand_intervalIntegrable_generalM
    hsol ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  have hmild := paper3StrongDuhamel_restart_eq_generalM
    hsol ha hat htT heq hgap hsigma hma hmt hN hint
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

/-- Actual local strong Duhamel inequality for the faithful chemotaxis
nonlinearity.  The premise is the load-bearing positivity/Nemytskii ball on
the open integration window; the terminal slice itself is not used by the
nonlinear source estimate. -/
theorem paper3StrongDuhamel_restart_actual_local_norm_le_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmem : ∀ s ∈ Set.Icc a t,
      IntervalDomainX2SigmaPerturbation sigma uStar (u s))
    (hsmall : ∀ s ∈ Set.Ioo a t,
      intervalDomainX2SigmaDistance sigma uStar (u s) ≤
        intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar) :
    intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      Real.exp (-gap * (t - a)) *
          intervalDomainX2SigmaDistance sigma uStar (u a) +
        ∫ s in a..t,
          unitIntervalLinearizedStrongSmoothingConstant
              p uStar vStar gap sigma *
            (t - s) ^ (-sigma) *
            Real.exp (-(gap / 2) * (t - s)) *
            (intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
                p sigma uStar vStar heq *
              intervalDomainX2SigmaDistance sigma uStar (u s) ^ 2) := by
  have hsigma : 0 < sigma := by linarith
  let K := intervalDomainX2SigmaUniformNemytskiiConstantGeneralM
    p sigma uStar vStar heq
  let R := intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar
  have hK : 0 ≤ K := by
    exact (intervalDomainX2SigmaUniformNemytskiiConstantGeneralM_pos
      p sigma uStar vStar heq).le
  have hR : 0 ≤ R := by
    exact (intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM_pos p sigma heq.u_pos).le
  have hNdata : ∀ s ∈ Set.Ioo a t,
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤
        K * intervalDomainX2SigmaDistance sigma uStar (u s) ^ 2 := by
    intro s hs
    have hsTime : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans ha hs.1, lt_trans hs.2 htT⟩
    have hmems := hmem s (Set.Ioo_subset_Icc_self hs)
    have hsmallS : intervalDomainX2SigmaDistance sigma uStar (u s) ≤
        intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar := hsmall s hs
    simpa [K] using
      paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_of_mem_generalM
        heq hsol hsTime hsigmaStrong hmems hsmallS
  let B := K * R ^ 2
  have hB : 0 ≤ B := mul_nonneg hK (sq_nonneg R)
  have hNnormB : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B := by
    intro s hs
    have hd0 : 0 ≤ intervalDomainX2SigmaDistance sigma uStar (u s) :=
      Real.sqrt_nonneg _
    have hsq : intervalDomainX2SigmaDistance sigma uStar (u s) ^ 2 ≤
        R ^ 2 := by
      nlinarith [hsmall s hs]
    exact (hNdata s hs).2.trans
      (mul_le_mul_of_nonneg_left hsq hK)
  have hquadInt :=
    paper3StrongQuadraticKernel_intervalIntegrable_of_local_ball_generalM
      hsol ha hat htT hgap hsigma hsigma1 hK hR
      (fun s hs => hmem s (Set.Ioo_subset_Icc_self hs)) hsmall
  have hbase := paper3StrongDuhamel_restart_quadratic_norm_le_generalM
    hsol ha hat htT heq hgap hsigma hsigma1
    (hmem a ⟨le_rfl, hat⟩) (hmem t ⟨hat, le_rfl⟩)
    (fun s hs => (hNdata s hs).1) hB hNnormB hK
    (fun s hs => (hNdata s hs).2) hquadInt
  simpa [K] using hbase

#print axioms intervalDomainPerturbationCosineCoeff_continuousOn_generalM
#print axioms
  intervalDomainX2SigmaDistance_aestronglyMeasurable_restrict_Ioo_generalM
#print axioms
  paper3StrongQuadraticKernel_intervalIntegrable_of_local_ball_generalM
#print axioms paper3StrongDuhamelIntegrand_intervalIntegrable_generalM
#print axioms
  intervalDomainPerturbationCosineCoeff_full_restart_windowed_generalM
#print axioms
  intervalDomainX2SigmaPerturbation_of_strongDuhamel_restart_generalM
#print axioms paper3StrongDuhamel_restart_eq_generalM
#print axioms paper3StrongDuhamel_restart_quadratic_norm_le_generalM
#print axioms paper3StrongDuhamel_restart_actual_local_norm_le_generalM

end

end ShenWork.Paper3
