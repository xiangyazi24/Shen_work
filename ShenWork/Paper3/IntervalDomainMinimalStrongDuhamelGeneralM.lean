/- Strong-space Duhamel realization on the physical-mass hyperplane for the
faithful general-`m` interval model.

This file merges the two existing specializations: the mass-constrained
coefficient layer of `IntervalDomainMinimalStrongDuhamel.lean` (which is
domain-free) and the faithful general-`m` domain layer of
`IntervalDomainStrongDuhamelGeneralM.lean`.  The linearized semigroup decay
uses only the nonzero-mode spectral gap, because both the datum and the
minimal-model nonlinear source vanish on the zeroth cosine mode.  No
`p.m = 1` hypothesis appears. -/
import ShenWork.Paper3.IntervalDomainMinimalStrongDuhamel
import ShenWork.Paper3.IntervalDomainStrongDuhamelGeneralM

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

/-- Physical mass compatibility removes the zeroth perturbation coefficient
at every positive classical time of a faithful general-`m` solution. -/
theorem intervalDomainMPerturbationCosineCoeff_zero_of_physicalMass
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    intervalDomainPerturbationCosineCoeff uStar (u t) 0 = 0 := by
  have hphi : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x - uStar) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hcoeff := paper3PerturbationCoeffM_eq_cosineCoeff_sub_const
    (u := u) (uStar := uStar) (t := t) 0 hphi
  change ((cosineCoeffs
    (fun x => intervalDomainLift (u t) x - uStar) 0 : ℝ) : ℂ) = 0
  rw [← hcoeff]
  have hmass' : intervalDomain.integral (u t) = uStar := by
    simpa [intervalDomain, intervalDomainM] using hmass t ht.1
  simp [paper3PerturbationCoeffM, solutionCoeffM,
    paper3EquilibriumCosineCoeff,
    intervalDomain_cosineCoeffs_zero_eq_integral, hmass']

/-- Mass-constrained singular Duhamel integrand is Bochner integrable on the
faithful general-`m` orbit. -/
theorem paper3MassStrongDuhamelIntegrand_intervalIntegrable_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
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
      (paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN) volume a t := by
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
      (paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN)
      (volume.restrict (Set.Ioo a t)) := by
    exact aestronglyMeasurable_weightedCoeffToLp_of_ae
      1 sigma
      (fun s => diagonalSemigroupCoeff
        (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
        (paper3WindowedNonlinearCoeff p uStar vStar a t u v s))
      (paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
        p ha0 hb0 u v heq hgap hsigma hN) hcoordAE
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hat]
  apply Integrable.mono'
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hat).mp hmajor) hAE
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsmooth := paper3MassStrongDuhamelIntegrand_norm_le
    p ha0 hb0 u v heq hgap hsigma hN
      (show s ∈ Set.Ioc a t from ⟨hs.1, hs.2.le⟩)
  have hfactor : 0 ≤
      unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma *
        (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) := by
    exact mul_nonneg
      (mul_nonneg
        (unitIntervalLinearizedStrongSmoothingConstant_pos
          p hgap.1 hsigma).le
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _))
      (Real.exp_nonneg _)
  calc
    ‖paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN s‖ ≤
        unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma *
          (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
            coeffL2Norm (fun n =>
              ((paper3FullModeNonlinearRemainderCoeffM
                p uStar vStar u v s n : ℝ) : ℂ)) := hsmooth
    _ ≤ unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma *
          (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) * B :=
      mul_le_mul_of_nonneg_left (hNnorm s hs) hfactor
    _ ≤ major s := by
      dsimp [major, C, ShenWork.PDE.restartedSmoothingKernel]
      have hrpow : 0 ≤ (t - s) ^ (-sigma) :=
        Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _
      have hexp : 0 ≤ Real.exp (-(gap / 2) * (t - s)) :=
        Real.exp_nonneg _
      nlinarith [mul_nonneg hC.le hexp,
        mul_nonneg (add_nonneg zero_le_one hrpow) hexp,
        mul_nonneg hB (mul_nonneg hC.le hexp)]

/-- The scalar quadratic convolution remains integrable on the
mass-constrained subspace of the faithful general-`m` orbit.  Only positivity
of the nonzero-mode gap enters this analytic statement. -/
theorem paper3MassStrongQuadraticKernel_intervalIntegrable_of_local_ball_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap K R : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
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

/-- Strong membership propagates along the mass-constrained faithful orbit
under a qualitative local `L²` bound for the nonlinear source. -/
theorem intervalDomainX2SigmaPerturbation_of_massStrongDuhamel_restart_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
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
  have hint := paper3MassStrongDuhamelIntegrand_intervalIntegrable_generalM
    hsol ha0 hb0 ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  have haT : a < T := lt_of_le_of_lt hat htT
  have hzeroA := intervalDomainMPerturbationCosineCoeff_zero_of_physicalMass
    hsol (show a ∈ Set.Ioo (0 : ℝ) T from ⟨ha, haT⟩) hmass
  exact fractionalPowerEnergy_summable_of_mild
    (L := 1) (sigma := sigma) (a := a) (t := t)
    (growth := unitIntervalLinearizedGrowth p uStar vStar)
    (c := fun r => intervalDomainPerturbationCosineCoeff uStar (u r))
    (source := fun r =>
      paper3WindowedNonlinearCoeff p uStar vStar a t u v r)
    (unitIntervalLinearizedMass_fractionalPower_summable_exp
      p hgap (sub_nonneg.mpr hat) hma hzeroA)
    (paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
      p ha0 hb0 u v heq hgap hsigma hN)
    hint
    (intervalDomainPerturbationCosineCoeff_full_restart_windowed_generalM
      hsol ha hat htT)

/-- Exact complete-space restart identity on the physical mass hyperplane of
the faithful general-`m` orbit. -/
theorem paper3MassStrongDuhamel_restart_eq_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hma : IntervalDomainX2SigmaPerturbation sigma uStar (u a))
    (hmt : IntervalDomainX2SigmaPerturbation sigma uStar (u t))
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hint : IntervalIntegrable
      (paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN) volume a t) :
    weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) hmt =
      weightedCoeffToLp 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
            (intervalDomainPerturbationCosineCoeff uStar (u a)))
          (unitIntervalLinearizedMass_fractionalPower_summable_exp
            p hgap (sub_nonneg.mpr hat) hma
              (intervalDomainMPerturbationCosineCoeff_zero_of_physicalMass
                hsol
                  (show a ∈ Set.Ioo (0 : ℝ) T from
                    ⟨ha, lt_of_le_of_lt hat htT⟩)
                  hmass)) +
        ∫ s in a..t,
          paper3MassStrongDuhamelIntegrand
            p ha0 hb0 u v heq hgap hsigma hN s := by
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
    (hsource := paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
      p ha0 hb0 u v heq hgap hsigma hN)
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

/-- The exact mass-constrained restart identity yields the singular quadratic
Duhamel inequality on the faithful general-`m` orbit, with the linear
estimate restricted to nonzero modes. -/
theorem paper3MassStrongDuhamel_restart_quadratic_norm_le_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B K : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {size : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
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
  have hint := paper3MassStrongDuhamelIntegrand_intervalIntegrable_generalM
    hsol ha0 hb0 ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  have hmild := paper3MassStrongDuhamel_restart_eq_generalM
    hsol ha0 hb0 ha hat htT heq hgap hsigma hmass hma hmt hN hint
  have hzeroA := intervalDomainMPerturbationCosineCoeff_zero_of_physicalMass
    hsol
      (show a ∈ Set.Ioo (0 : ℝ) T from
        ⟨ha, lt_of_le_of_lt hat htT⟩)
      hmass
  let linear : CoeffL2 := weightedCoeffToLp 1 sigma
    (diagonalSemigroupCoeff
      (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
      (intervalDomainPerturbationCosineCoeff uStar (u a)))
    (unitIntervalLinearizedMass_fractionalPower_summable_exp
      p hgap (sub_nonneg.mpr hat) hma hzeroA)
  have hlinear : ‖linear‖ ≤ Real.exp (-gap * (t - a)) *
      intervalDomainX2SigmaDistance sigma uStar (u a) := by
    rw [show ‖linear‖ = Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
            (intervalDomainPerturbationCosineCoeff uStar (u a))) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    simpa [intervalDomainX2SigmaDistance] using
      unitIntervalLinearizedMass_fractionalPowerNorm_le_exp
        p hgap (sub_nonneg.mpr hat) hma hzeroA
  have hintegral :
      ‖∫ s in a..t,
          paper3MassStrongDuhamelIntegrand
            p ha0 hb0 u v heq hgap hsigma hN s‖ ≤
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
      have hintegrand : paper3MassStrongDuhamelIntegrand
          p ha0 hb0 u v heq hgap hsigma hN t = 0 := by
        ext n
        change paper3MassStrongDuhamelIntegrand
          p ha0 hb0 u v heq hgap hsigma hN t n = (0 : ℂ)
        simp [paper3MassStrongDuhamelIntegrand, weightedCoeffSequence,
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
      have hsmooth := paper3MassStrongDuhamelIntegrand_norm_le
        p ha0 hb0 u v heq hgap hsigma hN hs
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

/-- Actual local strong Duhamel inequality for the faithful general-`m`
chemotaxis nonlinearity on the physical-mass hyperplane. -/
theorem paper3MassStrongDuhamel_restart_actual_local_norm_le_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
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
    paper3MassStrongQuadraticKernel_intervalIntegrable_of_local_ball_generalM
      hsol ha hat htT hgap hsigma hsigma1 hK hR
      (fun s hs => hmem s (Set.Ioo_subset_Icc_self hs)) hsmall
  have hbase := paper3MassStrongDuhamel_restart_quadratic_norm_le_generalM
    hsol ha0 hb0 ha hat htT heq hgap hsigma hsigma1 hmass
    (hmem a ⟨le_rfl, hat⟩) (hmem t ⟨hat, le_rfl⟩)
    (fun s hs => (hNdata s hs).1) hB hNnormB hK
    (fun s hs => (hNdata s hs).2) hquadInt
  simpa [K] using hbase

/-- The mass-constrained full Duhamel formula regularizes a zero-mean
unweighted slice of the faithful general-`m` orbit into the strong space. -/
theorem intervalDomainMassX2SigmaPerturbation_and_norm_le_of_L2_restart_generalM
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hma0 : Summable fun n : ℕ =>
      ‖intervalDomainPerturbationCosineCoeff uStar (u a) n‖ ^ 2)
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hB : 0 ≤ B)
    (hNnorm : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B) :
    IntervalDomainX2SigmaPerturbation sigma uStar (u t) ∧
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma * (t - a) ^ (-sigma) *
          Real.exp (-(gap / 2) * (t - a)) *
            coeffL2Norm
              (intervalDomainPerturbationCosineCoeff uStar (u a)) +
        B * restartedKernelMassPositive
          (unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma) sigma (gap / 2) := by
  have haLe : a ≤ t := hat.le
  have hgapTime : 0 < t - a := sub_pos.mpr hat
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  have hC : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap.1 hsigma
  have hzeroA := intervalDomainMPerturbationCosineCoeff_zero_of_physicalMass
    hsol (show a ∈ Set.Ioo (0 : ℝ) T from ⟨ha, hat.trans htT⟩) hmass
  have hlinear : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
          (intervalDomainPerturbationCosineCoeff uStar (u a))) n :=
    unitIntervalLinearizedMass_fractionalPower_summable
      p heq hgap hsigma hgapTime hma0 hzeroA
  have hint := paper3MassStrongDuhamelIntegrand_intervalIntegrable_generalM
    hsol ha0 hb0 ha haLe htT heq hgap hsigma hsigma1 hN hB hNnorm
  have htarget : IntervalDomainX2SigmaPerturbation sigma uStar (u t) :=
    fractionalPowerEnergy_summable_of_mild
      (L := 1) (sigma := sigma) (a := a) (t := t)
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (c := fun r => intervalDomainPerturbationCosineCoeff uStar (u r))
      (source := fun r =>
        paper3WindowedNonlinearCoeff p uStar vStar a t u v r)
      hlinear
      (paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
        p ha0 hb0 u v heq hgap hsigma hN)
      hint
      (intervalDomainPerturbationCosineCoeff_full_restart_windowed_generalM
        hsol ha haLe htT)
  refine ⟨htarget, ?_⟩
  have hmild :
      weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u t)) htarget =
        weightedCoeffToLp 1 sigma
            (diagonalSemigroupCoeff
              (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
              (intervalDomainPerturbationCosineCoeff uStar (u a))) hlinear +
          ∫ s in a..t,
            paper3MassStrongDuhamelIntegrand
              p ha0 hb0 u v heq hgap hsigma hN s := by
    apply weightedCoeffToLp_mild_eq
      (hsource := paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
        p ha0 hb0 u v heq hgap hsigma hN)
      (hint := hint)
    exact intervalDomainPerturbationCosineCoeff_full_restart_windowed_generalM
      hsol ha haLe htT
  let linear : CoeffL2 := weightedCoeffToLp 1 sigma
    (diagonalSemigroupCoeff
      (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
      (intervalDomainPerturbationCosineCoeff uStar (u a))) hlinear
  have hlinearNorm : ‖linear‖ ≤
      C * (t - a) ^ (-sigma) *
        Real.exp (-(gap / 2) * (t - a)) *
          coeffL2Norm
            (intervalDomainPerturbationCosineCoeff uStar (u a)) := by
    rw [show ‖linear‖ = Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
            (intervalDomainPerturbationCosineCoeff uStar (u a))) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    simpa [C] using unitIntervalLinearizedMass_fractionalPowerNorm_le
      p heq hgap hsigma hgapTime hma0 hzeroA
  let major : ℝ → ℝ := fun s =>
    B * restartedSmoothingKernel C sigma (gap / 2) (t - s)
  have hkernel : IntervalIntegrable
      (restartedSmoothingKernel C sigma (gap / 2)) volume 0 (t - a) :=
    restartedSmoothingKernel_intervalIntegrable_positive
      hsigma hsigma1 (by linarith [hgap.1]) hgapTime.le
  have hmajorInt : IntervalIntegrable major volume a t := by
    have hcomp : IntervalIntegrable
        (fun s => restartedSmoothingKernel C sigma (gap / 2) (t - s))
        volume a t := by
      simpa using (hkernel.comp_sub_left t).symm
    simpa [major] using hcomp.const_mul B
  have hintegralMajor :
      ‖∫ s in a..t,
          paper3MassStrongDuhamelIntegrand
            p ha0 hb0 u v heq hgap hsigma hN s‖ ≤
        ∫ s in a..t, major s := by
    apply intervalIntegral.norm_integral_le_of_norm_le haLe
      (Filter.Eventually.of_forall fun s hs => ?_) hmajorInt
    by_cases hst : s = t
    · subst s
      have hnot : t ∉ Set.Ioo a t := by simp
      have hintegrand : paper3MassStrongDuhamelIntegrand
          p ha0 hb0 u v heq hgap hsigma hN t = 0 := by
        ext n
        change paper3MassStrongDuhamelIntegrand
          p ha0 hb0 u v heq hgap hsigma hN t n = (0 : ℂ)
        simp [paper3MassStrongDuhamelIntegrand, weightedCoeffSequence,
          diagonalSemigroupCoeff, paper3WindowedNonlinearCoeff, hnot]
      rw [hintegrand, norm_zero]
      have hrzero : 0 ≤ (t - t) ^ (-sigma) :=
        Real.rpow_nonneg (by linarith) _
      exact mul_nonneg hB (by
        dsimp [major, restartedSmoothingKernel]
        exact mul_nonneg
          (mul_nonneg hC.le (add_nonneg zero_le_one hrzero))
          (Real.exp_nonneg _))
    have hsopen : s ∈ Set.Ioo a t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hsmooth := paper3MassStrongDuhamelIntegrand_norm_le
      p ha0 hb0 u v heq hgap hsigma hN hs
    have hfactor : 0 ≤ C * (t - s) ^ (-sigma) *
        Real.exp (-(gap / 2) * (t - s)) :=
      mul_nonneg
        (mul_nonneg hC.le
          (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
        (Real.exp_nonneg _)
    refine hsmooth.trans ?_
    calc
      C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
          coeffL2Norm (fun n =>
            ((paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s n : ℝ) : ℂ)) ≤
        C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) * B := by
          exact mul_le_mul_of_nonneg_left (hNnorm s hsopen) hfactor
      _ ≤ major s := by
        dsimp [major, restartedSmoothingKernel]
        have hrpow : 0 ≤ (t - s) ^ (-sigma) :=
          Real.rpow_nonneg (sub_nonneg.mpr hs.2) _
        have hexp : 0 ≤ Real.exp (-(gap / 2) * (t - s)) :=
          Real.exp_nonneg _
        nlinarith [mul_nonneg hB (mul_nonneg hC.le hexp),
          mul_nonneg (add_nonneg zero_le_one hrpow) hexp]
  have hmajorMass : (∫ s in a..t, major s) ≤
      B * restartedKernelMassPositive C sigma (gap / 2) := by
    have heqInt : (∫ s in a..t, major s) =
        B * (∫ r in (0 : ℝ)..(t - a),
          restartedSmoothingKernel C sigma (gap / 2) r) := by
      dsimp [major]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simpa only [sub_self] using (intervalIntegral.integral_comp_sub_left
        (f := restartedSmoothingKernel C sigma (gap / 2))
        (a := a) (b := t) t)
    rw [heqInt]
    exact mul_le_mul_of_nonneg_left
      (restartedSmoothingKernel_integral_le_positive
        hC.le hsigma hsigma1 (by linarith [hgap.1]) hgapTime.le) hB
  rw [show intervalDomainX2SigmaDistance sigma uStar (u t) =
      ‖weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) htarget‖ by
    symm
    simpa [intervalDomainX2SigmaDistance] using
      norm_weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) htarget]
  rw [hmild]
  have htri := norm_add_le linear
    (∫ s in a..t,
      paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN s)
  change ‖linear + ∫ s in a..t,
      paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN s‖ ≤ _
  exact htri.trans (add_le_add hlinearNorm (hintegralMajor.trans hmajorMass))

#print axioms intervalDomainMPerturbationCosineCoeff_zero_of_physicalMass
#print axioms paper3MassStrongDuhamelIntegrand_intervalIntegrable_generalM
#print axioms
  paper3MassStrongQuadraticKernel_intervalIntegrable_of_local_ball_generalM
#print axioms
  intervalDomainX2SigmaPerturbation_of_massStrongDuhamel_restart_generalM
#print axioms paper3MassStrongDuhamel_restart_eq_generalM
#print axioms paper3MassStrongDuhamel_restart_quadratic_norm_le_generalM
#print axioms paper3MassStrongDuhamel_restart_actual_local_norm_le_generalM
#print axioms
  intervalDomainMassX2SigmaPerturbation_and_norm_le_of_L2_restart_generalM

end

end ShenWork.Paper3
