import ShenWork.Paper3.EventualGlobalStability
import ShenWork.Paper3.IntervalDomainMinimalLinearizedNormSmoothing
import ShenWork.Paper3.IntervalDomainStrongDuhamel

/-!
# Mass-constrained strong Duhamel inequality for the minimal model

The positive-logistic proof uses a full spectral gap.  Here the zero mode is
neutral, but it vanishes identically: the chemotaxis source is a divergence,
the reaction is zero, and physical mass compatibility removes the zeroth
perturbation coefficient.  All semigroup estimates therefore use
`UnitIntervalLinearMassSpectralGap`.
-/

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.PDE.FractionalPower
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- With no reaction, the exact full nonlinear remainder has zero mean. -/
@[simp] theorem paper3FullModeNonlinearRemainderCoeffM_zero_of_minimal
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    (uStar vStar : ℝ) (u v : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    paper3FullModeNonlinearRemainderCoeffM
      p uStar vStar u v t 0 = 0 := by
  rw [paper3FullModeNonlinearRemainderCoeffM_eq_parts,
    paper3ChemotaxisRemainderCoeffM_zero]
  simp only [paper3LogisticRemainderCoeffM, logisticLiftedM, ha, hb,
    zero_mul, sub_self, mul_zero, add_zero]
  have hliftZero : intervalDomainLift
      (fun _ : intervalDomainPoint => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [intervalDomainLift]
  rw [hliftZero,
    ShenWork.Paper2.IntervalConjugateSourceBridge.cosineCoeffs_zero_fun]
  simp

/-- Physical mass compatibility removes the zeroth perturbation coefficient
at every positive classical time. -/
theorem intervalDomainPerturbationCosineCoeff_zero_of_physicalMass
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
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
    simpa [intervalDomain] using hmass t ht.1
  simp [paper3PerturbationCoeffM, solutionCoeffM,
    paper3EquilibriumCosineCoeff,
    intervalDomain_cosineCoeffs_zero_eq_integral, hmass']

/-- The windowed nonlinear source belongs to `X_2^sigma` after propagation on
the mass-constrained subspace. -/
noncomputable def paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    {uStar vStar gap sigma a t : ℝ}
    (u v : ℝ → intervalDomainPoint → ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
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
    apply unitIntervalLinearizedMass_fractionalPower_summable
      p heq hgap hsigma (sub_pos.mpr hs.2) (hN s hs)
    simp [paper3FullModeNonlinearRemainderCoeffM_zero_of_minimal
      p ha hb uStar vStar u v s]
  · have hsource :
        paper3WindowedNonlinearCoeff p uStar vStar a t u v s = 0 := by
      funext n
      simp [paper3WindowedNonlinearCoeff, hs]
    rw [hsource]
    simp [diagonalSemigroupCoeff, fractionalPowerEnergyTerm]

/-- Complete weighted Duhamel integrand on the neutral-mode-free subspace. -/
def paper3MassStrongDuhamelIntegrand
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    {uStar vStar gap sigma a t : ℝ}
    (u v : ℝ → intervalDomainPoint → ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (s : ℝ) : CoeffL2 :=
  weightedCoeffToLp 1 sigma
    (diagonalSemigroupCoeff
      (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
      (paper3WindowedNonlinearCoeff p uStar vStar a t u v s))
    (paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
      p ha hb u v heq hgap hsigma hN s)

/-- Pointwise singular smoothing estimate for the mass-constrained Duhamel
integrand. -/
theorem paper3MassStrongDuhamelIntegrand_norm_le
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    {a t sigma uStar vStar gap s : ℝ}
    (u v : ℝ → intervalDomainPoint → ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hN : ∀ r ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v r n : ℝ) : ℂ)‖ ^ 2)
    (hs : s ∈ Set.Ioc a t) :
    ‖paper3MassStrongDuhamelIntegrand
        p ha hb u v heq hgap hsigma hN s‖ ≤
      unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma *
        (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
          coeffL2Norm (fun n =>
            ((paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s n : ℝ) : ℂ)) := by
  by_cases hst : s = t
  · subst s
    have hnot : t ∉ Set.Ioo a t := by simp
    have hintegrand : paper3MassStrongDuhamelIntegrand
        p ha hb u v heq hgap hsigma hN t = 0 := by
      ext n
      change paper3MassStrongDuhamelIntegrand
        p ha hb u v heq hgap hsigma hN t n = (0 : ℂ)
      simp [paper3MassStrongDuhamelIntegrand, weightedCoeffSequence,
        diagonalSemigroupCoeff, paper3WindowedNonlinearCoeff, hnot]
    rw [hintegrand, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (unitIntervalLinearizedStrongSmoothingConstant_pos
            p hgap.1 hsigma).le
          (Real.rpow_nonneg (sub_nonneg.mpr (le_refl t)) _))
        (Real.exp_nonneg _))
      (coeffL2Norm_nonneg _)
  · have hsopen : s ∈ Set.Ioo a t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hsourceZero :
        (fun n => ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) 0 = 0 := by
      simp [paper3FullModeNonlinearRemainderCoeffM_zero_of_minimal
        p ha hb uStar vStar u v s]
    have hsmooth := unitIntervalLinearizedMass_fractionalPowerNorm_le
      p heq hgap hsigma (sub_pos.mpr hsopen.2) (hN s hsopen) hsourceZero
    have hsourceEq :
        paper3WindowedNonlinearCoeff p uStar vStar a t u v s =
          fun n => ((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u v s n : ℝ) : ℂ) := by
      funext n
      simp [paper3WindowedNonlinearCoeff, hsopen]
    rw [show ‖paper3MassStrongDuhamelIntegrand
          p ha hb u v heq hgap hsigma hN s‖ =
        Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - s)
            (paper3WindowedNonlinearCoeff
              p uStar vStar a t u v s)) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    rw [hsourceEq]
    exact hsmooth

/-- On a compact positive restart window, a bounded physical nonlinear source
makes the mass-constrained Bochner integrand interval-integrable. -/
theorem paper3MassStrongDuhamelIntegrand_intervalIntegrable
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
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
  have _hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
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
    have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
      p hm hsol
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
mass-constrained subspace.  Only positivity of the nonzero-mode gap enters
this analytic statement. -/
theorem paper3MassStrongQuadraticKernel_intervalIntegrable_of_local_ball
    {p : CM2Params} {T a t sigma uStar vStar gap K R : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
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
      intervalDomainX2SigmaDistance_aestronglyMeasurable_restrict_Ioo
        hsol hm ha hat htT hmem
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
      Real.exp (-(gap / 2) * (t - s)) := by
    exact mul_nonneg (mul_nonneg hC.le hrpow) hexp
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

/-- Strong membership propagates on the physical mass hyperplane. -/
theorem intervalDomainX2SigmaPerturbation_of_massStrongDuhamel_restart
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
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
  have hint := paper3MassStrongDuhamelIntegrand_intervalIntegrable
    hsol hm ha0 hb0 ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  have haT : a < T := lt_of_le_of_lt hat htT
  have hzeroA := intervalDomainPerturbationCosineCoeff_zero_of_physicalMass
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
    (intervalDomainPerturbationCosineCoeff_full_restart_windowed
      hsol hm ha hat htT)

/-- Exact complete-space restart identity on the physical mass hyperplane. -/
theorem paper3MassStrongDuhamel_restart_eq
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
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
              (intervalDomainPerturbationCosineCoeff_zero_of_physicalMass
                hsol
                  (show a ∈ Set.Ioo (0 : ℝ) T from
                    ⟨ha, lt_of_le_of_lt hat htT⟩)
                  hmass)) +
        ∫ s in a..t,
          paper3MassStrongDuhamelIntegrand
            p ha0 hb0 u v heq hgap hsigma hN s := by
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
    (hsource := paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
      p ha0 hb0 u v heq hgap hsigma hN)
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

/-- The exact mass-constrained restart identity yields the same singular
quadratic Duhamel inequality, with the linear estimate restricted to nonzero
modes. -/
theorem paper3MassStrongDuhamel_restart_quadratic_norm_le
    {p : CM2Params} {T a t sigma uStar vStar gap B K : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {size : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
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
  have hint := paper3MassStrongDuhamelIntegrand_intervalIntegrable
    hsol hm ha0 hb0 ha hat htT heq hgap hsigma hsigma1 hN hB hNnormB
  have hmild := paper3MassStrongDuhamel_restart_eq
    hsol hm ha0 hb0 ha hat htT heq hgap hsigma hmass hma hmt hN hint
  have hzeroA := intervalDomainPerturbationCosineCoeff_zero_of_physicalMass
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

/-- Actual local strong Duhamel inequality for the minimal chemotaxis model.
The positivity radius and the route-(a) `H¹` flux estimate are inherited from
the faithful local Nemytskii theorem; the mass premise is used only to remove
the neutral mode. -/
theorem paper3MassStrongDuhamel_restart_actual_local_norm_le
    {p : CM2Params} {T a t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hmem : ∀ s ∈ Set.Icc a t,
      IntervalDomainX2SigmaPerturbation sigma uStar (u s))
    (hsmall : ∀ s ∈ Set.Ioo a t,
      intervalDomainX2SigmaDistance sigma uStar (u s) ≤
        intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar) :
    intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      Real.exp (-gap * (t - a)) *
          intervalDomainX2SigmaDistance sigma uStar (u a) +
        ∫ s in a..t,
          unitIntervalLinearizedStrongSmoothingConstant
              p uStar vStar gap sigma *
            (t - s) ^ (-sigma) *
            Real.exp (-(gap / 2) * (t - s)) *
            (intervalDomainX2SigmaUniformNemytskiiConstant
                p sigma uStar vStar heq *
              intervalDomainX2SigmaDistance sigma uStar (u s) ^ 2) := by
  have hsigma : 0 < sigma := by linarith
  let K := intervalDomainX2SigmaUniformNemytskiiConstant
    p sigma uStar vStar heq
  let R := intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar
  have hK : 0 ≤ K := by
    exact (intervalDomainX2SigmaUniformNemytskiiConstant_pos
      p sigma uStar vStar heq).le
  have hR : 0 ≤ R := by
    exact (intervalDomainX2SigmaLocalNemytskiiRadius_pos heq.u_pos).le
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
        intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar := hsmall s hs
    simpa [K] using
      paper3FullModeNonlinearRemainderCoeffM_uniform_self_bound_of_mem
        heq hsol hsTime hsigmaStrong hm hmems hsmallS
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
    paper3MassStrongQuadraticKernel_intervalIntegrable_of_local_ball
      hsol hm ha hat htT hgap hsigma hsigma1 hK hR
      (fun s hs => hmem s (Set.Ioo_subset_Icc_self hs)) hsmall
  have hbase := paper3MassStrongDuhamel_restart_quadratic_norm_le
    hsol hm ha0 hb0 ha hat htT heq hgap hsigma hsigma1 hmass
    (hmem a ⟨le_rfl, hat⟩) (hmem t ⟨hat, le_rfl⟩)
    (fun s hs => (hNdata s hs).1) hB hNnormB hK
    (fun s hs => (hNdata s hs).2) hquadInt
  simpa [K] using hbase

#print axioms paper3FullModeNonlinearRemainderCoeffM_zero_of_minimal
#print axioms intervalDomainPerturbationCosineCoeff_zero_of_physicalMass
#print axioms paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
#print axioms paper3MassStrongDuhamelIntegrand_norm_le
#print axioms paper3MassStrongDuhamelIntegrand_intervalIntegrable
#print axioms
  paper3MassStrongQuadraticKernel_intervalIntegrable_of_local_ball
#print axioms
  intervalDomainX2SigmaPerturbation_of_massStrongDuhamel_restart
#print axioms paper3MassStrongDuhamel_restart_eq
#print axioms paper3MassStrongDuhamel_restart_quadratic_norm_le
#print axioms paper3MassStrongDuhamel_restart_actual_local_norm_le

end

end ShenWork.Paper3
