import ShenWork.Paper2.IntervalBFormPIDUnconditional
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalBankChemSliceFix
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.Paper2.IntervalBFormSpectralProviderDischargeOn

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugateMildSolutionData_of_data conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1
   bFormSource_duhamelSourceTimeC1On
   LogisticCosineFourierData ChemDivCosineFourierData
   logisticCosineFourierData_constExtend
   chemDivCosineFourierData_constExtend)
open ShenWork.Paper2.BankChemSliceFix
  (ChemDivCosineFourierDataIoo)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
   coupledChemical_ellipticPDE_of_closedC2_neumann
   coupledChemical_neumannBC_of_closedC2_neumann)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierAssembly
open ShenWork.IntervalResolverSpatialC2
  (resolverR_summability)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainCosineSlice_contDiffOn_Ioo
   intervalDomainCosineSlice_neumann_limit_left
   intervalDomainCosineSlice_neumann_limit_right
   intervalDomainCosineSlice_conjunct7)
open ShenWork.PDE

noncomputable section

namespace ShenWork.Paper2.BFormDirectClassical

/-- Banked B-form inputs needed for the direct classical assembly.

This is the B-form half of the old end-to-end file, without any gradient-form
solution record or output-derivative bridge. -/
structure BFormBankedInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  MInit : ℝ
  haInit : ∀ n,
    |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit
  hsrcBDirect : DuhamelSourceTimeC1On
    (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
  hB_global : ∀ t, 0 < t → t ≤ DB.T →
    Set.EqOn
      (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
      (fun x => ∑' n,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
          t n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hlogCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p
          ((conjugatePicardLimit p u₀ DB.T) t)))
  hlogFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (ShenWork.IntervalDomainExistence.intervalLogisticSource p
              ((conjugatePicardLimit p u₀ DB.T) t)))) n)
  hchemIoo : ∀ t, 0 < t → t < DB.T →
    ChemDivCosineFourierDataIoo p
      ((conjugatePicardLimit p u₀ DB.T) t)
      (coupledChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t)

def BFormBankedInputs.hsrcB
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T :=
  B.hsrcBDirect

/-- Windowed restriction of the B-form source for the `On`-based regularity path. -/
def BFormBankedInputs.hsrcB_on
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T :=
  B.hsrcB

/-- Eigenvalue-weighted restart coefficient summability from the windowed
`DuhamelSourceTimeC1On` source via the homogeneous + Duhamel triangle split. -/
private theorem bform_restartCoeff_eigenvalue_summable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    {t : ℝ} (ht : 0 < t) (htT : t < DB.T) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
          t n|) := by
  have hhom :=
    ShenWork.IntervalMildRegularityBootstrap.restartHomogeneousCoeff_eigenvalue_summable
      ht B.haInit
  have hduh :=
    ShenWork.IntervalDuhamelSourceTimeC1On.duhamelSpectralCoeff_eigenvalue_summable_on
      B.hsrcB_on ht htT.le
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)) (fun n => ?_) (hhom.add hduh)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (by simp only [localRestartCoeff]; exact abs_add_le _ _)
    (by unfold unitIntervalCosineEigenvalue; positivity)

private theorem bform_B_global_as_restartCoeff_eqOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T) :
    Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
      (fun x : ℝ => ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
          t n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  exact B.hB_global t ht htT hx


theorem BFormBankedInputs.hpde_u
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α) :=
  ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_PID_global_restart_on
      DB B.huPaper B.Hinf B.hsmall
      (fun σ n => localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
        (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) σ n)
      (fun σ hσ hσT => bform_restartCoeff_eigenvalue_summable B hσ hσT)
      (fun σ hσ hσT => bform_B_global_as_restartCoeff_eqOn B hσ hσT.le)
      (cosineCoeffs (intervalDomainLift u₀))
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
      B.hsrcB
      (fun _ _ _ _ => rfl)
      B.hB_global
      (fun t ht htT => by
        have hhom : Summable (fun n : ℕ =>
            |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n|) := by
          refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
            ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right
              B.MInit)
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (B.haInit n) (Real.exp_pos _).le
        have hduh : Summable (fun n : ℕ =>
            |ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff
              (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) t n|) := by
          refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
            (B.hsrcB.henv_summable.mul_left t)
          unfold ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff
          rw [← Real.norm_eq_abs]
          calc ‖∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
                  bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T) s n‖
              ≤ B.hsrcB.envelope n * |t - 0| := by
                apply intervalIntegral.norm_integral_le_of_norm_le_const
                intro s hs
                rw [Set.uIoc_of_le ht.le] at hs
                rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
                calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
                      |bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T) s n|
                    ≤ 1 * |bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T) s n| := by
                      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                      rw [Real.exp_le_one_iff]
                      have hts : 0 ≤ t - s := by linarith [hs.2]
                      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
                        unfold unitIntervalCosineEigenvalue; positivity
                      nlinarith [mul_nonneg hts hlam]
                  _ = |bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T) s n| :=
                      one_mul _
                  _ ≤ B.hsrcB.envelope n :=
                      B.hsrcB.henv_bound s ⟨le_of_lt hs.1, le_trans hs.2 htT⟩ n
            _ = t * B.hsrcB.envelope n := by rw [sub_zero, abs_of_pos ht]; ring
        exact (hhom.add hduh).of_nonneg_of_le
          (fun n => abs_nonneg _)
          (fun n => by simp only [localRestartCoeff]; exact abs_add_le _ _))
      (fun t ht htT =>
        logisticCosineFourierData_constExtend p
          (conjugatePicardLimit p u₀ DB.T) t (B.hlogCont t ht htT)
          (B.hlogFourier t ht htT))
      (fun t ht htT => B.hchemIoo t ht htT)


/-- Direct B-form frontier for one datum.  Every field is map-agnostic: no
gradient mild record and no output-derivative bridge. -/
structure BFormDirectFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
  hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t x

private theorem bform_u_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  exact ShenWork.IntervalConjugatePicard.conjugatePicardLimit_pos_of_PID
    B.huPaper B.Hinf B.hsmall t ht (le_of_lt htT) x

private theorem bform_u_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t, 0 < t → t < DB.T →
      ContDiffOn ℝ 2
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
          (Set.Icc (0 : ℝ) 1)
        ∧ deriv
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)) 0 = 0
        ∧ deriv
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)) 1 = 0 := by
  intro t ht htT
  have heig := bform_restartCoeff_eigenvalue_summable B ht htT
  have hagree := bform_B_global_as_restartCoeff_eqOn B ht htT.le
  have h0 : intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) 0 ≠ 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (bform_u_pos B t ⟨0, hmem⟩ ht htT)
  have h1 : intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) 1 ≠ 0 := by
    have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (bform_u_pos B t ⟨1, hmem⟩ ht htT)
  exact intervalDomainCosineSlice_conjunct7 heig hagree h0 h1

private theorem bform_u_neumann_left
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t, 0 < t → t < DB.T →
      Filter.Tendsto
        (deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro t ht htT
  exact intervalDomainCosineSlice_neumann_limit_left
    (bform_restartCoeff_eigenvalue_summable B ht htT)
    (bform_B_global_as_restartCoeff_eqOn B ht htT.le)

private theorem bform_u_neumann_right
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t, 0 < t → t < DB.T →
      Filter.Tendsto
        (deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht htT
  exact intervalDomainCosineSlice_neumann_limit_right
    (bform_restartCoeff_eigenvalue_summable B ht htT)
    (bform_B_global_as_restartCoeff_eqOn B ht htT.le)

private theorem lift_resolver_eqOn_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Set.EqOn
      (intervalDomainLift (intervalNeumannResolverR p u))
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hxIcc
  simp only [intervalDomainLift, dif_pos hxIcc,
    ShenWork.IntervalResolverGradientBridge.resolverR_apply_eq, cosineMode]

private theorem resolver_lift_ne_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint)
    (hpos : 0 < intervalNeumannResolverR p u x) :
    intervalDomainLift (intervalNeumannResolverR p u) x.1 ≠ 0 := by
  have heq : intervalDomainLift (intervalNeumannResolverR p u) x.1 =
      intervalNeumannResolverR p u x := by
    unfold intervalDomainLift
    split
    · rfl
    · exact absurd x.2 ‹_›
  rw [heq]
  exact ne_of_gt hpos

private def bform_sourceDecay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    {t : ℝ} (ht : 0 < t) (htT : t < DB.T) :
    SourceCoeffQuadraticDecay p
      (conjugatePicardLimit p u₀ DB.T t) := by
  have hpos_lift :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact bform_u_pos B t ⟨y, hy⟩ ht htT
  exact sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    (p := p)
    (u := conjugatePicardLimit p u₀ DB.T t)
    (bform_u_closedC2_endpointDerivs B t ht htT).1
    (bform_u_neumann_left B t ht htT)
    (bform_u_neumann_right B t ht htT)
    hpos_lift

private theorem bform_vSpatialInterior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      ContDiffOn ℝ 2
        (intervalDomainLift
          (mildChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T) t))
        (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  change ContDiffOn ℝ 2
    (intervalDomainLift
      (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t)))
    (Set.Ioo (0 : ℝ) 1)
  exact intervalDomainCosineSlice_contDiffOn_Ioo
    (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))

private theorem bform_vNeumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      Filter.Tendsto
          (deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht
  change Filter.Tendsto
          (deriv (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  exact
    ⟨intervalDomainCosineSlice_neumann_limit_left
        (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t)),
      intervalDomainCosineSlice_neumann_limit_right
        (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))⟩

private theorem bform_vClosedSpatial
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    (hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t x) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      ContDiffOn ℝ 2
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)) 0 = 0 ∧
        deriv
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)) 1 = 0 := by
  intro t ht
  change ContDiffOn ℝ 2
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t)))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))) 0 = 0 ∧
        deriv
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))) 1 = 0
  have hv0 : 0 < intervalNeumannResolverR p
      (conjugatePicardLimit p u₀ DB.T t) ⟨0, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      hVpos t ht.1 ht.2 ⟨0, by constructor <;> norm_num⟩
  have hv1 : 0 < intervalNeumannResolverR p
      (conjugatePicardLimit p u₀ DB.T t) ⟨1, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      hVpos t ht.1 ht.2 ⟨1, by constructor <;> norm_num⟩
  exact intervalDomainCosineSlice_conjunct7
    (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))
    (resolver_lift_ne_zero ⟨0, by constructor <;> norm_num⟩ hv0)
    (resolver_lift_ne_zero ⟨1, by constructor <;> norm_num⟩ hv1)

theorem intervalConjugatePicardLimit_classicalRegularity_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    intervalDomainClassicalRegularity DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  unfold intervalDomainClassicalRegularity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact
      ⟨(bform_u_closedC2_endpointDerivs F.bank t ht.1 ht.2).1.mono
          Set.Ioo_subset_Icc_self,
        bform_vSpatialInterior F.bank t ht⟩
  · intro x t ht
    have hu := timeSlices_u_of_spectralAgreement F.hTimeNhd x
    have hv := timeSlices_v_of_resolverSpectral F.hResolverData x
    exact ⟨⟨hu.1 t ht, hv.1 t ht⟩, ⟨hu.2, hv.2⟩⟩
  · exact
      ⟨jointTimeDerivInterior_u_of_spectralAgreement F.hTimeNhd,
       jointTimeDerivInterior_v_of_resolverSpectral F.hResolverData⟩
  · intro t ht
    exact
      ⟨⟨bform_u_neumann_left F.bank t ht.1 ht.2,
          bform_u_neumann_right F.bank t ht.1 ht.2⟩,
        bform_vNeumannLimits F.bank t ht⟩
  · intro t ht
    exact
      ⟨bform_u_closedC2_endpointDerivs F.bank t ht.1 ht.2,
        bform_vClosedSpatial F.bank F.hVpos t ht⟩
  · exact
      ⟨jointTimeDerivClosed_u_of_spectralAgreement F.hTimeNhd,
       jointTimeDerivClosed_v_of_resolverSpectral F.hResolverData⟩
  · exact
      ⟨jointSolutionClosed_u_of_spectralAgreement F.hTimeNhd,
       jointSolutionClosed_v_of_resolverSpectral F.hResolverData⟩

theorem intervalConjugatePicardLimit_initialTrace_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    InitialTrace intervalDomain u₀
      (conjugatePicardLimit p u₀ DB.T) :=
  ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
    p (PaperPositiveInitialDatum.admissible F.bank.huPaper).2 DB

theorem intervalConjugatePicardLimit_isClassicalSolution_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    IsPaper2ClassicalSolution intervalDomain p DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  refine IsPaper2ClassicalSolution.of_components DB.hT
    (intervalConjugatePicardLimit_classicalRegularity_direct F)
    ?_ ?_ ?_ ?_ ?_
  · exact bform_u_pos F.bank
  · intro t x ht htT
    exact le_of_lt (F.hVpos t ht htT x)
  · exact F.bank.hpde_u
  · have h :=
      coupledChemical_ellipticPDE_of_closedC2_neumann p
        (bform_u_pos F.bank)
        (fun t ht htT => (bform_u_closedC2_endpointDerivs F.bank t ht htT).1)
        (bform_u_neumann_left F.bank)
        (bform_u_neumann_right F.bank)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h
  · have h :=
      coupledChemical_neumannBC_of_closedC2_neumann p
        (bform_u_pos F.bank)
        (fun t ht htT => (bform_u_closedC2_endpointDerivs F.bank t ht htT).1)
        (bform_u_neumann_left F.bank)
        (bform_u_neumann_right F.bank)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h

theorem localClassicalSolution_of_BFormDirectFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine ⟨DB.T, DB.hT,
    conjugatePicardLimit p u₀ DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T), ?_⟩
  exact ⟨intervalConjugatePicardLimit_isClassicalSolution_direct F,
    intervalConjugatePicardLimit_initialTrace_direct F⟩

def BFormPaperLocalFrontier (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormDirectFrontier p DB)

theorem paperPositive_localExistence_of_BFormDirect
    {p : CM2Params}
    (hPerDatum : BFormPaperLocalFrontier p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨F⟩⟩ := hPerDatum u₀ hu₀
  exact localClassicalSolution_of_BFormDirectFrontier F

/-- The actual gamma-`≥ 1` continuation umbrella still asks for local existence
for the weaker `PositiveInitialDatum` interface.  This wrapper records that
requirement explicitly rather than pretending that the B-form PID bank proves
`PositiveInitialDatum → PaperPositiveInitialDatum`. -/
theorem paper2_theorem_1_1_general_chi_bform
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p := by
  let hData : IntervalDomainPaper2ContinuationDataGammaGeOne_no_hextend_mge p :=
    { localExistence := hlocal
      uniformLocal := hUniform }
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge_bundled
    p hχ ha hb hγ_ge_one hData

#print axioms BFormBankedInputs.hsrcB
#print axioms BFormBankedInputs.hsrcB_on
#print axioms BFormBankedInputs.hpde_u
#print axioms intervalConjugatePicardLimit_classicalRegularity_direct
#print axioms intervalConjugatePicardLimit_initialTrace_direct
#print axioms intervalConjugatePicardLimit_isClassicalSolution_direct
#print axioms localClassicalSolution_of_BFormDirectFrontier
#print axioms paperPositive_localExistence_of_BFormDirect
#print axioms paper2_theorem_1_1_general_chi_bform

end ShenWork.Paper2.BFormDirectClassical
