/-
  ShenWork/Paper2/IntervalBFormEndToEnd.lean

  End-to-end B-form wiring for the general-chi interval theorem.

  This file deliberately uses the restart-cosine local-data interface rather than
  the half-step logistic-source interface: for chi != 0, a B-form solution is not
  represented by a logistic-only half-step source.  The restart-cosine interface
  is the faithful bridge consumed by the existing gamma >= 1 umbrella.

-/
import ShenWork.Paper2.IntervalDomainThm11Assembly
import ShenWork.Paper2.IntervalBFormPIDUnconditional
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalRegularityFrontierWiring
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.Paper2.IntervalBFormSpectralProviderDischargeOn

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
  (IntervalMildSolution intervalGradientDuhamelMap)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugateMildSolutionData_of_data conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildToLocalExistence
  (GradientMildClassicalFrontierCoreData)
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
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring

noncomputable section

namespace ShenWork.Paper2.BFormEndToEnd

/-- Package the banked B-form analytic inputs used to obtain the canonical
global cosine representation, the B-form restart representation, and the
interior PDE identity for `conjugatePicardLimit`. -/
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
  hlogSrc : DuhamelSourceTimeC1On
    (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
  hchemSrc : DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
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
  hchemCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (fun x : intervalDomainPoint =>
          intervalDomainChemotaxisDiv p
            ((conjugatePicardLimit p u₀ DB.T) t)
            (coupledChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t) x))
  hchemFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p
                ((conjugatePicardLimit p u₀ DB.T) t)
                (coupledChemicalConcentration p
                  (conjugatePicardLimit p u₀ DB.T) t) x))) n)

/-- The canonical B-form source coefficients have the time-`C¹` package required
by restart-cosine regularity. -/
def BFormBankedInputs.hsrcB
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T :=
  bFormSource_duhamelSourceTimeC1On B.hlogSrc B.hchemSrc

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
      B.hsrcB ht htT.le
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

/-- Banked B-form interior PDE for the conjugate Picard limit. -/
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
      (fun t ht htT =>
        chemDivCosineFourierData_constExtend p
          ((conjugatePicardLimit p u₀ DB.T) t)
          (coupledChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T) t)
          (B.hchemCont t ht htT) (B.hchemFourier t ht htT))

/-- View the B-form Picard fixed point as the existing gradient-mild solution
record, once the genuine map bridge to `IntervalMildSolution` is supplied. -/
def conjugateAsGradientMildSolutionData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (hGradient :
      IntervalMildSolution p DB.T u₀ (conjugatePicardLimit p u₀ DB.T)) :
    GradientMildSolutionData p u₀ where
  T := DB.T
  hT := DB.hT
  M := DB.M
  hM := DB.hM
  u := conjugatePicardLimit p u₀ DB.T
  hmild := hGradient
  hbound := (conjugateMildSolutionData_of_data DB).hbound
  hnonneg := (conjugateMildSolutionData_of_data DB).hnonneg
  hpos := (conjugateMildSolutionData_of_data DB).hpos
  hcont := (conjugateMildSolutionData_of_data DB).hcont
  hmeas := (conjugateMildSolutionData_of_data DB).hmeas

/-- B-form per-datum frontier over `conjugatePicardLimit`.

The `hGradientBridge` field is the honest bridge required by the existing local
existence stack, whose solution record is still `GradientMildSolutionData`.
The Neumann regularity is supplied through `bank.hB_global`, not through the
old output-derivative map. -/
structure BFormSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hGradientBridge :
    IntervalMildSolution p DB.T u₀ (conjugatePicardLimit p u₀ DB.T)
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
  hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t x

/-- The B-form initial approach transfers to the gradient mild map using the
B-form fixed point and the explicit gradient-map bridge. -/
theorem gradientInitialApproach_of_BForm
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀
              (conjugatePicardLimit p u₀ DB.T) t x - u₀ x| < ε := by
  intro ε hε
  have hBInitial :=
    ShenWork.Paper2.BFormInitialTrace.intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
      p (PaperPositiveInitialDatum.admissible F.bank.huPaper).2 DB
  obtain ⟨δ, hδ, hδclose⟩ := hBInitial ε hε
  refine ⟨min δ DB.T, lt_min hδ DB.hT, ?_⟩
  intro t ht htδT x
  have htδ : t < δ := lt_of_lt_of_le htδT (min_le_left _ _)
  have htT_lt : t < DB.T := lt_of_lt_of_le htδT (min_le_right _ _)
  have htT : t ≤ DB.T := le_of_lt htT_lt
  have hBfix :
      (conjugatePicardLimit p u₀ DB.T) t x =
        intervalConjugateDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x :=
    (conjugateMildSolutionData_of_data DB).hmild t ht htT x
  have hGfix :
      (conjugatePicardLimit p u₀ DB.T) t x =
        intervalGradientDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x :=
    F.hGradientBridge t ht htT x
  have hmap :
      intervalGradientDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x =
        intervalConjugateDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x := by
    rw [← hGfix, hBfix]
  rw [hmap]
  exact hδclose t ht htδ x

#print axioms BFormBankedInputs.hsrcB
#print axioms BFormBankedInputs.hpde_u
#print axioms conjugateAsGradientMildSolutionData
#print axioms gradientInitialApproach_of_BForm

end ShenWork.Paper2.BFormEndToEnd
