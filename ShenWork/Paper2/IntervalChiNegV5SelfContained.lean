import ShenWork.Paper2.IntervalChiNegFinalAssemblyV5
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2Concrete
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalNegativePartEnergyTimeLeibniz
import ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
import ShenWork.Paper2.IntervalTruncatedTestedSpectral
import ShenWork.Paper2.IntervalTruncatedPicardLimitJointContinuity
import ShenWork.PDE.P3MoserGradientContinuityFromDx
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Self-contained V5 atom supply from the truncated Picard construction.

This file deliberately does not call the Batch1/Batch2/A1--A5 conditional
constructors.  It starts from a `UniformConjugateMildExistenceCore`, converts it
to the faithful truncated Picard data, extracts the raw Picard limit facts, and
then packages the V5 atoms.

The remaining `sorry`s are narrow analytic sub-steps for which the present
repository does not expose a reusable Mathlib/API theorem in the needed shape:
source-coefficient time continuity, positive-time weighted summability and
tested series interchanges, endpoint weak-test closure, energy differentiability,
the a.e. lift/chain fields, Jensen witness construction, and the final
truncated/full Picard agreement.
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugatePicard
  (UniformConjugateMildExistenceCore conjugatePicardLimit)
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
  (continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (TruncatedConjugateMildExistenceData TruncatedConjugateMildSolutionData
   truncatedConjugateMildSolutionData_of_data truncatedConjugatePicardLimit
   truncatedConjugatePicardLimit_initialTrace_of_truncated_data
   truncatedPicardCoeff truncatedPicardCoeffTimeDeriv
   truncatedBFormSourceCoeff truncatedLogisticSourceCoeff truncatedChemDivSourceCoeff
   truncatedNegativePartCoefficientWeakTestData_of_truncatedPicard
   truncatedNegativePartWeakTestIdentityAt_of_coefficientData
   truncatedPicard_A2_time_chain truncatedPicard_A2_diffusion_chain
   truncatedPicard_A2_diffusion_nonneg truncatedPicard_A2_logistic_integrable
   truncatedPicard_A2_neg_deriv_zero_on_pos
   TruncatedNegativePartCoefficientWeakTestData
   TruncatedPicardNegativePartEnergyEstimateA2Data
   TruncatedPicardNegativePartEnergyA3Data
   TruncatedPicardNegativePartEnergyCoreRegularData
   truncatedPositiveTimeSpectralData_of_existenceData
   weightedCoeff_summable_of_spectralData
   tested_time_leibniz_of_spectralData
   tested_gradient_ibp_of_spectralData
   tested_source_pairing_of_spectralData
   truncatedPicardEnergyCoreRegularData_of_atomData
   truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
   uniformTruncatedConjugateMildExistenceCore_of_uniformCore
   UniformTruncatedConjugateMildExistenceCore
   negativePartEnergy negativePartDissipation negativePartTest negativePartLift
   negativePart negativePart_eq_neg_of_nonpos deriv_negativePartLift_eq_zero_of_pos
   cosineTestCoeff truncatedChemFluxLifted truncatedLogisticLifted truncatedLogisticLocal
   truncatedConjugatePicardLimitJoint
   cosineCoeffs_continuousOn_of_jointContinuousOn_Ioc
   positiveInitialDatum_intervalDomainLift_nonneg)
open ShenWork.Paper2.IntervalChiNegFinalAssemblyV4
  (JensenBypassStrictPosDataFor)
open ShenWork.Paper2.IntervalChiNegFinalAssemblyV5
  (Paper2ChiNegV5AtomSupply V5EnergyAtoms)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegV5SelfContained

private theorem intervalMeasure_integral_eq_intervalIntegral_v5
    (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) =
    ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The truncated Picard data canonically associated to a uniform full core. -/
def truncatedDataOfUniformCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedConjugateMildExistenceData p u₀ :=
  (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C).toData

/-- The actual Picard-limit package produced by the truncated contraction. -/
def rawPicardLimitData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedConjugateMildSolutionData p u₀ :=
  truncatedConjugateMildSolutionData_of_data
    (truncatedDataOfUniformCore C)

/-- The energy derivative candidate dictated by testing the coefficient ODE
against `-u_-`. -/
def energyDerivativeCandidate
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : ℝ → ℝ :=
  fun t =>
    2 * (∫ x,
      intervalDomainLift
          (fun z : intervalDomainPoint =>
            intervalDomain.timeDeriv (truncatedConjugatePicardLimit p u₀ T) t z) x *
        negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
      ∂ intervalMeasure 1)

theorem raw_hasContinuousSlices
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    HasContinuousSlices C.T (truncatedConjugatePicardLimit p u₀ C.T) := by
  simpa [rawPicardLimitData, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using (rawPicardLimitData C).hcont

theorem raw_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ C.T t x| ≤ C.R := by
  intro t ht htT x
  simpa [rawPicardLimitData, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using (rawPicardLimitData C).hbound t ht htT x

theorem raw_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    HasJointMeasurability (truncatedConjugatePicardLimit p u₀ C.T) := by
  simpa [rawPicardLimitData, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using (rawPicardLimitData C).hmeas

def raw_truncated_mild
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedConjugateMildSolutionData p u₀ := rawPicardLimitData C

/-- (1) Source coefficient continuity in time.  This is the intended
composition theorem: continuous slices of the Picard limit, the continuous
truncated nonlinearities, and continuous linear coefficient functionals. -/
theorem sourceCoeff_time_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (hjoint : ContinuousOn
      (truncatedConjugatePicardLimitJoint p u₀ DT.T)
      (Set.Ioc (0 : ℝ) DT.T ×ˢ Set.Icc (0 : ℝ) 1))
    (hchem_cont : ∀ k : ℕ,
      ContinuousOn
        (fun s =>
          truncatedChemDivSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) s k)
        (Set.Ioc (0 : ℝ) DT.T)) :
    ∀ k : ℕ,
      ContinuousOn
        (fun s =>
          truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) s k)
        (Set.Ioc (0 : ℝ) DT.T) := by
  intro k
  set U : ℝ → intervalDomainPoint → ℝ :=
    truncatedConjugatePicardLimit p u₀ DT.T
  have hlog_joint :
      ContinuousOn
        (Function.uncurry (fun s x => truncatedLogisticLifted p (U s) x))
        (Set.Ioc (0 : ℝ) DT.T ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hpos : ContinuousOn
        (fun q : ℝ × ℝ =>
          positivePart (truncatedConjugatePicardLimitJoint p u₀ DT.T q))
        (Set.Ioc (0 : ℝ) DT.T ×ˢ Set.Icc (0 : ℝ) 1) := by
      have hpp : Continuous (fun r : ℝ => positivePart r) := by
        simpa [positivePart] using
          ((continuous_id : Continuous (fun r : ℝ => r)).max continuous_const)
      exact hpp.continuousOn.comp hjoint (fun _ _ => Set.mem_univ _)
    have hpow : ContinuousOn
        (fun q : ℝ × ℝ =>
          positivePart (truncatedConjugatePicardLimitJoint p u₀ DT.T q) ^ p.α)
        (Set.Ioc (0 : ℝ) DT.T ×ˢ Set.Icc (0 : ℝ) 1) :=
      ContinuousOn.rpow_const hpos (fun _ _ => Or.inr p.hα.le)
    have hbody : ContinuousOn
        (fun q : ℝ × ℝ =>
          positivePart (truncatedConjugatePicardLimitJoint p u₀ DT.T q) *
            (p.a - p.b *
              positivePart (truncatedConjugatePicardLimitJoint p u₀ DT.T q) ^ p.α))
        (Set.Ioc (0 : ℝ) DT.T ×ˢ Set.Icc (0 : ℝ) 1) :=
      hpos.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
    refine hbody.congr ?_
    intro q hq
    obtain ⟨_, hx⟩ := Set.mem_prod.mp hq
    simp [U, Function.uncurry, truncatedLogisticLifted, truncatedLogisticLocal,
      truncatedConjugatePicardLimitJoint, intervalDomainLift, hx]
  have hlog_coeff :
      ContinuousOn
        (fun s => truncatedLogisticSourceCoeff p U s k)
        (Set.Ioc (0 : ℝ) DT.T) := by
    simpa [truncatedLogisticSourceCoeff] using
      cosineCoeffs_continuousOn_of_jointContinuousOn_Ioc
        (f := fun s x => truncatedLogisticLifted p (U s) x)
        (T := DT.T) k hlog_joint
  have hchem := hchem_cont k
  simpa [U, truncatedBFormSourceCoeff] using
    hlog_coeff.sub (continuousOn_const.mul hchem)

/-- (2) Positive-time eigenvalue-weighted coefficient summability.  The proof is
the spectral smoothing estimate for the restart coefficient: the heat factor
`exp (-t * λ_k)` dominates polynomial eigenvalue weights for `0 < t`. -/
theorem weightedCoeff_summable_at_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < DT.T) :
    Summable (fun k : ℕ =>
        unitIntervalCosineEigenvalue k *
          truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
      ∧
    Summable (fun k : ℕ =>
        truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k) := by
  exact weightedCoeff_summable_of_spectralData ht htT.le
    (truncatedPositiveTimeSpectralData_of_existenceData DT ht htT)

/-- The three tested spectral identities needed after the scalar coefficient
ODE: time Leibniz/tsum interchange, gradient IBP/tsum, and source pairing. -/
structure TestedSpectralIdentities
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) (t : ℝ) : Prop where
  time_leibniz_tsum :
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                intervalDomain.timeDeriv
                  (truncatedConjugatePicardLimit p u₀ DT.T) t z) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        truncatedPicardCoeffTimeDeriv p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k
  gradient_ibp_tsum :
      (∫ x,
          deriv (intervalDomainLift
            ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x *
            deriv
              (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        unitIntervalCosineEigenvalue k *
          truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k
  source_pairing :
      (∑' k : ℕ,
        truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
        =
      p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p
              ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
            deriv
              (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
          ∂ intervalMeasure 1)
        + (∫ x,
            truncatedLogisticLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
              negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
            ∂ intervalMeasure 1)

theorem testedSpectralIdentities
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < DT.T) :
    TestedSpectralIdentities p DT t := by
  let D := truncatedPositiveTimeSpectralData_of_existenceData DT ht htT
  exact
    { time_leibniz_tsum := tested_time_leibniz_of_spectralData ht htT.le D
      gradient_ibp_tsum := tested_gradient_ibp_of_spectralData ht htT.le D
      source_pairing := tested_source_pairing_of_spectralData ht htT.le D }

/-- (3) Coefficient ODE plus the tested identities gives the A1 weak-test atom
on the open time interval. -/
def A1_open
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < DT.T) :
    TruncatedNegativePartCoefficientWeakTestData p DT t := by
  have hs := weightedCoeff_summable_at_positive_time DT ht htT
  have hids := testedSpectralIdentities DT ht htT
  exact
    { coeff := truncatedPicardCoeff p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t
      coeffTimeDeriv := truncatedPicardCoeffTimeDeriv p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t
      sourceCoeff := truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) t
      coeff_ode :=
        ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedPicardCoeff_ode
          p u₀ (truncatedConjugatePicardLimit p u₀ DT.T) t
      lap_summable := hs.1
      source_summable := hs.2
      time_leibniz_tsum := hids.time_leibniz_tsum
      gradient_ibp_tsum := hids.gradient_ibp_tsum
      source_pairing := hids.source_pairing }

def A1_all
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) :
    ∀ t, 0 < t → t < DT.T →
      TruncatedNegativePartCoefficientWeakTestData p DT t := by
  intro t ht htT
  exact A1_open DT ht htT

theorem lift_continuousAt_ae_of_slices
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T)) :
    ∀ t, 0 < t → t ≤ T →
      ∀ᵐ x ∂ intervalMeasure 1,
        ContinuousAt
          (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x := by
  intro t ht htT
  have hcontOn :
      ContinuousOn
        (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t))
        (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn.continuousOn_intervalDomainLift_of_hasContinuousSlices
      hcont ht htT
  have hmem :
      ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 := by
    unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
    exact ae_restrict_mem measurableSet_Icc
  have hne0 : ∀ᵐ x ∂ intervalMeasure 1, x ≠ (0 : ℝ) := by
    rw [ae_iff]
    apply le_antisymm
    · calc
        intervalMeasure 1 {x : ℝ | ¬ x ≠ (0 : ℝ)}
            ≤ volume ({0} : Set ℝ) := by
              simpa [intervalMeasure, ShenWork.IntervalDomain.intervalSet] using
                (Measure.restrict_apply_le (μ := volume)
                  (s := Set.Icc (0 : ℝ) 1) (t := ({0} : Set ℝ)))
        _ = 0 := by simp
    · exact zero_le _
  have hne1 : ∀ᵐ x ∂ intervalMeasure 1, x ≠ (1 : ℝ) := by
    rw [ae_iff]
    apply le_antisymm
    · calc
        intervalMeasure 1 {x : ℝ | ¬ x ≠ (1 : ℝ)}
            ≤ volume ({1} : Set ℝ) := by
              simpa [intervalMeasure, ShenWork.IntervalDomain.intervalSet] using
                (Measure.restrict_apply_le (μ := volume)
                  (s := Set.Icc (0 : ℝ) 1) (t := ({1} : Set ℝ)))
        _ = 0 := by simp
    · exact zero_le _
  filter_upwards [hmem, hne0, hne1] with x hx h0 h1
  have hx0 : (0 : ℝ) < x := lt_of_le_of_ne hx.1 h0.symm
  have hx1 : x < (1 : ℝ) := lt_of_le_of_ne hx.2 h1
  exact hcontOn.continuousAt (Icc_mem_nhds hx0 hx1)

lemma deriv_negativePartLift_eq_neg_of_neg
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hw : ContinuousAt (intervalDomainLift w) x)
    (hneg : intervalDomainLift w x < 0) :
    deriv (negativePartLift w) x = -deriv (intervalDomainLift w) x := by
  have hmem : intervalDomainLift w x ∈ Set.Iio (0 : ℝ) := hneg
  have hnhds : Set.Iio (0 : ℝ) ∈ 𝓝 (intervalDomainLift w x) :=
    isOpen_Iio.mem_nhds hmem
  have hev_neg : ∀ᶠ y in 𝓝 x, intervalDomainLift w y ∈ Set.Iio (0 : ℝ) :=
    hw hnhds
  have hev : negativePartLift w =ᶠ[𝓝 x]
      fun y : ℝ => -intervalDomainLift w y :=
    hev_neg.mono (fun y hy => negativePart_eq_neg_of_nonpos hy.le)
  rw [hev.deriv_eq]
  simp

lemma deriv_negativePartLift_eq_zero_of_zero
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hzero : intervalDomainLift w x = 0) :
    deriv (negativePartLift w) x = 0 := by
  have hmin : IsLocalMin (negativePartLift w) x := by
    unfold IsLocalMin IsMinFilter
    filter_upwards [] with y
    have hnn : 0 ≤ negativePart (intervalDomainLift w y) := by
      simp [negativePart]
    simpa [negativePartLift, hzero, negativePart] using hnn
  exact hmin.deriv_eq_zero

lemma diffusion_chain_pointwise
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hw : ContinuousAt (intervalDomainLift w) x) :
    deriv (intervalDomainLift w) x *
        deriv (fun y : ℝ => -negativePartLift w y) x =
      (deriv (negativePartLift w) x) ^ 2 := by
  by_cases hpos : 0 < intervalDomainLift w x
  · have hv : deriv (negativePartLift w) x = 0 :=
      deriv_negativePartLift_eq_zero_of_pos hw hpos
    simp [hv]
  · by_cases hneg : intervalDomainLift w x < 0
    · have hv : deriv (negativePartLift w) x =
          -deriv (intervalDomainLift w) x :=
        deriv_negativePartLift_eq_neg_of_neg hw hneg
      simp [hv]
      ring
    · have hzero : intervalDomainLift w x = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hv : deriv (negativePartLift w) x = 0 :=
        deriv_negativePartLift_eq_zero_of_zero hzero
      simp [hv]

theorem diffusion_chain_ae_of_slices
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ} :
    HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T) →
    ∀ t, 0 < t → t ≤ T →
      (fun x =>
        deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x *
          deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t) x)
        =ᵐ[intervalMeasure 1]
      fun x =>
        (deriv (negativePartLift
          (truncatedConjugatePicardLimit p u₀ T t)) x) ^ 2 := by
  intro hcont t ht htT
  filter_upwards [lift_continuousAt_ae_of_slices hcont t ht htT] with x hx
  change
      deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x *
          deriv
            (fun y : ℝ =>
              -negativePartLift (truncatedConjugatePicardLimit p u₀ T t) y) x =
        (deriv (negativePartLift
          (truncatedConjugatePicardLimit p u₀ T t)) x) ^ 2
  exact
    diffusion_chain_pointwise
      (w := truncatedConjugatePicardLimit p u₀ T t)
      (x := x)
      hx

theorem diffusion_chain_ae
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T)) :
    ∀ t, 0 < t → t ≤ T →
      (fun x =>
        deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x *
          deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t) x)
        =ᵐ[intervalMeasure 1]
      fun x =>
        (deriv (negativePartLift
          (truncatedConjugatePicardLimit p u₀ T t)) x) ^ 2 := by
  exact diffusion_chain_ae_of_slices hcont

theorem logistic_test_aestronglyMeasurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T R : ℝ}
    (hcont : HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T))
    (_hbound : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ T t x| ≤ R) :
    ∀ t, 0 < t → t ≤ T →
      AEStronglyMeasurable
        (fun x =>
          truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
        (intervalMeasure 1) := by
  intro t ht htT
  let w : intervalDomainPoint → ℝ := truncatedConjugatePicardLimit p u₀ T t
  have hw : Continuous w := hcont t ht htT
  have hlift :
      ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
      hw
  have hposCont : Continuous fun r : ℝ => positivePart r := by
    simpa [positivePart] using (continuous_id.max continuous_const)
  have hlogLocal :
      ContinuousOn
        (fun r : ℝ =>
          ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedLogisticLocal p r)
        Set.univ := by
    unfold ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedLogisticLocal
    apply ContinuousOn.mul hposCont.continuousOn
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hposCont.continuousOn
      (fun _ _ => Or.inr p.hα.le)
  have hlog :
      ContinuousOn
        (truncatedLogisticLifted p w) (Set.Icc (0 : ℝ) 1) := by
    simpa [truncatedLogisticLifted] using
      hlogLocal.comp hlift (fun _ _ => Set.mem_univ _)
  have htest :
      ContinuousOn
        (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t)
        (Set.Icc (0 : ℝ) 1) := by
    have hneg :
        ContinuousOn (negativePartLift w) (Set.Icc (0 : ℝ) 1) :=
      ShenWork.Paper2.BFormPositiveDatumNegPart.negativePart_continuous.continuousOn.comp hlift
          (fun _ _ => Set.mem_univ _)
    simpa [w, negativePartTest] using hneg.neg
  have hprod :
      ContinuousOn
        (fun x =>
          truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
        (Set.Icc (0 : ℝ) 1) := by
    simpa [w] using hlog.mul htest
  exact
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hprod

def A2_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedPicardNegativePartEnergyEstimateA2Data
      p (u₀ := u₀) C.T (energyDerivativeCandidate p u₀ C.T) := by
  refine
    { neg_deriv_zero_on_pos :=
        ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedPicard_A2_neg_deriv_zero_on_pos
          (lift_continuousAt_ae_of_slices (raw_hasContinuousSlices C))
      time_chain := truncatedPicard_A2_time_chain ?_
      diffusion_chain :=
        truncatedPicard_A2_diffusion_chain
          (diffusion_chain_ae (raw_hasContinuousSlices C))
      diffusion_nonneg := fun _ _ _ => truncatedPicard_A2_diffusion_nonneg
      logistic_integrable :=
        truncatedPicard_A2_logistic_integrable C.hR
          (raw_bound C)
          (logistic_test_aestronglyMeasurable (raw_hasContinuousSlices C) (raw_bound C))
      energy_integrable := ?_ }
  · intro t _ht _htT
    rfl
  · intro t ht htT
    exact
      ShenWork.Paper2.BFormPositiveDatumNegPart.negativePart_sq_integrable_of_continuous_bound
          (raw_hasContinuousSlices C t ht htT)
          (le_of_lt C.hR)
          (raw_bound C t ht htT)

theorem raw_jointContinuousOn_positive_windows
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b ≤ C.T →
      ContinuousOn
        (fun q : ℝ × ℝ =>
          intervalDomainLift
            (truncatedConjugatePicardLimit p u₀ C.T q.1) q.2)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  -- Residual analytic input: positive-time joint continuity of the truncated
  -- Picard limit on every compact time-space window `[a,b] × [0,1]`.
  -- The existing producer only gives an `Ioc` theorem after one supplies
  -- joint continuity of all Picard iterates, and this file does not currently
  -- have that iterate-level producer.
  sorry

theorem raw_energy_continuousOn_positive_windows
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b ≤ C.T →
      ContinuousOn
        (negativePartEnergy (truncatedConjugatePicardLimit p u₀ C.T))
        (Set.Icc a b) := by
  intro a b ha hab hbT
  set u : ℝ → intervalDomainPoint → ℝ :=
    truncatedConjugatePicardLimit p u₀ C.T
  let F : ℝ → ℝ → ℝ :=
    fun t x => (negativePart (intervalDomainLift (u t) x)) ^ 2
  have hjoint :
      ContinuousOn
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [u] using
      raw_jointContinuousOn_positive_windows
        (p := p) (u₀ := u₀) C ha hab hbT
  have hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hneg :
        ContinuousOn
          (fun z : ℝ × ℝ => negativePart (intervalDomainLift (u z.1) z.2))
          (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
      (ShenWork.Paper2.BFormPositiveDatumNegPart.negativePart_continuous.continuousOn).comp
        hjoint (fun _ _ => Set.mem_univ _)
    simpa [F, Function.uncurry] using hneg.pow 2
  have hint :
      ContinuousOn (fun t => ∫ x in (0 : ℝ)..1, F t x)
        (Set.Icc a b) :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hFcont
  have hrewrite :
      (negativePartEnergy u) = fun t => ∫ x in (0 : ℝ)..1, F t x := by
    funext t
    simp [negativePartEnergy, negativePartLift, F,
      intervalMeasure_integral_eq_intervalIntegral_v5]
  simpa [u, hrewrite]

theorem energy_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    ContinuousOn
      (negativePartEnergy (truncatedConjugatePicardLimit p u₀ C.T))
      (Set.Icc (0 : ℝ) C.T) := by
  set u : ℝ → intervalDomainPoint → ℝ :=
    truncatedConjugatePicardLimit p u₀ C.T
  set E : ℝ → ℝ := negativePartEnergy u
  have htrace : InitialTrace intervalDomain u₀ u := by
    simpa [u, truncatedDataOfUniformCore,
      UniformTruncatedConjugateMildExistenceCore.toData]
      using truncatedConjugatePicardLimit_initialTrace_of_truncated_data
        p hu₀.admissible.2 (truncatedDataOfUniformCore C)
  have hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x := by
    intro x
    have h := positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
    simpa [intervalDomainLift, x.2] using h
  have hvanish :
      ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < C.T → E s < ε := by
    simpa [u, E] using
      (ShenWork.Paper2.BFormPositiveDatumNegPart.negativePartEnergy_initial_vanishes_of_trace_nonneg
          hu₀.admissible hu₀_nonneg htrace (raw_hasContinuousSlices C)
          (le_of_lt C.hR) (raw_bound C))
  have hE_zero : E 0 = 0 := by
    simp [E, u, negativePartEnergy, negativePartLift,
      truncatedConjugatePicardLimit]
  have h0 : ContinuousWithinAt E (Set.Ici (0 : ℝ)) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hvanish ε hε
    refine ⟨min δ₀ C.T, lt_min hδ₀_pos C.hT, ?_⟩
    intro y hy_mem hy_dist
    rw [hE_zero]
    by_cases hy0 : y = 0
    · subst y
      simp [hE_zero, hε]
    · have hy_pos : 0 < y := lt_of_le_of_ne hy_mem hy0.symm
      have hy_delta : y < δ₀ := by
        have hdist : dist y 0 < min δ₀ C.T := by simpa [dist_comm] using hy_dist
        have hy_abs : |y| < min δ₀ C.T := by
          simpa [Real.dist_eq] using hdist
        have hy_lt_min : y < min δ₀ C.T := by
          simpa [abs_of_nonneg hy_mem] using hy_abs
        exact lt_of_lt_of_le hy_lt_min (min_le_left _ _)
      have hy_T : y < C.T := by
        have hdist : dist y 0 < min δ₀ C.T := by simpa [dist_comm] using hy_dist
        have hy_abs : |y| < min δ₀ C.T := by
          simpa [Real.dist_eq] using hdist
        have hy_lt_min : y < min δ₀ C.T := by
          simpa [abs_of_nonneg hy_mem] using hy_abs
        exact lt_of_lt_of_le hy_lt_min (min_le_right _ _)
      have hEnonneg : 0 ≤ E y := by
        exact integral_nonneg (fun x => sq_nonneg (negativePartLift (u y) x))
      have hE_lt : E y < ε := hδ₀ y hy_pos hy_delta hy_T
      rw [Real.dist_eq]
      exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  intro t ht
  by_cases ht_zero : t = 0
  · subst t
    exact h0.mono (by
      intro y hy
      exact hy.1)
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    have hhalf_pos : 0 < t / 2 := by linarith
    have hhalf_le_T : t / 2 ≤ C.T := by linarith [ht.2]
    have ht_mem : t ∈ Set.Icc (t / 2) C.T := ⟨by linarith, ht.2⟩
    have hcont :
        ContinuousOn E (Set.Icc (t / 2) C.T) := by
      simpa [E, u] using
        raw_energy_continuousOn_positive_windows
          (p := p) (u₀ := u₀) C hhalf_pos hhalf_le_T le_rfl
    have hnhds : Set.Icc (t / 2) C.T ∈
        𝓝[Set.Icc (0 : ℝ) C.T] t := by
      have hopen : Set.Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
      have hself : Set.Icc (0 : ℝ) C.T ∈ 𝓝[Set.Icc (0 : ℝ) C.T] t :=
        self_mem_nhdsWithin
      have hinter :
          Set.Ioi (t / 2) ∩ Set.Icc (0 : ℝ) C.T ∈
            𝓝[Set.Icc (0 : ℝ) C.T] t :=
        Filter.inter_mem (Filter.mem_inf_of_left hopen) hself
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      exact ⟨le_of_lt hy.1, hy.2.2⟩
    exact (hcont.continuousWithinAt ht_mem).mono_of_mem_nhdsWithin hnhds

theorem raw_timeDerivativeWindowData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < C.T) :
    ∃ d : ℝ, t < d ∧ d < C.T ∧ ∃ B : ℝ,
      ∀ᵐ x ∂ intervalMeasure 1, ∀ r ∈ Set.Icc t d,
        HasDerivWithinAt
          (fun s : ℝ =>
            intervalDomainLift
              (truncatedConjugatePicardLimit p u₀ C.T s) x)
          (intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv
              (truncatedConjugatePicardLimit p u₀ C.T) r z) x)
          (Set.Icc t d) r ∧
        |intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv
                (truncatedConjugatePicardLimit p u₀ C.T) r z) x| ≤ B := by
  -- Residual analytic input: positive-time genuine time differentiability of
  -- the truncated Picard limit on a compact interior window, with a uniform
  -- lifted time-derivative bound.  The window must stop before `C.T`: the
  -- globally zero-extended limit generally has no two-sided derivative at
  -- the terminal time.
  sorry

theorem energy_has_deriv
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    ∀ t ∈ Set.Ico (0 : ℝ) C.T,
      HasDerivWithinAt
        (negativePartEnergy (truncatedConjugatePicardLimit p u₀ C.T))
        (energyDerivativeCandidate p u₀ C.T t) (Set.Ici t) t := by
  intro t htmem
  rcases htmem with ⟨ht, htT⟩
  rcases raw_timeDerivativeWindowData C ht htT with
    ⟨d, htd, hdT, B, hwindow⟩
  have hcont_d :
      HasContinuousSlices d
        (truncatedConjugatePicardLimit p u₀ C.T) := by
    intro r hr hrd
    exact raw_hasContinuousSlices C r hr (hrd.trans hdT.le)
  have hbound_d :
      ∀ r, 0 < r → r ≤ d → ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardLimit p u₀ C.T r x| ≤ C.R := by
    intro r hr hrd x
    exact raw_bound C r hr (hrd.trans hdT.le) x
  simpa [energyDerivativeCandidate] using
    (ShenWork.Paper2.BFormPositiveDatumNegPart.negativePartEnergy_hasDerivWithinAt_Ici_of_window_data
        (T := d) (t := t) (R := C.R) (B := B)
        (u := truncatedConjugatePicardLimit p u₀ C.T)
        ht htd (le_of_lt C.hR) hcont_d hbound_d
        hwindow)

def A3_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedPicardNegativePartEnergyA3Data
      p (u₀ := u₀) C.T (energyDerivativeCandidate p u₀ C.T) := by
  refine
    { R := C.R
      hR := le_of_lt C.hR
      hcont := raw_hasContinuousSlices C
      hbound := raw_bound C
      hu₀_adm := hu₀.admissible
      hu₀_nonneg := ?_
      htrace := ?_
      energy_cont := energy_continuous hu₀ C
      energy_has_deriv := energy_has_deriv C }
  · intro x
    have h := positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
    simpa [intervalDomainLift, x.2] using h
  · simpa [truncatedDataOfUniformCore,
      UniformTruncatedConjugateMildExistenceCore.toData]
      using truncatedConjugatePicardLimit_initialTrace_of_truncated_data
        p hu₀.admissible.2 (truncatedDataOfUniformCore C)

def energyAtoms
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    V5EnergyAtoms p C where
  E' := energyDerivativeCandidate p u₀ C.T
  A1 := by
    intro t ht htT
    simpa [truncatedDataOfUniformCore,
      UniformTruncatedConjugateMildExistenceCore.toData]
      using A1_all (truncatedDataOfUniformCore C) t ht (by
        simpa [truncatedDataOfUniformCore,
          UniformTruncatedConjugateMildExistenceCore.toData] using htT)
  A2 := A2_data C
  A3 := A3_data hu₀ C

def energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedPicardNegativePartEnergyCoreRegularData p (u₀ := u₀) C.T := by
  let DT := truncatedDataOfUniformCore C
  let HA := energyAtoms hu₀ C
  simpa [DT, HA, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using truncatedPicardEnergyCoreRegularData_of_atomData
      DT HA.A1 HA.A2 HA.A3

/-- (4)--(5) The weak identity tested against `-u_-`, the sign of the truncated
logistic term, and Gronwall force the negative-part energy to vanish. -/
theorem nonnegative_from_energy_and_gronwall
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x :=
  truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
    (energyCore hu₀ C)

/-- (6) Jensen positive-time bypass: strict positivity of the truncated Picard
limit after any positive time. -/
theorem jensenStrictPosData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    JensenBypassStrictPosDataFor C.T
      (truncatedConjugatePicardLimit p u₀ C.T) := by
  -- Missing API: construction of the positive restart seed, positive-time
  -- Jensen inequality, and reaction-discounted mild lower bound for this exact
  -- truncated Picard limit.
  sorry

theorem fullAgreement
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀) :
    truncatedConjugatePicardLimit p u₀ C.T =
      conjugatePicardLimit p u₀ C.T := by
  -- Residual analytic input: nonnegativity of every truncated Picard
  -- ITERATE.  NOTE: `nonnegative_from_energy_and_gronwall hu₀ C` gives
  -- nonnegativity of the truncated Picard LIMIT only; it does NOT imply
  -- iterate-level nonnegativity (the truncated map truncates its input, not
  -- its output, and its kernel-gradient chemotaxis leg is sign-indefinite).
  -- See the Q3875 oracle drop: "do not claim it implies iterate
  -- nonnegativity."  This `have` isolates the exact missing atom.
  have hiter_nonneg :
      ∀ n : ℕ, ∀ s : ℝ, ∀ y : intervalDomainPoint,
        0 ≤ ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugatePicardIter
              p u₀ n s y := by
    sorry
  -- On nonnegative inputs the faithful truncated map agrees with the full
  -- B-form map, so the two Picard iterations coincide stage by stage.
  have hiter_eq :
      ∀ n : ℕ,
        ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugatePicardIter
            p u₀ n
          = ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      funext s y
      simp only
        [ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugatePicardIter,
         ShenWork.IntervalConjugatePicard.conjugatePicardIter]
      rw [← ih]
      exact
        ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg
          p u₀ (hiter_nonneg n) s y
  -- Identical iterate sequences have identical `limUnder` limits, and the
  -- zero-extension conventions off `(0, C.T]` match definitionally.
  funext t x
  simp only [truncatedConjugatePicardLimit,
    ShenWork.IntervalConjugatePicard.conjugatePicardLimit, hiter_eq]

instance paper2ChiNegV5AtomSupply (p : CM2Params) :
    Paper2ChiNegV5AtomSupply p where
  energyAtoms := by
    intro _M _hM _u₀ hu₀ _hbound C
    exact energyAtoms hu₀ C
  jensenStrictPos := by
    intro _M _hM _u₀ hu₀ _hbound C
    exact jensenStrictPosData hu₀ C
  fullAgreement := by
    intro _M _hM _u₀ hu₀ _hbound C
    exact fullAgreement hu₀ C

end ShenWork.Paper2.IntervalChiNegV5SelfContained
