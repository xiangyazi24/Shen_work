import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalNegativePartEnergyTimeLeibniz
import ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
import ShenWork.Paper2.IntervalBFormCron2TruncatedCoefficientWeakTest
import ShenWork.Paper2.IntervalTruncatedPicardLimitJointContinuity
import ShenWork.Paper2.IntervalBFormFaithfulBridgeProducer
import ShenWork.PDE.IntervalFullKernelMass
import ShenWork.PDE.P3MoserGradientContinuityFromDx
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Self-contained V5 atom supply from the truncated Picard construction.

This file deliberately does not call the Batch1/Batch2/A1--A5 conditional
constructors.  It starts from a `UniformConjugateMildExistenceCore`, converts it
to the faithful truncated Picard data, extracts the raw Picard limit facts, and
then packages the V5 atoms.

The exact unresolved analytic input is recorded by `V5AnalyticResidual`:
coefficient weak testing (including the restart/IBP/Fubini step), the initial
trace, joint continuity, positive-time time regularity, and the Jensen/restart
witness.  The energy and truncated/full agreement
arguments below are then derived from those explicit hypotheses.
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData UniformConjugateMildExistenceCore
   conjugatePicardLimit)
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
  (continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod)
open ShenWork.Paper2.BFormPositiveDatumNegPart
   (TruncatedConjugateMildExistenceData TruncatedConjugateMildSolutionData
   truncatedConjugateMildSolutionData_of_data truncatedConjugatePicardLimit
   truncatedNegativePartWeakTestIdentityAt_of_coefficientData
   TruncatedNegativePartCoefficientWeakTestData
   TruncatedPicardNegativePartEnergyEstimateA2Data
   TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData
   truncatedConjugatePicardLimit_nonneg_of_positiveTime_regular_energyCore
   negativePartEnergy negativePartDissipation negativePartTest negativePartLift
   negativePart negativePart_eq_neg_of_nonpos deriv_negativePartLift_eq_zero_of_pos
   truncatedLogisticLifted truncatedLogisticLocal
   truncatedConjugatePicardLimitJoint
   truncatedConjugatePicardIterJoint
   positiveInitialDatum_intervalDomainLift_nonneg
   UniformTruncatedConjugateMildExistenceCore
   UniformTruncatedFullCoreResidual)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegV5SelfContained

/-- Positive-time Jensen inequality in the exact form consumed by the strict
positivity bypass. -/
def FullKernelJensenInequalityV5 (f : ℝ → ℝ) : Prop :=
  ∀ ⦃σ x : ℝ⦄, 0 < σ →
    (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ f x) ^ 2 ≤
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ
        (fun y => (f y) ^ 2) x

/-- Reaction-discounted lower mild inequality on a positive time increment. -/
def ReactionDiscountedMildLowerV5
    (D : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃s σ x : ℝ⦄, 0 < σ →
    Real.exp (-D * σ) *
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ
          (fun y => u s y) x
      ≤ u (s + σ) x

/-- Exact Jensen/restart witness still needed for strict positivity. -/
structure JensenBypassStrictPosDataForV5
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  witness :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      ∃ D s σ : ℝ, ∃ f : ℝ → ℝ,
        0 < σ ∧
        s + σ = t ∧
        ReactionDiscountedMildLowerV5 D
          (fun r y => u r (ShenWork.IntervalMildPicardThreshold.unitClip y)) ∧
        FullKernelJensenInequalityV5 f ∧
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ
            (fun y => (f y) ^ 2) x.1 ≤
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ
            (fun y => u s
              (ShenWork.IntervalMildPicardThreshold.unitClip y)) x.1 ∧
        0 < ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          σ f x.1

/-- Honest residual for the analytic gaps audited in this file.

The inherited fields are the actual truncated and full contraction data,
together with the horizon and ball compatibility needed by the faithful-limit
bridge.  The local fields record the coefficient weak test, initial trace,
joint continuity, compact-window time regularity, and the full Jensen/restart
witness. -/
structure V5AnalyticResidual
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    extends UniformTruncatedFullCoreResidual p C where
  coefficient_weak_test :
    ∀ t, 0 < t → t ≤ C.T →
      TruncatedNegativePartCoefficientWeakTestData p truncCore.toData t
  initial_trace : InitialTrace intervalDomain u₀
    (truncatedConjugatePicardLimit p u₀ C.T)
  iterate_joint : ∀ n,
    ContinuousOn (truncatedConjugatePicardIterJoint p u₀ n)
      (Set.Ioc (0 : ℝ) C.T ×ˢ Set.Icc (0 : ℝ) 1)
  limit_time_differentiable :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < C.T →
      ∀ r ∈ Set.Icc a b, ∀ z : intervalDomainPoint,
        DifferentiableAt ℝ
          (fun s : ℝ => truncatedConjugatePicardLimit p u₀ C.T s z) r
  timeDeriv_joint :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < C.T →
      ContinuousOn
        (fun q : ℝ × ℝ =>
          intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv
                (truncatedConjugatePicardLimit p u₀ C.T) q.1 z) q.2)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
  jensen : JensenBypassStrictPosDataForV5 C.T
    (truncatedConjugatePicardLimit p u₀ C.T)

/-- Tested weak identity and energy-estimate atoms at one residual-backed
truncated core. -/
structure V5EnergyAtoms
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) where
  E' : ℝ → ℝ
  A1 : ∀ t, 0 < t → t ≤ C.T →
    TruncatedNegativePartCoefficientWeakTestData p H.truncCore.toData t
  A2 : TruncatedPicardNegativePartEnergyEstimateA2Data
    p (u₀ := u₀) C.T E'

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
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    TruncatedConjugateMildExistenceData p u₀ :=
  H.truncCore.toData

/-- The actual Picard-limit package produced by the truncated contraction. -/
def rawPicardLimitData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    TruncatedConjugateMildSolutionData p u₀ :=
  truncatedConjugateMildSolutionData_of_data
    (truncatedDataOfUniformCore C H)

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
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    HasContinuousSlices C.T (truncatedConjugatePicardLimit p u₀ C.T) := by
  simpa [rawPicardLimitData, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using (rawPicardLimitData C H).hcont

theorem raw_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ C.T t x| ≤ C.R := by
  intro t ht htT x
  simpa [rawPicardLimitData, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using (rawPicardLimitData C H).hbound t ht htT x

theorem raw_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    HasJointMeasurability (truncatedConjugatePicardLimit p u₀ C.T) := by
  simpa [rawPicardLimitData, truncatedDataOfUniformCore,
    UniformTruncatedConjugateMildExistenceCore.toData]
    using (rawPicardLimitData C H).hmeas

def raw_truncated_mild
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    TruncatedConjugateMildSolutionData p u₀ := rawPicardLimitData C H

/-- The coefficient weak-test route is an independent frontier.  In
particular, it contains the restart kernel IBP/Fubini data missing from the
current positive-time gradient wiring. -/
def A1_all
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    ∀ t, 0 < t → t ≤ C.T →
      TruncatedNegativePartCoefficientWeakTestData p H.truncCore.toData t :=
  H.coefficient_weak_test

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
      Integrable
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
    apply ContinuousOn.mul continuousOn_id
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
  have hint : IntegrableOn
      (fun x =>
        truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x *
          negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
      (Set.Icc (0 : ℝ) 1) :=
    hprod.integrableOn_compact isCompact_Icc
  simpa [intervalMeasure, ShenWork.IntervalDomain.intervalSet] using hint

def A2_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    TruncatedPicardNegativePartEnergyEstimateA2Data
      p (u₀ := u₀) C.T (energyDerivativeCandidate p u₀ C.T) := by
  refine
    { neg_deriv_zero_on_pos := by
        intro t ht htT
        filter_upwards
          [lift_continuousAt_ae_of_slices
            (raw_hasContinuousSlices C H) t ht htT] with x hx hpos
        exact deriv_negativePartLift_eq_zero_of_pos hx hpos
      time_chain := by
        intro t _ht _htT
        dsimp [energyDerivativeCandidate]
        ring
      diffusion_chain := by
        intro t ht htT
        unfold negativePartDissipation
        exact integral_congr_ae
          (diffusion_chain_ae (raw_hasContinuousSlices C H) t ht htT)
      diffusion_nonneg := by
        intro t _ht _htT
        unfold negativePartDissipation
        exact integral_nonneg_of_ae
          (Eventually.of_forall fun x =>
            sq_nonneg (deriv (negativePartLift
              (truncatedConjugatePicardLimit p u₀ C.T t)) x))
      logistic_integrable :=
        logistic_test_aestronglyMeasurable
          (raw_hasContinuousSlices C H) (raw_bound C H)
      energy_integrable := ?_ }
  · intro t ht htT
    exact
      ShenWork.Paper2.BFormPositiveDatumNegPart.negativePart_sq_integrable_of_continuous_bound
          (raw_hasContinuousSlices C H t ht htT)
          (le_of_lt C.hR)
          (raw_bound C H t ht htT)

theorem raw_jointContinuousOn_positive_windows
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b ≤ C.T →
      ContinuousOn
        (fun q : ℝ × ℝ =>
          intervalDomainLift
            (truncatedConjugatePicardLimit p u₀ C.T q.1) q.2)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro a b ha _hab hbT
  have hIoc :
      ContinuousOn
        (truncatedConjugatePicardLimitJoint p u₀ C.T)
        (Set.Ioc (0 : ℝ) C.T ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [truncatedDataOfUniformCore,
      UniformTruncatedConjugateMildExistenceCore.toData] using
      ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugatePicardLimit_jointContinuousOn_Ioc_of_data
        (truncatedDataOfUniformCore C H) H.iterate_joint
  have hsub : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioc (0 : ℝ) C.T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    exact ⟨⟨lt_of_lt_of_le ha hq.1.1, hq.1.2.trans hbT⟩, hq.2⟩
  simpa [truncatedConjugatePicardLimitJoint] using hIoc.mono hsub

theorem raw_energy_continuousOn_positive_windows
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
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
        (p := p) (u₀ := u₀) C H ha hab hbT
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
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    ContinuousOn
      (negativePartEnergy (truncatedConjugatePicardLimit p u₀ C.T))
      (Set.Icc (0 : ℝ) C.T) := by
  set u : ℝ → intervalDomainPoint → ℝ :=
    truncatedConjugatePicardLimit p u₀ C.T
  set E : ℝ → ℝ := negativePartEnergy u
  have htrace : InitialTrace intervalDomain u₀ u := by
    simpa [u] using H.initial_trace
  have hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x := by
    intro x
    have h := positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
    simpa [intervalDomainLift, x.2] using h
  have hvanish :
      ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < C.T → E s < ε := by
    simpa [u, E] using
      (ShenWork.Paper2.BFormPositiveDatumNegPart.negativePartEnergy_initial_vanishes_of_trace_nonneg
          hu₀.admissible hu₀_nonneg htrace (raw_hasContinuousSlices C H)
          (le_of_lt C.hR) (raw_bound C H))
  have hE_zero : E 0 = 0 := by
    have hu_zero : u 0 = fun _ : intervalDomainPoint => 0 := by
      funext x
      simp [u, truncatedConjugatePicardLimit]
    simp [E, negativePartEnergy, hu_zero, negativePartLift,
      intervalDomainLift, negativePart]
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
    · have hy_nonneg : 0 ≤ y := hy_mem
      have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
      have hy_delta : y < δ₀ := by
        have hdist : dist y 0 < min δ₀ C.T := by simpa [dist_comm] using hy_dist
        have hy_abs : |y| < min δ₀ C.T := by
          simpa [Real.dist_eq] using hdist
        have hy_lt_min : y < min δ₀ C.T := by
          simpa [abs_of_nonneg hy_nonneg] using hy_abs
        exact lt_of_lt_of_le hy_lt_min (min_le_left _ _)
      have hy_T : y < C.T := by
        have hdist : dist y 0 < min δ₀ C.T := by simpa [dist_comm] using hy_dist
        have hy_abs : |y| < min δ₀ C.T := by
          simpa [Real.dist_eq] using hdist
        have hy_lt_min : y < min δ₀ C.T := by
          simpa [abs_of_nonneg hy_nonneg] using hy_abs
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
          (p := p) (u₀ := u₀) C H hhalf_pos hhalf_le_T le_rfl
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
    (H : V5AnalyticResidual p C)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < C.T) :
    ∃ B : ℝ,
      ∀ᵐ x ∂ intervalMeasure 1, ∀ r ∈ Set.Icc a b,
        HasDerivWithinAt
          (fun s : ℝ =>
            intervalDomainLift
              (truncatedConjugatePicardLimit p u₀ C.T s) x)
          (intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv
                (truncatedConjugatePicardLimit p u₀ C.T) r z) x)
          (Set.Icc a b) r ∧
        |intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv
                (truncatedConjugatePicardLimit p u₀ C.T) r z) x| ≤ B := by
  exact
    ShenWork.Paper2.BFormPositiveDatumNegPart.timeDerivativeWindowData_of_jointContinuousOn
      (H.limit_time_differentiable ha hab hbT)
      (H.timeDeriv_joint ha hab hbT)

theorem energy_has_deriv
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    ∀ t, 0 < t → t < C.T →
      HasDerivWithinAt
        (negativePartEnergy (truncatedConjugatePicardLimit p u₀ C.T))
        (energyDerivativeCandidate p u₀ C.T t) (Set.Ici t) t := by
  intro t ht htT
  let b := (t + C.T) / 2
  have htb : t < b := by
    dsimp [b]
    linarith
  have hbT : b < C.T := by
    dsimp [b]
    linarith
  rcases raw_timeDerivativeWindowData C H ht htb.le hbT with ⟨B, hwindow⟩
  have hcont_b : HasContinuousSlices b
      (truncatedConjugatePicardLimit p u₀ C.T) := by
    intro r hr hrb
    exact raw_hasContinuousSlices C H r hr (hrb.trans hbT.le)
  have hbound_b : ∀ r, 0 < r → r ≤ b → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ C.T r x| ≤ C.R := by
    intro r hr hrb x
    exact raw_bound C H r hr (hrb.trans hbT.le) x
  simpa [energyDerivativeCandidate] using
    (ShenWork.Paper2.BFormPositiveDatumNegPart.negativePartEnergy_hasDerivWithinAt_Ici_of_window_data
        (T := b) (t := t) (R := C.R) (B := B)
        (u := truncatedConjugatePicardLimit p u₀ C.T)
        ht htb (le_of_lt C.hR) hcont_b hbound_b hwindow)

def energyAtoms
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    V5EnergyAtoms p C H where
  E' := energyDerivativeCandidate p u₀ C.T
  A1 := A1_all C H
  A2 := A2_data C H

def energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData
      p (u₀ := u₀) C.T := by
  let HA := energyAtoms C H
  have hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x := by
    intro x
    have h := positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
    simpa [intervalDomainLift, x.2] using h
  exact
    { weak_test := fun t ht htT =>
        truncatedNegativePartWeakTestIdentityAt_of_coefficientData
          (HA.A1 t ht htT)
      ell := p.a
      hell_nonneg := p.ha
      E' := HA.E'
      estimate := HA.A2.toEstimate
      energy_cont := energy_continuous hu₀ C H
      energy_has_deriv := energy_has_deriv C H
      energy_integrable := HA.A2.energy_integrable
      initial_vanishes :=
        ShenWork.Paper2.BFormPositiveDatumNegPart.negativePartEnergy_initial_vanishes_of_trace_nonneg
          hu₀.admissible hu₀_nonneg H.initial_trace
          (raw_hasContinuousSlices C H) (le_of_lt C.hR) (raw_bound C H)
      zero_energy_to_pointwise_nonneg :=
        ShenWork.Paper2.BFormPositiveDatumNegPart.negativePartEnergy_zero_to_pointwise_nonneg_of_continuous
          (raw_hasContinuousSlices C H) HA.A2.energy_integrable }

/-- (4)--(5) The weak identity tested against `-u_-`, the sign of the truncated
logistic term, and Gronwall force the negative-part energy to vanish. -/
theorem nonnegative_from_energy_and_gronwall
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x :=
  truncatedConjugatePicardLimit_nonneg_of_positiveTime_regular_energyCore
    (energyCore hu₀ C H)

/-- (6) Jensen positive-time bypass: strict positivity of the truncated Picard
limit after any positive time. -/
theorem jensenStrictPosData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    JensenBypassStrictPosDataForV5 C.T
      (truncatedConjugatePicardLimit p u₀ C.T) :=
  H.jensen

theorem fullAgreement
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) :
    truncatedConjugatePicardLimit p u₀ C.T =
      conjugatePicardLimit p u₀ C.T := by
  let DT := H.truncCore.toData
  let DB := H.fullData
  have hbridge :
      ShenWork.Paper2.BFormPositiveDatumNegPart.TruncatedConjugateLimitBridge
        p DB DT :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugateLimitBridge_of_faithful_truncation
      { hT := by
          simpa [DT, DB, UniformTruncatedConjugateMildExistenceCore.toData,
            H.full_horizon]
        truncated_nonneg := by
          simpa [DT, UniformTruncatedConjugateMildExistenceCore.toData] using
            nonnegative_from_energy_and_gronwall hu₀ C H
        truncated_bound_in_full_ball := by
          intro t ht htT x
          have htC : t ≤ C.T := by
            simpa [DB, H.full_horizon] using htT
          exact (raw_bound C H t ht htC x).trans
            H.truncated_ball_le_full_ball }
  rcases hbridge with ⟨hT, hlim⟩
  have hagree :
      truncatedConjugatePicardLimit p u₀ DT.T =
        conjugatePicardLimit p u₀ DB.T := by
    funext t x
    by_cases ht : 0 < t ∧ t ≤ DB.T
    · exact (hlim t ht.1 ht.2 x).symm
    · have htDT : ¬(0 < t ∧ t ≤ DT.T) := by
        intro h
        exact ht ⟨h.1, by simpa [hT] using h.2⟩
      simp [truncatedConjugatePicardLimit, conjugatePicardLimit, ht, htDT]
  simpa [DT, DB, UniformTruncatedConjugateMildExistenceCore.toData,
    H.full_horizon] using hagree

/-- The three closed V5 outputs, with every unresolved analytic producer
visible in `V5AnalyticResidual`. -/
structure V5ClosedAtoms
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) : Type where
  energy : TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData
    p (u₀ := u₀) C.T
  jensen : JensenBypassStrictPosDataForV5 C.T
    (truncatedConjugatePicardLimit p u₀ C.T)
  agreement : truncatedConjugatePicardLimit p u₀ C.T =
    conjugatePicardLimit p u₀ C.T

def closedAtoms
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (C : UniformConjugateMildExistenceCore p u₀)
    (H : V5AnalyticResidual p C) : V5ClosedAtoms p C where
  energy := energyCore hu₀ C H
  jensen := jensenStrictPosData hu₀ C H
  agreement := fullAgreement hu₀ C H

#print axioms raw_jointContinuousOn_positive_windows
#print axioms raw_timeDerivativeWindowData
#print axioms nonnegative_from_energy_and_gronwall
#print axioms fullAgreement
#print axioms closedAtoms

end ShenWork.Paper2.IntervalChiNegV5SelfContained
