import ShenWork.Paper2.IntervalChiNegStampacchiaRefactor
import ShenWork.Paper2.IntervalBFormFaithfulBridgeProducer

open Filter Topology Set MeasureTheory

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore
   conjugatePicardIter conjugatePicardLimit)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Analytic certificate for the faithful truncated Duhamel map on the scalar
budget carried by `C`.

This is deliberately separate from `UniformConjugateMildExistenceCore`: the
uniform core fixes only scalar budgets and base-datum estimates, while the
fields below assert the actual maps-to, regularity, and contraction facts for
the truncated map. -/
structure UniformTruncatedConjugateMapCertificate
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) where
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T w →
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |truncatedConjugateDuhamelMap p u₀ w t x| ≤ C.R
  hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T w →
    HasJointMeasurability w →
    HasContinuousSlices C.T
      (fun t x => truncatedConjugateDuhamelMap p u₀ w t x)
  hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R) →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T u →
    HasContinuousSlices C.T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |truncatedConjugateDuhamelMap p u₀ u t x
        - truncatedConjugateDuhamelMap p u₀ w t x| ≤ C.K * d
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability
      (fun t x => truncatedConjugateDuhamelMap p u₀ w t x)

/-- Uniform truncated B-form Picard core, anchored to the floor-free uniform
full core but using the faithful truncated map.  The analytic map/contraction
fields are explicit; the fixed point is produced by
`truncatedConjugateMildSolutionData_of_data`. -/
structure UniformTruncatedConjugateMildExistenceCore
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) where
  hbase_cont : HasContinuousSlices C.T (truncatedConjugatePicardIter p u₀ 0)
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T w →
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |truncatedConjugateDuhamelMap p u₀ w t x| ≤ C.R
  hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T w →
    HasJointMeasurability w →
    HasContinuousSlices C.T
      (fun t x => truncatedConjugateDuhamelMap p u₀ w t x)
  hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R) →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T u →
    HasContinuousSlices C.T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |truncatedConjugateDuhamelMap p u₀ u t x
        - truncatedConjugateDuhamelMap p u₀ w t x| ≤ C.K * d
  hbase_diff : ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
    |truncatedConjugatePicardIter p u₀ 1 t x
      - truncatedConjugatePicardIter p u₀ 0 t x| ≤ C.C₀
  hbase_meas : HasJointMeasurability (truncatedConjugatePicardIter p u₀ 0)
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability
      (fun t x => truncatedConjugateDuhamelMap p u₀ w t x)

def UniformTruncatedConjugateMildExistenceCore.toData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C) :
    TruncatedConjugateMildExistenceData p u₀ where
  T := C.T
  M := C.R
  K := C.K
  C₀ := C.C₀
  hT := C.hT
  hM := C.hR
  hK := C.hK
  hK_nn := C.hK_nn
  hC₀ := C.hC₀
  hbase_ball := by
    intro t ht htT x
    simpa [truncatedConjugatePicardIter,
      ShenWork.IntervalConjugatePicard.conjugatePicardIter]
      using C.hbase_picard_ball t ht htT x
  hbase_lift_bound := by
    intro y
    have hM0_le_R : C.M0 ≤ C.R := by
      rw [C.hR_eq]
      linarith [C.hM0.le]
    unfold intervalDomainLift
    split_ifs with hy
    · exact (C.hbase_ball ⟨y, hy⟩).trans hM0_le_R
    · simpa using C.hR.le
  hbase_lift_meas := by
    have hmeas : Measurable (intervalDomainLift u₀) :=
      ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
        C.hbase_cont
    exact hmeas.aestronglyMeasurable
  hbase_cont := HT.hbase_cont
  hmapsTo := HT.hmapsTo
  hcont_preserved := HT.hcont_preserved
  hcontr := HT.hcontr
  hbase_diff := HT.hbase_diff
  hbase_meas := HT.hbase_meas
  hmeas_preserved := HT.hmeas_preserved

def UniformTruncatedConjugateMildExistenceCore.solutionData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C) :
    TruncatedConjugateMildSolutionData p u₀ :=
  truncatedConjugateMildSolutionData_of_data HT.toData

/-- Positive part applied pointwise to an interval slice. -/
def positivePartSlice (w : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun x => positivePart (w x)

theorem abs_positivePart_le_abs (r : ℝ) :
    |positivePart r| ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [positivePart, hr]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [positivePart, hr']

theorem positivePartSlice_nonneg (w : intervalDomainPoint → ℝ) :
    ∀ x, 0 ≤ positivePartSlice w x := by
  intro x
  exact positivePart_nonneg (w x)

theorem intervalDomainLift_positivePartSlice
    (w : intervalDomainPoint → ℝ) (y : ℝ) :
    intervalDomainLift (positivePartSlice w) y =
      positivePart (intervalDomainLift w y) := by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simp [intervalDomainLift, positivePartSlice, hy]
  · simp [intervalDomainLift, positivePart, hy]

theorem positivePart_lipschitz_abs (r s : ℝ) :
    |positivePart r - positivePart s| ≤ |r - s| := by
  simpa [positivePart] using
    (abs_max_sub_max_le_abs r s (0 : ℝ))

/-- Positive part applied time-slice-wise to a trajectory. -/
def positivePartTrajectory
    (w : ℝ → intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t => positivePartSlice (w t)

theorem positivePartTrajectory_ball
    {T R : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    (hwb : ∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ R) :
    ∀ t, 0 < t → t ≤ T → ∀ x,
      |positivePartTrajectory w t x| ≤ R := by
  intro t ht htT x
  exact (abs_positivePart_le_abs (w t x)).trans (hwb t ht htT x)

theorem positivePartTrajectory_nonneg
    (w : ℝ → intervalDomainPoint → ℝ) :
    ∀ t, 0 < t → t ≤ T → ∀ x,
      0 ≤ positivePartTrajectory w t x := by
  intro t _ _ x
  exact positivePart_nonneg (w t x)

theorem positivePartTrajectory_continuous
    {T : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    (hwc : HasContinuousSlices T w) :
    HasContinuousSlices T (positivePartTrajectory w) := by
  intro t ht htT
  simpa [positivePartTrajectory, positivePartSlice, positivePart] using
    (hwc t ht htT).max continuous_const

theorem positivePartTrajectory_measurable
    {w : ℝ → intervalDomainPoint → ℝ}
    (hwm : HasJointMeasurability w) :
    HasJointMeasurability (positivePartTrajectory w) := by
  change Measurable (fun q : ℝ × ℝ =>
    intervalDomainLift (positivePartTrajectory w q.1) q.2)
  have hEq :
      (fun q : ℝ × ℝ =>
        intervalDomainLift (positivePartTrajectory w q.1) q.2)
        =
      fun q : ℝ × ℝ => positivePart (intervalDomainLift (w q.1) q.2) := by
    funext q
    exact intervalDomainLift_positivePartSlice (w q.1) q.2
  rw [hEq]
  simpa [positivePart] using hwm.max measurable_const

theorem positivePartTrajectory_diff
    {T d : ℝ} {u w : ℝ → intervalDomainPoint → ℝ}
    (hd : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) :
    ∀ t, 0 < t → t ≤ T → ∀ x,
      |positivePartTrajectory u t x
        - positivePartTrajectory w t x| ≤ d := by
  intro t ht htT x
  exact (positivePart_lipschitz_abs (u t x) (w t x)).trans
    (hd t ht htT x)

/-- The chemotaxis part of the faithful truncation is the ordinary flux of the
positive-part slice.  The analogous statement for the logistic part is false:
`truncatedLogisticLocal p r` retains the leading factor `r`, not `r⁺`. -/
theorem truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    truncatedChemFluxLifted p w =
      ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
        (positivePartSlice w) := by
  funext y
  unfold truncatedChemFluxLifted
    ShenWork.IntervalGradientDuhamelMap.chemFluxLifted
  rw [intervalDomainLift_positivePartSlice]
  rfl

theorem truncatedConjugatePicardIter_zero_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    HasContinuousSlices C.T (truncatedConjugatePicardIter p u₀ 0) := by
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ C.M0 := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact C.hbase_ball ⟨y, hy⟩
    · simpa using C.hM0.le
  intro t ht _htT
  simp only [truncatedConjugatePicardIter]
  exact
    (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ht C.hM0.le hLift_bound C.hmeas_preserved.aestronglyMeasurable).comp
        continuous_subtype_val

theorem truncatedConjugatePicardIter_zero_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    HasJointMeasurability (truncatedConjugatePicardIter p u₀ 0) := by
  have hSg_meas : Measurable (fun q : ℝ × ℝ =>
      intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
    ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_joint_measurable'
      C.hmeas_preserved
  have hfield :
      (fun q : ℝ × ℝ =>
        intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 q.1) q.2)
        =
      fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Icc (0 : ℝ) 1 then
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
        else 0 := by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [truncatedConjugatePicardIter, intervalDomainLift, hy]
    · simp [intervalDomainLift, hy]
  change Measurable (fun q : ℝ × ℝ =>
    intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 q.1) q.2)
  rw [hfield]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
    hSg_meas measurable_const

/-- Combine the uniform scalar budget with an independent analytic certificate
for the faithful truncated map. -/
def uniformTruncatedConjugateMildExistenceCore_of_uniformCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (A : UniformTruncatedConjugateMapCertificate p C) :
    UniformTruncatedConjugateMildExistenceCore p C where
  hbase_cont := truncatedConjugatePicardIter_zero_continuous C
  hmapsTo := A.hmapsTo
  hcont_preserved := A.hcont_preserved
  hcontr := A.hcontr
  hbase_diff := by
    intro t ht htT x
    have hiter0_ball :
        ∀ τ, 0 < τ → τ ≤ C.T → ∀ z,
          |truncatedConjugatePicardIter p u₀ 0 τ z| ≤ C.R := by
      intro τ hτ hτT z
      simpa [truncatedConjugatePicardIter, conjugatePicardIter]
        using C.hbase_picard_ball τ hτ hτT z
    have hiter1_le :
        |truncatedConjugatePicardIter p u₀ 1 t x| ≤ C.R := by
      simpa only [truncatedConjugatePicardIter] using
        A.hmapsTo (truncatedConjugatePicardIter p u₀ 0)
          hiter0_ball (truncatedConjugatePicardIter_zero_continuous C)
          t ht htT x
    have hiter0_le :
        |truncatedConjugatePicardIter p u₀ 0 t x| ≤ C.R :=
      hiter0_ball t ht htT x
    calc
      |truncatedConjugatePicardIter p u₀ 1 t x
          - truncatedConjugatePicardIter p u₀ 0 t x|
          ≤ |truncatedConjugatePicardIter p u₀ 1 t x|
            + |truncatedConjugatePicardIter p u₀ 0 t x| := abs_sub _ _
      _ ≤ C.R + C.R := add_le_add hiter1_le hiter0_le
      _ = 2 * C.R := by ring
      _ = C.C₀ := C.hC₀_eq.symm
  hbase_meas := truncatedConjugatePicardIter_zero_measurable C
  hmeas_preserved := A.hmeas_preserved

theorem intervalConjugateMildSolution_of_uniformTruncatedCore_nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C)
    (hnonneg : ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x) :
    IntervalConjugateMildSolution p C.T u₀
      (truncatedConjugatePicardLimit p u₀ C.T) := by
  intro t ht htT x
  have hglobal :
      ∀ s : ℝ, ∀ y : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ C.T s y :=
    truncatedConjugatePicardLimit_nonneg_global
      (DT := HT.toData)
      (by
        simpa [UniformTruncatedConjugateMildExistenceCore.toData]
          using hnonneg)
  calc
    truncatedConjugatePicardLimit p u₀ C.T t x
        = truncatedConjugateDuhamelMap p u₀
            (truncatedConjugatePicardLimit p u₀ C.T) t x := by
          simpa [UniformTruncatedConjugateMildExistenceCore.toData]
            using (HT.solutionData).hmild t ht htT x
    _ = ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
            p u₀ (truncatedConjugatePicardLimit p u₀ C.T) t x :=
          truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg
            p u₀ hglobal t x

def conjugateMildSolutionData_of_uniformTruncatedCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C)
    (hnonneg : ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x)
    (hpos : ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      0 < truncatedConjugatePicardLimit p u₀ C.T t x) :
    ConjugateMildSolutionData p u₀ where
  T := C.T
  hT := C.hT
  M := C.R
  hM := C.hR
  u := truncatedConjugatePicardLimit p u₀ C.T
  hmild := intervalConjugateMildSolution_of_uniformTruncatedCore_nonneg
    HT hnonneg
  hbound := by
    intro t ht htT x
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using (HT.solutionData).hbound t ht htT x
  hnonneg := hnonneg
  hpos := hpos
  hcont := by
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using (HT.solutionData).hcont
  hmeas := by
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using (HT.solutionData).hmeas

/-- Bare-horizon regular negative-part energy core for the faithful truncated
Picard limit. -/
structure TruncatedPicardNegativePartEnergyCoreRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (T : ℝ) where
  weak_test :
    ∀ t, 0 < t → t < T →
      NegativePartWeakTestIdentityAt p
        (truncatedConjugatePicardLimit p u₀ T) t
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate :
    NegativePartEnergyEstimateRegularData p T
      (truncatedConjugatePicardLimit p u₀ T) ell E'
  energy_cont :
    ContinuousOn
      (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
      (Set.Icc (0 : ℝ) T)
  energy_has_deriv :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
        (E' t) (Set.Ici t) t
  energy_integrable :
    ∀ t, 0 < t → t ≤ T →
      Integrable
        (fun x =>
          (negativePartLift (truncatedConjugatePicardLimit p u₀ T t) x) ^ 2)
        (intervalMeasure 1)
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      negativePartEnergy (truncatedConjugatePicardLimit p u₀ T) s < ε
  zero_energy_to_pointwise_nonneg :
    ∀ t, 0 < t → t ≤ T →
      negativePartEnergy (truncatedConjugatePicardLimit p u₀ T) t = 0 →
        ∀ x : intervalDomainPoint,
          0 ≤ truncatedConjugatePicardLimit p u₀ T t x

/-- Repackage the bare truncated Picard energy core as the trajectory-typed
Stampacchia input consumed by the uniform closure. -/
def TruncatedPicardNegativePartEnergyCoreRegularData.toEnergyCoreRegularDataFor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (H : TruncatedPicardNegativePartEnergyCoreRegularData p (u₀ := u₀) T) :
    NegativePartEnergyCoreRegularDataFor p T
      (truncatedConjugatePicardLimit p u₀ T) where
  weak_test := H.weak_test
  ell := H.ell
  hell_nonneg := H.hell_nonneg
  E' := H.E'
  estimate := H.estimate
  energy_cont := H.energy_cont
  energy_has_deriv := H.energy_has_deriv
  energy_integrable := H.energy_integrable
  initial_vanishes := H.initial_vanishes
  zero_energy_to_pointwise_nonneg := H.zero_energy_to_pointwise_nonneg

/-- Stampacchia nonnegativity for the truncated Picard limit from the bare
energy core. -/
theorem truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (H : TruncatedPicardNegativePartEnergyCoreRegularData p (u₀ := u₀) T) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ T t x := by
  exact nonneg_of_negativePartEnergyCoreRegularDataFor
    H.toEnergyCoreRegularDataFor

/-- Uniform family of analytic certificates for the faithful truncated map. -/
abbrev UniformTruncatedConjugateMapCertificateData
    (p : CM2Params) : Prop :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      UniformTruncatedConjugateMapCertificate p C

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV3

open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The `truncCore` field of `UniformTruncatedStampacchiaBarrierInputs`. -/
def uniformTruncatedStampacchiaBarrierInputs_truncCore
    {p : CM2Params}
    (Hmap : UniformTruncatedConjugateMapCertificateData p) :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        UniformTruncatedConjugateMildExistenceCore p C := by
  intro _M hM _u₀ hu₀ hbound C
  exact uniformTruncatedConjugateMildExistenceCore_of_uniformCore C
    (Hmap hM hu₀ hbound C)

/-- Regular energy data for the uniform truncated Picard limit, with no
`ConjugateMildExistenceData` witness. -/
abbrev UniformTruncatedStampacchiaEnergyRegularData
    (p : CM2Params) : Type :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      TruncatedPicardNegativePartEnergyCoreRegularData p (u₀ := u₀) C.T

/-- The `energy` field of `UniformTruncatedStampacchiaBarrierInputs`, produced
from the bare regular truncated Picard energy core. -/
def uniformTruncatedStampacchiaBarrierInputs_energy
    {p : CM2Params}
    (Henergy : UniformTruncatedStampacchiaEnergyRegularData p) :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        NegativePartEnergyCoreRegularDataFor p C.T
          (truncatedConjugatePicardLimit p u₀ C.T) := by
  intro _M hM _u₀ hu₀ hbound C
  exact (Henergy hM hu₀ hbound C).toEnergyCoreRegularDataFor

/-- The remaining explicit inputs for the truncated-limit closure of the
uniform chi-negative core.  Stampacchia and square-heat certificates are stated
for the truncated fixed point, and the final field records the identification
with the older full Picard-limit name required by the V3 frontier. -/
structure UniformTruncatedStampacchiaBarrierInputs (p : CM2Params) where
  truncCore :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        UniformTruncatedConjugateMildExistenceCore p C
  energy :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        NegativePartEnergyCoreRegularDataFor p C.T
          (truncatedConjugatePicardLimit p u₀ C.T)
  strictPosBarrier :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        SqrtSeedSquareHeatStrictPosInputs C.T u₀
          (truncatedConjugatePicardLimit p u₀ C.T)
  initialTrace :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        InitialTrace intervalDomain u₀
          (truncatedConjugatePicardLimit p u₀ C.T)
  agreesWithFullPicard :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        truncatedConjugatePicardLimit p u₀ C.T =
          conjugatePicardLimit p u₀ C.T

theorem uniformCoreStampacchiaPackage_of_truncatedLimitStrategy
    {p : CM2Params} (H : UniformTruncatedStampacchiaBarrierInputs p) :
    UniformCoreStampacchiaPackage p := by
  intro M hM u₀ hu₀ hbound C _hnonneg_old _hpos_old
  let HT := H.truncCore (M := M) hM hu₀ hbound C
  have hnonnegT :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x :=
    nonneg_of_negativePartEnergyCoreRegularDataFor
      (H.energy (M := M) hM hu₀ hbound C)
  have hposT :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 < truncatedConjugatePicardLimit p u₀ C.T t x := by
    exact strictPos_of_squareHeatStrictPosDataFor C.hT
      (SqrtSeedSquareHeatStrictPosInputs.toSquareHeatStrictPosDataFor hu₀
        (H.strictPosBarrier (M := M) hM hu₀ hbound C))
  let S : ConjugateMildSolutionData p u₀ :=
    conjugateMildSolutionData_of_uniformTruncatedCore HT hnonnegT hposT
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · dsimp [S, conjugateMildSolutionData_of_uniformTruncatedCore]
    exact H.agreesWithFullPicard (M := M) hM hu₀ hbound C
  · dsimp [S, conjugateMildSolutionData_of_uniformTruncatedCore]
    exact H.initialTrace (M := M) hM hu₀ hbound C

theorem uniformCoreMildSolutionConditionalInputs_of_truncatedLimitStrategy
    {p : CM2Params} (H : UniformTruncatedStampacchiaBarrierInputs p) :
    UniformCoreMildSolutionConditionalInputs p where
  hnonneg := by
    intro M hM u₀ hu₀ hbound C t ht htT x
    have hT :=
      nonneg_of_negativePartEnergyCoreRegularDataFor
        (H.energy (M := M) hM hu₀ hbound C) t ht htT x
    simpa [H.agreesWithFullPicard (M := M) hM hu₀ hbound C] using hT
  hpos := by
    intro M hM u₀ hu₀ hbound C t ht htT x
    have hT := strictPos_of_squareHeatStrictPosDataFor C.hT
      (SqrtSeedSquareHeatStrictPosInputs.toSquareHeatStrictPosDataFor hu₀
        (H.strictPosBarrier (M := M) hM hu₀ hbound C)) t ht htT x
    simpa [H.agreesWithFullPicard (M := M) hM hu₀ hbound C] using hT
  package := uniformCoreStampacchiaPackage_of_truncatedLimitStrategy H

theorem uniformCoreMildSolutionFrontier_of_truncatedLimitStrategy
    {p : CM2Params} (H : UniformTruncatedStampacchiaBarrierInputs p) :
    UniformCoreMildSolutionFrontier p :=
  uniformCoreMildSolutionFrontier_of_conditionalInputs
    (uniformCoreMildSolutionConditionalInputs_of_truncatedLimitStrategy H)

end ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
