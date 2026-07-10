import ShenWork.Paper2.IntervalChiNegStampacchiaRefactor
import ShenWork.Paper2.IntervalBFormFaithfulBridgeProducer
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy

/-!
Faithful truncated-core interfaces for the uniform chi-negative route.

`UniformConjugateMildExistenceCore` stores scalar budgets, but it does not
store the analytic estimates saying that those budgets control the actual
full or truncated Duhamel maps.  In particular, its `CQ`, `CL`, `CQsup`, and
`CLsup` fields only carry nonnegativity.  Therefore an arbitrary uniform core
cannot canonically produce truncated contraction data.

This file keeps that frontier explicit.  `UniformTruncatedFullCoreResidual`
is the minimal per-core input used below: an actual truncated contraction core,
an actual full Picard data set on the same horizon, and inclusion of the
truncated ball in the full ball.  These fields are independently checkable and
are exactly what the faithful-limit uniqueness bridge consumes.
-/

open Filter Topology Set MeasureTheory

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugateMildSolutionData
   UniformConjugateMildExistenceCore conjugatePicardLimit)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Actual contraction data for the faithful truncated map, indexed by a
uniform scalar-budget core with the same horizon and radius. -/
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
    unfold ShenWork.IntervalDomain.intervalDomainLift
    split_ifs with hy
    · exact (C.hbase_ball ⟨y, hy⟩).trans hM0_le_R
    · simpa using C.hR.le
  hbase_lift_meas := by
    have hmeas : Measurable
        (ShenWork.IntervalDomain.intervalDomainLift u₀) :=
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

/-- Minimal honest residual relating one uniform scalar core to actual full and
truncated contraction data. -/
structure UniformTruncatedFullCoreResidual
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) where
  truncCore : UniformTruncatedConjugateMildExistenceCore p C
  fullData : ConjugateMildExistenceData p u₀
  full_horizon : fullData.T = C.T
  truncated_ball_le_full_ball : C.R ≤ fullData.M

/-- A nonnegative faithful truncated fixed point is also a full B-form mild
solution. -/
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
    _ = intervalConjugateDuhamelMap p u₀
            (truncatedConjugatePicardLimit p u₀ C.T) t x :=
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

/-- Minimal trajectory-indexed regular negative-part energy data.  The
Gronwall argument starts at an arbitrary positive time, so it only needs the
energy derivative strictly inside `(0, T)`. -/
structure NegativePartEnergyCoreRegularPositiveTimeDataFor
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  weak_test : ∀ t, 0 < t → t ≤ T → NegativePartWeakTestIdentityAt p u t
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate : NegativePartEnergyEstimateRegularData p T u ell E'
  energy_cont : ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T)
  energy_has_deriv : ∀ t, 0 < t → t < T →
    HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t
  energy_integrable : ∀ t, 0 < t → t ≤ T →
    Integrable (fun x => (negativePartLift (u t) x) ^ 2) (intervalMeasure 1)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    negativePartEnergy u s < ε
  zero_energy_to_pointwise_nonneg : ∀ t, 0 < t → t ≤ T →
    negativePartEnergy u t = 0 → ∀ x : intervalDomainPoint, 0 ≤ u t x

theorem nonneg_of_negativePartEnergyCoreRegularPositiveTimeDataFor
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : NegativePartEnergyCoreRegularPositiveTimeDataFor p T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u t x := by
  intro t ht htT x
  let E := negativePartEnergy u
  have hE_nonneg : ∀ τ, 0 < τ → τ ≤ T → 0 ≤ E τ := by
    intro τ hτ0 hτT
    have _hint := H.energy_integrable τ hτ0 hτT
    exact MeasureTheory.integral_nonneg_of_ae
      (Eventually.of_forall fun y => negativePartEnergyDensity_nonneg u τ y)
  have hderiv_le : ∀ τ, 0 < τ → τ < T →
      H.E' τ ≤ (2 * H.ell) * E τ := by
    intro τ hτ0 hτT
    have hhalf := negativePart_half_energy_deriv_le_regular
      H.estimate (H.weak_test τ hτ0 hτT.le) hτ0 hτT.le
    nlinarith
  have hgron :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ s τ, 0 < s → s ≤ τ → τ ≤ T →
        E τ ≤ E s * Real.exp (K * (τ - s)) := by
    refine ⟨2 * H.ell, mul_nonneg (by norm_num) H.hell_nonneg, ?_⟩
    intro s τ hs hsτ hτT
    have hcont : ContinuousOn E (Set.Icc s τ) :=
      H.energy_cont.mono (by
        intro r hr
        exact ⟨le_trans (le_of_lt hs) hr.1, le_trans hr.2 hτT⟩)
    have hderiv : ∀ r ∈ Set.Ico s τ,
        HasDerivWithinAt E (H.E' r) (Set.Ici r) r := by
      intro r hr
      exact H.energy_has_deriv r
        (lt_of_lt_of_le hs hr.1) (lt_of_lt_of_le hr.2 hτT)
    have hbound : ∀ r ∈ Set.Ico s τ,
        H.E' r ≤ (2 * H.ell) * E r := by
      intro r hr
      exact hderiv_le r (lt_of_lt_of_le hs hr.1)
        (lt_of_lt_of_le hr.2 hτT)
    exact ShenWork.Paper2.intervalDomainL2_gronwall_exp_of_diffIneq
      (E := E) (E' := H.E') (K := 2 * H.ell)
      hsτ hcont hderiv hbound
  have hE_zero : E t = 0 :=
    energy_eq_zero_of_positive_time_gronwall hE_nonneg hgron
      H.initial_vanishes t ht htT
  exact H.zero_energy_to_pointwise_nonneg t ht htT hE_zero x

/-- Endpoint-strong compatibility package used by the older A3 wiring.  New
closures should prefer `NegativePartEnergyCoreRegularPositiveTimeDataFor`. -/
structure NegativePartEnergyCoreRegularDataFor
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  weak_test : ∀ t, 0 < t → t ≤ T → NegativePartWeakTestIdentityAt p u t
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate : NegativePartEnergyEstimateRegularData p T u ell E'
  energy_cont : ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T)
  energy_has_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
    HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t
  energy_integrable : ∀ t, 0 < t → t ≤ T →
    Integrable (fun x => (negativePartLift (u t) x) ^ 2) (intervalMeasure 1)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    negativePartEnergy u s < ε
  zero_energy_to_pointwise_nonneg : ∀ t, 0 < t → t ≤ T →
    negativePartEnergy u t = 0 → ∀ x : intervalDomainPoint, 0 ≤ u t x

theorem nonneg_of_negativePartEnergyCoreRegularDataFor
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : NegativePartEnergyCoreRegularDataFor p T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u t x :=
  nonneg_of_negativePartEnergyCoreRegularPositiveTimeDataFor
    { weak_test := H.weak_test
      ell := H.ell
      hell_nonneg := H.hell_nonneg
      E' := H.E'
      estimate := H.estimate
      energy_cont := H.energy_cont
      energy_has_deriv := fun t ht htT => H.energy_has_deriv t ⟨ht.le, htT⟩
      energy_integrable := H.energy_integrable
      initial_vanishes := H.initial_vanishes
      zero_energy_to_pointwise_nonneg := H.zero_energy_to_pointwise_nonneg }

/-- Minimal bare-horizon regular negative-part energy core for the faithful
truncated Picard limit. -/
structure TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (T : ℝ) where
  weak_test : ∀ t, 0 < t → t ≤ T →
    NegativePartWeakTestIdentityAt p (truncatedConjugatePicardLimit p u₀ T) t
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate : NegativePartEnergyEstimateRegularData p T
    (truncatedConjugatePicardLimit p u₀ T) ell E'
  energy_cont : ContinuousOn
    (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
    (Set.Icc (0 : ℝ) T)
  energy_has_deriv : ∀ t, 0 < t → t < T →
    HasDerivWithinAt
      (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
      (E' t) (Set.Ici t) t
  energy_integrable : ∀ t, 0 < t → t ≤ T →
    Integrable
      (fun x => (negativePartLift
        (truncatedConjugatePicardLimit p u₀ T t) x) ^ 2)
      (intervalMeasure 1)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    negativePartEnergy (truncatedConjugatePicardLimit p u₀ T) s < ε
  zero_energy_to_pointwise_nonneg : ∀ t, 0 < t → t ≤ T →
    negativePartEnergy (truncatedConjugatePicardLimit p u₀ T) t = 0 →
      ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ T t x

def TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData.toEnergyCoreDataFor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (H : TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData
      p (u₀ := u₀) T) :
    NegativePartEnergyCoreRegularPositiveTimeDataFor p T
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

theorem truncatedConjugatePicardLimit_nonneg_of_positiveTime_regular_energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (H : TruncatedPicardNegativePartEnergyCoreRegularPositiveTimeData
      p (u₀ := u₀) T) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ T t x :=
  nonneg_of_negativePartEnergyCoreRegularPositiveTimeDataFor
    H.toEnergyCoreDataFor

/-- Endpoint-strong compatibility core retained for the older A3 wiring. -/
structure TruncatedPicardNegativePartEnergyCoreRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (T : ℝ) where
  weak_test : ∀ t, 0 < t → t ≤ T →
    NegativePartWeakTestIdentityAt p (truncatedConjugatePicardLimit p u₀ T) t
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate : NegativePartEnergyEstimateRegularData p T
    (truncatedConjugatePicardLimit p u₀ T) ell E'
  energy_cont : ContinuousOn
    (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
    (Set.Icc (0 : ℝ) T)
  energy_has_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
    HasDerivWithinAt
      (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
      (E' t) (Set.Ici t) t
  energy_integrable : ∀ t, 0 < t → t ≤ T →
    Integrable
      (fun x => (negativePartLift
        (truncatedConjugatePicardLimit p u₀ T t) x) ^ 2)
      (intervalMeasure 1)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    negativePartEnergy (truncatedConjugatePicardLimit p u₀ T) s < ε
  zero_energy_to_pointwise_nonneg : ∀ t, 0 < t → t ≤ T →
    negativePartEnergy (truncatedConjugatePicardLimit p u₀ T) t = 0 →
      ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ T t x

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

theorem truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (H : TruncatedPicardNegativePartEnergyCoreRegularData p (u₀ := u₀) T) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ T t x :=
  nonneg_of_negativePartEnergyCoreRegularDataFor
    H.toEnergyCoreRegularDataFor

#print axioms intervalConjugateMildSolution_of_uniformTruncatedCore_nonneg
#print axioms nonneg_of_negativePartEnergyCoreRegularPositiveTimeDataFor
#print axioms truncatedConjugatePicardLimit_nonneg_of_positiveTime_regular_energyCore
#print axioms nonneg_of_negativePartEnergyCoreRegularDataFor
#print axioms truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore

end ShenWork.Paper2.BFormPositiveDatumNegPart
