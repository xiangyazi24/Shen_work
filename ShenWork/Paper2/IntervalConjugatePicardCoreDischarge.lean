import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalConjugatePicardBounds
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicardBounds
  (intervalConjugateDuhamelMap_diff_bound_of_banked)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- Reduced B-form Picard core.  Compared with `ConjugateMildExistenceData`, the
global contraction field is not carried: it is rebuilt from the banked
conjugate-kernel `sqrt T` estimate plus the named flux/logistic component
bounds below. -/
structure ConjugateMildExistenceCore (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M : ℝ
  K : ℝ
  C₀ : ℝ
  CQ : ℝ
  CL : ℝ
  hT : 0 < T
  hM : 0 < M
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hCQ : 0 ≤ CQ
  hCL : 0 ≤ CL
  hK_eq :
    K =
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
        + T * CL
  hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ 0 t x| ≤ M
  hbase_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ conjugatePicardIter p u₀ 0 t x
  hbase_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0)
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalConjugateDuhamelMap p u₀ w t x| ≤ M
  hmapsTo_nn : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ intervalConjugateDuhamelMap p u₀ w t x
  hmapsTo_pos : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 < intervalConjugateDuhamelMap p u₀ w t x
  hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    HasJointMeasurability w →
    HasContinuousSlices T (fun t x => intervalConjugateDuhamelMap p u₀ w t x)
  hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x| ≤ C₀
  hbase_meas : HasJointMeasurability (conjugatePicardIter p u₀ 0)
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability (fun t x => intervalConjugateDuhamelMap p u₀ w t x)
  hflux_diff_bound : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ s y, |chemFluxLifted p (u s) y - chemFluxLifted p (w s) y| ≤ CQ * d
  hflux_diff_integrable : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ s, Integrable
      (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y)
      (intervalMeasure 1)
  hflux_kernel_integrable_left : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, ∀ s,
      Integrable
        (fun y =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y
            * chemFluxLifted p (u s) y)
        (intervalMeasure 1)
  hflux_kernel_integrable_right : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, ∀ s,
      Integrable
        (fun y =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y
            * chemFluxLifted p (w s) y)
        (intervalMeasure 1)
  hflux_duhamel_integrable_left : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      IntervalIntegrable
        (fun s : ℝ =>
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x.1)
        volume 0 t
  hflux_duhamel_integrable_right : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      IntervalIntegrable
        (fun s : ℝ =>
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
        volume 0 t
  hflux_duhamel_diff_integrable : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      IntervalIntegrable
        (fun s : ℝ =>
          intervalConjugateKernelOperator (t - s)
            (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y) x.1)
        volume 0 t
  hlogistic_duhamel_diff_bound : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |(∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
        - (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)|
        ≤ T * (CL * d)

private def endpointZero : intervalDomainPoint :=
  ⟨0, by constructor <;> norm_num⟩

theorem ConjugateMildExistenceCore.contraction_from_banked
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : ConjugateMildExistenceCore p u₀) :
    ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.M) →
      (∀ t, 0 < t → t ≤ C.T → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.M) →
      (∀ t, 0 < t → t ≤ C.T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices C.T u →
      HasContinuousSlices C.T w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀ u t x
          - intervalConjugateDuhamelMap p u₀ w t x| ≤ C.K * d := by
  intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x
  have hd_nonneg : 0 ≤ d := by
    have h := hd C.T C.hT le_rfl endpointZero
    exact (abs_nonneg _).trans h
  have hDq : 0 ≤ C.CQ * d := mul_nonneg C.hCQ hd_nonneg
  have hbank :
      |intervalConjugateDuhamelMap p u₀ u t x
        - intervalConjugateDuhamelMap p u₀ w t x|
        ≤ |p.χ₀| *
            (heatGradientLinftyLinftyConstant * (2 * Real.sqrt C.T) * (C.CQ * d))
          + C.T * (C.CL * d) :=
    intervalConjugateDuhamelMap_diff_bound_of_banked
      (p := p) (u₀ := u₀) (u := u) (w := w)
      (t := t) (T := C.T) ht htT x
      (Dq := C.CQ * d) (Cv := C.T * (C.CL * d)) hDq
      (C.hflux_diff_bound u w d hub hun hwb hwn huc hwc hum hwm hd)
      (C.hflux_diff_integrable u w d hub hun hwb hwn huc hwc hum hwm hd)
      (C.hflux_kernel_integrable_left u w d hub hun hwb hwn huc hwc hum hwm hd
        t ht htT x)
      (C.hflux_kernel_integrable_right u w d hub hun hwb hwn huc hwc hum hwm hd
        t ht htT x)
      (C.hflux_duhamel_integrable_left u w d hub hun hwb hwn huc hwc hum hwm hd
        t ht htT x)
      (C.hflux_duhamel_integrable_right u w d hub hun hwb hwn huc hwc hum hwm hd
        t ht htT x)
      (C.hflux_duhamel_diff_integrable u w d hub hun hwb hwn huc hwc hum hwm hd
        t ht htT x)
      (C.hlogistic_duhamel_diff_bound u w d hub hun hwb hwn huc hwc hum hwm hd
        t ht htT x)
  calc
    |intervalConjugateDuhamelMap p u₀ u t x
      - intervalConjugateDuhamelMap p u₀ w t x|
        ≤ |p.χ₀| *
            (heatGradientLinftyLinftyConstant * (2 * Real.sqrt C.T) * (C.CQ * d))
          + C.T * (C.CL * d) := hbank
    _ = C.K * d := by
      rw [C.hK_eq]
      ring

/-- Rebuild the original Picard data from the reduced core. -/
def ConjugateMildExistenceCore.toData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : ConjugateMildExistenceCore p u₀) :
    ConjugateMildExistenceData p u₀ where
  T := C.T
  M := C.M
  K := C.K
  C₀ := C.C₀
  hT := C.hT
  hM := C.hM
  hK := C.hK
  hK_nn := C.hK_nn
  hC₀ := C.hC₀
  hbase_ball := C.hbase_ball
  hbase_nonneg := C.hbase_nonneg
  hbase_cont := C.hbase_cont
  hmapsTo := C.hmapsTo
  hmapsTo_nn := C.hmapsTo_nn
  hmapsTo_pos := C.hmapsTo_pos
  hcont_preserved := C.hcont_preserved
  hcontr := C.contraction_from_banked
  hbase_diff := C.hbase_diff
  hbase_meas := C.hbase_meas
  hmeas_preserved := C.hmeas_preserved

/-- Mathlib Banach closure for the complete sup-ball model.  The model-specific
construction of the complete ball and its metric is the remaining standard
fact; once supplied, fixed-point existence is obtained here from
`ContractingWith.exists_fixedPoint'`. -/
theorem conjugateMild_fixedPoint_from_complete_contraction
    {α : Type*} [MetricSpace α]
    {s : Set α} {Φ : α → α} {K : ℝ}
    (hK : K < 1) (hK_nn : 0 ≤ K)
    (hcomplete : IsComplete s) (hself : MapsTo Φ s s)
    (hdist : ∀ a b : s,
      dist (hself.restrict Φ s s a) (hself.restrict Φ s s b) ≤
        K * dist a b)
    {x₀ : α} (hx₀ : x₀ ∈ s) (hedist : edist x₀ (Φ x₀) ≠ ⊤) :
    ∃ y ∈ s, Function.IsFixedPt Φ y ∧
      Tendsto (fun n => Φ^[n] x₀) atTop (𝓝 y) := by
  have hcontract : ContractingWith K.toNNReal (hself.restrict Φ s s) := by
    refine ⟨?_, ?_⟩
    · exact Real.toNNReal_lt_one.mpr hK
    · refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.coe_toNNReal K hK_nn]
      exact hdist a b
  obtain ⟨y, hy_mem, hy_fix, hy_tendsto, _⟩ :=
    hcontract.exists_fixedPoint' hcomplete hself hx₀ hedist
  exact ⟨y, hy_mem, hy_fix, hy_tendsto⟩

/-- The reduced core produces the same B-form Picard limit package as the old
data, but the contraction field inside that data is reconstructed from the
banked component estimates above. -/
def conjugateMildSolutionData_of_core
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : ConjugateMildExistenceCore p u₀) :
    ConjugateMildSolutionData p u₀ :=
  conjugateMildSolutionData_of_data C.toData

/-- Combined constructor: the concrete B-form Picard package is obtained from
the reduced core, while fixed-point existence in any supplied complete sup-ball
model is obtained by Mathlib's Banach theorem. -/
theorem conjugateMildSolutionData_and_banachFixedPoint_of_core
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : ConjugateMildExistenceCore p u₀)
    {α : Type*} [MetricSpace α]
    {s : Set α} {Φ : α → α}
    (hcomplete : IsComplete s) (hself : MapsTo Φ s s)
    (hdist : ∀ a b : s,
      dist (hself.restrict Φ s s a) (hself.restrict Φ s s b) ≤
        C.K * dist a b)
    {x₀ : α} (hx₀ : x₀ ∈ s) (hedist : edist x₀ (Φ x₀) ≠ ⊤) :
    ∃ D : ConjugateMildSolutionData p u₀,
      D = conjugateMildSolutionData_of_core C ∧
        ∃ y ∈ s, Function.IsFixedPt Φ y ∧
          Tendsto (fun n => Φ^[n] x₀) atTop (𝓝 y) :=
  ⟨conjugateMildSolutionData_of_core C,
    rfl,
    conjugateMild_fixedPoint_from_complete_contraction C.hK C.hK_nn
      hcomplete hself hdist hx₀ hedist⟩

end ShenWork.IntervalConjugatePicard
