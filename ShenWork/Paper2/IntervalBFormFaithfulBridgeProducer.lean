import ShenWork.Paper2.IntervalBFormCron2Concrete
import ShenWork.Paper2.IntervalConjugatePicardUniqueness

open Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap
   intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit
   intervalConjugateMildSolution_unique_of_data)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalDomainExistence
  (intervalLogisticSource)
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- A nonnegative interval slice has a nonnegative zero extension. -/
lemma intervalDomainLift_nonneg_of_slice_nonneg
    {w : intervalDomainPoint → ℝ} (hw : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    ∀ y : ℝ, 0 ≤ intervalDomainLift w y := by
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · exact hw ⟨y, hy⟩
  · exact le_rfl

/-- On nonnegative slices, the faithful truncated flux is the original flux. -/
theorem truncatedChemFluxLifted_eq_chemFluxLifted_of_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    truncatedChemFluxLifted p w = chemFluxLifted p w := by
  have hpositivePart : (fun x : intervalDomainPoint => positivePart (w x)) = w := by
    funext x
    exact positivePart_eq_self_of_nonneg (hw x)
  funext y
  have hy_nonneg : 0 ≤ intervalDomainLift w y :=
    intervalDomainLift_nonneg_of_slice_nonneg hw y
  -- `simp only` avoids unfolding `positivePart` inside the resolver argument
  -- `fun x => positivePart (w x)`, so `hpositivePart` can still rewrite it to `w`
  -- (full `simp` rewrites it to `max (w ·) 0` first and the match is lost).
  simp only [truncatedChemFluxLifted, chemFluxLifted, hpositivePart,
    positivePart_eq_self_of_nonneg hy_nonneg]

/-- On nonnegative slices, the truncated logistic source is the original source. -/
theorem truncatedLogisticLifted_eq_logisticLifted_of_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    truncatedLogisticLifted p w = logisticLifted p w := by
  funext y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hwy : 0 ≤ w ⟨y, hy⟩ := hw ⟨y, hy⟩
    simp [truncatedLogisticLifted, truncatedLogisticLocal, logisticLifted,
      intervalLogisticSource, intervalDomainLift, hy,
      positivePart_eq_self_of_nonneg hwy]
  · simp [truncatedLogisticLifted, truncatedLogisticLocal, logisticLifted,
      intervalDomainLift, hy]

/-- If a trajectory is pointwise nonnegative, the faithful truncated B-form map
agrees with the full B-form map at that trajectory. -/
theorem truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu : ∀ t : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u t x) :
    ∀ t x,
      truncatedConjugateDuhamelMap p u₀ u t x
        = intervalConjugateDuhamelMap p u₀ u t x := by
  intro t x
  have hflux :
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (u s)) x.1)
        =
      fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x.1 := by
    funext s
    rw [truncatedChemFluxLifted_eq_chemFluxLifted_of_nonneg
      (p := p) (w := u s) (hu s)]
  have hlog :
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (u s)) x.1)
        =
      fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (u s)) x.1 := by
    funext s
    rw [truncatedLogisticLifted_eq_logisticLifted_of_nonneg
      (p := p) (w := u s) (hu s)]
  unfold truncatedConjugateDuhamelMap intervalConjugateDuhamelMap
  rw [hflux, hlog]

/-- Satisfiable producer inputs for the bridge.

`truncated_nonneg` is the endpoint of the negative-part energy argument for the
faithful truncated fixed point.  `truncated_bound_in_full_ball` is the ball
membership needed to apply the full-map contraction uniqueness from `DB`. -/
structure TruncatedConjugateLimitBridgeProducerData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀) : Prop where
  hT : DT.T = DB.T
  truncated_nonneg :
    ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x
  truncated_bound_in_full_ball :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ DT.T t x| ≤ DB.M

/-- The truncated Picard limit is globally nonnegative when it is nonnegative
on its active time window, since it is zero outside that window. -/
lemma truncatedConjugatePicardLimit_nonneg_global
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (htrunc :
      ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x) :
    ∀ t : ℝ, ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x := by
  intro t x
  by_cases ht : 0 < t ∧ t ≤ DT.T
  · exact htrunc t ht.1 ht.2 x
  · simp [truncatedConjugatePicardLimit, ht]

/-- Producer for the concrete bridge between the faithful truncated fixed point
and the full B-form Picard limit. -/
theorem truncatedConjugateLimitBridge_of_faithful_truncation
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (H : TruncatedConjugateLimitBridgeProducerData p DB DT) :
    TruncatedConjugateLimitBridge p DB DT := by
  refine ⟨H.hT, ?_⟩
  let uT : ℝ → intervalDomainPoint → ℝ :=
    truncatedConjugatePicardLimit p u₀ DT.T
  have huT_nonneg_global : ∀ t : ℝ, ∀ x : intervalDomainPoint, 0 ≤ uT t x := by
    intro t x
    exact truncatedConjugatePicardLimit_nonneg_global
      H.truncated_nonneg t x
  have htrunc_mild : TruncatedConjugateMildSolution p DT.T u₀ uT := by
    simpa [uT] using (truncatedConjugateMildSolutionData_of_data DT).hmild
  have hfull_mild : IntervalConjugateMildSolution p DB.T u₀ uT := by
    intro t ht htT x
    have htDT : t ≤ DT.T := by
      simpa [H.hT] using htT
    calc
      uT t x = truncatedConjugateDuhamelMap p u₀ uT t x :=
        htrunc_mild t ht htDT x
      _ = intervalConjugateDuhamelMap p u₀ uT t x :=
        truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg
          p u₀ huT_nonneg_global t x
  have huT_nonneg_DB :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint, 0 ≤ uT t x := by
    intro t _ht _htT x
    exact huT_nonneg_global t x
  have huT_cont : HasContinuousSlices DB.T uT := by
    have hc : HasContinuousSlices DT.T uT := by
      simpa [uT] using (truncatedConjugateMildSolutionData_of_data DT).hcont
    intro t ht htT
    exact hc t ht (by simpa [H.hT] using htT)
  have huT_meas : HasJointMeasurability uT := by
    simpa [uT] using (truncatedConjugateMildSolutionData_of_data DT).hmeas
  have huniq :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        uT t x = conjugatePicardLimit p u₀ DB.T t x :=
    intervalConjugateMildSolution_unique_of_data DB hfull_mild
      H.truncated_bound_in_full_ball huT_nonneg_DB huT_cont huT_meas
  intro t ht htT x
  exact (huniq t ht htT x).symm

end ShenWork.Paper2.BFormPositiveDatumNegPart
