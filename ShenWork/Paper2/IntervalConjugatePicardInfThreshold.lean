/-
  B-form Picard positivity from an absolute initial-data floor.

  This file is additive.  It proves the small-time inf-threshold positivity
  estimate for the conjugate Picard limit without using the
  `ConjugateMildExistenceData.hmapsTo_pos` field.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalConjugatePicardBounds
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter conjugatePicardLimit)
open ShenWork.IntervalMildPicard
  (real_cauchySeq_of_geometric_bound)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalFullSemigroupOperator_lower_bound)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.Paper2
  (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- The paper-positive closed-interval floor. -/
def paperPositiveFloor {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) : ℝ :=
  (PaperPositiveInitialDatum.floor hu₀).choose

theorem paperPositiveFloor_pos {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    0 < paperPositiveFloor hu₀ :=
  (PaperPositiveInitialDatum.floor hu₀).choose_spec.1

theorem paperPositiveFloor_le {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (x : intervalDomainPoint) :
    paperPositiveFloor hu₀ ≤ u₀ x :=
  (PaperPositiveInitialDatum.floor hu₀).choose_spec.2 x

/-- B-form Picard facts needed by the inf-threshold argument.  This package
contains ball-derived source bounds and geometric convergence, but no positivity
field for the map or the limit. -/
structure ConjugatePicardInfThresholdData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) where
  K : ℝ
  C₀ : ℝ
  CQ : ℝ
  CL : ℝ
  hT : 0 < T
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hCQ : 0 ≤ CQ
  hCL : 0 ≤ CL
  hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
    ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀
  hQ_int : ∀ n s,
    Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s))
      (intervalMeasure 1)
  hQ_bound : ∀ n s y,
    |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ
  hB_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
  hL_bound : ∀ n s y,
    |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
  hL_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t

private theorem intervalDomainLift_abs_bound_of_subtype_bound
    {u₀ : intervalDomainPoint → ℝ} {B : ℝ} (hBnn : 0 ≤ B)
    (hB : ∀ x : intervalDomainPoint, |u₀ x| ≤ B) :
    ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ B := by
  intro y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa [intervalDomainLift, hy] using hB ⟨y, hy⟩
  · simp [intervalDomainLift, hy, hBnn]

/-- The full Neumann semigroup preserves a closed-interval positive floor for
paper-positive interval data. -/
theorem intervalFullSemigroupOperator_ge_paperPositiveFloor
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    paperPositiveFloor hu₀ ≤
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x := by
  have hadm := PaperPositiveInitialDatum.admissible hu₀
  change BddAbove (Set.range fun x : intervalDomainPoint => |u₀ x|)
      ∧ Continuous u₀ at hadm
  rcases hadm with ⟨hBdd, hu₀_cont⟩
  rcases hBdd with ⟨B, hB⟩
  set B' : ℝ := max (max B (paperPositiveFloor hu₀)) 0 with hB'def
  have hB'_nn : 0 ≤ B' := by
    rw [hB'def]
    exact le_max_right _ _
  have hcB : paperPositiveFloor hu₀ ≤ B' := by
    rw [hB'def]
    exact le_trans (le_max_right B (paperPositiveFloor hu₀)) (le_max_left _ _)
  have hsub_bound : ∀ z : intervalDomainPoint, |u₀ z| ≤ B' := by
    intro z
    exact le_trans (hB (Set.mem_range_self z))
      (le_trans (le_max_left B (paperPositiveFloor hu₀)) (le_max_left _ _))
  have hlift_bound : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ B' :=
    intervalDomainLift_abs_bound_of_subtype_bound hB'_nn hsub_bound
  have hmeas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1) :=
    (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      hu₀_cont).aestronglyMeasurable
  refine intervalFullSemigroupOperator_lower_bound ht
    (le_of_lt (paperPositiveFloor_pos hu₀)) hcB hmeas ?_ hlift_bound x
  intro y hy
  simpa [intervalDomainLift, hy] using paperPositiveFloor_le hu₀ ⟨y, hy⟩

/-- One B-form Picard-map step stays above half the initial floor under the
absolute inf-threshold smallness condition. -/
theorem intervalConjugateDuhamelMap_ge_half_floor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (H : ConjugatePicardInfThresholdData p u₀ T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
        + T * H.CL ≤ paperPositiveFloor hu₀ / 2)
    (n : ℕ) {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint) :
    paperPositiveFloor hu₀ / 2 ≤
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x := by
  set S : ℝ := intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  set B : ℝ := ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s)
      (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1
  set R : ℝ := ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s)
      (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1
  have hS : paperPositiveFloor hu₀ ≤ S := by
    simpa [S] using intervalFullSemigroupOperator_ge_paperPositiveFloor
      hu₀ ht x.1
  have hB_abs : |B| ≤
      heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ := by
    simpa [B] using
      ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
        ht htT (fun s _ _ => H.hQ_int n s) H.hCQ
        (fun s _ _ => H.hQ_bound n s) x.1 (H.hB_int n t ht htT x)
  have hchem_abs :
      |(-p.χ₀) * B| ≤
        |p.χ₀| *
          (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hB_abs (abs_nonneg p.χ₀)
  have hchem_lower :
      -(|p.χ₀| *
          (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ))
        ≤ (-p.χ₀) * B :=
    (abs_le.mp hchem_abs).1
  have hR_abs : |R| ≤ T * H.CL := by
    simpa [R] using
      ShenWork.IntervalGradDuhamelBound.valueDuhamel_sup_bound
        ht htT H.hCL (H.hL_bound n) x.1 (H.hL_int n t ht htT x)
  have hR_lower : -(T * H.CL) ≤ R := (abs_le.mp hR_abs).1
  change paperPositiveFloor hu₀ / 2 ≤ S + (-p.χ₀) * B + R
  linarith

/-- Every B-form Picard iterate stays above half the closed-domain initial floor
on the small inf-threshold horizon. -/
theorem conjugatePicardIter_ge_half_floor_of_PID
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (H : ConjugatePicardInfThresholdData p u₀ T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
        + T * H.CL ≤ paperPositiveFloor hu₀ / 2) :
    ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      paperPositiveFloor hu₀ / 2 ≤ conjugatePicardIter p u₀ n t x := by
  intro n
  induction n with
  | zero =>
      intro t ht _htT x
      have hS := intervalFullSemigroupOperator_ge_paperPositiveFloor hu₀ ht x.1
      have hhalf : paperPositiveFloor hu₀ / 2 ≤ paperPositiveFloor hu₀ := by
        linarith [paperPositiveFloor_pos hu₀]
      simpa [conjugatePicardIter] using le_trans hhalf hS
  | succ n _ih =>
      intro t ht htT x
      simpa [conjugatePicardIter] using
        intervalConjugateDuhamelMap_ge_half_floor hu₀ H hsmall n ht htT x

/-- Absolute inf-threshold positivity of the B-form Picard limit. -/
theorem conjugatePicardLimit_pos_of_PID
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (H : ConjugatePicardInfThresholdData p u₀ T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
        + T * H.CL ≤ paperPositiveFloor hu₀ / 2) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 < conjugatePicardLimit p u₀ T t x := by
  intro t ht htT x
  have hiter :=
    conjugatePicardIter_ge_half_floor_of_PID hu₀ H hsmall
  have hlim_ge : paperPositiveFloor hu₀ / 2 ≤
      conjugatePicardLimit p u₀ T t x := by
    unfold conjugatePicardLimit
    simp only [ht, htT, and_self, ite_true]
    set a := fun m => conjugatePicardIter p u₀ m t x
    have hcauchy : CauchySeq a :=
      real_cauchySeq_of_geometric_bound H.hK H.hK_nn H.hC₀
        (fun n => H.hgeom n t ht htT x)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
    rw [hL.limUnder_eq]
    exact ge_of_tendsto hL
      (Eventually.of_forall (fun n => hiter n t ht htT x))
  have hhalf_pos : 0 < paperPositiveFloor hu₀ / 2 := by
    linarith [paperPositiveFloor_pos hu₀]
  exact lt_of_lt_of_le hhalf_pos hlim_ge

/-- Interval-lift form of `conjugatePicardLimit_pos_of_PID`, matching the
`hpost` field consumed by localized source machinery. -/
theorem conjugatePicardLimit_hpost_of_PID
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (H : ConjugatePicardInfThresholdData p u₀ T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
        + T * H.CL ≤ paperPositiveFloor hu₀ / 2) :
    ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardLimit p u₀ T σ) x := by
  intro σ hσ hσT x hx
  have hpos := conjugatePicardLimit_pos_of_PID hu₀ H hsmall
    σ hσ hσT.le ⟨x, hx⟩
  simpa [intervalDomainLift, hx] using hpos

#print axioms intervalFullSemigroupOperator_ge_paperPositiveFloor
#print axioms conjugatePicardLimit_pos_of_PID
#print axioms conjugatePicardLimit_hpost_of_PID

end ShenWork.IntervalConjugatePicard
