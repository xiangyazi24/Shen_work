import ShenWork.Paper1.WholeLineWeightedRegularityDQSources
import ShenWork.Paper1.WholeLineWeightedRegularityFourProfilePower

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

def capShiftedReactionSpatialDQSelfConst
    (p : CMParams) (M : ℝ) : ℝ :=
  1 + reactionLip p.α M +
    fourProfileReactionDerivativeLip p.α M * M

def capShiftedReactionSpatialDQValueConst
    (p : CMParams) (M eta DU : ℝ) : ℝ :=
  capShiftedReactionSpatialDQSelfConst p M * eta +
    fourProfileReactionDerivativeLip p.α M * DU

theorem capShiftedReactionSpatialDQSelfConst_nonneg
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ capShiftedReactionSpatialDQSelfConst p M := by
  unfold capShiftedReactionSpatialDQSelfConst
  have hr := reactionLip_nonneg p.hα hM
  have hd := fourProfileReactionDerivativeLip_nonneg p.hα hM
  positivity

theorem capShiftedReactionSpatialDQValueConst_nonneg
    (p : CMParams) {M eta DU : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (hDU : 0 ≤ DU) :
    0 ≤ capShiftedReactionSpatialDQValueConst p M eta DU := by
  unfold capShiftedReactionSpatialDQValueConst
  exact add_nonneg
    (mul_nonneg (capShiftedReactionSpatialDQSelfConst_nonneg p hM) heta)
    (mul_nonneg
      (fourProfileReactionDerivativeLip_nonneg p.hα hM) hDU)

/-- A logarithmic-derivative bound and a profile ceiling give a quotient
ceiling uniform for all steps of size at most one. -/
theorem profile_spatialDifferenceQuotient_le_of_logDerivative_bound
    {U : ℝ → ℝ} {B M h : ℝ}
    (hB : 0 ≤ B)
    (hUpos : ∀ x, 0 < U x)
    (hUle : ∀ x, U x ≤ M)
    (hUdiff : Differentiable ℝ U)
    (hlog : ∀ x, |deriv U x / U x| ≤ B)
    (hh : h ≠ 0) (hh_one : |h| ≤ 1) :
    ∀ x, |spatialDifferenceQuotient h U x| ≤
      B * Real.exp (2 * B) * M := by
  intro x
  have hraw := profile_shift_quotient_le_convex_of_logDerivative_bound
    (x := x) hB hUpos hUdiff hlog hh (0 : ℝ)
    (by constructor <;> norm_num)
  have hexp : Real.exp (2 * B * |h|) ≤ Real.exp (2 * B) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    |spatialDifferenceQuotient h U x| =
        |(U (x + h) - U x) / h| := rfl
    _ ≤ (B * Real.exp (2 * B * |h|)) * U x := by
      norm_num at hraw ⊢
      exact hraw
    _ ≤ (B * Real.exp (2 * B)) * U x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hB) (hUpos x).le
    _ ≤ (B * Real.exp (2 * B)) * M :=
      mul_le_mul_of_nonneg_left (hUle x)
        (mul_nonneg hB (Real.exp_nonneg _))
    _ = B * Real.exp (2 * B) * M := by ring

/-- Matched four-profile difference quotient for the full shifted reaction.
The raw conjugated quotient is the self field; the wave quotient appears only
through its pointwise logarithmic-derivative bound. -/
theorem capWeight_wholeLineShiftedReactionDifference_spatialDQ_l2_bounded
    (p : CMParams) {M eta R h DU : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (hDU : 0 ≤ DU) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hU_quot : ∀ x, |spatialDifferenceQuotient h U x| ≤ DU)
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * (u x - U x) +
        spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2))
    (hvalue : Integrable (fun x => capWeight eta R x *
      |u x - U x| ^ 2)) :
    let LQ := capShiftedReactionSpatialDQSelfConst p M
    let CQ := capShiftedReactionSpatialDQValueConst p M eta DU
    Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h
        (fun y => wholeLineCauchyShiftedReaction p u y -
          wholeLineCauchyShiftedReaction p U y) x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |spatialDifferenceQuotient h
          (fun y => wholeLineCauchyShiftedReaction p u y -
            wholeLineCauchyShiftedReaction p U y) x| ^ 2) ≤
        2 * LQ ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |eta * (u x - U x) +
              spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        2 * CQ ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
  dsimp only
  let w : ℝ → ℝ := fun x => u x - U x
  let q : ℝ → ℝ := fun x => eta * w x + spatialDifferenceQuotient h w x
  let out : ℝ → ℝ := spatialDifferenceQuotient h
    (fun y => wholeLineCauchyShiftedReaction p u y -
      wholeLineCauchyShiftedReaction p U y)
  let LQ : ℝ := capShiftedReactionSpatialDQSelfConst p M
  let CQ : ℝ := capShiftedReactionSpatialDQValueConst p M eta DU
  have hw_cont : Continuous w := hu.1.sub hU.1
  have hshift_cont_u : Continuous (wholeLineCauchyShiftedReaction p u) :=
    hu.1.add (wholeLineLogisticSource_continuous p hu.1)
  have hshift_cont_U : Continuous (wholeLineCauchyShiftedReaction p U) :=
    hU.1.add (wholeLineLogisticSource_continuous p hU.1)
  have hout_cont : Continuous out := by
    dsimp only [out, spatialDifferenceQuotient]
    exact ((((hshift_cont_u.sub hshift_cont_U).comp
      (continuous_id.add continuous_const)).sub
        (hshift_cont_u.sub hshift_cont_U))).div_const h
  have hLQ : 0 ≤ LQ := by
    exact capShiftedReactionSpatialDQSelfConst_nonneg p hM
  have hCQ : 0 ≤ CQ := by
    exact capShiftedReactionSpatialDQValueConst_nonneg p hM heta hDU
  have hpoint : ∀ x, |out x| ≤ LQ * |q x| + CQ * |w x| := by
    intro x
    let a2 := u (x + h)
    let b2 := U (x + h)
    let a1 := u x
    let b1 := U x
    let dw := ((a2 - b2) - (a1 - b1)) / h
    let rr := ((reactionFun p.α a2 - reactionFun p.α b2) -
      (reactionFun p.α a1 - reactionFun p.α b1)) / h
    have hbase : |(b2 - b1) / h| ≤ DU := by
      simpa only [b2, b1, spatialDifferenceQuotient] using hU_quot x
    have hrr := reaction_matched_fourPoint_quotient_abs_le
      p.hα hM hDU hh (hu_mem (x + h)) (hU_mem (x + h))
      (hu_mem x) (hU_mem x) hbase
    have hdw : dw = spatialDifferenceQuotient h w x := by
      dsimp only [dw, a2, b2, a1, b1, w, spatialDifferenceQuotient]
    have hqeq : q x = eta * w x + dw := by
      rw [hdw]
    have hdw_abs : |dw| ≤ |q x| + eta * |w x| := by
      have heq : dw = q x - eta * w x := by linarith [hqeq]
      rw [heq]
      calc
        |q x - eta * w x| ≤ |q x| + |eta * w x| := abs_sub _ _
        _ = |q x| + eta * |w x| := by
          rw [abs_mul, abs_of_nonneg heta]
    have hout_eq : out x = dw + rr := by
      dsimp only [out, spatialDifferenceQuotient, dw, rr, a2, b2, a1, b1,
        wholeLineCauchyShiftedReaction, wholeLineLogisticSource]
      ring
    have hrr' : |rr| ≤
        (reactionLip p.α M +
          fourProfileReactionDerivativeLip p.α M * M) * |dw| +
        fourProfileReactionDerivativeLip p.α M * DU * |w x| := by
      simpa only [rr, dw, a2, b2, a1, b1, w] using hrr
    rw [hout_eq]
    calc
      |dw + rr| ≤ |dw| + |rr| := abs_add_le _ _
      _ ≤ |dw| +
          ((reactionLip p.α M +
            fourProfileReactionDerivativeLip p.α M * M) * |dw| +
          fourProfileReactionDerivativeLip p.α M * DU * |w x|) :=
        add_le_add le_rfl hrr'
      _ = LQ * |dw| +
          fourProfileReactionDerivativeLip p.α M * DU * |w x| := by
        dsimp only [LQ, capShiftedReactionSpatialDQSelfConst]
        ring
      _ ≤ LQ * (|q x| + eta * |w x|) +
          fourProfileReactionDerivativeLip p.α M * DU * |w x| :=
        add_le_add (mul_le_mul_of_nonneg_left hdw_abs hLQ) le_rfl
      _ = LQ * |q x| + CQ * |w x| := by
        dsimp only [CQ, capShiftedReactionSpatialDQValueConst]
        ring
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) hLQ hCQ hout_cont
    (by simpa only [q, w] using hraw)
    (by simpa only [w] using hvalue) hpoint
  refine ⟨?_, ?_⟩
  · refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x (out x)
  · calc
      (∫ x : ℝ, capWeight eta R x * |out x| ^ 2) =
          ∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          (capWeightSqrt_mul_sq_eq eta R x (out x)).symm
      _ ≤ 2 * LQ ^ 2 *
          (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
          2 * CQ ^ 2 *
            ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := hcore.2
      _ = _ := by rfl

#print axioms capWeight_wholeLineShiftedReactionDifference_spatialDQ_l2_bounded
#print axioms profile_spatialDifferenceQuotient_le_of_logDerivative_bound

end ShenWork.Paper1
