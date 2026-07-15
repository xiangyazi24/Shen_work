import ShenWork.Paper1.WholeLineWeightedRegularityMatchedFluxDQ
import ShenWork.Paper1.WholeLineWeightedRegularityMatchedReactionDQ
import ShenWork.Paper1.WholeLineWeightedRegularityNonlinearity

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Raw spatial quotients of the matched nonlinear sources

The spatial Henry argument controls the conjugated raw quotient
`eta * w + D_h w`.  The matched four-profile estimates are stated first for
`D_h` itself.  This file performs the two elementary, but load-bearing,
conversions without ever isolating a weighted difference quotient of the
traveling wave.
-/

/-- Recover the ordinary spatial difference quotient from the conjugated raw
quotient and the value field.  The estimate is uniform in the cap radius. -/
theorem capWeight_spatialDifferenceQuotient_l2_bounded_of_raw
    {eta R h : ℝ} (heta : 0 ≤ eta)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hvalue : Integrable (fun x : ℝ =>
      capWeight eta R x * |w x| ^ 2))
    (hraw : Integrable (fun x : ℝ => capWeight eta R x *
      |eta * w x + spatialDifferenceQuotient h w x| ^ 2)) :
    Integrable (fun x : ℝ => capWeight eta R x *
        |spatialDifferenceQuotient h w x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h w x| ^ 2) ≤
        2 * (∫ x : ℝ, capWeight eta R x *
          |eta * w x + spatialDifferenceQuotient h w x| ^ 2) +
        2 * eta ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
  let q : ℝ → ℝ := fun x =>
    eta * w x + spatialDifferenceQuotient h w x
  let d : ℝ → ℝ := w
  let out : ℝ → ℝ := spatialDifferenceQuotient h w
  have hout_cont : Continuous out := by
    dsimp only [out, spatialDifferenceQuotient]
    exact ((hw.comp (continuous_id.add continuous_const)).sub hw).div_const h
  have hpoint : ∀ x, |out x| ≤ 1 * |q x| + eta * |d x| := by
    intro x
    have heq : out x = q x - eta * d x := by
      dsimp only [out, q, d]
      ring
    rw [heq]
    calc
      |q x - eta * d x| ≤ |q x| + |eta * d x| := abs_sub _ _
      _ = 1 * |q x| + eta * |d x| := by
        rw [abs_mul, abs_of_nonneg heta]
        ring
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (Cq := (1 : ℝ)) (C0 := eta)
    zero_le_one heta hout_cont
    (by simpa only [q] using hraw)
    (by simpa only [d] using hvalue) hpoint
  have hout_int : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h w x| ^ 2) := by
    refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x
      (spatialDifferenceQuotient h w x)
  refine ⟨hout_int, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |spatialDifferenceQuotient h w x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2 := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x =>
            (capWeightSqrt_mul_sq_eq eta R x (out x)).symm
    _ ≤ 2 * 1 ^ 2 *
          (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
        2 * eta ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |d x| ^ 2 := hcore.2
    _ = 2 * (∫ x : ℝ, capWeight eta R x *
          |eta * w x + spatialDifferenceQuotient h w x| ^ 2) +
        2 * eta ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
            simp only [q, d, one_pow, mul_one]

/-- Coefficient of the perturbation raw-quotient energy in the matched flux
raw-source estimate. -/
def matchedFluxRawQSquareConstant
    (p : CMParams) (M eta : ℝ) : ℝ :=
  4 * matchedFluxQuotientQSquareConstant p M eta

/-- Coefficient of the perturbation value energy in the matched flux
raw-source estimate. -/
def matchedFluxRawWSquareConstant
    (p : CMParams) (M Brel DU eta h : ℝ) : ℝ :=
  4 * matchedFluxQuotientQSquareConstant p M eta * eta ^ 2 +
    2 * matchedFluxQuotientWSquareConstant p M Brel DU eta h +
    2 * eta ^ 2 * capWeightedFluxSquareConstant p M eta

theorem matchedFluxQuotientQSquareConstant_nonneg
    (p : CMParams) (M eta : ℝ) :
    0 ≤ matchedFluxQuotientQSquareConstant p M eta := by
  simp only [matchedFluxQuotientQSquareConstant]
  positivity

theorem matchedFluxQuotientWSquareConstant_nonneg
    (p : CMParams) (M Brel DU eta h : ℝ) :
    0 ≤ matchedFluxQuotientWSquareConstant p M Brel DU eta h := by
  simp only [matchedFluxQuotientWSquareConstant]
  positivity

theorem capWeightedFluxSquareConstant_nonneg
    (p : CMParams) (M eta : ℝ) :
    0 ≤ capWeightedFluxSquareConstant p M eta := by
  unfold capWeightedFluxSquareConstant
  positivity

/-- Continuity of the physical flux on a bounded physical strip. -/
theorem wholeLineChemotaxisFlux_continuous_of_Icc
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) :
    Continuous (wholeLineChemotaxisFlux p u) := by
  unfold wholeLineChemotaxisFlux
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  exact (hu.1.rpow_const (fun _ => Or.inr hm0)).mul
    ((frozenElliptic_deriv_lipschitz_of_Icc
      p hM hu hu_mem).continuous)

/-- The conjugated raw spatial quotient of the genuine matched chemotactic
flux is controlled by the raw perturbation quotient and the perturbation
value.  No weighted quotient of the traveling wave occurs. -/
theorem capWeight_genuineFluxDifference_rawSpatialDQ_l2_bounded
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hbase : ∀ x, |(U (x + h) - U x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        Brel * (tau * U (x + h) + (1 - tau) * U x))
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * (u x - U x) +
        spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2)) :
    let F := fun y => wholeLineChemotaxisFlux p u y -
      wholeLineChemotaxisFlux p U y
    Integrable (fun x => capWeight eta R x *
        |eta * F x + spatialDifferenceQuotient h F x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |eta * F x + spatialDifferenceQuotient h F x| ^ 2) ≤
        matchedFluxRawQSquareConstant p M eta *
          (∫ x : ℝ, capWeight eta R x *
            |eta * (u x - U x) +
              spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        matchedFluxRawWSquareConstant p M Brel DU eta h *
          ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
  dsimp only
  let w : ℝ → ℝ := fun x => u x - U x
  let q : ℝ → ℝ := fun x => eta * w x + spatialDifferenceQuotient h w x
  let F : ℝ → ℝ := fun y => wholeLineChemotaxisFlux p u y -
    wholeLineChemotaxisFlux p U y
  let D : ℝ → ℝ := spatialDifferenceQuotient h F
  let Fq : ℝ → ℝ := fun x => eta * F x + D x
  let IW : ℝ := ∫ x : ℝ, capWeight eta R x * |w x| ^ 2
  let IQ : ℝ := ∫ x : ℝ, capWeight eta R x * |q x| ^ 2
  let ID : ℝ := ∫ x : ℝ, capWeight eta R x * |D x| ^ 2
  let IDw : ℝ := ∫ x : ℝ, capWeight eta R x *
    |spatialDifferenceQuotient h w x| ^ 2
  let IF : ℝ := ∫ x : ℝ, capWeight eta R x * |F x| ^ 2
  let CQ : ℝ := matchedFluxQuotientQSquareConstant p M eta
  let CW : ℝ := matchedFluxQuotientWSquareConstant p M Brel DU eta h
  let CF : ℝ := capWeightedFluxSquareConstant p M eta
  have hw_cont : Continuous w := hu.1.sub hU.1
  have hDw := capWeight_spatialDifferenceQuotient_l2_bounded_of_raw
    (eta := eta) (R := R) (h := h) heta0 hw_cont
    (by simpa only [w] using hW) (by simpa only [w, q] using hraw)
  have hD :=
    capWeighted_genuineFluxDifference_matchedSpatialDQ_l2_bounded_by_perturbation_energies
      p hM hBrel hDU heta0 heta1 hh hu hU hu_mem hU_mem hUpos
        hbase hrelative hW hDw.1
  have hFbase := capWeighted_flux_difference_l2_bounded
    p hM heta0 heta1 hu hU hu_mem hU_mem hW
  have hDint : Integrable (fun x => capWeight eta R x * |D x| ^ 2) := by
    refine hD.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x (D x)
  have hFint : Integrable (fun x => capWeight eta R x * |F x| ^ 2) := by
    simpa only [F, capWeightedFluxDifference, wholeLineChemotaxisFlux,
      capWeightSqrt_mul_sq_eq] using hFbase.1
  have hF_cont : Continuous F :=
    (wholeLineChemotaxisFlux_continuous_of_Icc p hM hu hu_mem).sub
      (wholeLineChemotaxisFlux_continuous_of_Icc p hM hU hU_mem)
  have hD_cont : Continuous D := by
    dsimp only [D, spatialDifferenceQuotient]
    exact ((hF_cont.comp (continuous_id.add continuous_const)).sub
      hF_cont).div_const h
  have hFq_cont : Continuous Fq :=
    (hF_cont.const_mul eta).add hD_cont
  have hpoint : ∀ x, |Fq x| ≤ 1 * |D x| + eta * |F x| := by
    intro x
    dsimp only [Fq]
    calc
      |eta * F x + D x| ≤ |D x| + |eta * F x| := by
        simpa [add_comm] using abs_add_le (D x) (eta * F x)
      _ = 1 * |D x| + eta * |F x| := by
        rw [abs_mul, abs_of_nonneg heta0]
        ring
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (Cq := (1 : ℝ)) (C0 := eta)
    zero_le_one heta0 hFq_cont hDint hFint hpoint
  have hout : Integrable (fun x => capWeight eta R x * |Fq x| ^ 2) := by
    refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x (Fq x)
  refine ⟨by simpa only [Fq, F, D] using hout, ?_⟩
  have hCQ : 0 ≤ CQ := by
    exact matchedFluxQuotientQSquareConstant_nonneg p M eta
  have hCW : 0 ≤ CW := by
    exact matchedFluxQuotientWSquareConstant_nonneg p M Brel DU eta h
  have hCF : 0 ≤ CF := by
    exact capWeightedFluxSquareConstant_nonneg p M eta
  have hD_eq : ID = ∫ x : ℝ,
      (capWeightSqrt eta R x * D x) ^ 2 := by
    dsimp only [ID]
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      (capWeightSqrt_mul_sq_eq eta R x (D x)).symm
  have hD_le : ID ≤ CQ * IDw + CW * IW := by
    rw [hD_eq]
    simpa only [D, CQ, IDw, w, CW, IW] using hD.2
  have hDw_le : IDw ≤ 2 * IQ + 2 * eta ^ 2 * IW := by
    simpa only [IDw, w, IQ, q, IW] using hDw.2
  have hF_le : IF ≤ CF * IW := by
    simpa only [IF, F, CF, IW, w, capWeightedFluxDifference,
      wholeLineChemotaxisFlux, capWeightSqrt_mul_sq_eq] using hFbase.2
  calc
    (∫ x : ℝ, capWeight eta R x * |eta * F x + D x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * Fq x) ^ 2 := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change capWeight eta R x * |Fq x| ^ 2 =
              (capWeightSqrt eta R x * Fq x) ^ 2
            exact (capWeightSqrt_mul_sq_eq eta R x (Fq x)).symm
    _ ≤ 2 * 1 ^ 2 * ID + 2 * eta ^ 2 * IF := by
      simpa only [ID, IF, one_pow, mul_one] using hcore.2
    _ = 2 * ID + 2 * eta ^ 2 * IF := by ring
    _ ≤ 2 * (CQ * IDw + CW * IW) +
        2 * eta ^ 2 * (CF * IW) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hD_le (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hF_le
          (mul_nonneg (by norm_num) (sq_nonneg eta)))
    _ ≤ 2 * (CQ * (2 * IQ + 2 * eta ^ 2 * IW) + CW * IW) +
        2 * eta ^ 2 * (CF * IW) := by
      have hinner : CQ * IDw + CW * IW ≤
          CQ * (2 * IQ + 2 * eta ^ 2 * IW) + CW * IW :=
        by simpa only [add_comm] using
          (add_le_add_right (mul_le_mul_of_nonneg_left hDw_le hCQ)
            (CW * IW))
      simpa only [add_comm] using
        (add_le_add_right
          (mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 2))
          (2 * eta ^ 2 * (CF * IW)))
    _ = matchedFluxRawQSquareConstant p M eta * IQ +
        matchedFluxRawWSquareConstant p M Brel DU eta h * IW := by
      dsimp only [matchedFluxRawQSquareConstant,
        matchedFluxRawWSquareConstant, CQ, CW, CF]
      ring
    _ = _ := by rfl

/-- Coefficient of the perturbation raw-quotient energy in the matched
shifted-reaction raw-source estimate. -/
def matchedShiftedReactionRawQSquareConstant
    (p : CMParams) (M : ℝ) : ℝ :=
  4 * capShiftedReactionSpatialDQSelfConst p M ^ 2

/-- Coefficient of the perturbation value energy in the matched
shifted-reaction raw-source estimate. -/
def matchedShiftedReactionRawWSquareConstant
    (p : CMParams) (M eta DU : ℝ) : ℝ :=
  4 * capShiftedReactionSpatialDQValueConst p M eta DU ^ 2 +
    2 * eta ^ 2 * (1 + reactionLip p.α M) ^ 2

/-- The conjugated raw spatial quotient of the genuine matched shifted
reaction is controlled by the same two perturbation energies as the flux
leg. -/
theorem capWeight_genuineShiftedReactionDifference_rawSpatialDQ_l2_bounded
    (p : CMParams) {M eta R h DU : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (hDU : 0 ≤ DU) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hU_quot : ∀ x, |spatialDifferenceQuotient h U x| ≤ DU)
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * (u x - U x) +
        spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2)) :
    let F := fun y => wholeLineCauchyShiftedReaction p u y -
      wholeLineCauchyShiftedReaction p U y
    Integrable (fun x => capWeight eta R x *
        |eta * F x + spatialDifferenceQuotient h F x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |eta * F x + spatialDifferenceQuotient h F x| ^ 2) ≤
        matchedShiftedReactionRawQSquareConstant p M *
          (∫ x : ℝ, capWeight eta R x *
            |eta * (u x - U x) +
              spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        matchedShiftedReactionRawWSquareConstant p M eta DU *
          ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
  dsimp only
  let w : ℝ → ℝ := fun x => u x - U x
  let q : ℝ → ℝ := fun x => eta * w x + spatialDifferenceQuotient h w x
  let F : ℝ → ℝ := fun y => wholeLineCauchyShiftedReaction p u y -
    wholeLineCauchyShiftedReaction p U y
  let D : ℝ → ℝ := spatialDifferenceQuotient h F
  let Fq : ℝ → ℝ := fun x => eta * F x + D x
  let IW : ℝ := ∫ x : ℝ, capWeight eta R x * |w x| ^ 2
  let IQ : ℝ := ∫ x : ℝ, capWeight eta R x * |q x| ^ 2
  let ID : ℝ := ∫ x : ℝ, capWeight eta R x * |D x| ^ 2
  let IF : ℝ := ∫ x : ℝ, capWeight eta R x * |F x| ^ 2
  let LQ : ℝ := capShiftedReactionSpatialDQSelfConst p M
  let CQ : ℝ := capShiftedReactionSpatialDQValueConst p M eta DU
  let LF : ℝ := 1 + reactionLip p.α M
  have hD := capWeight_wholeLineShiftedReactionDifference_spatialDQ_l2_bounded
    p hM heta hDU hh hu hU hu_mem hU_mem hU_quot hraw hW
  have hFbase := capWeighted_shiftedReaction_difference_l2_bounded
    p hM hu hU hu_mem hU_mem hW
  have hFint : Integrable (fun x => capWeight eta R x * |F x| ^ 2) := by
    simpa only [F, capWeightedShiftedReactionDifference,
      capWeightSqrt_mul_sq_eq] using hFbase.1
  have hF_cont : Continuous F :=
    (wholeLineCauchyShiftedReaction_continuous p hu.1).sub
      (wholeLineCauchyShiftedReaction_continuous p hU.1)
  have hD_cont : Continuous D := by
    dsimp only [D, spatialDifferenceQuotient]
    exact ((hF_cont.comp (continuous_id.add continuous_const)).sub
      hF_cont).div_const h
  have hFq_cont : Continuous Fq :=
    (hF_cont.const_mul eta).add hD_cont
  have hpoint : ∀ x, |Fq x| ≤ 1 * |D x| + eta * |F x| := by
    intro x
    dsimp only [Fq]
    calc
      |eta * F x + D x| ≤ |D x| + |eta * F x| := by
        simpa [add_comm] using abs_add_le (D x) (eta * F x)
      _ = 1 * |D x| + eta * |F x| := by
        rw [abs_mul, abs_of_nonneg heta]
        ring
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (Cq := (1 : ℝ)) (C0 := eta)
    zero_le_one heta hFq_cont hD.1 hFint hpoint
  have hout : Integrable (fun x => capWeight eta R x * |Fq x| ^ 2) := by
    refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x (Fq x)
  refine ⟨by simpa only [Fq, F, D] using hout, ?_⟩
  have hD_le : ID ≤ 2 * LQ ^ 2 * IQ + 2 * CQ ^ 2 * IW := by
    simpa only [ID, D, LQ, IQ, q, CQ, IW, w] using hD.2
  have hF_le : IF ≤ LF ^ 2 * IW := by
    simpa only [IF, F, LF, IW, w,
      capWeightedShiftedReactionDifference, capWeightSqrt_mul_sq_eq]
      using hFbase.2
  calc
    (∫ x : ℝ, capWeight eta R x * |eta * F x + D x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * Fq x) ^ 2 := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change capWeight eta R x * |Fq x| ^ 2 =
              (capWeightSqrt eta R x * Fq x) ^ 2
            exact (capWeightSqrt_mul_sq_eq eta R x (Fq x)).symm
    _ ≤ 2 * 1 ^ 2 * ID + 2 * eta ^ 2 * IF := by
      simpa only [ID, IF] using hcore.2
    _ = 2 * ID + 2 * eta ^ 2 * IF := by ring
    _ ≤ 2 * (2 * LQ ^ 2 * IQ + 2 * CQ ^ 2 * IW) +
        2 * eta ^ 2 * (LF ^ 2 * IW) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hD_le (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hF_le
          (mul_nonneg (by norm_num) (sq_nonneg eta)))
    _ = matchedShiftedReactionRawQSquareConstant p M * IQ +
        matchedShiftedReactionRawWSquareConstant p M eta DU * IW := by
      dsimp only [matchedShiftedReactionRawQSquareConstant,
        matchedShiftedReactionRawWSquareConstant, LQ, CQ, LF]
      ring
    _ = _ := by rfl

#print axioms capWeight_spatialDifferenceQuotient_l2_bounded_of_raw
#print axioms capWeight_genuineFluxDifference_rawSpatialDQ_l2_bounded
#print axioms
  capWeight_genuineShiftedReactionDifference_rawSpatialDQ_l2_bounded

end ShenWork.Paper1
