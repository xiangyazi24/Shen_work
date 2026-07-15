import ShenWork.Paper1.WholeLineWeightedRegularitySpatialDifference
import ShenWork.Paper1.WholeLineWeightedRegularityFourProfileReaction

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

theorem capWeight_spatialDifferenceQuotient_integrable_of_value
    {eta R h : ℝ} (heta : 0 ≤ eta) (hh : h ≠ 0)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hvalue : Integrable (fun x : ℝ =>
      capWeight eta R x * |w x| ^ 2)) :
    Integrable (fun x : ℝ =>
        capWeight eta R x * |spatialDifferenceQuotient h w x| ^ 2) ∧
      (∫ x : ℝ,
          capWeight eta R x * |spatialDifferenceQuotient h w x| ^ 2) ≤
        2 * |h⁻¹| ^ 2 *
          (Real.exp (2 * eta * |h|) + 1) *
            ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
  have hshift := capWeight_shift_sq_integrable_and_integral_le
    (eta := eta) (R := R) (d := h) heta hw hvalue
  let q : ℝ → ℝ := fun x => w (x + h)
  let d : ℝ → ℝ := w
  let out : ℝ → ℝ := spatialDifferenceQuotient h w
  have hhinv : 0 ≤ |h⁻¹| := abs_nonneg _
  have hout_cont : Continuous out := by
    dsimp [out, spatialDifferenceQuotient]
    exact ((hw.comp (continuous_id.add continuous_const)).sub hw).div_const h
  have hpoint : ∀ x, |out x| ≤ |h⁻¹| * |q x| + |h⁻¹| * |d x| := by
    intro x
    dsimp [out, q, d, spatialDifferenceQuotient]
    rw [div_eq_mul_inv, abs_mul]
    calc
      |w (x + h) - w x| * |h⁻¹| ≤
          (|w (x + h)| + |w x|) * |h⁻¹| :=
        mul_le_mul_of_nonneg_right (abs_sub _ _ ) (abs_nonneg _)
      _ = |h⁻¹| * |w (x + h)| + |h⁻¹| * |w x| := by ring
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) hhinv hhinv hout_cont
    (by simpa only [q] using hshift.1)
    (by simpa only [d] using hvalue) hpoint
  have hout : Integrable (fun x : ℝ =>
      capWeight eta R x * |spatialDifferenceQuotient h w x| ^ 2) := by
    refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x
      (spatialDifferenceQuotient h w x)
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |spatialDifferenceQuotient h w x| ^ 2) =
        ∫ x : ℝ,
          (capWeightSqrt eta R x * spatialDifferenceQuotient h w x) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        (capWeightSqrt_mul_sq_eq eta R x
          (spatialDifferenceQuotient h w x)).symm
    _ ≤ 2 * |h⁻¹| ^ 2 *
          (∫ x : ℝ, capWeight eta R x * |w (x + h)| ^ 2) +
        2 * |h⁻¹| ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
      simpa only [out, q, d] using hcore.2
    _ ≤ 2 * |h⁻¹| ^ 2 *
          (Real.exp (2 * eta * |h|) *
            ∫ x : ℝ, capWeight eta R x * |w x| ^ 2) +
        2 * |h⁻¹| ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hshift.2
          (mul_nonneg (by norm_num) (sq_nonneg _))) le_rfl
    _ = 2 * |h⁻¹| ^ 2 *
          (Real.exp (2 * eta * |h|) + 1) *
            ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by ring

private theorem wholeLineChemotaxisFlux_comp_add_const_direct
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu0 : ∀ x, 0 ≤ u x) (h x : ℝ) :
    wholeLineChemotaxisFlux p u (x + h) =
      wholeLineChemotaxisFlux p (fun y => u (y + h)) x := by
  unfold wholeLineChemotaxisFlux
  rw [frozenElliptic_deriv_comp_add_const p hu hu0 h x]

private theorem capWeighted_flux_spatialDifferenceQuotient_l2_bounded
    (p : CMParams) {M eta R h : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (hh : h ≠ 0) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h u x| ^ 2)) :
    Integrable (fun x : ℝ =>
        (capWeightSqrt eta R x *
          spatialDifferenceQuotient h (wholeLineChemotaxisFlux p u) x) ^ 2) ∧
      (∫ x : ℝ,
          (capWeightSqrt eta R x *
            spatialDifferenceQuotient h (wholeLineChemotaxisFlux p u) x) ^ 2) ≤
        capWeightedFluxSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u x| ^ 2 := by
  let u₂ : ℝ → ℝ := fun y => u (y + h)
  have hu₂ : IsCUnifBdd u₂ := isCUnifBdd_comp_add_const hu h
  have hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M := fun x => hu_mem (x + h)
  have hraw : Integrable (fun x : ℝ =>
      capWeight eta R x * |u₂ x - u x| ^ 2) := by
    have hs := hquot.const_mul (h ^ 2)
    refine hs.congr (Eventually.of_forall fun x => ?_)
    dsimp [u₂, spatialDifferenceQuotient]
    rw [abs_div, div_pow, sq_abs h]
    field_simp
  have hsource := capWeighted_flux_difference_l2_bounded
    p hM heta heta_one hu₂ hu hu₂_mem hu_mem hraw
  let F : ℝ → ℝ := fun x => capWeightedFluxDifference p eta R u₂ u x
  have hF : Integrable (fun x => F x ^ 2) := by
    simpa only [F] using hsource.1
  have hout : Integrable (fun x => (F x / h) ^ 2) := by
    have hs := hF.const_mul (h⁻¹ ^ 2)
    simpa [div_eq_mul_inv, mul_pow, mul_comm] using hs
  have heq : ∀ x,
      capWeightSqrt eta R x *
          spatialDifferenceQuotient h (wholeLineChemotaxisFlux p u) x =
        F x / h := by
    intro x
    dsimp [spatialDifferenceQuotient]
    rw [wholeLineChemotaxisFlux_comp_add_const_direct p hu
      (fun y => (hu_mem y).1) h x]
    dsimp [F, capWeightedFluxDifference, u₂, wholeLineChemotaxisFlux]
    ring
  refine ⟨by
    refine hout.congr (Eventually.of_forall fun x => ?_)
    exact congrArg (fun z : ℝ => z ^ 2) (heq x).symm, ?_⟩
  have hraw_eq :
      (∫ x : ℝ, capWeight eta R x * |u₂ x - u x| ^ 2) =
        h ^ 2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u x| ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [u₂, spatialDifferenceQuotient]
      rw [abs_div, div_pow, sq_abs h]
      field_simp
  rw [show (∫ x : ℝ,
      (capWeightSqrt eta R x *
        spatialDifferenceQuotient h (wholeLineChemotaxisFlux p u) x) ^ 2) =
      h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 by
    rw [show (fun x : ℝ =>
        (capWeightSqrt eta R x *
          spatialDifferenceQuotient h (wholeLineChemotaxisFlux p u) x) ^ 2) =
        fun x : ℝ => h⁻¹ ^ 2 * F x ^ 2 by
      funext x
      rw [heq x]
      simp only [div_eq_mul_inv, mul_pow]
      ring,
      MeasureTheory.integral_const_mul]]
  have hscaled := mul_le_mul_of_nonneg_left hsource.2 (sq_nonneg h⁻¹)
  calc
    h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 ≤
        h⁻¹ ^ 2 *
          (capWeightedFluxSquareConstant p M eta *
            ∫ x : ℝ, capWeight eta R x * |u₂ x - u x| ^ 2) := by
      simpa only [F] using hscaled
    _ = capWeightedFluxSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u x| ^ 2 := by
      rw [hraw_eq]
      field_simp

private theorem capWeight_population_spatialDifferenceQuotient_l2_bounded
    {eta R h : ℝ} (hh : h ≠ 0) {u U : ℝ → ℝ}
    (hu : Continuous u) (hU : Continuous U)
    (hWquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2))
    (hUquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h U x| ^ 2)) :
    Integrable (fun x : ℝ => capWeight eta R x *
        |spatialDifferenceQuotient h u x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u x| ^ 2) ≤
        2 * (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2 := by
  let q : ℝ → ℝ := spatialDifferenceQuotient h (fun y => u y - U y)
  let d : ℝ → ℝ := spatialDifferenceQuotient h U
  let out : ℝ → ℝ := spatialDifferenceQuotient h u
  have hout_cont : Continuous out := by
    dsimp [out, spatialDifferenceQuotient]
    exact ((hu.comp (continuous_id.add continuous_const)).sub hu).div_const h
  have hpoint : ∀ x, |out x| ≤ 1 * |q x| + 1 * |d x| := by
    intro x
    have heq : out x = q x + d x := by
      dsimp [out, q, d, spatialDifferenceQuotient]
      field_simp
      ring
    rw [heq, one_mul, one_mul]
    exact abs_add_le _ _
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) hout_cont
    (by simpa only [q] using hWquot)
    (by simpa only [d] using hUquot) hpoint
  have hout : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h u x| ^ 2) := by
    refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    simpa only [out] using
      capWeightSqrt_mul_sq_eq eta R x (spatialDifferenceQuotient h u x)
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |spatialDifferenceQuotient h u x| ^ 2) =
        ∫ x : ℝ,
          (capWeightSqrt eta R x * spatialDifferenceQuotient h u x) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        (capWeightSqrt_mul_sq_eq eta R x
          (spatialDifferenceQuotient h u x)).symm
    _ ≤ 2 * 1 ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        2 * 1 ^ 2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2 := by
      simpa only [out, q, d] using hcore.2
    _ = 2 * (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2 := by norm_num

private theorem wholeLineChemotaxisFlux_continuous_direct
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) :
    Continuous (wholeLineChemotaxisFlux p u) := by
  unfold wholeLineChemotaxisFlux
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  exact (hu.1.rpow_const (fun _ => Or.inr hm0)).mul
    ((frozenElliptic_deriv_lipschitz_of_Icc
      p hM hu hu_mem).continuous)

/-- The genuine spatial difference quotient of the flux difference
`Flux(u)-Flux(U)` is controlled by the quotient of `u-U` and the independent
reference quotient.  This uses the existing two-profile flux theorem twice;
no derivative of `s ↦ s^m` is compared at four points. -/
theorem capWeighted_genuineFluxDifference_spatialDifferenceQuotient_l2_bounded
    (p : CMParams) {M eta R h : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (hh : h ≠ 0) {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hWquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2))
    (hUquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h U x| ^ 2)) :
    Integrable (fun x : ℝ =>
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (fun y => wholeLineChemotaxisFlux p u y -
            wholeLineChemotaxisFlux p U y) x) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (fun y => wholeLineChemotaxisFlux p u y -
            wholeLineChemotaxisFlux p U y) x) ^ 2) ≤
        4 * capWeightedFluxSquareConstant p M eta *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        6 * capWeightedFluxSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h U x| ^ 2 := by
  let w : ℝ → ℝ := fun y => u y - U y
  let fu : ℝ → ℝ := wholeLineChemotaxisFlux p u
  let fU : ℝ → ℝ := wholeLineChemotaxisFlux p U
  let q : ℝ → ℝ := spatialDifferenceQuotient h fu
  let d : ℝ → ℝ := spatialDifferenceQuotient h fU
  let out : ℝ → ℝ := spatialDifferenceQuotient h (fun y => fu y - fU y)
  have huquot := capWeight_population_spatialDifferenceQuotient_l2_bounded
    (eta := eta) (R := R) hh hu.1 hU.1
    (by simpa only [w] using hWquot) hUquot
  have hfu := capWeighted_flux_spatialDifferenceQuotient_l2_bounded
    p hM heta heta_one hh hu hu_mem huquot.1
  have hfU := capWeighted_flux_spatialDifferenceQuotient_l2_bounded
    p hM heta heta_one hh hU hU_mem hUquot
  have hq : Integrable (fun x : ℝ => capWeight eta R x * |q x| ^ 2) := by
    refine hfu.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [q, fu]
    exact capWeightSqrt_mul_sq_eq eta R x _
  have hd : Integrable (fun x : ℝ => capWeight eta R x * |d x| ^ 2) := by
    refine hfU.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [d, fU]
    exact capWeightSqrt_mul_sq_eq eta R x _
  have hfu_cont := wholeLineChemotaxisFlux_continuous_direct p hM hu hu_mem
  have hfU_cont := wholeLineChemotaxisFlux_continuous_direct p hM hU hU_mem
  have hout_cont : Continuous out := by
    dsimp [out, fu, fU, spatialDifferenceQuotient]
    exact ((((hfu_cont.sub hfU_cont).comp
      (continuous_id.add continuous_const)).sub
        (hfu_cont.sub hfU_cont))).div_const h
  have hpoint : ∀ x, |out x| ≤ 1 * |q x| + 1 * |d x| := by
    intro x
    have heq : out x = q x - d x := by
      dsimp [out, q, d, spatialDifferenceQuotient]
      field_simp
      ring
    rw [heq, one_mul, one_mul]
    exact abs_sub _ _
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) hout_cont hq hd hpoint
  have hout_ident : out = spatialDifferenceQuotient h
      (fun y => wholeLineChemotaxisFlux p u y -
        wholeLineChemotaxisFlux p U y) := by
    rfl
  refine ⟨by simpa only [out, fu, fU] using hcore.1, ?_⟩
  let C : ℝ := capWeightedFluxSquareConstant p M eta
  have hq_int_eq :
      (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * q x) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      (capWeightSqrt_mul_sq_eq eta R x _).symm
  have hd_int_eq :
      (∫ x : ℝ, capWeight eta R x * |d x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * d x) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      (capWeightSqrt_mul_sq_eq eta R x _).symm
  have hcore_le :
      (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤
        2 * (∫ x : ℝ,
          (capWeightSqrt eta R x * q x) ^ 2) +
        2 * ∫ x : ℝ, (capWeightSqrt eta R x * d x) ^ 2 := by
    simpa only [one_pow, mul_one, hq_int_eq, hd_int_eq] using hcore.2
  change (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤ _
  calc
    (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤
        2 * (∫ x : ℝ, (capWeightSqrt eta R x * q x) ^ 2) +
        2 * ∫ x : ℝ, (capWeightSqrt eta R x * d x) ^ 2 := hcore_le
    _ ≤ 2 * (C * (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u x| ^ 2)) +
        2 * (C * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [q, fu, C] using hfu.2)
          (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [d, fU, C] using hfU.2)
          (by norm_num))
    _ ≤ 2 * (C * (2 *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h w x| ^ 2) +
          2 * ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h U x| ^ 2)) +
        2 * (C * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2) := by
      have hC : 0 ≤ C := by
        dsimp [C, capWeightedFluxSquareConstant]
        positivity
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (by simpa only [w] using huquot.2) hC) (by norm_num)) le_rfl
    _ = 4 * C * (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h w x| ^ 2) +
        6 * C * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2 := by ring
    _ = _ := by rfl

private theorem capWeighted_shiftedReaction_spatialDifferenceQuotient_l2_bounded
    (p : CMParams) {M eta R h : ℝ}
    (hM : 0 ≤ M) (hh : h ≠ 0) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h u x| ^ 2)) :
    Integrable (fun x : ℝ =>
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (wholeLineCauchyShiftedReaction p u) x) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (wholeLineCauchyShiftedReaction p u) x) ^ 2) ≤
        (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u x| ^ 2 := by
  let u₂ : ℝ → ℝ := fun y => u (y + h)
  have hu₂ : IsCUnifBdd u₂ := isCUnifBdd_comp_add_const hu h
  have hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M := fun x => hu_mem (x + h)
  have hraw : Integrable (fun x : ℝ =>
      capWeight eta R x * |u₂ x - u x| ^ 2) := by
    have hs := hquot.const_mul (h ^ 2)
    refine hs.congr (Eventually.of_forall fun x => ?_)
    dsimp [u₂, spatialDifferenceQuotient]
    rw [abs_div, div_pow, sq_abs h]
    field_simp
  have hsource := capWeighted_shiftedReaction_difference_l2_bounded
    p hM hu₂ hu hu₂_mem hu_mem hraw
  let F : ℝ → ℝ := fun x =>
    capWeightedShiftedReactionDifference p eta R u₂ u x
  have hF : Integrable (fun x => F x ^ 2) := by
    simpa only [F] using hsource.1
  have hout : Integrable (fun x => (F x / h) ^ 2) := by
    have hs := hF.const_mul (h⁻¹ ^ 2)
    simpa [div_eq_mul_inv, mul_pow, mul_comm] using hs
  have heq : ∀ x,
      capWeightSqrt eta R x * spatialDifferenceQuotient h
          (wholeLineCauchyShiftedReaction p u) x = F x / h := by
    intro x
    dsimp [spatialDifferenceQuotient, F,
      capWeightedShiftedReactionDifference, u₂,
      wholeLineCauchyShiftedReaction, wholeLineLogisticSource]
    ring
  refine ⟨by
    refine hout.congr (Eventually.of_forall fun x => ?_)
    exact congrArg (fun z : ℝ => z ^ 2) (heq x).symm, ?_⟩
  have hraw_eq :
      (∫ x : ℝ, capWeight eta R x * |u₂ x - u x| ^ 2) =
        h ^ 2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u x| ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [u₂, spatialDifferenceQuotient]
      rw [abs_div, div_pow, sq_abs h]
      field_simp
  rw [show (∫ x : ℝ,
      (capWeightSqrt eta R x * spatialDifferenceQuotient h
        (wholeLineCauchyShiftedReaction p u) x) ^ 2) =
      h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 by
    rw [show (fun x : ℝ =>
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (wholeLineCauchyShiftedReaction p u) x) ^ 2) =
        fun x : ℝ => h⁻¹ ^ 2 * F x ^ 2 by
      funext x
      rw [heq x]
      simp only [div_eq_mul_inv, mul_pow]
      ring,
      MeasureTheory.integral_const_mul]]
  have hscaled := mul_le_mul_of_nonneg_left hsource.2 (sq_nonneg h⁻¹)
  calc
    h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 ≤
        h⁻¹ ^ 2 * ((1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |u₂ x - u x| ^ 2) := by
      simpa only [F] using hscaled
    _ = (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u x| ^ 2 := by
      rw [hraw_eq]
      field_simp

/-- Parallel genuine source estimate for the shifted logistic reaction. -/
theorem capWeighted_genuineShiftedReactionDifference_spatialDifferenceQuotient_l2_bounded
    (p : CMParams) {M eta R h : ℝ}
    (hM : 0 ≤ M) (hh : h ≠ 0) {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hWquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2))
    (hUquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h U x| ^ 2)) :
    Integrable (fun x : ℝ =>
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (fun y => wholeLineCauchyShiftedReaction p u y -
            wholeLineCauchyShiftedReaction p U y) x) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x * spatialDifferenceQuotient h
          (fun y => wholeLineCauchyShiftedReaction p u y -
            wholeLineCauchyShiftedReaction p U y) x) ^ 2) ≤
        4 * (1 + reactionLip p.α M) ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        6 * (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h U x| ^ 2 := by
  let w : ℝ → ℝ := fun y => u y - U y
  let fu : ℝ → ℝ := wholeLineCauchyShiftedReaction p u
  let fU : ℝ → ℝ := wholeLineCauchyShiftedReaction p U
  let q : ℝ → ℝ := spatialDifferenceQuotient h fu
  let d : ℝ → ℝ := spatialDifferenceQuotient h fU
  let out : ℝ → ℝ := spatialDifferenceQuotient h (fun y => fu y - fU y)
  have huquot := capWeight_population_spatialDifferenceQuotient_l2_bounded
    (eta := eta) (R := R) hh hu.1 hU.1
    (by simpa only [w] using hWquot) hUquot
  have hfu := capWeighted_shiftedReaction_spatialDifferenceQuotient_l2_bounded
    p hM hh hu hu_mem huquot.1
  have hfU := capWeighted_shiftedReaction_spatialDifferenceQuotient_l2_bounded
    p hM hh hU hU_mem hUquot
  have hq : Integrable (fun x : ℝ => capWeight eta R x * |q x| ^ 2) := by
    refine hfu.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [q, fu]
    exact capWeightSqrt_mul_sq_eq eta R x _
  have hd : Integrable (fun x : ℝ => capWeight eta R x * |d x| ^ 2) := by
    refine hfU.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [d, fU]
    exact capWeightSqrt_mul_sq_eq eta R x _
  have hfu_cont := wholeLineCauchyShiftedReaction_continuous p hu.1
  have hfU_cont := wholeLineCauchyShiftedReaction_continuous p hU.1
  have hout_cont : Continuous out := by
    dsimp [out, fu, fU, spatialDifferenceQuotient]
    exact ((((hfu_cont.sub hfU_cont).comp
      (continuous_id.add continuous_const)).sub
        (hfu_cont.sub hfU_cont))).div_const h
  have hpoint : ∀ x, |out x| ≤ 1 * |q x| + 1 * |d x| := by
    intro x
    have heq : out x = q x - d x := by
      dsimp [out, q, d, spatialDifferenceQuotient]
      field_simp
      ring
    rw [heq, one_mul, one_mul]
    exact abs_sub _ _
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) hout_cont hq hd hpoint
  refine ⟨by simpa only [out, fu, fU] using hcore.1, ?_⟩
  let C : ℝ := (1 + reactionLip p.α M) ^ 2
  have hq_int_eq :
      (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * q x) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      (capWeightSqrt_mul_sq_eq eta R x _).symm
  have hd_int_eq :
      (∫ x : ℝ, capWeight eta R x * |d x| ^ 2) =
        ∫ x : ℝ, (capWeightSqrt eta R x * d x) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      (capWeightSqrt_mul_sq_eq eta R x _).symm
  have hcore_le :
      (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤
        2 * (∫ x : ℝ,
          (capWeightSqrt eta R x * q x) ^ 2) +
        2 * ∫ x : ℝ, (capWeightSqrt eta R x * d x) ^ 2 := by
    simpa only [one_pow, mul_one, hq_int_eq, hd_int_eq] using hcore.2
  change (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤ _
  calc
    (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤
        2 * (∫ x : ℝ, (capWeightSqrt eta R x * q x) ^ 2) +
        2 * ∫ x : ℝ, (capWeightSqrt eta R x * d x) ^ 2 := hcore_le
    _ ≤ 2 * (C * (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u x| ^ 2)) +
        2 * (C * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [q, fu, C] using hfu.2)
          (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [d, fU, C] using hfU.2)
          (by norm_num))
    _ ≤ 2 * (C * (2 *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h w x| ^ 2) +
          2 * ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h U x| ^ 2)) +
        2 * (C * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2) := by
      have hC : 0 ≤ C := by dsimp [C]; positivity
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (by simpa only [w] using huquot.2) hC) (by norm_num)) le_rfl
    _ = 4 * C * (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h w x| ^ 2) +
        6 * C * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h U x| ^ 2 := by ring
    _ = _ := by rfl
#print axioms capWeight_spatialDifferenceQuotient_integrable_of_value
#print axioms wholeLineChemotaxisFlux_comp_add_const_direct
#print axioms capWeighted_flux_spatialDifferenceQuotient_l2_bounded
#print axioms capWeight_population_spatialDifferenceQuotient_l2_bounded
#print axioms wholeLineChemotaxisFlux_continuous_direct
#print axioms
  capWeighted_genuineFluxDifference_spatialDifferenceQuotient_l2_bounded
#print axioms capWeighted_shiftedReaction_spatialDifferenceQuotient_l2_bounded
#print axioms
  capWeighted_genuineShiftedReactionDifference_spatialDifferenceQuotient_l2_bounded

end ShenWork.Paper1
