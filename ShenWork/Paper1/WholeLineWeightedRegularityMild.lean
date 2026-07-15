import ShenWork.Paper1.WholeLineCauchyBUCFixedPoint
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import ShenWork.Paper1.WholeLineWeightedRegularityNonlinearity
import ShenWork.Paper1.WholeLineWeightedRegularityVolterra
import ShenWork.Paper1.WavePositiveLeftEndpoint

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Cap-weighted one-step mild estimates

This file connects the canonical whole-line BUC mild map to the cap-weighted
`L²(ℝ)` estimates.  The cap radius never occurs in any operator constant.
In particular, the results below do not try to infer cap integrability from a
BUC bound: the logistic cap has a nonzero plateau on the right, so the weighted
`L²` seed is an explicit, indispensable input.
-/

private theorem capWeightedMovingHeat_measurable
    {eta R c t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Measurable f) :
    AEStronglyMeasurable
      (fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c t f x) volume := by
  let q : ℝ → ℝ := fun y => capWeightSqrt eta R y * f y
  let J : ℝ × ℝ → ℝ := fun z =>
    capMovingHeatKernel eta R c t z.1 z.2 * q z.2
  have hq : Measurable q :=
    (capWeightSqrt_continuous eta R).measurable.mul hf
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    exact ((capMovingHeatKernel_measurable eta R c t).aestronglyMeasurable.mul
      (hq.comp measurable_snd).aestronglyMeasurable)
  have hint : AEStronglyMeasurable
      (fun x : ℝ => ∫ y : ℝ, J (x, y)) volume :=
    AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have hscaled : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-t) * ∫ y : ℝ, J (x, y)) volume :=
    hint.const_mul _
  refine hscaled.congr (Eventually.of_forall fun x => ?_)
  change (Real.exp (-t) * ∫ y : ℝ,
      capMovingHeatKernel eta R c t x y *
        (capWeightSqrt eta R y * f y)) =
    capWeightSqrt eta R x * paper5MovingFrameHeatOp c t f x
  rw [capWeightSqrt_mul_movingFrameHeatOp_eq ht]

private theorem capWeightedMovingHeatGradient_measurable
    {eta R c t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Measurable f) :
    AEStronglyMeasurable
      (fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c t f x) volume := by
  let q : ℝ → ℝ := fun y => capWeightSqrt eta R y * f y
  let J : ℝ × ℝ → ℝ := fun z =>
    capMovingHeatGradientKernel eta R c t z.1 z.2 * q z.2
  have hq : Measurable q :=
    (capWeightSqrt_continuous eta R).measurable.mul hf
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    exact
      ((capMovingHeatGradientKernel_measurable ht eta R c).aestronglyMeasurable.mul
        (hq.comp measurable_snd).aestronglyMeasurable)
  have hint : AEStronglyMeasurable
      (fun x : ℝ => ∫ y : ℝ, J (x, y)) volume :=
    AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have hscaled : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-t) * ∫ y : ℝ, J (x, y)) volume :=
    hint.const_mul _
  refine hscaled.congr (Eventually.of_forall fun x => ?_)
  change (Real.exp (-t) * ∫ y : ℝ,
      capMovingHeatGradientKernel eta R c t x y *
        (capWeightSqrt eta R y * f y)) =
    capWeightSqrt eta R x * paper5MovingFrameHeatGradOp c t f x
  rw [capWeightSqrt_mul_movingFrameHeatGradOp_eq ht]

/-- A cap-weighted moving heat slice has an honest `L²` representative.
The norm estimate is linear in an input energy radius `B`, and its constant
is independent of the cap radius `R`. -/
theorem exists_capWeightedMovingHeatL2
    {eta t B : ℝ} (heta : 0 ≤ eta) (ht : 0 < t) (hB : 0 ≤ B)
    (R c : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hcap : Integrable (fun y => capWeight eta R y * |f y| ^ 2))
    (henergy : (∫ y : ℝ, capWeight eta R y * |f y| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume]
        fun x => capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c t f x) ∧
      ‖Z‖ ≤ Real.exp (-t) * capHeatSchurMass eta c t * B := by
  have hop := capWeight_movingFrameHeatOp_l2_bounded
    heta ht R c hf hcap
  let g : ℝ → ℝ := fun x => capWeightSqrt eta R x *
    paper5MovingFrameHeatOp c t f x
  have hg_sq : Integrable (fun x => g x ^ 2) := by
    refine hop.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [g]
    exact (capWeightSqrt_mul_sq_eq eta R x
      (paper5MovingFrameHeatOp c t f x)).symm
  have hg_meas : AEStronglyMeasurable g volume :=
    capWeightedMovingHeat_measurable ht hf
  let Z := wholeLineRealL2OfSqIntegrable g hg_meas hg_sq
  refine ⟨Z, wholeLineRealL2OfSqIntegrable_coe_ae g hg_meas hg_sq, ?_⟩
  have hnormsq : ‖Z‖ ^ 2 = ∫ x : ℝ, g x ^ 2 :=
    wholeLineRealL2OfSqIntegrable_norm_sq g hg_meas hg_sq
  have hint_eq : (∫ x : ℝ, g x ^ 2) =
      ∫ x : ℝ, capWeight eta R x *
        |paper5MovingFrameHeatOp c t f x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x
        (paper5MovingFrameHeatOp c t f x)
  have hA : 0 ≤ Real.exp (-t) * capHeatSchurMass eta c t :=
    mul_nonneg (Real.exp_nonneg _) (capHeatSchurMass_pos eta c t).le
  have hsq : ‖Z‖ ^ 2 ≤
      (Real.exp (-t) * capHeatSchurMass eta c t * B) ^ 2 := by
    rw [hnormsq, hint_eq]
    calc
      (∫ x : ℝ, capWeight eta R x *
          |paper5MovingFrameHeatOp c t f x| ^ 2) ≤
          (Real.exp (-t) * capHeatSchurMass eta c t) ^ 2 *
            ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := hop.2
      _ ≤ (Real.exp (-t) * capHeatSchurMass eta c t) ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = (Real.exp (-t) * capHeatSchurMass eta c t * B) ^ 2 := by ring
  nlinarith [norm_nonneg Z, mul_nonneg hA hB]

/-- Gradient analogue of `exists_capWeightedMovingHeatL2`.  Its Schur mass
contains the integrable `t⁻¹˲` singularity and is independent of `R`. -/
theorem exists_capWeightedMovingHeatGradientL2
    {eta t B : ℝ} (heta : 0 ≤ eta) (ht : 0 < t) (hB : 0 ≤ B)
    (R c : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hcap : Integrable (fun y => capWeight eta R y * |f y| ^ 2))
    (henergy : (∫ y : ℝ, capWeight eta R y * |f y| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume]
        fun x => capWeightSqrt eta R x *
          paper5MovingFrameHeatGradOp c t f x) ∧
      ‖Z‖ ≤ Real.exp (-t) * capHeatGradientSchurMass eta c t * B := by
  have hop := capWeight_movingFrameHeatGradOp_l2_bounded
    heta ht R c hf hcap
  let g : ℝ → ℝ := fun x => capWeightSqrt eta R x *
    paper5MovingFrameHeatGradOp c t f x
  have hg_sq : Integrable (fun x => g x ^ 2) := by
    refine hop.1.congr (Eventually.of_forall fun x => ?_)
    dsimp [g]
    exact (capWeightSqrt_mul_sq_eq eta R x
      (paper5MovingFrameHeatGradOp c t f x)).symm
  have hg_meas : AEStronglyMeasurable g volume :=
    capWeightedMovingHeatGradient_measurable ht hf
  let Z := wholeLineRealL2OfSqIntegrable g hg_meas hg_sq
  refine ⟨Z, wholeLineRealL2OfSqIntegrable_coe_ae g hg_meas hg_sq, ?_⟩
  have hnormsq : ‖Z‖ ^ 2 = ∫ x : ℝ, g x ^ 2 :=
    wholeLineRealL2OfSqIntegrable_norm_sq g hg_meas hg_sq
  have hint_eq : (∫ x : ℝ, g x ^ 2) =
      ∫ x : ℝ, capWeight eta R x *
        |paper5MovingFrameHeatGradOp c t f x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x
        (paper5MovingFrameHeatGradOp c t f x)
  have hA : 0 ≤ Real.exp (-t) * capHeatGradientSchurMass eta c t :=
    mul_nonneg (Real.exp_nonneg _)
      (capHeatGradientSchurMass_pos ht heta c).le
  have hsq : ‖Z‖ ^ 2 ≤
      (Real.exp (-t) * capHeatGradientSchurMass eta c t * B) ^ 2 := by
    rw [hnormsq, hint_eq]
    calc
      (∫ x : ℝ, capWeight eta R x *
          |paper5MovingFrameHeatGradOp c t f x| ^ 2) ≤
          (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
            ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := hop.2
      _ ≤ (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = (Real.exp (-t) * capHeatGradientSchurMass eta c t * B) ^ 2 := by ring
  nlinarith [norm_nonneg Z, mul_nonneg hA hB]

/-! ## Cap contraction and co-moving nonlinear sources -/

/-- Pointwise clamping is a contraction in every cap-weighted `L²` space.
This is the step that lets the globally truncated BUC Picard map inherit the
weighted seed, without using the false implication `BUC ⇒ cap-L²`. -/
theorem capWeight_clampProfile_difference_l2_bounded
    {eta R M : ℝ} (hM : 0 ≤ M) {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x => capWeight eta R x *
        |wholeLineCauchyClampProfile M u₂ x -
          wholeLineCauchyClampProfile M u₁ x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |wholeLineCauchyClampProfile M u₂ x -
            wholeLineCauchyClampProfile M u₁ x| ^ 2) ≤
        ∫ x : ℝ, capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
  have hpoint : ∀ x,
      capWeight eta R x *
          |wholeLineCauchyClampProfile M u₂ x -
            wholeLineCauchyClampProfile M u₁ x| ^ 2 ≤
        capWeight eta R x * |u₂ x - u₁ x| ^ 2 := by
    intro x
    have hc := (clampIcc_lipschitz M).dist_le_mul (u₂ x) (u₁ x)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at hc
    have hsq :
        |wholeLineCauchyClampProfile M u₂ x -
          wholeLineCauchyClampProfile M u₁ x| ^ 2 ≤
          |u₂ x - u₁ x| ^ 2 := by
      exact (sq_le_sq₀ (abs_nonneg _)
        (abs_nonneg _)).2 hc
    exact mul_le_mul_of_nonneg_left hsq (capWeight_pos eta R x).le
  have hclamp₂ := wholeLineCauchyClampProfile_isCUnifBdd hM hu₂
  have hclamp₁ := wholeLineCauchyClampProfile_isCUnifBdd hM hu₁
  have hout_meas : AEStronglyMeasurable (fun x =>
      capWeight eta R x *
        |wholeLineCauchyClampProfile M u₂ x -
          wholeLineCauchyClampProfile M u₁ x| ^ 2) volume :=
    ((capWeight_continuous eta R).mul
      ((hclamp₂.1.sub hclamp₁.1).abs.pow 2)).aestronglyMeasurable
  have hout : Integrable (fun x => capWeight eta R x *
      |wholeLineCauchyClampProfile M u₂ x -
        wholeLineCauchyClampProfile M u₁ x| ^ 2) := by
    refine Integrable.mono' hclose hout_meas ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (capWeight_pos eta R x).le (sq_nonneg _))]
      exact hpoint x
  exact ⟨hout, integral_mono hout hclose hpoint⟩

/-- The physical truncated flux commutes with a spatial translation. -/
theorem wholeLineCauchyTruncatedFlux_comp_add_const
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (a x : ℝ) :
    wholeLineCauchyTruncatedFlux p M u (x + a) =
      wholeLineChemotaxisFlux p
        (fun y => wholeLineCauchyClampProfile M u (y + a)) x := by
  let q : ℝ → ℝ := wholeLineCauchyClampProfile M u
  have hq : IsCUnifBdd q :=
    wholeLineCauchyClampProfile_isCUnifBdd hM hu
  have hq0 : ∀ y, 0 ≤ q y := fun y =>
    (wholeLineCauchyClampProfile_mem_Icc hM u y).1
  unfold wholeLineCauchyTruncatedFlux wholeLineChemotaxisFlux
  change q (x + a) ^ p.m * deriv (frozenElliptic p q) (x + a) =
    q (x + a) ^ p.m *
      deriv (frozenElliptic p (fun y => q (y + a))) x
  rw [frozenElliptic_deriv_comp_add_const p hq hq0 a x]

/-- The shifted reaction commutes with the same translation. -/
theorem wholeLineCauchyTruncatedReaction_comp_add_const
    (p : CMParams) {M : ℝ} (u : ℝ → ℝ) (a x : ℝ) :
    wholeLineCauchyTruncatedReaction p M u (x + a) =
      wholeLineCauchyShiftedReaction p
        (fun y => wholeLineCauchyClampProfile M u (y + a)) x := by
  rfl

/-- Co-moving cap-conjugated chemotaxis source difference for two BUC
profiles. -/
def capWeightedCoMovingTruncatedChemotaxisDifference
    (p : CMParams) (M eta R c s : ℝ)
    (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightSqrt eta R x * (-p.χ) *
    (wholeLineCauchyTruncatedFlux p M u₂ (x + c * s) -
      wholeLineCauchyTruncatedFlux p M u₁ (x + c * s))

/-- Co-moving cap-conjugated shifted-reaction source difference. -/
def capWeightedCoMovingTruncatedReactionDifference
    (p : CMParams) (M eta R c s : ℝ)
    (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    (wholeLineCauchyTruncatedReaction p M u₂ (x + c * s) -
      wholeLineCauchyTruncatedReaction p M u₁ (x + c * s))

/-- The translated, truncated chemotaxis source is `L²`-Lipschitz in the
co-moving cap energy.  The constant is independent of `R`, `c`, and `s`. -/
theorem capWeighted_coMovingTruncatedChemotaxis_l2_bounded
    (p : CMParams) {M eta R c s : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    {u₂ u₁ : ℝ → ℝ} (hu₂ : IsCUnifBdd u₂)
    (hu₁ : IsCUnifBdd u₁)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂ (x + c * s) - u₁ (x + c * s)| ^ 2)) :
    Integrable (fun x =>
        capWeightedCoMovingTruncatedChemotaxisDifference
          p M eta R c s u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ, capWeightedCoMovingTruncatedChemotaxisDifference
          p M eta R c s u₂ u₁ x ^ 2) ≤
        capWeightedChemotaxisOperatorSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x *
            |u₂ (x + c * s) - u₁ (x + c * s)| ^ 2 := by
  let q₂ : ℝ → ℝ := fun x => u₂ (x + c * s)
  let q₁ : ℝ → ℝ := fun x => u₁ (x + c * s)
  let v₂ : ℝ → ℝ := wholeLineCauchyClampProfile M q₂
  let v₁ : ℝ → ℝ := wholeLineCauchyClampProfile M q₁
  have hq₂ : IsCUnifBdd q₂ := isCUnifBdd_comp_add_const hu₂ (c * s)
  have hq₁ : IsCUnifBdd q₁ := isCUnifBdd_comp_add_const hu₁ (c * s)
  have hv₂ : IsCUnifBdd v₂ :=
    wholeLineCauchyClampProfile_isCUnifBdd hM hq₂
  have hv₁ : IsCUnifBdd v₁ :=
    wholeLineCauchyClampProfile_isCUnifBdd hM hq₁
  have hv₂_mem : ∀ x, v₂ x ∈ Set.Icc (0 : ℝ) M :=
    wholeLineCauchyClampProfile_mem_Icc hM q₂
  have hv₁_mem : ∀ x, v₁ x ∈ Set.Icc (0 : ℝ) M :=
    wholeLineCauchyClampProfile_mem_Icc hM q₁
  have hclamp := capWeight_clampProfile_difference_l2_bounded
    hM hq₂ hq₁ (by simpa only [q₂, q₁] using hclose)
  have hsource := capWeighted_chemotaxis_operator_l2_bounded
    p hM heta heta_one hv₂ hv₁ hv₂_mem hv₁_mem hclamp.1
  have heq : (fun x =>
      capWeightedCoMovingTruncatedChemotaxisDifference
        p M eta R c s u₂ u₁ x) =
      capWeightedChemotaxisOperatorDifference p eta R v₂ v₁ := by
    funext x
    rw [capWeightedCoMovingTruncatedChemotaxisDifference,
      wholeLineCauchyTruncatedFlux_comp_add_const p hM hu₂ (c * s) x,
      wholeLineCauchyTruncatedFlux_comp_add_const p hM hu₁ (c * s) x]
    change capWeightSqrt eta R x * (-p.χ) *
        (wholeLineChemotaxisFlux p v₂ x -
          wholeLineChemotaxisFlux p v₁ x) =
      (-p.χ) * (capWeightSqrt eta R x *
        (wholeLineChemotaxisFlux p v₂ x -
          wholeLineChemotaxisFlux p v₁ x))
    ring
  have hsq : (fun x =>
      capWeightedCoMovingTruncatedChemotaxisDifference
        p M eta R c s u₂ u₁ x ^ 2) =
      fun x => capWeightedChemotaxisOperatorDifference
        p eta R v₂ v₁ x ^ 2 := by
    funext x
    rw [congrFun heq x]
  rw [hsq]
  exact ⟨hsource.1, hsource.2.trans
    (mul_le_mul_of_nonneg_left hclamp.2
      (by unfold capWeightedChemotaxisOperatorSquareConstant
            capWeightedFluxSquareConstant
          positivity))⟩

/-- The translated, truncated shifted reaction has the parallel cap bound. -/
theorem capWeighted_coMovingTruncatedReaction_l2_bounded
    (p : CMParams) {M eta R c s : ℝ} (hM : 0 ≤ M)
    {u₂ u₁ : ℝ → ℝ} (hu₂ : IsCUnifBdd u₂)
    (hu₁ : IsCUnifBdd u₁)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂ (x + c * s) - u₁ (x + c * s)| ^ 2)) :
    Integrable (fun x =>
        capWeightedCoMovingTruncatedReactionDifference
          p M eta R c s u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ, capWeightedCoMovingTruncatedReactionDifference
          p M eta R c s u₂ u₁ x ^ 2) ≤
        (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |u₂ (x + c * s) - u₁ (x + c * s)| ^ 2 := by
  let q₂ : ℝ → ℝ := fun x => u₂ (x + c * s)
  let q₁ : ℝ → ℝ := fun x => u₁ (x + c * s)
  let v₂ : ℝ → ℝ := wholeLineCauchyClampProfile M q₂
  let v₁ : ℝ → ℝ := wholeLineCauchyClampProfile M q₁
  have hq₂ : IsCUnifBdd q₂ := isCUnifBdd_comp_add_const hu₂ (c * s)
  have hq₁ : IsCUnifBdd q₁ := isCUnifBdd_comp_add_const hu₁ (c * s)
  have hv₂ : IsCUnifBdd v₂ :=
    wholeLineCauchyClampProfile_isCUnifBdd hM hq₂
  have hv₁ : IsCUnifBdd v₁ :=
    wholeLineCauchyClampProfile_isCUnifBdd hM hq₁
  have hv₂_mem : ∀ x, v₂ x ∈ Set.Icc (0 : ℝ) M :=
    wholeLineCauchyClampProfile_mem_Icc hM q₂
  have hv₁_mem : ∀ x, v₁ x ∈ Set.Icc (0 : ℝ) M :=
    wholeLineCauchyClampProfile_mem_Icc hM q₁
  have hclamp := capWeight_clampProfile_difference_l2_bounded
    hM hq₂ hq₁ (by simpa only [q₂, q₁] using hclose)
  have hsource := capWeighted_shiftedReaction_difference_l2_bounded
    p hM hv₂ hv₁ hv₂_mem hv₁_mem hclamp.1
  have heq : (fun x =>
      capWeightedCoMovingTruncatedReactionDifference
        p M eta R c s u₂ u₁ x) =
      capWeightedShiftedReactionDifference p eta R v₂ v₁ := by
    funext x
    rw [capWeightedCoMovingTruncatedReactionDifference,
      wholeLineCauchyTruncatedReaction_comp_add_const p u₂ (c * s) x,
      wholeLineCauchyTruncatedReaction_comp_add_const p u₁ (c * s) x]
    rfl
  have hsq : (fun x =>
      capWeightedCoMovingTruncatedReactionDifference
        p M eta R c s u₂ u₁ x ^ 2) =
      fun x => capWeightedShiftedReactionDifference
        p eta R v₂ v₁ x ^ 2 := by
    funext x
    rw [congrFun heq x]
  rw [hsq]
  exact ⟨hsource.1, hsource.2.trans
    (mul_le_mul_of_nonneg_left hclamp.2 (sq_nonneg _))⟩

/-! ## Honest `L²` slices of the two nonlinear Duhamel integrands -/

/-- The raw co-moving chemotaxis source difference, including `-chi` but
before multiplication by the square root of the cap. -/
def coMovingTruncatedChemotaxisDifference
    (p : CMParams) (M c s : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (-p.χ) *
    (wholeLineCauchyTruncatedFlux p M u₂ (x + c * s) -
      wholeLineCauchyTruncatedFlux p M u₁ (x + c * s))

/-- The raw co-moving shifted-reaction source difference. -/
def coMovingTruncatedReactionDifference
    (p : CMParams) (M c s : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineCauchyTruncatedReaction p M u₂ (x + c * s) -
    wholeLineCauchyTruncatedReaction p M u₁ (x + c * s)

theorem coMovingTruncatedChemotaxisDifference_measurable
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (c s : ℝ)
    (u₂ u₁ : WholeLineBUC) :
    Measurable (coMovingTruncatedChemotaxisDifference
      p M c s u₂.1 u₁.1) := by
  have hshift : Continuous (fun x : ℝ => x + c * s) := by fun_prop
  have h₂ : Continuous (fun x : ℝ =>
      wholeLineCauchyTruncatedFlux p M u₂.1 (x + c * s)) :=
    (wholeLineCauchyTruncatedFlux_uniformContinuous p hM u₂).continuous.comp
      hshift
  have h₁ : Continuous (fun x : ℝ =>
      wholeLineCauchyTruncatedFlux p M u₁.1 (x + c * s)) :=
    (wholeLineCauchyTruncatedFlux_uniformContinuous p hM u₁).continuous.comp
      hshift
  exact (continuous_const.mul (h₂.sub h₁)).measurable

theorem coMovingTruncatedReactionDifference_measurable
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (c s : ℝ)
    (u₂ u₁ : WholeLineBUC) :
    Measurable (coMovingTruncatedReactionDifference
      p M c s u₂.1 u₁.1) := by
  have hshift : Continuous (fun x : ℝ => x + c * s) := by fun_prop
  have h₂ : Continuous (fun x : ℝ =>
      wholeLineCauchyTruncatedReaction p M u₂.1 (x + c * s)) :=
    (wholeLineCauchyTruncatedReaction_uniformContinuous p hM u₂).continuous.comp
      hshift
  have h₁ : Continuous (fun x : ℝ =>
      wholeLineCauchyTruncatedReaction p M u₁.1 (x + c * s)) :=
    (wholeLineCauchyTruncatedReaction_uniformContinuous p hM u₁).continuous.comp
      hshift
  exact (h₂.sub h₁).measurable

private theorem capWeightedCoMovingChemotaxis_sq_eq
    (p : CMParams) (M eta R c s : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) :
    capWeight eta R x *
        |coMovingTruncatedChemotaxisDifference p M c s u₂ u₁ x| ^ 2 =
      capWeightedCoMovingTruncatedChemotaxisDifference
        p M eta R c s u₂ u₁ x ^ 2 := by
  rw [← capWeightSqrt_mul_sq_eq eta R x
    (coMovingTruncatedChemotaxisDifference p M c s u₂ u₁ x)]
  unfold coMovingTruncatedChemotaxisDifference
    capWeightedCoMovingTruncatedChemotaxisDifference
  ring

private theorem capWeightedCoMovingReaction_sq_eq
    (p : CMParams) (M eta R c s : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) :
    capWeight eta R x *
        |coMovingTruncatedReactionDifference p M c s u₂ u₁ x| ^ 2 =
      capWeightedCoMovingTruncatedReactionDifference
        p M eta R c s u₂ u₁ x ^ 2 := by
  rw [← capWeightSqrt_mul_sq_eq eta R x
    (coMovingTruncatedReactionDifference p M c s u₂ u₁ x)]
  unfold coMovingTruncatedReactionDifference
    capWeightedCoMovingTruncatedReactionDifference
  rfl

/-- At each positive lag, the cap-conjugated gradient evolution of the
truncated chemotaxis difference has an honest `L²` representative.  The
constant is uniform in the cap radius and in the history time. -/
theorem exists_capWeightedMovingHeatGradient_truncatedChemotaxisL2
    (p : CMParams) {M eta R c s tau B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (htau : 0 < tau) (hB : 0 ≤ B) (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c tau
          (coMovingTruncatedChemotaxisDifference
            p M c s u₂.1 u₁.1) x) ∧
      ‖Z‖ ≤ Real.exp (-tau) * capHeatGradientSchurMass eta c tau *
        Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta) * B := by
  let C : ℝ := capWeightedChemotaxisOperatorSquareConstant p M eta
  have hC : 0 ≤ C := by
    dsimp [C]
    unfold capWeightedChemotaxisOperatorSquareConstant
      capWeightedFluxSquareConstant
    positivity
  have hsource := capWeighted_coMovingTruncatedChemotaxis_l2_bounded
    p hM heta heta_one (WholeLineBUC.isCUnifBdd u₂)
      (WholeLineBUC.isCUnifBdd u₁) hclose
  have hcap : Integrable (fun x => capWeight eta R x *
      |coMovingTruncatedChemotaxisDifference p M c s u₂.1 u₁.1 x| ^ 2) := by
    refine hsource.1.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightedCoMovingChemotaxis_sq_eq
      p M eta R c s u₂.1 u₁.1 x).symm
  have hsource_energy : (∫ x : ℝ, capWeight eta R x *
      |coMovingTruncatedChemotaxisDifference p M c s u₂.1 u₁.1 x| ^ 2) ≤
      (Real.sqrt C * B) ^ 2 := by
    have heq : (∫ x : ℝ, capWeight eta R x *
        |coMovingTruncatedChemotaxisDifference p M c s u₂.1 u₁.1 x| ^ 2) =
        ∫ x : ℝ, capWeightedCoMovingTruncatedChemotaxisDifference
          p M eta R c s u₂.1 u₁.1 x ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        capWeightedCoMovingChemotaxis_sq_eq
          p M eta R c s u₂.1 u₁.1 x
    rw [heq]
    calc
      (∫ x : ℝ, capWeightedCoMovingTruncatedChemotaxisDifference
          p M eta R c s u₂.1 u₁.1 x ^ 2) ≤ C * B ^ 2 :=
        hsource.2.trans (mul_le_mul_of_nonneg_left henergy hC)
      _ = (Real.sqrt C * B) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC]
  rcases exists_capWeightedMovingHeatGradientL2
      heta htau (mul_nonneg (Real.sqrt_nonneg _) hB) R c
      (coMovingTruncatedChemotaxisDifference_measurable p hM c s u₂ u₁)
      hcap hsource_energy with ⟨Z, hrep, hZ⟩
  refine ⟨Z, hrep, hZ.trans_eq ?_⟩
  dsimp only [C]
  ring

/-- Value-semigroup analogue for the shifted-reaction difference. -/
theorem exists_capWeightedMovingHeat_truncatedReactionL2
    (p : CMParams) {M eta R c s tau B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (htau : 0 < tau) (hB : 0 ≤ B) (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c tau
          (coMovingTruncatedReactionDifference
            p M c s u₂.1 u₁.1) x) ∧
      ‖Z‖ ≤ Real.exp (-tau) * capHeatSchurMass eta c tau *
        (1 + reactionLip p.α M) * B := by
  let L : ℝ := 1 + reactionLip p.α M
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg zero_le_one (reactionLip_nonneg p.hα hM)
  have hsource := capWeighted_coMovingTruncatedReaction_l2_bounded
    p hM (WholeLineBUC.isCUnifBdd u₂)
      (WholeLineBUC.isCUnifBdd u₁) hclose
  have hcap : Integrable (fun x => capWeight eta R x *
      |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2) := by
    refine hsource.1.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightedCoMovingReaction_sq_eq
      p M eta R c s u₂.1 u₁.1 x).symm
  have hsource_energy : (∫ x : ℝ, capWeight eta R x *
      |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2) ≤
      (L * B) ^ 2 := by
    have heq : (∫ x : ℝ, capWeight eta R x *
        |coMovingTruncatedReactionDifference p M c s u₂.1 u₁.1 x| ^ 2) =
        ∫ x : ℝ, capWeightedCoMovingTruncatedReactionDifference
          p M eta R c s u₂.1 u₁.1 x ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        capWeightedCoMovingReaction_sq_eq
          p M eta R c s u₂.1 u₁.1 x
    rw [heq]
    calc
      (∫ x : ℝ, capWeightedCoMovingTruncatedReactionDifference
          p M eta R c s u₂.1 u₁.1 x ^ 2) ≤ L ^ 2 * B ^ 2 :=
        hsource.2.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg L))
      _ = (L * B) ^ 2 := by rw [mul_pow]
  simpa only [L, mul_assoc] using exists_capWeightedMovingHeatL2
    heta htau (mul_nonneg hL hB) R c
      (coMovingTruncatedReactionDifference_measurable p hM c s u₂ u₁)
      hcap hsource_energy

/-! ## A cap-independent Volterra kernel -/

/-- A common bound for the two exponential tilts on a finite time window. -/
def capMildGrowthBound (eta c T : ℝ) : ℝ :=
  Real.exp ((eta ^ 2 + |c| * eta) * T)

theorem weightedMovingHeatGrowth_le_capMildGrowthBound
    {eta c tau T : ℝ} (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (htauT : tau ≤ T) :
    weightedMovingHeatGrowth eta c tau ≤ capMildGrowthBound eta c T := by
  unfold weightedMovingHeatGrowth capMildGrowthBound
  apply Real.exp_le_exp.mpr
  have hcoef : eta ^ 2 - c * eta ≤ eta ^ 2 + |c| * eta := by
    have hc : -c * eta ≤ |c| * eta :=
      mul_le_mul_of_nonneg_right (neg_le_abs c) heta
    linarith
  have hA : 0 ≤ eta ^ 2 + |c| * eta := by positivity
  exact (mul_le_mul_of_nonneg_right hcoef htau).trans
    (mul_le_mul_of_nonneg_left htauT hA)

theorem weightedMovingHeatGrowth_neg_le_capMildGrowthBound
    {eta c tau T : ℝ} (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (htauT : tau ≤ T) :
    weightedMovingHeatGrowth (-eta) c tau ≤
      capMildGrowthBound eta c T := by
  unfold weightedMovingHeatGrowth capMildGrowthBound
  apply Real.exp_le_exp.mpr
  have hcoef : (-eta) ^ 2 - c * (-eta) ≤
      eta ^ 2 + |c| * eta := by
    have hc : c * eta ≤ |c| * eta :=
      mul_le_mul_of_nonneg_right (le_abs_self c) heta
    nlinarith
  have hA : 0 ≤ eta ^ 2 + |c| * eta := by positivity
  exact (mul_le_mul_of_nonneg_right hcoef htau).trans
    (mul_le_mul_of_nonneg_left htauT hA)

/-- Uniform finite-window bound for the value-semigroup Schur mass. -/
theorem capHeatSchurMass_le_capMildGrowthBound
    {eta c tau T : ℝ} (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (htauT : tau ≤ T) :
    capHeatSchurMass eta c tau ≤ 2 * capMildGrowthBound eta c T := by
  unfold capHeatSchurMass
  linarith [weightedMovingHeatGrowth_le_capMildGrowthBound
      (c := c) heta htau htauT,
    weightedMovingHeatGrowth_neg_le_capMildGrowthBound
      (c := c) heta htau htauT]

/-- Uniform finite-window bound for the gradient-semigroup Schur mass,
split into its regular and inverse-square-root parts. -/
theorem capHeatGradientSchurMass_le_capMildKernel
    {eta c tau T : ℝ} (heta : 0 ≤ eta) (htau : 0 < tau)
    (htauT : tau ≤ T) :
    capHeatGradientSchurMass eta c tau ≤
      2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            tau ^ (-(1 / 2 : ℝ)) := by
  let G : ℝ := capMildGrowthBound eta c T
  let b : ℝ := 1 / Real.sqrt (Real.pi * tau) + eta
  have hG₂ := weightedMovingHeatGrowth_le_capMildGrowthBound
    (c := c) heta htau.le htauT
  have hG₁ := weightedMovingHeatGrowth_neg_le_capMildGrowthBound
    (c := c) heta htau.le htauT
  have hb : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _)) heta
  have hraw : capHeatGradientSchurMass eta c tau ≤ 2 * G * b := by
    unfold capHeatGradientSchurMass tiltedHeatGradientSchurMass
    dsimp only [G, b] at hG₂ hG₁ ⊢
    calc
      weightedMovingHeatGrowth eta c tau *
            (1 / Real.sqrt (Real.pi * tau) + eta) +
          weightedMovingHeatGrowth (-eta) c tau *
            (1 / Real.sqrt (Real.pi * tau) + eta) ≤
          capMildGrowthBound eta c T *
              (1 / Real.sqrt (Real.pi * tau) + eta) +
            capMildGrowthBound eta c T *
              (1 / Real.sqrt (Real.pi * tau) + eta) :=
        add_le_add (mul_le_mul_of_nonneg_right hG₂ hb)
          (mul_le_mul_of_nonneg_right hG₁ hb)
      _ = 2 * capMildGrowthBound eta c T *
          (1 / Real.sqrt (Real.pi * tau) + eta) := by ring
  have hs : 0 < Real.sqrt (Real.pi * tau) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs4 : Real.sqrt (4 * Real.pi * tau) =
      2 * Real.sqrt (Real.pi * tau) := by
    rw [show 4 * Real.pi * tau = 4 * (Real.pi * tau) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hinv : 1 / Real.sqrt (Real.pi * tau) =
      (2 / Real.sqrt (4 * Real.pi)) *
        tau ^ (-(1 / 2 : ℝ)) := by
    calc
      1 / Real.sqrt (Real.pi * tau) =
          2 / Real.sqrt (4 * Real.pi * tau) := by
        rw [hs4]
        field_simp [ne_of_gt hs]
      _ = (2 / Real.sqrt (4 * Real.pi)) *
          tau ^ (-(1 / 2 : ℝ)) :=
        two_div_sqrt_four_pi_mul_eq_rpow_cauchy htau
  calc
    capHeatGradientSchurMass eta c tau ≤ 2 * G * b := hraw
    _ = 2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            tau ^ (-(1 / 2 : ℝ)) := by
      dsimp only [G, b]
      rw [hinv]
      ring

/-- Regular part of the cap-Picard Volterra kernel. -/
def capMildKernelConstant (p : CMParams) (M eta c T : ℝ) : ℝ :=
  2 * capMildGrowthBound eta c T * (1 + reactionLip p.α M) +
    2 * capMildGrowthBound eta c T * eta *
      Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)

/-- Inverse-square-root coefficient of the cap-Picard Volterra kernel. -/
def capMildKernelInvSqrtConstant
    (p : CMParams) (M eta c T : ℝ) : ℝ :=
  2 * capMildGrowthBound eta c T *
    (2 / Real.sqrt (4 * Real.pi)) *
      Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)

theorem capMildKernelConstant_nonneg
    (p : CMParams) {M eta T : ℝ} (hM : 0 ≤ M)
    (heta : 0 ≤ eta) (hT : 0 ≤ T) (c : ℝ) :
    0 ≤ capMildKernelConstant p M eta c T := by
  unfold capMildKernelConstant capMildGrowthBound
  have hreact : 0 ≤ reactionLip p.α M := reactionLip_nonneg p.hα hM
  positivity

theorem capMildKernelInvSqrtConstant_nonneg
    (p : CMParams) {M eta T : ℝ} (_hM : 0 ≤ M)
    (_heta : 0 ≤ eta) (_hT : 0 ≤ T) (c : ℝ) :
    0 ≤ capMildKernelInvSqrtConstant p M eta c T := by
  unfold capMildKernelInvSqrtConstant capMildGrowthBound
  positivity

/-- The chemotaxis Duhamel slice has the common finite-window Volterra
majorant. -/
theorem exists_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
    (p : CMParams) {M eta R c s tau T B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (htau : 0 < tau) (htauT : tau ≤ T) (hB : 0 ≤ B)
    (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c tau
          (coMovingTruncatedChemotaxisDifference
            p M c s u₂.1 u₁.1) x) ∧
      ‖Z‖ ≤
        ((2 * capMildGrowthBound eta c T * eta *
              Real.sqrt
                (capWeightedChemotaxisOperatorSquareConstant p M eta)) +
          capMildKernelInvSqrtConstant p M eta c T *
            tau ^ (-(1 / 2 : ℝ))) * B := by
  let C : ℝ := capWeightedChemotaxisOperatorSquareConstant p M eta
  have hC : 0 ≤ C := by
    dsimp [C]
    unfold capWeightedChemotaxisOperatorSquareConstant
      capWeightedFluxSquareConstant
    positivity
  rcases exists_capWeightedMovingHeatGradient_truncatedChemotaxisL2
      p hM heta heta_one htau hB u₂ u₁ hclose henergy with
    ⟨Z, hrep, hZ⟩
  refine ⟨Z, hrep, hZ.trans ?_⟩
  have hmass := capHeatGradientSchurMass_le_capMildKernel
    (c := c) heta htau htauT
  have hexp : Real.exp (-tau) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr htau.le)
  have hfactor : Real.exp (-tau) * capHeatGradientSchurMass eta c tau ≤
      2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            tau ^ (-(1 / 2 : ℝ)) := by
    exact (mul_le_mul_of_nonneg_right hexp
      (capHeatGradientSchurMass_pos htau heta c).le).trans
        (by simpa using hmass)
  have hsB : 0 ≤ Real.sqrt C * B :=
    mul_nonneg (Real.sqrt_nonneg _) hB
  calc
    Real.exp (-tau) * capHeatGradientSchurMass eta c tau *
          Real.sqrt C * B =
        (Real.exp (-tau) * capHeatGradientSchurMass eta c tau) *
          (Real.sqrt C * B) := by ring
    _ ≤ (2 * capMildGrowthBound eta c T * eta +
          (2 * capMildGrowthBound eta c T *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ))) * (Real.sqrt C * B) :=
      mul_le_mul_of_nonneg_right hfactor hsB
    _ = ((2 * capMildGrowthBound eta c T * eta *
              Real.sqrt
                (capWeightedChemotaxisOperatorSquareConstant p M eta)) +
          capMildKernelInvSqrtConstant p M eta c T *
            tau ^ (-(1 / 2 : ℝ))) * B := by
      dsimp only [C]
      unfold capMildKernelInvSqrtConstant
      ring

/-- The shifted-reaction Duhamel slice contributes only to the regular part
of the common Volterra kernel. -/
theorem exists_capWeightedMovingHeat_truncatedReactionL2_le_kernel
    (p : CMParams) {M eta R c s tau T B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (htau : 0 < tau) (htauT : tau ≤ T) (hB : 0 ≤ B)
    (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c tau
          (coMovingTruncatedReactionDifference
            p M c s u₂.1 u₁.1) x) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c T *
        (1 + reactionLip p.α M) * B := by
  rcases exists_capWeightedMovingHeat_truncatedReactionL2
      p hM heta htau hB u₂ u₁ hclose henergy with ⟨Z, hrep, hZ⟩
  refine ⟨Z, hrep, hZ.trans ?_⟩
  have hmass := capHeatSchurMass_le_capMildGrowthBound
    (c := c) heta htau.le htauT
  have hexp : Real.exp (-tau) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr htau.le)
  have hfactor : Real.exp (-tau) * capHeatSchurMass eta c tau ≤
      2 * capMildGrowthBound eta c T :=
    (mul_le_mul_of_nonneg_right hexp
      (capHeatSchurMass_pos eta c tau).le).trans (by simpa using hmass)
  have hLB : 0 ≤ (1 + reactionLip p.α M) * B :=
    mul_nonneg
      (add_nonneg zero_le_one (reactionLip_nonneg p.hα hM)) hB
  calc
    Real.exp (-tau) * capHeatSchurMass eta c tau *
          (1 + reactionLip p.α M) * B =
        (Real.exp (-tau) * capHeatSchurMass eta c tau) *
          ((1 + reactionLip p.α M) * B) := by ring
    _ ≤ (2 * capMildGrowthBound eta c T) *
          ((1 + reactionLip p.α M) * B) :=
      mul_le_mul_of_nonneg_right hfactor hLB
    _ = 2 * capMildGrowthBound eta c T *
        (1 + reactionLip p.α M) * B := by ring

/-! ## One-step Hilbert-space assembly

The remaining bridge is deliberately explicit.  Pointwise-in-time existence
of an `L²` class does not by itself give a strongly measurable choice in time.
Accordingly `hZG_int`, `hZR_int`, `hZG_rep`, and `hZR_rep` below are the exact
Bochner/Fubini history hypotheses; every spatial estimate used to discharge
their pointwise norm bounds is proved above.
-/

private theorem paper5MovingFrameHeatOp_sub_eq_buc_heat_sub
    {t : ℝ} (ht : 0 < t) (c : ℝ) (u₂ u₁ : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatOp c t (fun y => u₂.1 y - u₁.1 y) x =
      (wholeLineCauchyHeatBUCTotal t u₂).1 (x + c * t) -
        (wholeLineCauchyHeatBUCTotal t u₁).1 (x + c * t) := by
  have hlin : wholeLineCauchyHeatBUC t ht (u₂ - u₁) =
      wholeLineCauchyHeatBUC t ht u₂ -
        wholeLineCauchyHeatBUC t ht u₁ := by
    exact (kernelConvBUCLinearMap
      (wholeLineModifiedHeatKernel_continuous ht)
      (wholeLineModifiedHeatKernel_integrable ht)).map_sub u₂ u₁
  have hpoint := congrArg
    (fun w : WholeLineBUC => w.1 (x + c * t)) hlin
  change
    (wholeLineCauchyHeatBUC t ht (u₂ - u₁)).1 (x + c * t) =
      (wholeLineCauchyHeatBUC t ht u₂).1 (x + c * t) -
        (wholeLineCauchyHeatBUC t ht u₁).1 (x + c * t) at hpoint
  have hraw : ((u₂ - u₁).1 : ℝ → ℝ) =
      fun y => u₂.1 y - u₁.1 y := by
    funext y
    rfl
  rw [wholeLineCauchyHeatBUC_apply, wholeLineCauchyHeatBUC_apply,
    wholeLineCauchyHeatBUC_apply, hraw] at hpoint
  simpa only [paper5MovingFrameHeatOp,
    wholeLineCauchyHeatBUCTotal, ht, dif_pos,
    wholeLineCauchyHeatBUC_apply] using hpoint

/-- Assemble a homogeneous cap slice and the two honest `L²` Duhamel
histories.  This is the canonical one-step triangle estimate, with the
time-history/Fubini bridge exposed rather than hidden in a package. -/
theorem capWeightedMild_oneStep_l2_of_history
    {t A : ℝ} (ht : 0 ≤ t)
    (Z₀ : WholeLineRealL2) (ZG ZR : ℝ → WholeLineRealL2)
    (f₀ fG fR gG gR : ℝ → ℝ)
    (hZG_int : IntervalIntegrable ZG volume 0 t)
    (hZR_int : IntervalIntegrable ZR volume 0 t)
    (hgG_int : IntervalIntegrable gG volume 0 t)
    (hgR_int : IntervalIntegrable gR volume 0 t)
    (hZ₀ : ‖Z₀‖ ≤ A)
    (hZG : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖ZG s‖ ≤ gG s)
    (hZR : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖ZR s‖ ≤ gR s)
    (hZ₀_rep : ((Z₀ : ℝ → ℝ) =ᵐ[volume] f₀))
    (hZG_rep : (((∫ s in (0 : ℝ)..t, ZG s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fG)
    (hZR_rep : (((∫ s in (0 : ℝ)..t, ZR s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fR) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => f₀ x + fG x + fR x) ∧
      ‖Z‖ ≤ A + ∫ s in (0 : ℝ)..t, (gG s + gR s) := by
  let G : WholeLineRealL2 := ∫ s in (0 : ℝ)..t, ZG s
  let R : WholeLineRealL2 := ∫ s in (0 : ℝ)..t, ZR s
  let Z : WholeLineRealL2 := (Z₀ + G) + R
  have hGnorm : ‖∫ s in (0 : ℝ)..t, ZG s‖ ≤
      ∫ s in (0 : ℝ)..t, gG s :=
    wholeLineRealL2_intervalIntegral_norm_le_of_majorant
      ht hZG_int hgG_int hZG
  have hRnorm : ‖∫ s in (0 : ℝ)..t, ZR s‖ ≤
      ∫ s in (0 : ℝ)..t, gR s :=
    wholeLineRealL2_intervalIntegral_norm_le_of_majorant
      ht hZR_int hgR_int hZR
  refine ⟨Z, ?_, ?_⟩
  · have hadd₀ : (((Z₀ + G : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => Z₀ x + G x) := Lp.coeFn_add Z₀ G
    have hadd₁ : ((Z : ℝ → ℝ) =ᵐ[volume]
        fun x => (Z₀ + G) x + R x) := by
      simpa only [Z] using Lp.coeFn_add (Z₀ + G) R
    filter_upwards [hadd₀, hadd₁, hZ₀_rep, hZG_rep, hZR_rep]
      with x ha₀ ha₁ h₀ hG hR
    calc
      Z x = (Z₀ + G) x + R x := ha₁
      _ = (Z₀ x + G x) + R x := by rw [ha₀]
      _ = f₀ x + fG x + fR x := by
        dsimp only [G, R] at hG hR ⊢
        rw [h₀, hG, hR]
  · calc
      ‖Z‖ ≤ ‖Z₀‖ + ‖∫ s in (0 : ℝ)..t, ZG s‖ +
          ‖∫ s in (0 : ℝ)..t, ZR s‖ := by
        dsimp only [Z, G, R]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ A + (∫ s in (0 : ℝ)..t, gG s) +
          ∫ s in (0 : ℝ)..t, gR s := by linarith
      _ = A + ∫ s in (0 : ℝ)..t, (gG s + gR s) := by
        rw [intervalIntegral.integral_add hgG_int hgR_int]
        ring

private theorem bucMildMap_difference_decompose
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀₂ u₀₁ : WholeLineBUC) (U₂ U₁ : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1 x -
        (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1 x =
      ((wholeLineCauchyHeatBUCTotal z.1 u₀₂).1 x -
          (wholeLineCauchyHeatBUCTotal z.1 u₀₁).1 x) +
        (-p.χ) *
          ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ z.1).1 x -
            (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ z.1).1 x) +
        ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ z.1).1 x -
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ z.1).1 x) := by
  rw [wholeLineCauchyBUCMildMap_apply,
    wholeLineCauchyBUCMildMap_apply]
  change
    ((wholeLineCauchyHeatBUCTotal z.1 u₀₂).1 x +
          (-p.χ) *
            (wholeLineCauchyGradientDuhamelBUC p hM hT U₂ z.1).1 x +
          (wholeLineCauchyValueDuhamelBUC p hM hT U₂ z.1).1 x) -
        ((wholeLineCauchyHeatBUCTotal z.1 u₀₁).1 x +
          (-p.χ) *
            (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ z.1).1 x +
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ z.1).1 x) = _
  ring

/-- Canonical BUC one-step difference, realized in the cap-weighted `L²`
space.  The homogeneous term is built from the actual BUC initial data.  The
two time-history representatives remain explicit: this is precisely the
strong-measurability/Fubini bridge that must be supplied by a trajectory-level
construction rather than inferred from pointwise-in-time `L²` existence. -/
theorem exists_capWeighted_coMoving_bucMildMap_differenceL2_of_history
    (p : CMParams) {M eta c T B₀ : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (hT : 0 ≤ T) (hB₀ : 0 ≤ B₀)
    (R : ℝ) (u₀₂ u₀₁ : WholeLineBUC)
    (U₂ U₁ : WholeLineBUCTrajectory T) (z : Set.Icc (0 : ℝ) T)
    (hz : 0 < z.1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (ZG ZR : ℝ → WholeLineRealL2) (gG gR : ℝ → ℝ)
    (hZG_int : IntervalIntegrable ZG volume 0 z.1)
    (hZR_int : IntervalIntegrable ZR volume 0 z.1)
    (hgG_int : IntervalIntegrable gG volume 0 z.1)
    (hgR_int : IntervalIntegrable gR volume 0 z.1)
    (hZG : ∀ s ∈ Set.Icc (0 : ℝ) z.1, ‖ZG s‖ ≤ gG s)
    (hZR : ∀ s ∈ Set.Icc (0 : ℝ) z.1, ‖ZR s‖ ≤ gR s)
    (hZG_rep : (((∫ s in (0 : ℝ)..z.1, ZG s) : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x * (-p.χ) *
        ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)))
    (hZR_rep : (((∫ s in (0 : ℝ)..z.1, ZR s) : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x *
        ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1))) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1
              (x + c * z.1) -
            (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1
              (x + c * z.1))) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c T * B₀ +
        ∫ s in (0 : ℝ)..z.1, (gG s + gR s) := by
  rcases exists_capWeightedMovingHeatL2 heta hz hB₀ R c hdata_meas
      hdata_cap hdata_energy with ⟨Z₀, hZ₀_rep, hZ₀_bound⟩
  have hZ₀_rep' : ((Z₀ : ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x *
        ((wholeLineCauchyHeatBUCTotal z.1 u₀₂).1 (x + c * z.1) -
          (wholeLineCauchyHeatBUCTotal z.1 u₀₁).1 (x + c * z.1))) :=
    hZ₀_rep.trans (Eventually.of_forall fun x => by
      change capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c z.1
            (fun y => u₀₂.1 y - u₀₁.1 y) x =
        capWeightSqrt eta R x *
          ((wholeLineCauchyHeatBUCTotal z.1 u₀₂).1 (x + c * z.1) -
            (wholeLineCauchyHeatBUCTotal z.1 u₀₁).1 (x + c * z.1))
      rw [paper5MovingFrameHeatOp_sub_eq_buc_heat_sub hz])
  have hmass := capHeatSchurMass_le_capMildGrowthBound
    (c := c) heta hz.le z.2.2
  have hexp : Real.exp (-z.1) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz.le)
  have hfactor : Real.exp (-z.1) * capHeatSchurMass eta c z.1 ≤
      2 * capMildGrowthBound eta c T :=
    (mul_le_mul_of_nonneg_right hexp
      (capHeatSchurMass_pos eta c z.1).le).trans (by simpa using hmass)
  have hZ₀_bound' : ‖Z₀‖ ≤ 2 * capMildGrowthBound eta c T * B₀ :=
    hZ₀_bound.trans (mul_le_mul_of_nonneg_right hfactor hB₀)
  rcases capWeightedMild_oneStep_l2_of_history hz.le Z₀ ZG ZR
      (fun x => capWeightSqrt eta R x *
        ((wholeLineCauchyHeatBUCTotal z.1 u₀₂).1 (x + c * z.1) -
          (wholeLineCauchyHeatBUCTotal z.1 u₀₁).1 (x + c * z.1)))
      (fun x => capWeightSqrt eta R x * (-p.χ) *
        ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)))
      (fun x => capWeightSqrt eta R x *
        ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)))
      gG gR hZG_int hZR_int hgG_int hgR_int hZ₀_bound' hZG hZR
      hZ₀_rep' hZG_rep hZR_rep with ⟨Z, hZ_rep, hZ_bound⟩
  refine ⟨Z, hZ_rep.trans ?_, hZ_bound⟩
  filter_upwards with x
  rw [bucMildMap_difference_decompose]
  ring

/-- Constant-plus-inverse-square-root specialization of the one-step norm
estimate.  Its scalar right-hand side is exactly the recurrence consumed by
`volterraPicard_uniform_of_kernel_mass`. -/
theorem capWeightedMild_oneStep_norm_le_const_add_invSqrt
    {t A CG₀ CR₀ C₁ : ℝ} (ht : 0 ≤ t)
    {r : ℝ → ℝ}
    (Z₀ : WholeLineRealL2) (ZG ZR : ℝ → WholeLineRealL2)
    (hZG_int : IntervalIntegrable ZG volume 0 t)
    (hZR_int : IntervalIntegrable ZR volume 0 t)
    (hgrad_int : IntervalIntegrable
      (fun s : ℝ =>
        (CG₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s) volume 0 t)
    (hvalue_int : IntervalIntegrable
      (fun s : ℝ => CR₀ * r s) volume 0 t)
    (hZ₀ : ‖Z₀‖ ≤ A)
    (hZG : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖ZG s‖ ≤
        (CG₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s)
    (hZR : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖ZR s‖ ≤ CR₀ * r s) :
    ‖(Z₀ + ∫ s in (0 : ℝ)..t, ZG s) +
        ∫ s in (0 : ℝ)..t, ZR s‖ ≤
      A + ∫ s in (0 : ℝ)..t,
        (CG₀ + CR₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s := by
  have hGnorm : ‖∫ s in (0 : ℝ)..t, ZG s‖ ≤
      ∫ s in (0 : ℝ)..t,
        (CG₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s :=
    wholeLineRealL2_intervalIntegral_norm_le_of_majorant
      ht hZG_int hgrad_int hZG
  have hRnorm : ‖∫ s in (0 : ℝ)..t, ZR s‖ ≤
      ∫ s in (0 : ℝ)..t, CR₀ * r s :=
    wholeLineRealL2_intervalIntegral_norm_le_of_majorant
      ht hZR_int hvalue_int hZR
  calc
    ‖(Z₀ + ∫ s in (0 : ℝ)..t, ZG s) +
        ∫ s in (0 : ℝ)..t, ZR s‖ ≤
        ‖Z₀‖ + ‖∫ s in (0 : ℝ)..t, ZG s‖ +
          ‖∫ s in (0 : ℝ)..t, ZR s‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ A + (∫ s in (0 : ℝ)..t,
          (CG₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s) +
        ∫ s in (0 : ℝ)..t, CR₀ * r s := by linarith
    _ = A + ∫ s in (0 : ℝ)..t,
        (CG₀ + CR₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s := by
      have hfun : (fun s : ℝ =>
          (CG₀ + CR₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s) =
          fun s : ℝ => CR₀ * r s +
            (CG₀ + C₁ * (t - s) ^ (-(1 / 2 : ℝ))) * r s := by
        funext s
        ring
      rw [hfun, intervalIntegral.integral_add hvalue_int hgrad_int]
      ring

/-- The one-step estimate with the coefficients produced by the two cap
Schur bounds and the two truncated nonlinearities. -/
theorem capWeightedMild_oneStep_norm_le_capKernel
    (p : CMParams) {M eta c T t A : ℝ} (ht : 0 ≤ t)
    {r : ℝ → ℝ}
    (Z₀ : WholeLineRealL2) (ZG ZR : ℝ → WholeLineRealL2)
    (hZG_int : IntervalIntegrable ZG volume 0 t)
    (hZR_int : IntervalIntegrable ZR volume 0 t)
    (hgrad_int : IntervalIntegrable (fun s : ℝ =>
      ((2 * capMildGrowthBound eta c T * eta *
          Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)) +
        capMildKernelInvSqrtConstant p M eta c T *
          (t - s) ^ (-(1 / 2 : ℝ))) * r s) volume 0 t)
    (hvalue_int : IntervalIntegrable (fun s : ℝ =>
      (2 * capMildGrowthBound eta c T *
        (1 + reactionLip p.α M)) * r s) volume 0 t)
    (hZ₀ : ‖Z₀‖ ≤ A)
    (hZG : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖ZG s‖ ≤
        ((2 * capMildGrowthBound eta c T * eta *
            Real.sqrt
              (capWeightedChemotaxisOperatorSquareConstant p M eta)) +
          capMildKernelInvSqrtConstant p M eta c T *
            (t - s) ^ (-(1 / 2 : ℝ))) * r s)
    (hZR : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖ZR s‖ ≤ (2 * capMildGrowthBound eta c T *
        (1 + reactionLip p.α M)) * r s) :
    ‖(Z₀ + ∫ s in (0 : ℝ)..t, ZG s) +
        ∫ s in (0 : ℝ)..t, ZR s‖ ≤
      A + ∫ s in (0 : ℝ)..t,
        (capMildKernelConstant p M eta c T +
          capMildKernelInvSqrtConstant p M eta c T *
            (t - s) ^ (-(1 / 2 : ℝ))) * r s := by
  have h := capWeightedMild_oneStep_norm_le_const_add_invSqrt
    (CG₀ := 2 * capMildGrowthBound eta c T * eta *
      Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta))
    (CR₀ := 2 * capMildGrowthBound eta c T *
      (1 + reactionLip p.α M))
    (C₁ := capMildKernelInvSqrtConstant p M eta c T)
    ht Z₀ ZG ZR hZG_int hZR_int hgrad_int hvalue_int hZ₀ hZG hZR
  simpa only [capMildKernelConstant, add_assoc, add_comm, add_left_comm] using h

/-- Once the analytic one-step estimate has been reduced to the common
cap kernel, the whole Picard family stays in the same scalar ball on every
short window whose kernel mass is strictly below one. -/
theorem capMildPicard_uniform_of_short_time
    (p : CMParams) {M eta c T A B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq_lt : capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T < 1)
    (hclose : A +
        (capMildKernelConstant p M eta c T * T +
          2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    {r : ℕ → ℝ → ℝ}
    (hr_int : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      IntervalIntegrable (fun s : ℝ =>
        (capMildKernelConstant p M eta c T +
          capMildKernelInvSqrtConstant p M eta c T *
            (t - s) ^ (-(1 / 2 : ℝ))) * r n s) volume 0 t)
    (hr₀ : ∀ t ∈ Set.Icc (0 : ℝ) T, r 0 t ≤ B)
    (hr_nonneg : ∀ n t, t ∈ Set.Icc (0 : ℝ) T → 0 ≤ r n t)
    (hstep : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      r (n + 1) t ≤ A + ∫ s in (0 : ℝ)..t,
        (capMildKernelConstant p M eta c T +
          capMildKernelInvSqrtConstant p M eta c T *
            (t - s) ^ (-(1 / 2 : ℝ))) * r n s) :
    ∀ n t, t ∈ Set.Icc (0 : ℝ) T → r n t ≤ B := by
  let C₀ : ℝ := capMildKernelConstant p M eta c T
  let C₁ : ℝ := capMildKernelInvSqrtConstant p M eta c T
  let K : ℝ → ℝ := fun tau => C₀ + C₁ * tau ^ (-(1 / 2 : ℝ))
  let q : ℝ := C₀ * T + 2 * C₁ * Real.sqrt T
  have hC₀ : 0 ≤ C₀ := capMildKernelConstant_nonneg p hM heta hT c
  have hC₁ : 0 ≤ C₁ :=
    capMildKernelInvSqrtConstant_nonneg p hM heta hT c
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact add_nonneg (mul_nonneg hC₀ hT)
      (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Real.sqrt_nonneg _))
  apply volterraPicard_uniform_of_kernel_mass
    (K := K) (r := r) (q := q)
    hT hA hB hq (by simpa only [q, C₀, C₁] using hq_lt)
      (by simpa only [q, C₀, C₁] using hclose)
  · intro tau htau
    dsimp only [K]
    exact add_nonneg hC₀
      (mul_nonneg hC₁ (Real.rpow_nonneg htau.1 _))
  · intro t _ht
    simpa only [K] using
      (intervalIntegrable_const_add_mul_invSqrt_sub
        (t := t) (C0 := C₀) (C1 := C₁))
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp only [intervalIntegral.integral_same, q]
      exact hq
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      simpa only [K, q] using
        (intervalIntegral_const_add_mul_invSqrt_sub_le
          htpos ht.2 hC₀ hC₁)
  · intro n t ht
    simpa only [K, C₀, C₁] using hr_int n t ht
  · exact hr₀
  · exact hr_nonneg
  · intro n t ht
    simpa only [K, C₀, C₁] using hstep n t ht

section AxiomAudit

#print axioms exists_capWeightedMovingHeatL2
#print axioms exists_capWeightedMovingHeatGradientL2
#print axioms capWeight_clampProfile_difference_l2_bounded
#print axioms capWeighted_coMovingTruncatedChemotaxis_l2_bounded
#print axioms capWeighted_coMovingTruncatedReaction_l2_bounded
#print axioms coMovingTruncatedChemotaxisDifference_measurable
#print axioms coMovingTruncatedReactionDifference_measurable
#print axioms exists_capWeightedMovingHeatGradient_truncatedChemotaxisL2
#print axioms exists_capWeightedMovingHeat_truncatedReactionL2
#print axioms weightedMovingHeatGrowth_le_capMildGrowthBound
#print axioms weightedMovingHeatGrowth_neg_le_capMildGrowthBound
#print axioms capHeatSchurMass_le_capMildGrowthBound
#print axioms capHeatGradientSchurMass_le_capMildKernel
#print axioms capMildKernelConstant_nonneg
#print axioms capMildKernelInvSqrtConstant_nonneg
#print axioms
  exists_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
#print axioms exists_capWeightedMovingHeat_truncatedReactionL2_le_kernel
#print axioms capWeightedMild_oneStep_l2_of_history
#print axioms exists_capWeighted_coMoving_bucMildMap_differenceL2_of_history
#print axioms capWeightedMild_oneStep_norm_le_const_add_invSqrt
#print axioms capWeightedMild_oneStep_norm_le_capKernel
#print axioms capMildPicard_uniform_of_short_time

end AxiomAudit

end ShenWork.Paper1
