import ShenWork.Paper1.WholeLineWeightedRegularityMild

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Cap-weighted spatial difference quotients

Spatially differencing the canonical mild equation keeps one derivative on
the heat kernel and moves the other difference onto the nonlinear source.
The estimates below supply the nonlinear part of that argument directly,
without assuming an exact-weight population derivative.
-/

/-- Forward spatial difference quotient, totalized at `h = 0`. -/
def spatialDifferenceQuotient (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- Co-moving cap-weighted population difference quotient. -/
def capWeightedCoMovingSpatialDifferenceQuotient
    (eta R c s h : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightSqrt eta R x * spatialDifferenceQuotient h u (x + c * s)

/-- Co-moving cap-weighted truncated chemotaxis-source difference quotient.
The translated profile form is the one that commutes directly with the
truncated flux by `wholeLineCauchyTruncatedFlux_comp_add_const`. -/
def capWeightedCoMovingTruncatedChemotaxisSpatialDifferenceQuotient
    (p : CMParams) (M eta R c s h : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightedCoMovingTruncatedChemotaxisDifference
    p M eta R c s (fun y => u (y + h)) u x / h

/-- Co-moving cap-weighted shifted-reaction difference quotient. -/
def capWeightedCoMovingTruncatedReactionSpatialDifferenceQuotient
    (p : CMParams) (M eta R c s h : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  capWeightedCoMovingTruncatedReactionDifference
    p M eta R c s (fun y => u (y + h)) u x / h

private theorem spatialDifferenceQuotient_rescale_sq
    {h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (x : ℝ) :
    h ^ 2 * |spatialDifferenceQuotient h f x| ^ 2 =
      |f (x + h) - f x| ^ 2 := by
  unfold spatialDifferenceQuotient
  rw [abs_div, div_pow, sq_abs h]
  field_simp

private theorem capWeight_raw_spatial_difference_integrable
    {eta R h : ℝ} (hh : h ≠ 0) {f : ℝ → ℝ}
    (hquot : Integrable (fun x =>
      capWeight eta R x * |spatialDifferenceQuotient h f x| ^ 2)) :
    Integrable (fun x =>
      capWeight eta R x * |f (x + h) - f x| ^ 2) := by
  have hscaled := hquot.const_mul (h ^ 2)
  refine hscaled.congr (Eventually.of_forall fun x => ?_)
  change h ^ 2 *
      (capWeight eta R x * |spatialDifferenceQuotient h f x| ^ 2) =
    capWeight eta R x * |f (x + h) - f x| ^ 2
  calc
    _ = capWeight eta R x *
        (h ^ 2 * |spatialDifferenceQuotient h f x| ^ 2) := by ring
    _ = _ := by rw [spatialDifferenceQuotient_rescale_sq hh]

private theorem capWeight_raw_spatial_difference_integral_eq
    {eta R h : ℝ} (hh : h ≠ 0) {f : ℝ → ℝ} :
    (∫ x : ℝ, capWeight eta R x * |f (x + h) - f x| ^ 2) =
      h ^ 2 * ∫ x : ℝ,
        capWeight eta R x * |spatialDifferenceQuotient h f x| ^ 2 := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change capWeight eta R x * |f (x + h) - f x| ^ 2 =
      h ^ 2 *
        (capWeight eta R x * |spatialDifferenceQuotient h f x| ^ 2)
    rw [← spatialDifferenceQuotient_rescale_sq hh]
    ring

/-- The translated truncated chemotaxis source is cap-weighted `L²`
Lipschitz at the level of spatial difference quotients.  The constant is
independent of the quotient step `h`, cap radius `R`, frame speed, and time. -/
theorem capWeighted_coMovingTruncatedChemotaxis_spatialDifferenceQuotient_l2_bounded
    (p : CMParams) {M eta R c s h : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (hh : h ≠ 0) {u : ℝ → ℝ} (hu : IsCUnifBdd u)
    (hquot : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h u (x + c * s)| ^ 2)) :
    Integrable (fun x =>
        capWeightedCoMovingTruncatedChemotaxisSpatialDifferenceQuotient
          p M eta R c s h u x ^ 2) ∧
      (∫ x : ℝ,
          capWeightedCoMovingTruncatedChemotaxisSpatialDifferenceQuotient
            p M eta R c s h u x ^ 2) ≤
        capWeightedChemotaxisOperatorSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u (x + c * s)| ^ 2 := by
  let u₂ : ℝ → ℝ := fun y => u (y + h)
  have hu₂ : IsCUnifBdd u₂ := isCUnifBdd_comp_add_const hu h
  have hquot' : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u (y + c * s)) x| ^ 2) := by
    simpa [spatialDifferenceQuotient, add_assoc, add_comm, add_left_comm] using hquot
  have hraw : Integrable (fun x => capWeight eta R x *
      |u₂ (x + c * s) - u (x + c * s)| ^ 2) := by
    change Integrable (fun x => capWeight eta R x *
      |u ((x + c * s) + h) - u (x + c * s)| ^ 2)
    have hbase := capWeight_raw_spatial_difference_integrable
      (eta := eta) (R := R) hh
      (f := fun x => u (x + c * s)) hquot'
    simpa [add_assoc, add_comm, add_left_comm] using hbase
  have hsource := capWeighted_coMovingTruncatedChemotaxis_l2_bounded
    p hM heta heta_one hu₂ hu hraw
  let F : ℝ → ℝ := fun x =>
    capWeightedCoMovingTruncatedChemotaxisDifference
      p M eta R c s u₂ u x
  have hF : Integrable (fun x => F x ^ 2) := by
    simpa only [F] using hsource.1
  have hout : Integrable (fun x => (F x / h) ^ 2) := by
    have hs := hF.const_mul (h⁻¹ ^ 2)
    simpa [div_eq_mul_inv, mul_pow, mul_comm] using hs
  refine ⟨by
    simpa only [capWeightedCoMovingTruncatedChemotaxisSpatialDifferenceQuotient,
      F, u₂] using hout, ?_⟩
  have hraw_eq :
      (∫ x : ℝ, capWeight eta R x *
          |u₂ (x + c * s) - u (x + c * s)| ^ 2) =
        h ^ 2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u (x + c * s)| ^ 2 := by
    change (∫ x : ℝ, capWeight eta R x *
        |u ((x + c * s) + h) - u (x + c * s)| ^ 2) = _
    have heq := capWeight_raw_spatial_difference_integral_eq
      (eta := eta) (R := R) hh
      (f := fun x => u (x + c * s))
    simpa [spatialDifferenceQuotient, add_assoc, add_comm, add_left_comm] using heq
  have hscaled := mul_le_mul_of_nonneg_left hsource.2 (sq_nonneg h⁻¹)
  change (∫ x : ℝ, (F x / h) ^ 2) ≤ _
  rw [show (∫ x : ℝ, (F x / h) ^ 2) =
      h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 by
    rw [show (fun x : ℝ => (F x / h) ^ 2) =
        fun x : ℝ => h⁻¹ ^ 2 * F x ^ 2 by
      funext x
      simp only [div_eq_mul_inv, mul_pow]
      ring,
      MeasureTheory.integral_const_mul]]
  calc
    h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 ≤
        h⁻¹ ^ 2 *
          (capWeightedChemotaxisOperatorSquareConstant p M eta *
            ∫ x : ℝ, capWeight eta R x *
              |u₂ (x + c * s) - u (x + c * s)| ^ 2) := by
      simpa only [F] using hscaled
    _ = capWeightedChemotaxisOperatorSquareConstant p M eta *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u (x + c * s)| ^ 2 := by
      rw [hraw_eq]
      field_simp

/-- The translated shifted reaction satisfies the parallel spatial
difference-quotient estimate, with no singular heat-kernel factor. -/
theorem capWeighted_coMovingTruncatedReaction_spatialDifferenceQuotient_l2_bounded
    (p : CMParams) {M eta R c s h : ℝ}
    (hM : 0 ≤ M) (hh : h ≠ 0) {u : ℝ → ℝ} (hu : IsCUnifBdd u)
    (hquot : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h u (x + c * s)| ^ 2)) :
    Integrable (fun x =>
        capWeightedCoMovingTruncatedReactionSpatialDifferenceQuotient
          p M eta R c s h u x ^ 2) ∧
      (∫ x : ℝ,
          capWeightedCoMovingTruncatedReactionSpatialDifferenceQuotient
            p M eta R c s h u x ^ 2) ≤
        (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u (x + c * s)| ^ 2 := by
  let u₂ : ℝ → ℝ := fun y => u (y + h)
  have hu₂ : IsCUnifBdd u₂ := isCUnifBdd_comp_add_const hu h
  have hquot' : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u (y + c * s)) x| ^ 2) := by
    simpa [spatialDifferenceQuotient, add_assoc, add_comm, add_left_comm] using hquot
  have hraw : Integrable (fun x => capWeight eta R x *
      |u₂ (x + c * s) - u (x + c * s)| ^ 2) := by
    change Integrable (fun x => capWeight eta R x *
      |u ((x + c * s) + h) - u (x + c * s)| ^ 2)
    have hbase := capWeight_raw_spatial_difference_integrable
      (eta := eta) (R := R) hh
      (f := fun x => u (x + c * s)) hquot'
    simpa [add_assoc, add_comm, add_left_comm] using hbase
  have hsource := capWeighted_coMovingTruncatedReaction_l2_bounded
    p hM hu₂ hu hraw
  let F : ℝ → ℝ := fun x =>
    capWeightedCoMovingTruncatedReactionDifference
      p M eta R c s u₂ u x
  have hF : Integrable (fun x => F x ^ 2) := by
    simpa only [F] using hsource.1
  have hout : Integrable (fun x => (F x / h) ^ 2) := by
    have hs := hF.const_mul (h⁻¹ ^ 2)
    simpa [div_eq_mul_inv, mul_pow, mul_comm] using hs
  refine ⟨by
    simpa only [capWeightedCoMovingTruncatedReactionSpatialDifferenceQuotient,
      F, u₂] using hout, ?_⟩
  have hraw_eq :
      (∫ x : ℝ, capWeight eta R x *
          |u₂ (x + c * s) - u (x + c * s)| ^ 2) =
        h ^ 2 * ∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h u (x + c * s)| ^ 2 := by
    change (∫ x : ℝ, capWeight eta R x *
        |u ((x + c * s) + h) - u (x + c * s)| ^ 2) = _
    have heq := capWeight_raw_spatial_difference_integral_eq
      (eta := eta) (R := R) hh
      (f := fun x => u (x + c * s))
    simpa [spatialDifferenceQuotient, add_assoc, add_comm, add_left_comm] using heq
  have hscaled := mul_le_mul_of_nonneg_left hsource.2 (sq_nonneg h⁻¹)
  change (∫ x : ℝ, (F x / h) ^ 2) ≤ _
  rw [show (∫ x : ℝ, (F x / h) ^ 2) =
      h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 by
    rw [show (fun x : ℝ => (F x / h) ^ 2) =
        fun x : ℝ => h⁻¹ ^ 2 * F x ^ 2 by
      funext x
      simp only [div_eq_mul_inv, mul_pow]
      ring,
      MeasureTheory.integral_const_mul]]
  calc
    h⁻¹ ^ 2 * ∫ x : ℝ, F x ^ 2 ≤
        h⁻¹ ^ 2 * ((1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |u₂ (x + c * s) - u (x + c * s)| ^ 2) := by
      simpa only [F] using hscaled
    _ = (1 + reactionLip p.α M) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h u (x + c * s)| ^ 2 := by
      rw [hraw_eq]
      field_simp

section AxiomAudit

#print axioms
  capWeighted_coMovingTruncatedChemotaxis_spatialDifferenceQuotient_l2_bounded
#print axioms
  capWeighted_coMovingTruncatedReaction_spatialDifferenceQuotient_l2_bounded

end AxiomAudit

end ShenWork.Paper1
