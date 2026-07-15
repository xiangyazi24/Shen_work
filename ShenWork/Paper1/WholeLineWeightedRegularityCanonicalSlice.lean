import ShenWork.Paper1.WholeLineWeightedRegularityMild
import ShenWork.Paper1.WholeLineWeightedRegularityL2History

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

/-- Turn an arbitrary existential `L²` representative into the canonical
representative, retaining its norm bound. -/
theorem exists_sqIntegrable_canonicalRealL2_norm_le_of_exists_ae
    {g : ℝ → ℝ} {B : ℝ}
    (h : ∃ Z : WholeLineRealL2,
      (((Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g) ∧ ‖Z‖ ≤ B) :
    ∃ (hgmeas : AEStronglyMeasurable g volume)
      (hg2 : Integrable (fun x : ℝ => g x ^ 2) volume),
      ‖wholeLineRealL2OfSqIntegrable g hgmeas hg2‖ ≤ B := by
  rcases h with ⟨Z, hrep, hZ⟩
  have hgmeas : AEStronglyMeasurable g volume :=
    (Lp.memLp Z).1.congr hrep
  have hgmem : MemLp g 2 volume :=
    (memLp_congr_ae hrep).1 (Lp.memLp Z)
  have hg2 : Integrable (fun x : ℝ => g x ^ 2) volume :=
    (memLp_two_iff_integrable_sq hgmeas).1 hgmem
  refine ⟨hgmeas, hg2, ?_⟩
  have hcanon : wholeLineRealL2OfSqIntegrable g hgmeas hg2 = Z := by
    apply Lp.ext
    exact (wholeLineRealL2OfSqIntegrable_coe_ae g hgmeas hg2).trans hrep.symm
  rw [hcanon]
  exact hZ

/-- Canonical form of the already proved chemotaxis slice estimate. -/
theorem exists_canonical_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
    (p : CMParams) {M eta R c s tau T B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (htau : 0 < tau) (htauT : tau ≤ T) (hB : 0 ≤ B)
    (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    let g : ℝ → ℝ := fun x => capWeightSqrt eta R x *
      paper5MovingFrameHeatGradOp c tau
        (coMovingTruncatedChemotaxisDifference
          p M c s u₂.1 u₁.1) x
    ∃ (hgmeas : AEStronglyMeasurable g volume)
      (hg2 : Integrable (fun x : ℝ => g x ^ 2) volume),
      ‖wholeLineRealL2OfSqIntegrable g hgmeas hg2‖ ≤
        ((2 * capMildGrowthBound eta c T * eta *
              Real.sqrt
                (capWeightedChemotaxisOperatorSquareConstant p M eta)) +
          capMildKernelInvSqrtConstant p M eta c T *
            tau ^ (-(1 / 2 : ℝ))) * B := by
  dsimp only
  apply exists_sqIntegrable_canonicalRealL2_norm_le_of_exists_ae
  exact exists_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
    p hM heta heta_one htau htauT hB u₂ u₁ hclose henergy

/-- Canonical form of the already proved reaction slice estimate. -/
theorem exists_canonical_capWeightedMovingHeat_truncatedReactionL2_le_kernel
    (p : CMParams) {M eta R c s tau T B : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (htau : 0 < tau) (htauT : tau ≤ T) (hB : 0 ≤ B)
    (u₂ u₁ : WholeLineBUC)
    (hclose : Integrable (fun x => capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2))
    (henergy : (∫ x : ℝ, capWeight eta R x *
      |u₂.1 (x + c * s) - u₁.1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    let g : ℝ → ℝ := fun x => capWeightSqrt eta R x *
      paper5MovingFrameHeatOp c tau
        (coMovingTruncatedReactionDifference
          p M c s u₂.1 u₁.1) x
    ∃ (hgmeas : AEStronglyMeasurable g volume)
      (hg2 : Integrable (fun x : ℝ => g x ^ 2) volume),
      ‖wholeLineRealL2OfSqIntegrable g hgmeas hg2‖ ≤
        2 * capMildGrowthBound eta c T *
          (1 + reactionLip p.α M) * B := by
  dsimp only
  apply exists_sqIntegrable_canonicalRealL2_norm_le_of_exists_ae
  exact exists_capWeightedMovingHeat_truncatedReactionL2_le_kernel
    p hM heta htau htauT hB u₂ u₁ hclose henergy

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_sqIntegrable_canonicalRealL2_norm_le_of_exists_ae
#print axioms
  ShenWork.Paper1.exists_canonical_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
#print axioms
  ShenWork.Paper1.exists_canonical_capWeightedMovingHeat_truncatedReactionL2_le_kernel
