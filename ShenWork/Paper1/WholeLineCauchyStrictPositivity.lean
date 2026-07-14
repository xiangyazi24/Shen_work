import ShenWork.Paper1.WholeLineCauchyDuhamel
import ShenWork.Paper1.Statements

open MeasureTheory Set Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **STEP 1 (homogeneous strict positivity).**  The modified heat semigroup of a
nonnegative, bounded, measurable datum that is bounded below by `δ > 0` on a
left half-line `Iic A` is strictly positive everywhere at every positive time.
The strictly-positive heat kernel integrated against a datum that is `≥ δ` on a
set of positive measure is strictly positive; the reaction damping `e^{-t}` only
rescales. Reusable base for the whole-line Cauchy strict-positivity conjunct. -/
theorem wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {M : ℝ}
    (hf_bd : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    {δ A : ℝ} (hδ : 0 < δ) (hA : ∀ y ≤ A, δ ≤ f y) (x : ℝ) :
    0 < wholeLineCauchyHeatOp t f x := by
  have hg_nonneg : 0 ≤ fun y => heatKernel t (x - y) * f y := by
    intro y; exact mul_nonneg (heatKernel_nonneg ht _) (hf_nonneg y)
  have hg_int : Integrable (fun y => heatKernel t (x - y) * f y) volume :=
    heatKernel_mul_bounded_integrable ht x hf_bd hf_meas
  -- The integrand is strictly positive on `Icc (A-1) A`, a set of measure `1`.
  have hsub : Set.Icc (A - 1) A ⊆ Function.support (fun y => heatKernel t (x - y) * f y) := by
    intro y hy
    have hpos : 0 < heatKernel t (x - y) * f y :=
      mul_pos (heatKernel_pos ht _) (lt_of_lt_of_le hδ (hA y hy.2))
    exact ne_of_gt hpos
  have hmeas_pos : 0 < volume (Function.support (fun y => heatKernel t (x - y) * f y)) := by
    have hIcc : (0 : ENNReal) < volume (Set.Icc (A - 1) A) := by
      rw [Real.volume_Icc]
      simp only [sub_sub_cancel]
      exact ENNReal.ofReal_pos.mpr one_pos
    exact lt_of_lt_of_le hIcc (measure_mono hsub)
  have hint_pos : 0 < ∫ y, heatKernel t (x - y) * f y :=
    (integral_pos_iff_support_of_nonneg hg_nonneg hg_int).mpr hmeas_pos
  -- Unfold `wholeLineCauchyHeatOp = modifiedSemigroup = e^{-t} · heatSemigroup`.
  show 0 < modifiedSemigroup t f x
  rw [modifiedSemigroup, heatSemigroup]
  exact mul_pos (Real.exp_pos _) hint_pos

section WholeLineCauchyStrictPositivityAxiomAudit

#print axioms wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot

end WholeLineCauchyStrictPositivityAxiomAudit

end ShenWork.Paper1
