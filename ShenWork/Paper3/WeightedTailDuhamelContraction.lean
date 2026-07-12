/-
  Quantitative Banach fixed-point core for the weighted tail Duhamel map.

  The analytic realization of a trajectory is conjugated by its exponential
  weight before this lemma is applied.  In that norm the linear datum costs at
  most `R/2`, the quadratic Duhamel term costs `A*R^2`, and its difference costs
  `2*A*R`.  The condition `4*A*R <= 1` therefore gives both a self-map and a
  contraction with constant at most `1/2`.
-/
import Mathlib

namespace ShenWork.Paper3

open Set Metric
open scoped NNReal

noncomputable section

/-- Quantitative hypotheses produced by the weighted singular-convolution
estimate for a tail Picard map. -/
structure WeightedTailPicardBounds
    (X : Type*) [NormedAddCommGroup X] (Phi : X → X)
    (A R : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  R_pos : 0 < R
  datum_bound : norm (Phi (0 : X)) ≤ R / 2
  self_bound : ∀ x, norm x ≤ R → norm (Phi x) ≤ R / 2 + A * R ^ 2
  difference_bound : ∀ x y, norm x ≤ R → norm y ≤ R →
    norm (Phi x - Phi y) ≤ (2 * A * R) * norm (x - y)
  small : 4 * A * R ≤ 1

lemma WeightedTailPicardBounds.contraction_factor_nonneg
    {X : Type*} [NormedAddCommGroup X] {Phi : X → X} {A R : ℝ}
    (H : WeightedTailPicardBounds X Phi A R) :
    0 ≤ 2 * A * R :=
  mul_nonneg (mul_nonneg (by norm_num) H.A_nonneg) H.R_pos.le

lemma WeightedTailPicardBounds.contraction_factor_lt_one
    {X : Type*} [NormedAddCommGroup X] {Phi : X → X} {A R : ℝ}
    (H : WeightedTailPicardBounds X Phi A R) :
    2 * A * R < 1 := by
  have hhalf : 2 * A * R ≤ 1 / 2 := by nlinarith [H.small]
  nlinarith [H.R_pos]

/-- The quantitative weighted estimates force the Picard map to preserve the
closed radius-`R` ball around zero. -/
theorem WeightedTailPicardBounds.mapsTo_closedBall
    {X : Type*} [NormedAddCommGroup X] {Phi : X → X} {A R : ℝ}
    (H : WeightedTailPicardBounds X Phi A R) :
    MapsTo Phi (Metric.closedBall (0 : X) R) (Metric.closedBall 0 R) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  have hmain := H.self_bound x hx
  have hAR : A * R ≤ 1 / 4 := by nlinarith [H.small]
  have hquad : A * R ^ 2 ≤ R / 4 := by
    have hR0 : 0 ≤ R := H.R_pos.le
    have := mul_le_mul_of_nonneg_right hAR hR0
    nlinarith
  nlinarith [H.R_pos]

/-- The restriction of the weighted tail Picard map to its invariant ball is
a `ContractingWith` map in Mathlib's sense. -/
theorem WeightedTailPicardBounds.contractingWith_restrict
    {X : Type*} [NormedAddCommGroup X] {Phi : X → X} {A R : ℝ}
    (H : WeightedTailPicardBounds X Phi A R) :
    let B : Set X := Metric.closedBall 0 R
    ContractingWith (Real.toNNReal (2 * A * R))
      (H.mapsTo_closedBall.restrict Phi B B) := by
  let B : Set X := Metric.closedBall 0 R
  let q : ℝ := 2 * A * R
  have hq0 : 0 ≤ q := H.contraction_factor_nonneg
  have hq1 : q < 1 := H.contraction_factor_lt_one
  refine ⟨Real.toNNReal_lt_one.mpr hq1, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq,
    MapsTo.val_restrict_apply, MapsTo.val_restrict_apply,
    dist_eq_norm, dist_eq_norm, Real.coe_toNNReal q hq0]
  have hxnorm : ‖x.1‖ ≤ R := by
    have hxm : x.1 ∈ Metric.closedBall (0 : X) R := x.2
    rwa [Metric.mem_closedBall, dist_zero_right] at hxm
  have hynorm : ‖y.1‖ ≤ R := by
    have hym : y.1 ∈ Metric.closedBall (0 : X) R := y.2
    rwa [Metric.mem_closedBall, dist_zero_right] at hym
  exact H.difference_bound x.1 y.1
    hxnorm hynorm

/-- Banach fixed point for the weighted tail Duhamel map, with uniqueness among
all trajectories in the same weighted ball. -/
theorem existsUnique_weightedTail_fixedPoint
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
    {Phi : X → X} {A R : ℝ}
    (H : WeightedTailPicardBounds X Phi A R) :
    ∃ x ∈ Metric.closedBall (0 : X) R,
      Function.IsFixedPt Phi x ∧
        ∀ y ∈ Metric.closedBall (0 : X) R,
          Function.IsFixedPt Phi y → y = x := by
  let B : Set X := Metric.closedBall 0 R
  let self : MapsTo Phi B B := H.mapsTo_closedBall
  let q : ℝ := 2 * A * R
  have hBc : IsComplete B := Metric.isClosed_closedBall.isComplete
  have hcontract : ContractingWith (Real.toNNReal q)
      (self.restrict Phi B B) := H.contractingWith_restrict
  have hzero : (0 : X) ∈ B := by
    exact Metric.mem_closedBall_self H.R_pos.le
  have hedist : edist (0 : X) (Phi 0) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨x, hx, hfix, _, _⟩ :=
    hcontract.exists_fixedPoint' hBc self hzero hedist
  refine ⟨x, hx, hfix, ?_⟩
  intro y hy hyfix
  have hxs : Function.IsFixedPt (self.restrict Phi B B) ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa [MapsTo.val_restrict_apply] using hfix
  have hys : Function.IsFixedPt (self.restrict Phi B B) ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa [MapsTo.val_restrict_apply] using hyfix
  exact congrArg Subtype.val (hcontract.fixedPoint_unique' hys hxs)

#print axioms WeightedTailPicardBounds.mapsTo_closedBall
#print axioms WeightedTailPicardBounds.contractingWith_restrict
#print axioms existsUnique_weightedTail_fixedPoint

end

end ShenWork.Paper3
