/-
# Restarted mild smoothing: shared closure core

This file contains the problem-independent part of the restarted Duhamel
argument used by Paper 2 and Paper 3.  There are deliberately two exit doors:

* `bochner_mild_affine_bound` is an affine estimate and needs no smallness;
* `superlinear_closedBall_fixedPoint` is the Banach fixed-point exit and needs
  a strict superlinear smallness inequality.

The semigroup, source, and trajectory spaces are supplied by the application.
The strict inequality in the second exit is essential: a non-strict bound that
allows contraction factor one is not enough for Banach's theorem.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Contracting

namespace ShenWork.PDE

open MeasureTheory Set

noncomputable section

/-! ## Bochner-Duhamel norm extraction -/

/-- Taking the norm in a vector-valued Duhamel formula.  This is the common
Bochner-integral glue; all application-specific smoothing estimates enter only
through `hpoint`. -/
theorem bochner_mild_norm_le
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {w linear integrand : ℝ → Z} {major : ℝ → ℝ} {t L : ℝ}
    (ht : 0 ≤ t)
    (hmild : w t = linear t + ∫ s in (0 : ℝ)..t, integrand s)
    (hlinear : ‖linear t‖ ≤ L)
    (hmajor : IntervalIntegrable major volume 0 t)
    (hpoint : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖integrand s‖ ≤ major s) :
    ‖w t‖ ≤ L + ∫ s in (0 : ℝ)..t, major s := by
  rw [hmild]
  refine (norm_add_le _ _).trans (add_le_add hlinear ?_)
  exact intervalIntegral.norm_integral_le_of_norm_le ht
    (Filter.Eventually.of_forall fun s hs => hpoint s hs) hmajor

/-- L3a, the affine exit.  Once the forcing has a constant bound, a mild
trajectory is controlled by the kernel mass.  There is no smallness
assumption and no fixed-point argument in this branch. -/
theorem bochner_mild_affine_bound
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {w linear integrand : ℝ → Z} {kernel : ℝ → ℝ}
    {t M datum Lambda Kzero : ℝ}
    (ht : 0 ≤ t)
    (hmild : w t = linear t + ∫ s in (0 : ℝ)..t, integrand s)
    (hlinear : ‖linear t‖ ≤ M * datum)
    (hkernel : IntervalIntegrable kernel volume 0 t)
    (hpoint : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      ‖integrand s‖ ≤ Lambda * kernel s)
    (hLambda : 0 ≤ Lambda)
    (hkernelMass : (∫ s in (0 : ℝ)..t, kernel s) ≤ Kzero) :
    ‖w t‖ ≤ M * datum + Lambda * Kzero := by
  have hscaledInt : IntervalIntegrable (fun s => Lambda * kernel s) volume 0 t :=
    hkernel.const_mul Lambda
  have hnorm := bochner_mild_norm_le ht hmild hlinear hscaledInt hpoint
  calc
    ‖w t‖ ≤ M * datum + ∫ s in (0 : ℝ)..t, Lambda * kernel s := hnorm
    _ = M * datum + Lambda * ∫ s in (0 : ℝ)..t, kernel s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ M * datum + Lambda * Kzero :=
      add_le_add_right (mul_le_mul_of_nonneg_left hkernelMass hLambda) _

/-! ## The superlinear Banach exit -/

/-- Data needed after the singular Bochner convolution has been estimated on
a closed trajectory ball.  The exponent is a natural number because the P3
nonlinearity is quadratic; this avoids hiding any real-power side conditions.

`map_bound` is the Duhamel self-map estimate and `difference_bound` is the
corresponding local Lipschitz estimate. -/
structure SuperlinearClosedBallData
    {X : Type*} [MetricSpace X]
    (F : X → X) (center : X) where
  order : ℕ
  M : ℝ
  datum : ℝ
  Lambda : ℝ
  kernelMass : ℝ
  radius : ℝ
  order_pos : 0 < order
  M_nonneg : 0 ≤ M
  datum_nonneg : 0 ≤ datum
  Lambda_nonneg : 0 ≤ Lambda
  kernelMass_nonneg : 0 ≤ kernelMass
  radius_pos : 0 < radius
  radius_eq : radius = 2 * M * datum
  superlinear_small :
    Lambda * kernelMass * radius ^ order < 1 / 2
  map_bound : ∀ x ∈ Metric.closedBall center radius,
    dist (F x) center ≤
      M * datum + Lambda * kernelMass * radius ^ (order + 1)
  difference_bound : ∀ x ∈ Metric.closedBall center radius,
    ∀ y ∈ Metric.closedBall center radius,
      dist (F x) (F y) ≤
        (2 * Lambda * kernelMass * radius ^ order) * dist x y

namespace SuperlinearClosedBallData

variable {X : Type*} [MetricSpace X]
  {F : X → X} {center : X}

private theorem contractionFactor_nonneg
    (D : SuperlinearClosedBallData F center) :
    0 ≤ 2 * D.Lambda * D.kernelMass * D.radius ^ D.order := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) D.Lambda_nonneg)
      D.kernelMass_nonneg)
    (pow_nonneg D.radius_pos.le _)

private theorem contractionFactor_lt_one
    (D : SuperlinearClosedBallData F center) :
    2 * D.Lambda * D.kernelMass * D.radius ^ D.order < 1 := by
  nlinarith [D.superlinear_small]

/-- The Duhamel map sends the strong trajectory ball to itself. -/
theorem mapsTo (D : SuperlinearClosedBallData F center) :
    MapsTo F (Metric.closedBall center D.radius)
      (Metric.closedBall center D.radius) := by
  intro x hx
  rw [Metric.mem_closedBall]
  have hmap := D.map_bound x hx
  have hhalf :
      D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) <
        D.radius / 2 := by
    have hr0 : 0 ≤ D.radius := D.radius_pos.le
    have hmul := mul_lt_mul_of_pos_right D.superlinear_small D.radius_pos
    calc
      D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) =
          (D.Lambda * D.kernelMass * D.radius ^ D.order) * D.radius := by
            rw [pow_succ]
            ring
      _ < (1 / 2) * D.radius := hmul
      _ = D.radius / 2 := by ring
  have hdatum : D.M * D.datum = D.radius / 2 := by
    rw [D.radius_eq]
    ring
  have hlt : dist (F x) center < D.radius := by
    calc
      dist (F x) center ≤ D.M * D.datum +
          D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) := hmap
      _ = D.radius / 2 +
          D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) := by rw [hdatum]
      _ < D.radius / 2 + D.radius / 2 := add_lt_add_right hhalf _
      _ = D.radius := by ring
  exact hlt.le

/-- The restricted Duhamel map is a genuine Mathlib contraction. -/
theorem contracting (D : SuperlinearClosedBallData F center) :
    ContractingWith
      (2 * D.Lambda * D.kernelMass * D.radius ^ D.order).toNNReal
      (D.mapsTo.restrict F (Metric.closedBall center D.radius)
        (Metric.closedBall center D.radius)) := by
  refine ⟨Real.toNNReal_lt_one.mpr D.contractionFactor_lt_one, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq,
    MapsTo.val_restrict_apply, MapsTo.val_restrict_apply]
  rw [Real.coe_toNNReal _ D.contractionFactor_nonneg]
  exact D.difference_bound x x.2 y y.2

/-- L3b, the superlinear exit.  A strict smallness inequality makes the
singular Duhamel self-map invariant and contracting, hence produces a unique
mild fixed point in the strong trajectory ball. -/
theorem fixedPoint [CompleteSpace X]
    (D : SuperlinearClosedBallData F center) :
    ∃ y ∈ Metric.closedBall center D.radius,
      Function.IsFixedPt F y ∧
      ∀ z ∈ Metric.closedBall center D.radius,
        Function.IsFixedPt F z → z = y := by
  let B : Set X := Metric.closedBall center D.radius
  have hBc : IsComplete B := Metric.isClosed_closedBall.isComplete
  have hcenter : center ∈ B := by
    exact Metric.mem_closedBall_self D.radius_pos.le
  have hedist : edist center (F center) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y, hyB, hyfix, _hyconv, _hyrate⟩ :=
    D.contracting.exists_fixedPoint' hBc D.mapsTo hcenter hedist
  refine ⟨y, hyB, hyfix, ?_⟩
  intro z hzB hzfix
  let ys : B := ⟨y, hyB⟩
  let zs : B := ⟨z, hzB⟩
  have hysfix : Function.IsFixedPt
      (D.mapsTo.restrict F B B) ys := by
    apply Subtype.ext
    exact hyfix
  have hzsfix : Function.IsFixedPt
      (D.mapsTo.restrict F B B) zs := by
    apply Subtype.ext
    exact hzfix
  have hsub : zs = ys := D.contracting.fixedPoint_unique' hzsfix hysfix
  exact congrArg Subtype.val hsub

end SuperlinearClosedBallData

#print axioms bochner_mild_norm_le
#print axioms bochner_mild_affine_bound
#print axioms SuperlinearClosedBallData.mapsTo
#print axioms SuperlinearClosedBallData.contracting
#print axioms SuperlinearClosedBallData.fixedPoint

end

end ShenWork.PDE
