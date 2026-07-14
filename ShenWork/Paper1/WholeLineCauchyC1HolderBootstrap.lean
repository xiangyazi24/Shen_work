import ShenWork.Paper1.WholeLineCauchyFluxHolderBootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Holder regularity of the positive-time spatial derivative

The first spatial derivative contains a Hessian Duhamel history.  To control
its spatial Holder modulus, interpolate the cancellative Hessian sup bound
against the third-kernel Lipschitz bound.  The resulting time exponent is
integrable after choosing the output exponent strictly below
`theta / (1 + theta)`.
-/

lemma one_div_mul_sqrt_eq_rpow_neg_three_half
    {t : ℝ} (ht : 0 < t) :
    1 / (t * Real.sqrt t) = t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hst : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  have hmul : t * t ^ (1 / 2 : ℝ) = t ^ (3 / 2 : ℝ) := by
    calc
      t * t ^ (1 / 2 : ℝ) = t ^ (1 : ℝ) * t ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + 1 / 2) :=
        (Real.rpow_add ht (1 : ℝ) (1 / 2 : ℝ)).symm
      _ = t ^ (3 / 2 : ℝ) := by
        congr 1
        ring
  rw [hmul]
  rw [one_div]

/-- The whole-line modified heat Hessian is globally Lipschitz at positive
lag, with the third-kernel `t^(-3/2)` scale. -/
theorem wholeLineCauchyHeatHessOp_lipschitz
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x y : ℝ) :
    |wholeLineCauchyHeatHessOp t f x - wholeLineCauchyHeatHessOp t f y| ≤
      (heatThirdTailConstant * t ^ (-(3 / 2 : ℝ)) * M) * |x - y| := by
  let g : ℝ → ℝ := fun z => wholeLineCauchyHeatHessOp t f z
  let C : ℝ := heatThirdTailConstant * t ^ (-(3 / 2 : ℝ)) * M
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt g (deriv g z) Set.univ z := by
    intro z _hz
    exact (wholeLineCauchyHeatHessOp_hasDerivAt ht hf_meas hf
      (x := z)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv g z‖ ≤ C := by
    intro z _hz
    have hz := wholeLineCauchyHeatHessOp_hasDerivAt ht hf_meas hf (x := z)
    rw [Real.norm_eq_abs, hz.deriv]
    have hthird := wholeLineCauchyHeatThirdOp_abs_le ht hM hf_meas hf (x := z)
    calc
      |wholeLineCauchyHeatThirdOp t f z| ≤
          (heatThirdTailConstant / (t * Real.sqrt t)) * M := hthird
      _ = C := by
        rw [show heatThirdTailConstant / (t * Real.sqrt t) =
            heatThirdTailConstant * (1 / (t * Real.sqrt t)) by ring,
          one_div_mul_sqrt_eq_rpow_neg_three_half ht]
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (𝕜 := ℝ) (G := ℝ) (f := g) (s := Set.univ)
    hderiv hbound convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [g, C, Real.norm_eq_abs, abs_sub_comm] using hmv

/-- Interpolating the cancellative Hessian sup estimate with the
third-kernel Lipschitz estimate gives a `C^eta` Hessian bound. -/
theorem wholeLineCauchyHeatHessOp_Ctheta_to_Ceta
    {f : ℝ → ℝ} {t M H theta eta : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hf_holder : ∀ a b, |f a - f b| ≤ H * |a - b| ^ theta)
    (x y : ℝ) :
    |wholeLineCauchyHeatHessOp t f x -
        wholeLineCauchyHeatHessOp t f y| ≤
      ((2 * ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * H) ^
          (1 - eta) *
        (heatThirdTailConstant * M) ^ eta) *
        t ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ) *
        |x - y| ^ eta := by
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let C3 : ℝ := heatThirdTailConstant
  let aexp : ℝ := -1 + theta / 2
  let A : ℝ := (W * H) * t ^ aexp
  let B : ℝ := (C3 * M) * t ^ (-(3 / 2 : ℝ))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hxA : |wholeLineCauchyHeatHessOp t f x| ≤ A := by
    have h := wholeLineCauchyHeatHessOp_Ctheta_abs_le
      ht htheta0 htheta1 hH hf_meas hf hf_holder (x := x)
    simpa [A, W, aexp, mul_assoc, mul_left_comm, mul_comm] using h
  have hyA : |wholeLineCauchyHeatHessOp t f y| ≤ A := by
    have h := wholeLineCauchyHeatHessOp_Ctheta_abs_le
      ht htheta0 htheta1 hH hf_meas hf hf_holder (x := y)
    simpa [A, W, aexp, mul_assoc, mul_left_comm, mul_comm] using h
  have hval : |wholeLineCauchyHeatHessOp t f x -
      wholeLineCauchyHeatHessOp t f y| ≤ 2 * A := by
    calc
      |wholeLineCauchyHeatHessOp t f x - wholeLineCauchyHeatHessOp t f y| ≤
          |wholeLineCauchyHeatHessOp t f x| +
            |wholeLineCauchyHeatHessOp t f y| := abs_sub _ _
      _ ≤ A + A := add_le_add hxA hyA
      _ = 2 * A := by ring
  have hlip : |wholeLineCauchyHeatHessOp t f x -
      wholeLineCauchyHeatHessOp t f y| ≤ B * |x - y| := by
    simpa [B, C3, mul_assoc, mul_left_comm, mul_comm] using
      wholeLineCauchyHeatHessOp_lipschitz ht hM hf_meas hf x y
  let a : ℝ := 2 * A
  let b : ℝ := B * |x - y|
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hchain :
      |wholeLineCauchyHeatHessOp t f x -
          wholeLineCauchyHeatHessOp t f y| ≤
        a ^ (1 - eta) * b ^ eta :=
    (le_min hval hlip).trans
      (min_le_rpow_interp ha hb heta0.le heta1.le)
  have hatime :
      (t ^ aexp) ^ (1 - eta) = t ^ (aexp * (1 - eta)) := by
    rw [← Real.rpow_mul ht.le]
  have hbtime :
      (t ^ (-(3 / 2 : ℝ))) ^ eta = t ^ (-(3 / 2 : ℝ) * eta) := by
    rw [← Real.rpow_mul ht.le]
  have hapow :
      a ^ (1 - eta) =
        (2 * W * H) ^ (1 - eta) * t ^ (aexp * (1 - eta)) := by
    rw [show a = (2 * W * H) * t ^ aexp by
      dsimp [a, A]
      ring]
    rw [Real.mul_rpow (by positivity)
      (Real.rpow_nonneg ht.le _), hatime]
  have hbpow :
      b ^ eta = (C3 * M) ^ eta * t ^ (-(3 / 2 : ℝ) * eta) *
        |x - y| ^ eta := by
    rw [show b = ((C3 * M) * t ^ (-(3 / 2 : ℝ))) * |x - y| by rfl]
    rw [Real.mul_rpow hB (abs_nonneg _),
      Real.mul_rpow (mul_nonneg hC3 hM)
        (Real.rpow_nonneg ht.le _), hbtime]
  have htime :
      t ^ (aexp * (1 - eta)) * t ^ (-(3 / 2 : ℝ) * eta) =
        t ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ) := by
    rw [← Real.rpow_add ht]
    dsimp [aexp]
    congr 1
    ring
  rw [hapow, hbpow] at hchain
  rw [show
      (2 * W * H) ^ (1 - eta) * t ^ (aexp * (1 - eta)) *
          ((C3 * M) ^ eta * t ^ (-(3 / 2 : ℝ) * eta) *
            |x - y| ^ eta) =
        ((2 * W * H) ^ (1 - eta) * (C3 * M) ^ eta) *
          (t ^ (aexp * (1 - eta)) * t ^ (-(3 / 2 : ℝ) * eta)) *
          |x - y| ^ eta by ring,
    htime] at hchain
  simpa [W, C3] using hchain

/-- The new Hessian Holder time exponent is integrable precisely under the
strict interpolation restriction used by the next Duhamel rung. -/
theorem intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta
    {t theta eta : ℝ} (hrel : eta * (1 + theta) < theta) :
    IntervalIntegrable
      (fun s : ℝ =>
        (t - s) ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ))
      volume 0 t := by
  have hexp : (-1 : ℝ) <
      -1 + (theta - eta * (1 + theta)) / 2 := by linarith
  have hbase := intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := t) hexp
  have hshift := (hbase.comp_sub_left t).symm
  simpa using hshift

section WholeLineCauchyC1HolderBootstrapAxiomAudit

#print axioms wholeLineCauchyHeatHessOp_lipschitz
#print axioms wholeLineCauchyHeatHessOp_Ctheta_to_Ceta
#print axioms intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta

end WholeLineCauchyC1HolderBootstrapAxiomAudit

end ShenWork.Paper1
