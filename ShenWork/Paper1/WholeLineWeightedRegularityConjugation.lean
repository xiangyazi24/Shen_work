import ShenWork.Paper1.Theorem12WeightedFiniteness

open MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact exponential conjugation of the moving heat operators

These identities are the algebraic bridge between the canonical whole-line
mild formula and the weighted `L²` operators in
`Theorem12WeightedFiniteness`.  The damping `exp (-t)` from the modified heat
semigroup is kept explicitly.  For a divergence source the conjugated
gradient contains both the gradient term and the required zero-order
`-eta` correction.
-/

/-- The moving-frame version of the canonical Cauchy heat operator. -/
def paper5MovingFrameHeatOp (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineCauchyHeatOp t f (x + c * t)

/-- The moving-frame version of the canonical Cauchy heat-gradient operator. -/
def paper5MovingFrameHeatGradOp (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineCauchyHeatGradOp t f (x + c * t)

/-- Exponentially conjugating the moving modified heat semigroup gives the
weighted moving heat operator, including the semigroup damping factor. -/
theorem exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
    {eta c t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    Real.exp (eta * x) *
        paper5MovingFrameHeatOp c t f x =
      Real.exp (-t) *
        weightedMovingHeatEta eta c t
          (fun y => Real.exp (eta * y) * f y) x := by
  unfold paper5MovingFrameHeatOp wholeLineCauchyHeatOp
    modifiedSemigroup heatSemigroup
    weightedMovingHeatEta
  rw [show Real.exp (eta * x) *
      (Real.exp (-t) *
        ∫ y : ℝ, heatKernel t (x + c * t - y) * f y) =
      Real.exp (-t) *
        (Real.exp (eta * x) *
          ∫ y : ℝ, heatKernel t (x + c * t - y) * f y) by ring]
  congr 1
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have hk := weightedMovingHeat_conjugation_kernel_identity ht eta c x y
  calc
    Real.exp (eta * x) * (heatKernel t (x + c * t - y) * f y) =
        (Real.exp (eta * x) * heatKernel t (x + c * t - y)) * f y := by
          ring
    _ = (weightedMovingHeatGrowth eta c t *
        (weightedMovingHeatMarkovKernel eta c t x y *
          Real.exp (eta * y))) * f y := by rw [hk]
    _ = weightedMovingHeatGrowth eta c t *
        (weightedMovingHeatMarkovKernel eta c t x y *
          (Real.exp (eta * y) * f y)) := by ring

/-- Kernel-level derivative conjugation.  This is the differentiated form of
`weightedMovingHeat_conjugation_kernel_identity`, written without invoking a
two-variable chain rule. -/
theorem weightedMovingHeatGradient_conjugation_kernel_identity
    {t : ℝ} (ht : 0 < t) (eta c x y : ℝ) :
    Real.exp (eta * x) *
        deriv (fun z : ℝ => heatKernel t (z - y)) (x + c * t) =
      weightedMovingHeatGrowth eta c t *
        ((deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * eta) * t - y) * Real.exp (eta * y)) -
          eta *
            (weightedMovingHeatMarkovKernel eta c t x y *
              Real.exp (eta * y))) := by
  have htne : t ≠ 0 := ne_of_gt ht
  rw [deriv_heatKernel_translated_left ht,
    deriv_heatKernel ht]
  have hkernel :=
    weightedMovingHeat_conjugation_kernel_identity ht eta c x y
  rw [show heatKernel t (x + c * t - y) =
      heatKernel t ((x + c * t) - y) by ring] at hkernel
  calc
    Real.exp (eta * x) *
        (-(((x + c * t) - y) / (2 * t)) *
          heatKernel t ((x + c * t) - y)) =
      -(((x + c * t) - y) / (2 * t)) *
        (Real.exp (eta * x) * heatKernel t (x + c * t - y)) := by
          ring
    _ = -(((x + c * t) - y) / (2 * t)) *
        (weightedMovingHeatGrowth eta c t *
          (weightedMovingHeatMarkovKernel eta c t x y *
            Real.exp (eta * y))) := by rw [hkernel]
    _ = weightedMovingHeatGrowth eta c t *
        ((-((x + (c - 2 * eta) * t - y) / (2 * t)) *
              heatKernel t (x + (c - 2 * eta) * t - y) *
              Real.exp (eta * y)) -
          eta *
            (weightedMovingHeatMarkovKernel eta c t x y *
              Real.exp (eta * y))) := by
          have hcoef :
              -(((x + c * t) - y) / (2 * t)) =
                -((x + (c - 2 * eta) * t - y) / (2 * t)) - eta := by
            field_simp [htne]
            ring
          unfold weightedMovingHeatMarkovKernel
          rw [hcoef]
          ring

/-- The kernel-gradient analogue of
`exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta`.  The derivative of the
exponential conjugation contributes the indispensable `-eta` term. -/
theorem exp_mul_movingFrameHeatGradOp_eq_weightedMovingHeatGradientEta_sub
    {eta c t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ)
    (hgrad_int : Integrable (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) *
        (Real.exp (eta * y) * f y)))
    (hheat_int : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c t x y *
        (Real.exp (eta * y) * f y))) :
    Real.exp (eta * x) *
        paper5MovingFrameHeatGradOp c t f x =
      Real.exp (-t) *
        (weightedMovingHeatGradientEta eta c t
            (fun y => Real.exp (eta * y) * f y) x -
          eta * weightedMovingHeatEta eta c t
            (fun y => Real.exp (eta * y) * f y) x) := by
  unfold paper5MovingFrameHeatGradOp wholeLineCauchyHeatGradOp
    weightedMovingHeatGradientEta
    weightedMovingHeatEta
  rw [← integral_const_mul]
  calc
    (∫ y : ℝ, Real.exp (eta * x) *
        (Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) (x + c * t) *
            f y))) =
        ∫ y : ℝ, Real.exp (-t) * weightedMovingHeatGrowth eta c t *
          ((deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) *
                (Real.exp (eta * y) * f y)) -
            eta * (weightedMovingHeatMarkovKernel eta c t x y *
              (Real.exp (eta * y) * f y))) := by
          apply integral_congr_ae
          filter_upwards with y
          have hk :=
            weightedMovingHeatGradient_conjugation_kernel_identity
              ht eta c x y
          calc
            Real.exp (eta * x) *
                (Real.exp (-t) *
                  (deriv (fun z : ℝ => heatKernel t (z - y))
                    (x + c * t) * f y)) =
              Real.exp (-t) *
                ((Real.exp (eta * x) *
                  deriv (fun z : ℝ => heatKernel t (z - y))
                    (x + c * t)) * f y) := by ring
            _ = Real.exp (-t) *
                ((weightedMovingHeatGrowth eta c t *
                  ((deriv (fun z : ℝ => heatKernel t z)
                      (x + (c - 2 * eta) * t - y) * Real.exp (eta * y)) -
                    eta * (weightedMovingHeatMarkovKernel eta c t x y *
                      Real.exp (eta * y)))) * f y) := by rw [hk]
            _ = Real.exp (-t) * weightedMovingHeatGrowth eta c t *
                ((deriv (fun z : ℝ => heatKernel t z)
                    (x + (c - 2 * eta) * t - y) *
                      (Real.exp (eta * y) * f y)) -
                  eta * (weightedMovingHeatMarkovKernel eta c t x y *
                    (Real.exp (eta * y) * f y))) := by ring
    _ = Real.exp (-t) * weightedMovingHeatGrowth eta c t *
        (∫ y : ℝ,
          (deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) *
                (Real.exp (eta * y) * f y)) -
            eta * (weightedMovingHeatMarkovKernel eta c t x y *
              (Real.exp (eta * y) * f y))) := by
          rw [integral_const_mul]
    _ = Real.exp (-t) * weightedMovingHeatGrowth eta c t *
        ((∫ y : ℝ, deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) *
                (Real.exp (eta * y) * f y)) -
          ∫ y : ℝ, eta *
            (weightedMovingHeatMarkovKernel eta c t x y *
              (Real.exp (eta * y) * f y))) := by
          rw [integral_sub hgrad_int (hheat_int.const_mul eta)]
    _ = Real.exp (-t) * weightedMovingHeatGrowth eta c t *
        ((∫ y : ℝ, deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) *
                (Real.exp (eta * y) * f y)) -
          eta * (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y *
            (Real.exp (eta * y) * f y))) := by
          rw [integral_const_mul]
    _ = Real.exp (-t) *
        (weightedMovingHeatGrowth eta c t * (
            ∫ y : ℝ, deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) *
                (Real.exp (eta * y) * f y)) -
          eta * (weightedMovingHeatGrowth eta c t *
            (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y *
              (Real.exp (eta * y) * f y)))) := by ring

section AxiomAudit

#print axioms exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
#print axioms weightedMovingHeatGradient_conjugation_kernel_identity
#print axioms exp_mul_movingFrameHeatGradOp_eq_weightedMovingHeatGradientEta_sub

end AxiomAudit

end ShenWork.Paper1
