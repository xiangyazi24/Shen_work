import ShenWork.Paper1.WholeLineWeightedRegularityActualL2History
import ShenWork.Paper1.WholeLineWeightedRegularityH0Fatou
import ShenWork.Paper1.Theorem12TentWeightFiniteness

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

/-!
# Canonical cap and exact-weight H0 closure

This file combines the concrete fixed-cap Picard induction with the existing
Fatou passage to the canonical BUC fixed point.  A final monotone cap
exhaustion produces the exact exponential H0 history.  No weighted spatial
derivative and no time continuity in weighted `L²` is used.
-/

/-- The concrete closed-ball Picard estimate passes to the canonical BUC
fixed point at every slice of the restart window. -/
theorem exists_capWeighted_coMoving_mildFixedPoint_differenceL2_le_of_closed_ball
    (p : CMParams) {M T eta R c B₀ B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (hB₀B : B₀ ≤ B)
    (hball : 2 * capMildGrowthBound eta c T * B₀ +
      (capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (z : Set.Icc (0 : ℝ) T) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ∧
      ‖Z‖ ≤ B := by
  have hpicard : ∀ n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ∧
      ‖Z‖ ≤ B := fun n =>
    exists_capWeighted_coMoving_bucMildPicardFrom_differenceL2_le
      p hM hT heta heta_one hB₀ hB hB₀B hball u₀₂ u₀₁ W hfixed
        hdata_meas hdata_cap hdata_energy n z
  have hpicard_energy : ∀ n : ℕ,
      Integrable (fun x : ℝ =>
        (capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ^ 2) ≤ B ^ 2 := by
    intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hpicard n
    have hraw := capEnergy_of_wholeLineRealL2_rep hB Z hZrep hZnorm
    constructor
    · refine hraw.1.congr (ae_of_all _ ?_)
      intro x
      exact (capWeightSqrt_mul_sq_eq eta R x
        ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
          (x + c * z.1) - (W z).1 (x + c * z.1))).symm
    · calc
        (∫ x : ℝ,
          (capWeightSqrt eta R x *
            ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                (x + c * z.1) -
              (W z).1 (x + c * z.1))) ^ 2) =
            ∫ x : ℝ, capWeight eta R x *
              |(wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                  (x + c * z.1) -
                (W z).1 (x + c * z.1)| ^ 2 := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x =>
            capWeightSqrt_mul_sq_eq eta R x
              ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                (x + c * z.1) - (W z).1 (x + c * z.1)))
        _ ≤ B ^ 2 := hraw.2
  apply exists_capWeighted_mildFixedPoint_differenceL2_of_picard_uniform
    p hM hT heta hB u₀₂ hsmall W z
  · intro n
    simpa only [wholeLineCauchyBUCMildPicardFrom] using
      (hpicard_energy n).1
  · intro n
    simpa only [wholeLineCauchyBUCMildPicardFrom] using
      (hpicard_energy n).2

/-- Exact exponential H0 propagation on a canonical restart window.  The
initial exact-weight energy supplies every finite logistic cap, while the
closed-ball constant is cap-independent; monotone cap exhaustion therefore
recovers the full exponential weight at the fixed-point slice. -/
theorem coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_of_closed_ball
    (p : CMParams) {M T eta c B₀ B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 < eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (hB₀B : B₀ ≤ B)
    (hball : 2 * capMildGrowthBound eta c T * B₀ +
      (capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (z : Set.Icc (0 : ℝ) T) :
    Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1)| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1)| ^ 2) ≤ B ^ 2 := by
  let w : ℝ → ℝ := fun x =>
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
        (x + c * z.1) -
      (W z).1 (x + c * z.1)
  have hw : Continuous w := by
    dsimp only [w]
    exact ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1.continuous.comp
      (continuous_id.add continuous_const)).sub
        ((W z).1.continuous.comp (continuous_id.add continuous_const))
  have hdata_cont : Continuous (fun y : ℝ => u₀₂.1 y - u₀₁.1 y) :=
    u₀₂.1.continuous.sub u₀₁.1.continuous
  have hcap_rep : ∀ n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (n : ℝ) x * w x) ∧ ‖Z‖ ≤ B := by
    intro n
    have hdata_cap : Integrable (fun y : ℝ =>
        capWeight eta (n : ℝ) y * |u₀₂.1 y - u₀₁.1 y| ^ 2) :=
      capWeight_mul_sq_integrable_of_full hdata_cont hdata_full
    have hdata_cap_energy :
        (∫ y : ℝ, capWeight eta (n : ℝ) y *
          |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2 := by
      calc
        (∫ y : ℝ, capWeight eta (n : ℝ) y *
            |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤
            ∫ y : ℝ, Real.exp (2 * eta * y) *
              |u₀₂.1 y - u₀₁.1 y| ^ 2 := by
          apply integral_mono hdata_cap hdata_full
          intro y
          exact mul_le_mul_of_nonneg_right
            (capWeight_le_full eta (n : ℝ) y) (sq_nonneg _)
        _ ≤ B₀ ^ 2 := hdata_energy
    simpa only [w] using
      exists_capWeighted_coMoving_mildFixedPoint_differenceL2_le_of_closed_ball
        p hM hT heta.le heta_one hB₀ hB hB₀B hball u₀₂ u₀₁ W hfixed
          hsmall hdata_cont.measurable hdata_cap hdata_cap_energy z
  have hcap_int : ∀ n : ℕ,
      Integrable (fun x : ℝ => capWeight eta (n : ℝ) x * |w x| ^ 2) := by
    intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hcap_rep n
    exact (capEnergy_of_wholeLineRealL2_rep hB Z hZrep hZnorm).1
  have hcap_bound : ∀ n : ℕ,
      (∫ x : ℝ, capWeight eta (n : ℝ) x * |w x| ^ 2) ≤ B ^ 2 := by
    intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hcap_rep n
    exact (capEnergy_of_wholeLineRealL2_rep hB Z hZrep hZnorm).2
  have hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2) :=
    fullWeightedL2_integrable_of_uniform_cap
      (C := B ^ 2) heta hw hcap_int hcap_bound
  change Integrable (fun x : ℝ => Real.exp (2 * eta * x) * |w x| ^ 2) ∧
    (∫ x : ℝ, Real.exp (2 * eta * x) * |w x| ^ 2) ≤ B ^ 2
  refine ⟨hfull, ?_⟩
  exact le_of_tendsto (tentEnergy_mono_limit heta hw hfull)
    (Eventually.of_forall hcap_bound)

/-- Integrability-only projection of the quantitative exact-weight restart
propagator. -/
theorem coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_of_closed_ball
    (p : CMParams) {M T eta c B₀ B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 < eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (hB₀B : B₀ ≤ B)
    (hball : 2 * capMildGrowthBound eta c T * B₀ +
      (capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (z : Set.Icc (0 : ℝ) T) :
    Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
          (x + c * z.1) -
        (W z).1 (x + c * z.1)| ^ 2) :=
  (coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_of_closed_ball
    p hM hT heta heta_one hB₀ hB hB₀B hball u₀₂ u₀₁ W hfixed hsmall
      hdata_full hdata_energy z).1

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_mildFixedPoint_differenceL2_le_of_closed_ball
#print axioms
  ShenWork.Paper1.coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_of_closed_ball
#print axioms
  ShenWork.Paper1.coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_of_closed_ball
