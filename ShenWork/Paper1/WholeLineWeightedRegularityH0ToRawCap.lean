import ShenWork.Paper1.WholeLineWeightedRegularityDampedH0
import ShenWork.Paper1.WholeLineWeightedRegularityCrudeRawDQ
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIdentity

open Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact-weight H0 bounds as fixed-cap raw-DQ inputs

The damped H0 propagation theorem gives a bound in the full exponential
weight.  This file turns that bound into the four fixed-cap inputs consumed by
the raw-DQ history estimates.  The conversion is independent of the cap
radius and does not use any weighted spatial derivative.
-/

/-- Full exponential H0 control dominates the value energy at every fixed
logistic cap, with the same bound. -/
theorem capWeighted_value_integrable_and_energy_le_of_fullWeightedL2
    {eta R F : ℝ} {w : ℝ → ℝ} (hw : Continuous w)
    (hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2))
    (hfull_energy : (∫ x : ℝ,
      Real.exp (2 * eta * x) * |w x| ^ 2) ≤ F ^ 2) :
    Integrable (fun x : ℝ => capWeight eta R x * |w x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) ≤ F ^ 2 := by
  have hcap : Integrable (fun x : ℝ =>
      capWeight eta R x * |w x| ^ 2) :=
    capWeight_mul_sq_integrable_of_full hw hfull
  refine ⟨hcap, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) ≤
        ∫ x : ℝ, Real.exp (2 * eta * x) * |w x| ^ 2 := by
      apply integral_mono hcap hfull
      intro x
      exact mul_le_mul_of_nonneg_right
        (capWeight_le_full eta R x) (sq_nonneg _)
    _ ≤ F ^ 2 := hfull_energy

/-- Full exponential H0 control produces the crude fixed-step raw-DQ cap
bound.  The displayed constant depends on the step but not on the cap
radius. -/
theorem capWeighted_rawSpatialDifferenceQuotient_integrable_and_energy_le_of_fullWeightedL2
    {eta R h F : ℝ} (heta : 0 ≤ eta) (hh : h ≠ 0) (hF : 0 ≤ F)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2))
    (hfull_energy : (∫ x : ℝ,
      Real.exp (2 * eta * x) * |w x| ^ 2) ≤ F ^ 2) :
    Integrable (fun x : ℝ => capWeight eta R x *
      |rawSpatialDifferenceQuotient eta h w x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h w x| ^ 2) ≤
      (eta * F +
        Real.sqrt
          (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F) ^ 2 := by
  have hvalue :=
    capWeighted_value_integrable_and_energy_le_of_fullWeightedL2
      (R := R) hw hfull hfull_energy
  obtain ⟨Z, hZrep, hZnorm⟩ :=
    exists_capWeighted_rawSpatialDifferenceQuotientL2_of_value
      heta hh hF hw hvalue.1 hvalue.2
  have hK : 0 ≤ eta * F +
      Real.sqrt
        (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F :=
    add_nonneg (mul_nonneg heta hF)
      (mul_nonneg (Real.sqrt_nonneg _) hF)
  have hcap := capEnergy_of_wholeLineRealL2_rep hK Z
    (by simpa only [rawSpatialDifferenceQuotient] using hZrep) hZnorm
  exact hcap

/-- Bundled fixed-cap value/raw-DQ inputs obtained from one exact-weight H0
bound. -/
theorem capWeighted_value_rawDQ_inputs_of_fullWeightedL2
    {eta R h F : ℝ} (heta : 0 ≤ eta) (hh : h ≠ 0) (hF : 0 ≤ F)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2))
    (hfull_energy : (∫ x : ℝ,
      Real.exp (2 * eta * x) * |w x| ^ 2) ≤ F ^ 2) :
    (Integrable (fun x : ℝ => capWeight eta R x * |w x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) ≤ F ^ 2) ∧
    (Integrable (fun x : ℝ => capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h w x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h w x| ^ 2) ≤
      (eta * F +
        Real.sqrt
          (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F) ^ 2) := by
  exact ⟨
    capWeighted_value_integrable_and_energy_le_of_fullWeightedL2
      (R := R) hw hfull hfull_energy,
    capWeighted_rawSpatialDifferenceQuotient_integrable_and_energy_le_of_fullWeightedL2
      (R := R) heta hh hF hw hfull hfull_energy⟩

/-- Uniform-in-time exact-weight H0 control supplies the four hypotheses used
by the one-step raw-DQ histories, simultaneously for every cap radius. -/
theorem capWeighted_value_rawDQ_window_inputs_of_fullWeightedL2
    {eta h F H : ℝ} (heta : 0 ≤ eta) (hh : h ≠ 0) (hF : 0 ≤ F)
    {w : ℝ → ℝ → ℝ}
    (hw : ∀ s ∈ Set.Icc (0 : ℝ) H, Continuous (w s))
    (hfull : ∀ s ∈ Set.Icc (0 : ℝ) H,
      Integrable (fun x : ℝ =>
        Real.exp (2 * eta * x) * |w s x| ^ 2))
    (hfull_energy : ∀ s ∈ Set.Icc (0 : ℝ) H,
      (∫ x : ℝ, Real.exp (2 * eta * x) * |w s x| ^ 2) ≤ F ^ 2) :
    ∀ R : ℝ,
      (∀ s ∈ Set.Icc (0 : ℝ) H,
        Integrable (fun x : ℝ => capWeight eta R x * |w s x| ^ 2)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) H,
        Integrable (fun x : ℝ => capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (w s) x| ^ 2)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) H,
        (∫ x : ℝ, capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (w s) x| ^ 2) ≤
        (eta * F +
          Real.sqrt
            (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F) ^ 2) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) H,
        (∫ x : ℝ, capWeight eta R x * |w s x| ^ 2) ≤ F ^ 2) := by
  intro R
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta hh hF (hw s hs) (hfull s hs)
        (hfull_energy s hs)).1.1
  · intro s hs
    exact (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta hh hF (hw s hs) (hfull s hs)
        (hfull_energy s hs)).2.1
  · intro s hs
    exact (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta hh hF (hw s hs) (hfull s hs)
        (hfull_energy s hs)).2.2
  · intro s hs
    exact (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta hh hF (hw s hs) (hfull s hs)
        (hfull_energy s hs)).1.2

/-- Canonical co-moving specialization of the preceding window producer.
Its output order is exactly `hvalue`, `hraw`, `hraw_energy`,
`hvalue_energy` from the one-step raw-DQ history interface. -/
theorem capWeighted_coMoving_value_rawDQ_window_inputs_of_fullWeightedL2
    {T eta h c F : ℝ} (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (hh : h ≠ 0) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hfull : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2))
    (hfull_energy : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2) :
    ∀ R : ℝ,
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : ℝ => capWeight eta R x *
          |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x| ^ 2)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : ℝ => capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫ x : ℝ, capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) ≤
        (eta * F +
          Real.sqrt
            (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F) ^ 2) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫ x : ℝ, capWeight eta R x *
          |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x| ^ 2) ≤ F ^ 2) := by
  let w : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W.1 x
  have hw : ∀ s ∈ Set.Icc (0 : ℝ) T, Continuous (w s) := by
    intro s _hs
    exact ((wholeLineBUCTrajectoryExtend hT Traj s).1.continuous.comp
      (continuous_id.add continuous_const)).sub W.1.continuous
  simpa only [w] using
    capWeighted_value_rawDQ_window_inputs_of_fullWeightedL2
      heta hh hF hw hfull hfull_energy

/-- The fully discharged damped H0 theorem directly supplies uniform
fixed-cap value/raw-DQ inputs for the canonical mild fixed point relative to
any reference fixed-point trajectory.  A translated traveling-wave
trajectory is the intended reference instance. -/
theorem exists_uniform_capWeighted_mildFixedPoint_difference_value_rawDQ_inputs_finiteHorizon
    (p : CMParams) {M T eta c h B₀ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 < eta)
    (heta_one : eta < 1) (hh : h ≠ 0) (hB₀ : 0 ≤ B₀)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2) :
    ∃ F X : ℝ, 0 ≤ F ∧ 0 ≤ X ∧ ∀ R : ℝ,
      (∀ z : Set.Icc (0 : ℝ) T,
        Integrable (fun x : ℝ => capWeight eta R x *
          |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
              (x + c * z.1) - (W z).1 (x + c * z.1)| ^ 2)) ∧
      (∀ z : Set.Icc (0 : ℝ) T,
        Integrable (fun x : ℝ => capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (fun y =>
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
                (y + c * z.1) - (W z).1 (y + c * z.1)) x| ^ 2)) ∧
      (∀ z : Set.Icc (0 : ℝ) T,
        (∫ x : ℝ, capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (fun y =>
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
                (y + c * z.1) - (W z).1 (y + c * z.1)) x| ^ 2) ≤ X ^ 2) ∧
      (∀ z : Set.Icc (0 : ℝ) T,
        (∫ x : ℝ, capWeight eta R x *
          |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
              (x + c * z.1) - (W z).1 (x + c * z.1)| ^ 2) ≤ F ^ 2) := by
  obtain ⟨F, hF, hH0⟩ :=
    exists_bound_coMoving_mildFixedPoint_difference_fullWeightedL2_finiteHorizon
      p hM hT heta heta_one hB₀ u₀₂ u₀₁ W hfixed hsmall
        hdata_full hdata_energy
  let X : ℝ := eta * F +
    Real.sqrt
      (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact add_nonneg (mul_nonneg heta.le hF)
      (mul_nonneg (Real.sqrt_nonneg _) hF)
  refine ⟨F, X, hF, hX, ?_⟩
  intro R
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    let w : ℝ → ℝ := fun x =>
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
          (x + c * z.1) - (W z).1 (x + c * z.1)
    have hw : Continuous w := by
      exact ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1.continuous.comp
        (continuous_id.add continuous_const)).sub
          ((W z).1.continuous.comp (continuous_id.add continuous_const))
    exact (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta.le hh hF hw (hH0 z).1 (hH0 z).2).1.1
  · intro z
    let w : ℝ → ℝ := fun x =>
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
          (x + c * z.1) - (W z).1 (x + c * z.1)
    have hw : Continuous w := by
      exact ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1.continuous.comp
        (continuous_id.add continuous_const)).sub
          ((W z).1.continuous.comp (continuous_id.add continuous_const))
    simpa only [w] using
      (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
        (R := R) heta.le hh hF hw (hH0 z).1 (hH0 z).2).2.1
  · intro z
    let w : ℝ → ℝ := fun x =>
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
          (x + c * z.1) - (W z).1 (x + c * z.1)
    have hw : Continuous w := by
      exact ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1.continuous.comp
        (continuous_id.add continuous_const)).sub
          ((W z).1.continuous.comp (continuous_id.add continuous_const))
    simpa only [w, X] using
      (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
        (R := R) heta.le hh hF hw (hH0 z).1 (hH0 z).2).2.2
  · intro z
    let w : ℝ → ℝ := fun x =>
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
          (x + c * z.1) - (W z).1 (x + c * z.1)
    have hw : Continuous w := by
      exact ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1.continuous.comp
        (continuous_id.add continuous_const)).sub
          ((W z).1.continuous.comp (continuous_id.add continuous_const))
    exact (capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta.le hh hF hw (hH0 z).1 (hH0 z).2).1.2

#print axioms capWeighted_value_integrable_and_energy_le_of_fullWeightedL2
#print axioms
  capWeighted_rawSpatialDifferenceQuotient_integrable_and_energy_le_of_fullWeightedL2
#print axioms capWeighted_value_rawDQ_inputs_of_fullWeightedL2
#print axioms capWeighted_value_rawDQ_window_inputs_of_fullWeightedL2
#print axioms
  capWeighted_coMoving_value_rawDQ_window_inputs_of_fullWeightedL2
#print axioms
  exists_uniform_capWeighted_mildFixedPoint_difference_value_rawDQ_inputs_finiteHorizon

end ShenWork.Paper1
