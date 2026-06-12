import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.IntervalResolverSpectralTimeC2
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.Paper2.IntervalPicardLimitK1C2Coeff

/-!
# K1 C2 coefficient fields from heat smoothing

This module is reserved for the base, non-circular producer of
`SourceC2CoeffFields`.  It imports the K1 C2 field bridge, but no downstream
resolver C2 transport result is used here.
-/

noncomputable section

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalResolverSpectralTimeC2
open ShenWork.Paper2.PicardLimitK1C2Coeff (SourceC2CoeffFields)

namespace ShenWork.Paper2.PicardLimitK1C2Heat

/-- Homogeneous heat-smoothed coefficients with a positive time shift. -/
def shiftedHeatCoeff (ε : ℝ) (a₀ : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(ε + s) * unitIntervalCosineEigenvalue n) * a₀ n

/-- The time derivative of `shiftedHeatCoeff`. -/
def shiftedHeatCoeffAdot (ε : ℝ) (a₀ : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  -(unitIntervalCosineEigenvalue n *
      Real.exp (-(ε + s) * unitIntervalCosineEigenvalue n)) * a₀ n

theorem shiftedHeatCoeff_hasDerivAt
    (ε : ℝ) (a₀ : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => shiftedHeatCoeff ε a₀ r n)
      (shiftedHeatCoeffAdot ε a₀ s n) s := by
  set lam := unitIntervalCosineEigenvalue n
  have harg : HasDerivAt (fun r : ℝ => -(ε + r) * lam) (-lam) s := by
    simpa using ((hasDerivAt_id s).const_add ε).neg.mul_const lam
  simpa [shiftedHeatCoeff, shiftedHeatCoeffAdot, lam, mul_assoc,
    mul_left_comm, mul_comm] using harg.exp.mul_const (a₀ n)

private theorem shiftedHeatCoeff_abs_le
    {ε M : ℝ} {a₀ : ℕ → ℝ} (_hε : 0 < ε)
    (ha₀ : ∀ n, |a₀ n| ≤ M) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    |shiftedHeatCoeff ε a₀ s n| ≤
      Real.exp (-ε * unitIntervalCosineEigenvalue n) * M := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have hexp :
      Real.exp (-(ε + s) * lam) ≤ Real.exp (-ε * lam) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hs hlam]
  rw [shiftedHeatCoeff, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul hexp (ha₀ n) (abs_nonneg _) (Real.exp_nonneg _)

private theorem heat_lambda_exp_shift_le_inv
    {ε s lam : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hlam : 0 ≤ lam) :
    lam * Real.exp (-(ε + s) * lam) ≤ 1 / ε := by
  have hexp :
      Real.exp (-(ε + s) * lam) ≤ Real.exp (-ε * lam) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hs hlam]
  have hker₀ :
      lam * Real.exp (-(ε + s) * lam) ≤
        lam * Real.exp (-ε * lam) :=
    mul_le_mul_of_nonneg_left hexp hlam
  have hraw : (ε * lam) * Real.exp (-(ε * lam)) ≤ 1 :=
    real_mul_exp_neg_le_one (mul_nonneg hε.le hlam)
  have hscale :
      (1 / ε) * ((ε * lam) * Real.exp (-(ε * lam))) ≤
        (1 / ε) * 1 :=
    mul_le_mul_of_nonneg_left hraw (by positivity)
  have hker₁ : lam * Real.exp (-ε * lam) ≤ 1 / ε := by
    calc lam * Real.exp (-ε * lam)
        = (1 / ε) * ((ε * lam) * Real.exp (-(ε * lam))) := by
            field_simp [ne_of_gt hε]
      _ ≤ (1 / ε) * 1 := hscale
      _ = 1 / ε := by ring
  exact hker₀.trans hker₁

private theorem shiftedHeatCoeffAdot_abs_le
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε)
    (ha₀ : ∀ n, |a₀ n| ≤ M) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    |shiftedHeatCoeffAdot ε a₀ s n| ≤ M / ε := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hker := heat_lambda_exp_shift_le_inv
    (hε := hε) (hs := hs) (hlam := hlam)
  rw [shiftedHeatCoeffAdot, abs_mul, abs_neg, abs_mul,
    abs_of_nonneg hlam, abs_of_nonneg (Real.exp_nonneg _)]
  calc (lam * Real.exp (-(ε + s) * lam)) * |a₀ n|
      ≤ (lam * Real.exp (-(ε + s) * lam)) * M :=
        mul_le_mul_of_nonneg_left (ha₀ n)
          (mul_nonneg hlam (Real.exp_nonneg _))
    _ ≤ (1 / ε) * M := mul_le_mul_of_nonneg_right hker hM
    _ = M / ε := by ring

/-- The shifted homogeneous heat coefficients form a `DuhamelSourceTimeC1`
package.  The derivative bound is the elementary parabolic multiplier bound
`λe^{-ελ} ≤ ε^{-1}`. -/
def shiftedHeatCoeff_timeC1
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (_hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    DuhamelSourceTimeC1 (shiftedHeatCoeff ε a₀) where
  adot := shiftedHeatCoeffAdot ε a₀
  hderiv := shiftedHeatCoeff_hasDerivAt ε a₀
  hadotcont := by
    intro n
    dsimp [shiftedHeatCoeffAdot]
    fun_prop
  envelope := fun n =>
    Real.exp (-ε * unitIntervalCosineEigenvalue n) * M
  henv_summable :=
    (unitIntervalCosineHeatTrace_single_exp_summable hε).mul_right M
  henv_bound := fun s hs n => shiftedHeatCoeff_abs_le hε ha₀ hs n
  derivBound := M / ε
  hderivBound := fun s hs n =>
    shiftedHeatCoeffAdot_abs_le hε ha₀ hs n

private theorem shiftedHeatCoeffAdot_heat_abs_le
    {ε M : ℝ} {a₀ : ℕ → ℝ} (ha₀ : ∀ n, |a₀ n| ≤ M)
    {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    |shiftedHeatCoeffAdot ε a₀ s n| ≤
      unitIntervalCosineEigenvalue n *
        Real.exp (-ε * unitIntervalCosineEigenvalue n) * M := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have hexp :
      Real.exp (-(ε + s) * lam) ≤ Real.exp (-ε * lam) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hs hlam]
  rw [shiftedHeatCoeffAdot, abs_mul, abs_neg, abs_mul,
    abs_of_nonneg hlam, abs_of_nonneg (Real.exp_nonneg _)]
  calc (lam * Real.exp (-(ε + s) * lam)) * |a₀ n|
      ≤ (lam * Real.exp (-ε * lam)) * M := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hexp hlam) (ha₀ n)
          (abs_nonneg _) (mul_nonneg hlam (Real.exp_nonneg _))
    _ = lam * Real.exp (-ε * lam) * M := by ring

/-- Positive-time homogeneous heat smoothing gives all source-side C2
coefficient envelopes. -/
def shiftedHeatCoeff_sourceC2CoeffFields
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    SourceC2CoeffFields (shiftedHeatCoeff_timeC1 hε hM ha₀) where
  sourceEigenEnvelope := fun n =>
    (unitIntervalCosineEigenvalue n *
      Real.exp (-ε * unitIntervalCosineEigenvalue n)) * M
  sourceEigen_nonneg := by
    intro n
    exact mul_nonneg
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (Real.exp_nonneg _))
      hM
  sourceEigen_summable :=
    (unitIntervalCosineEigenvalue_mul_exp_summable hε).mul_right M
  sourceEigen_bound := by
    intro s hs n
    set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    have h := shiftedHeatCoeff_abs_le (a₀ := a₀) hε ha₀ hs n
    calc unitIntervalCosineEigenvalue n * |shiftedHeatCoeff ε a₀ s n|
        ≤ unitIntervalCosineEigenvalue n *
            (Real.exp (-ε * unitIntervalCosineEigenvalue n) * M) :=
          mul_le_mul_of_nonneg_left h hlam
      _ = (unitIntervalCosineEigenvalue n *
            Real.exp (-ε * unitIntervalCosineEigenvalue n)) * M := by ring
  sourceEigenSqEnvelope := fun n =>
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        Real.exp (-ε * unitIntervalCosineEigenvalue n))) * M
  sourceEigenSq_nonneg := by
    intro n
    exact mul_nonneg
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (Real.exp_nonneg _)))
      hM
  sourceEigenSq_summable :=
    (eigenvalue_sq_mul_exp_summable hε).mul_right M
  sourceEigenSq_bound := by
    intro s hs n
    set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    have h := shiftedHeatCoeff_abs_le (a₀ := a₀) hε ha₀ hs n
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |shiftedHeatCoeff ε a₀ s n|)
        ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (Real.exp (-ε * unitIntervalCosineEigenvalue n) * M)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h hlam) hlam
      _ = (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-ε * unitIntervalCosineEigenvalue n))) * M := by
          ring
  adotEigenEnvelope := fun n =>
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        Real.exp (-ε * unitIntervalCosineEigenvalue n))) * M
  adotEigen_nonneg := by
    intro n
    exact mul_nonneg
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (Real.exp_nonneg _)))
      hM
  adotEigen_summable :=
    (eigenvalue_sq_mul_exp_summable hε).mul_right M
  adotEigen_bound := by
    intro s hs n
    set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    change lam *
        |shiftedHeatCoeffAdot ε a₀ s n| ≤ _
    have h := shiftedHeatCoeffAdot_heat_abs_le
      (ε := ε) (M := M) (a₀ := a₀) ha₀ hs n
    have h' :
        |shiftedHeatCoeffAdot ε a₀ s n| ≤
          lam * Real.exp (-ε * lam) * M := by
      simpa [lam] using h
    calc lam *
          |shiftedHeatCoeffAdot ε a₀ s n|
        ≤ lam * (lam * Real.exp (-ε * lam) * M) := by
          exact mul_le_mul_of_nonneg_left h' hlam
      _ = (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-ε * unitIntervalCosineEigenvalue n))) * M := by
          simp [lam]
          ring
  adotEigenSqEnvelope := fun n =>
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          Real.exp (-ε * unitIntervalCosineEigenvalue n)))) * M
  adotEigenSq_nonneg := by
    intro n
    exact mul_nonneg
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (mul_nonneg
            (by unfold unitIntervalCosineEigenvalue; positivity)
            (Real.exp_nonneg _))))
      hM
  adotEigenSq_summable :=
    (eigenvalue_cube_mul_exp_summable hε).mul_right M
  adotEigenSq_bound := by
    intro s hs n
    set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    change lam *
        (lam *
          |shiftedHeatCoeffAdot ε a₀ s n|) ≤ _
    have h := shiftedHeatCoeffAdot_heat_abs_le
      (ε := ε) (M := M) (a₀ := a₀) ha₀ hs n
    have h' :
        |shiftedHeatCoeffAdot ε a₀ s n| ≤
          lam * Real.exp (-ε * lam) * M := by
      simpa [lam] using h
    calc lam *
          (lam *
            |shiftedHeatCoeffAdot ε a₀ s n|)
        ≤ lam * (lam * (lam * Real.exp (-ε * lam) * M)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h' hlam) hlam
      _ = (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                Real.exp (-ε * unitIntervalCosineEigenvalue n)))) * M := by
          simp [lam]
          ring

/-- The base `DuhamelSourceTimeC2Coeff` package obtained from the source fields. -/
def shiftedHeatCoeff_c2Coeff
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff
      (shiftedHeatCoeff ε a₀) :=
  (shiftedHeatCoeff_sourceC2CoeffFields hε hM ha₀).toC2Coeff

end ShenWork.Paper2.PicardLimitK1C2Heat
