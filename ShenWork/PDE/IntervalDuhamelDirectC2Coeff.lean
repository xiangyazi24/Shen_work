import ShenWork.PDE.IntervalDuhamelSourceTimeC2Coeff
import ShenWork.PDE.IntervalResolverSpectralJointC2Closed

/-!
# Direct Duhamel C² coefficient bounds

This file proves the Duhamel-branch C² coefficient bounds by the direct
kernel-mass estimate.  It does not use the time-IBP identity for
`λ * duhamelSpectralCoeff`.
-/

open MeasureTheory
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalResolverSpectralTimeC2
  (DuhamelSourceTimeC2Coeff localRestartCoeffAdot)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

namespace ShenWork
namespace IntervalDuhamelDirectC2Coeff

/-- A reusable direct bound for the heat kernel mass carrying one eigenvalue. -/
theorem heatKernelEigenMass_le_one {τ lam : ℝ}
    (hτ : 0 ≤ τ) (_hlam : 0 ≤ lam) :
    (∫ s in (0 : ℝ)..τ, lam * Real.exp (-(τ - s) * lam)) ≤ 1 := by
  have hcont :
      ContinuousOn (fun s : ℝ => Real.exp (-(τ - s) * lam))
        (Set.Icc (0 : ℝ) τ) := by
    exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) τ,
      HasDerivAt (fun u : ℝ => Real.exp (-(τ - u) * lam))
        (lam * Real.exp (-(τ - s) * lam)) s := by
    intro s _hs
    have harg : HasDerivAt (fun u : ℝ => -(τ - u) * lam) lam s := by
      convert ((hasDerivAt_const s τ).sub (hasDerivAt_id s)).neg.mul_const lam
        using 1
      ring
    simpa [mul_comm] using harg.exp
  have hint : IntervalIntegrable
      (fun s : ℝ => lam * Real.exp (-(τ - s) * lam))
      volume 0 τ := by
    exact (continuous_const.mul
      (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable 0 τ
  have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := τ)
    (f := fun s : ℝ => Real.exp (-(τ - s) * lam))
    (f' := fun s : ℝ => lam * Real.exp (-(τ - s) * lam))
    hτ hcont hderiv hint
  rw [hEq]
  calc Real.exp (-(τ - τ) * lam) - Real.exp (-(τ - 0) * lam)
      = 1 - Real.exp (-τ * lam) := by simp
    _ ≤ 1 := by
      linarith [Real.exp_nonneg (-τ * lam)]

/-- Direct Duhamel branch bound:
`λₙ² |bₙ(τ)| ≤ sourceEigenEnvelope n`.

This is the bound `λₙ² |∫₀ᵗ e^{-(t-s)λₙ} fₙ(s) ds|
≤ λₙ sup |fₙ|`, discharged with the committed λ¹ source envelope and
`∫₀ᵗ λₙ e^{-(t-s)λₙ} ds ≤ 1`. -/
theorem duhamelSpectralCoeff_eigenvalue_sq_bound_direct
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        |duhamelSpectralCoeff a τ n|) ≤
      src.sourceEigenEnvelope n := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have henv_nonneg : 0 ≤ src.sourceEigenEnvelope n :=
    src.sourceEigen_nonneg n
  set f : ℝ → ℝ := fun s => Real.exp (-(τ - s) * lam) * a s n
  have hf_cont : Continuous f := by
    dsimp [f]
    exact (Real.continuous_exp.comp (by fun_prop)).mul
      (continuous_iff_continuousAt.2
        (fun s => (src.toTimeC1.hderiv s n).continuousAt))
  have habs_int :
      |∫ s in (0 : ℝ)..τ, f s| ≤ ∫ s in (0 : ℝ)..τ, |f s| :=
    intervalIntegral.abs_integral_le_integral_abs hτ
  have hleft : lam * (lam * |∫ s in (0 : ℝ)..τ, f s|) ≤
      lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left habs_int hlam) hlam
  have hconst : lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|) =
      ∫ s in (0 : ℝ)..τ, lam * (lam * |f s|) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
  have hmono :
      (∫ s in (0 : ℝ)..τ, lam * (lam * |f s|)) ≤
        ∫ s in (0 : ℝ)..τ,
          (lam * Real.exp (-(τ - s) * lam)) *
            src.sourceEigenEnvelope n := by
    apply intervalIntegral.integral_mono_on hτ
    · exact (continuous_const.mul
        (continuous_const.mul hf_cont.abs)).intervalIntegrable 0 τ
    · exact ((continuous_const.mul
        (Real.continuous_exp.comp (by fun_prop))).mul
          continuous_const).intervalIntegrable 0 τ
    · intro s hs
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hsrc := src.sourceEigen_bound s hs.1 n
      calc lam * (lam *
            (Real.exp (-(τ - s) * lam) * |a s n|))
          = (lam * Real.exp (-(τ - s) * lam)) *
              (lam * |a s n|) := by ring
        _ ≤ (lam * Real.exp (-(τ - s) * lam)) *
              src.sourceEigenEnvelope n := by
            exact mul_le_mul_of_nonneg_left hsrc
              (mul_nonneg hlam (Real.exp_nonneg _))
  have hright :
      (∫ s in (0 : ℝ)..τ,
          (lam * Real.exp (-(τ - s) * lam)) *
            src.sourceEigenEnvelope n) ≤
        src.sourceEigenEnvelope n := by
    rw [intervalIntegral.integral_mul_const]
    calc (∫ s in (0 : ℝ)..τ, lam * Real.exp (-(τ - s) * lam)) *
          src.sourceEigenEnvelope n
        ≤ 1 * src.sourceEigenEnvelope n := by
          exact mul_le_mul_of_nonneg_right
            (heatKernelEigenMass_le_one hτ hlam) henv_nonneg
      _ = src.sourceEigenEnvelope n := one_mul _
  have hduh : duhamelSpectralCoeff a τ n =
      ∫ s in (0 : ℝ)..τ, f s := by
    simp [duhamelSpectralCoeff, f, lam]
  rw [hduh]
  exact hleft.trans (hconst.le.trans (hmono.trans hright))

/-- Summability of the Duhamel branch `λ²` coefficients by the direct bound. -/
theorem duhamelSpectralCoeff_eigenvalue_sq_summable_direct
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff a τ n|)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    src.sourceEigen_summable
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · exact duhamelSpectralCoeff_eigenvalue_sq_bound_direct src hτ n

/-- Direct Duhamel branch bound with one more coefficient weight:
`λₙ³ |bₙ(τ)| ≤ sourceEigenSqEnvelope n`. -/
theorem duhamelSpectralCoeff_eigenvalue_cube_bound_direct
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff a τ n|)) ≤
      src.sourceEigenSqEnvelope n := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have henv_nonneg : 0 ≤ src.sourceEigenSqEnvelope n :=
    src.sourceEigenSq_nonneg n
  set f : ℝ → ℝ := fun s => Real.exp (-(τ - s) * lam) * a s n
  have hf_cont : Continuous f := by
    dsimp [f]
    exact (Real.continuous_exp.comp (by fun_prop)).mul
      (continuous_iff_continuousAt.2
        (fun s => (src.toTimeC1.hderiv s n).continuousAt))
  have habs_int :
      |∫ s in (0 : ℝ)..τ, f s| ≤ ∫ s in (0 : ℝ)..τ, |f s| :=
    intervalIntegral.abs_integral_le_integral_abs hτ
  have hleft : lam * (lam * (lam * |∫ s in (0 : ℝ)..τ, f s|)) ≤
      lam * (lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left habs_int hlam) hlam) hlam
  have hconst : lam * (lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|)) =
      ∫ s in (0 : ℝ)..τ, lam * (lam * (lam * |f s|)) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
  have hmono :
      (∫ s in (0 : ℝ)..τ, lam * (lam * (lam * |f s|))) ≤
        ∫ s in (0 : ℝ)..τ,
          (lam * Real.exp (-(τ - s) * lam)) *
            src.sourceEigenSqEnvelope n := by
    apply intervalIntegral.integral_mono_on hτ
    · exact (continuous_const.mul (continuous_const.mul
        (continuous_const.mul hf_cont.abs))).intervalIntegrable 0 τ
    · exact ((continuous_const.mul
        (Real.continuous_exp.comp (by fun_prop))).mul
          continuous_const).intervalIntegrable 0 τ
    · intro s hs
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hsrc := src.sourceEigenSq_bound s hs.1 n
      calc lam * (lam *
            (lam * (Real.exp (-(τ - s) * lam) * |a s n|)))
          = (lam * Real.exp (-(τ - s) * lam)) *
              (lam * (lam * |a s n|)) := by ring
        _ ≤ (lam * Real.exp (-(τ - s) * lam)) *
              src.sourceEigenSqEnvelope n := by
            exact mul_le_mul_of_nonneg_left hsrc
              (mul_nonneg hlam (Real.exp_nonneg _))
  have hright :
      (∫ s in (0 : ℝ)..τ,
          (lam * Real.exp (-(τ - s) * lam)) *
            src.sourceEigenSqEnvelope n) ≤
        src.sourceEigenSqEnvelope n := by
    rw [intervalIntegral.integral_mul_const]
    calc (∫ s in (0 : ℝ)..τ, lam * Real.exp (-(τ - s) * lam)) *
          src.sourceEigenSqEnvelope n
        ≤ 1 * src.sourceEigenSqEnvelope n := by
          exact mul_le_mul_of_nonneg_right
            (heatKernelEigenMass_le_one hτ hlam) henv_nonneg
      _ = src.sourceEigenSqEnvelope n := one_mul _
  have hduh : duhamelSpectralCoeff a τ n =
      ∫ s in (0 : ℝ)..τ, f s := by
    simp [duhamelSpectralCoeff, f, lam]
  rw [hduh]
  exact hleft.trans (hconst.le.trans (hmono.trans hright))

/-- The Duhamel coefficient derivative identity `bₙ' = aₙ - λₙ bₙ`. -/
theorem duhamelSpectralCoeff_hasDerivAt_direct
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    (τ : ℝ) (n : ℕ) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a τ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ n) τ :=
  ShenWork.IntervalSourceCoefficientTimeC1.duhamelSpectralCoeff_hasDerivAt
    src.toTimeC1 τ n

/-- Direct derivative-coefficient bound from `bₙ' = aₙ - λₙ bₙ`. -/
theorem duhamelSpectralCoeff_deriv_eigenvalue_sq_bound_direct
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        |a τ n - unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff a τ n|) ≤
      2 * src.sourceEigenSqEnvelope n := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have hsrc := src.sourceEigenSq_bound τ hτ n
  have hduh :
      lam * (lam * (lam * |duhamelSpectralCoeff a τ n|)) ≤
        src.sourceEigenSqEnvelope n := by
    exact duhamelSpectralCoeff_eigenvalue_cube_bound_direct src hτ n
  calc lam * (lam *
          |a τ n - lam * duhamelSpectralCoeff a τ n|)
      ≤ lam * (lam *
          (|a τ n| + |lam * duhamelSpectralCoeff a τ n|)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (a τ n)
                  (-(lam * duhamelSpectralCoeff a τ n)))
            hlam)
          hlam
    _ = lam * (lam * |a τ n|) +
          lam * (lam * (lam * |duhamelSpectralCoeff a τ n|)) := by
        rw [abs_mul, abs_of_nonneg hlam]
        ring
    _ ≤ src.sourceEigenSqEnvelope n + src.sourceEigenSqEnvelope n :=
        add_le_add hsrc hduh
    _ = 2 * src.sourceEigenSqEnvelope n := by ring

/-- Summability of the Duhamel derivative `λ²` coefficients by the direct bound. -/
theorem duhamelSpectralCoeff_deriv_eigenvalue_sq_summable_direct
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |a τ n - unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a τ n|)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (src.sourceEigenSq_summable.mul_left 2)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · exact duhamelSpectralCoeff_deriv_eigenvalue_sq_bound_direct src hτ n

/-- Full restart coefficient `λ²` summability: homogeneous heat tail plus the
direct Duhamel branch. -/
theorem localRestartCoeff_eigenvalue_sq_summable_direct
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |localRestartCoeff a₀ a τ n|)) := by
  have hhom :=
    ShenWork.IntervalResolverSpectralJointC2Closed.restartHomogeneousCoeff_eigenvalue_sq_summable
      (τ := τ) (M := M) (a₀ := a₀) hτ ha₀
  have hduh :=
    duhamelSpectralCoeff_eigenvalue_sq_summable_direct src hτ.le
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hhom.add hduh)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    calc lam * (lam * |localRestartCoeff a₀ a τ n|)
        ≤ lam * (lam *
            (|Real.exp (-τ * lam) * a₀ n| +
              |duhamelSpectralCoeff a τ n|)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (by
                simp only [localRestartCoeff]
                exact abs_add_le _ _)
              hlam)
            hlam
      _ = lam * (lam * |Real.exp (-τ * lam) * a₀ n|) +
            lam * (lam * |duhamelSpectralCoeff a τ n|) := by ring

end IntervalDuhamelDirectC2Coeff
end ShenWork
