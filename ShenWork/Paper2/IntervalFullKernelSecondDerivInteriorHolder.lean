/-
  Cancellable Neumann heat Hessian estimate when the source Holder condition
  is known only on the open physical interval.  Endpoint values are irrelevant
  to the interval measure; this is the form needed for derivatives of zero
  extensions, whose two-sided endpoint derivatives are artificially zero.
-/
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- Interior-Holder version of `neumannHeatSecondDeriv_Ctheta_to_Linfty`.
The bounded measurable source may have arbitrary endpoint values. -/
theorem neumannHeatSecondDeriv_interiorCtheta_to_Linfty
    {t theta : ℝ} (ht : 0 < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) {h : ℝ → ℝ}
    (hh_meas : AEStronglyMeasurable h (intervalMeasure 1))
    {Ch : ℝ} (hh : ∀ y, |h y| ≤ Ch) {Hh : ℝ} (hHh_nn : 0 ≤ Hh)
    (hHh : ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
      |h a - h b| ≤ Hh * |a - b| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z : ℝ => deriv
      (fun w : ℝ => intervalFullSemigroupOperator t h w) z) x| ≤
      weightedHeatHessConst theta * t ^ (-1 + theta / 2 : ℝ) * Hh := by
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hrepr :=
    (intervalFullSemigroupOperator_hasDerivAt_deriv_fst ht hh_meas hh x).deriv
  rw [hrepr]
  set K : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => deriv
      (fun w : ℝ => intervalNeumannFullKernel t w y) z) x with hK
  have hKcont : ContinuousOn K (Set.Icc (0 : ℝ) 1) :=
    continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x
  have hKint : Integrable K (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact hKcont.integrableOn_Icc
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖h y‖ ≤ Ch :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hh y
  have hKhint : Integrable (fun y => K y * h y) (intervalMeasure 1) :=
    hKint.mul_bdd hh_meas hbdd
  have hmean0 : (∫ y, K y ∂(intervalMeasure 1)) = 0 :=
    intervalNeumannFullKernel_secondDeriv_integral_zero ht x
  have hsub : (∫ y, K y * h y ∂(intervalMeasure 1)) =
      ∫ y, K y * (h y - h x) ∂(intervalMeasure 1) := by
    have hxint : Integrable (fun y => K y * h x) (intervalMeasure 1) :=
      hKint.mul_const (h x)
    rw [show (fun y => K y * (h y - h x)) =
        (fun y => K y * h y - K y * h x) by
          funext y
          ring,
      MeasureTheory.integral_sub hKhint hxint,
      show (fun y => K y * h x) = (fun y => h x * K y) by
        funext y
        ring,
      MeasureTheory.integral_const_mul, hmean0, mul_zero, sub_zero]
  rw [hsub]
  have hpt : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      ‖K y * (h y - h x)‖ ≤ Hh * (|K y| * |x - y| ^ theta) := by
    intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hhy := hHh y hy x hx
    rw [abs_sub_comm y x] at hhy
    calc
      |K y| * |h y - h x| ≤ |K y| * (Hh * |x - y| ^ theta) :=
        mul_le_mul_of_nonneg_left hhy (abs_nonneg _)
      _ = Hh * (|K y| * |x - y| ^ theta) := by ring
  have hweight_int : Integrable
      (fun y => |K y| * |x - y| ^ theta) (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (hKcont.abs.mul (((continuous_abs.comp (by fun_prop)).rpow_const
      (fun _ => Or.inr htheta0.le)).continuousOn)).integrableOn_Icc
  have hne0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hne1 : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  calc
    |∫ y, K y * (h y - h x) ∂(intervalMeasure 1)|
        ≤ ∫ y, ‖K y * (h y - h x)‖ ∂(intervalMeasure 1) := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, Hh * (|K y| * |x - y| ^ theta) ∂(intervalMeasure 1) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y => norm_nonneg _)
        (hweight_int.const_mul Hh) ?_
      simp only [intervalMeasure, intervalSet]
      refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards [hne0, hne1] with y hy0 hy1 hy
      exact hpt y ⟨lt_of_le_of_ne hy.1 hy0.symm, lt_of_le_of_ne hy.2 hy1⟩
    _ = Hh * ∫ y, |K y| * |x - y| ^ theta ∂(intervalMeasure 1) :=
      MeasureTheory.integral_const_mul _ _
    _ ≤ Hh * (weightedHeatHessConst theta * t ^ (-1 + theta / 2 : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ hHh_nn
      have hcv :
          (∫ y, |K y| * |x - y| ^ theta ∂(intervalMeasure 1)) =
            ∫ y in (0 : ℝ)..1, |K y| * |x - y| ^ theta := by
        simp only [intervalMeasure, intervalSet]
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [hcv, hK]
      exact intervalNeumannFullKernel_secondDeriv_weighted_mass
        ht htheta0 htheta1 hxIcc
    _ = weightedHeatHessConst theta * t ^ (-1 + theta / 2 : ℝ) * Hh := by ring

end ShenWork.IntervalNeumannFullKernel
