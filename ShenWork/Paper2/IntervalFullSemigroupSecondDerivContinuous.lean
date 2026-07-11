/-
  Continuity of the second spatial derivative of the full Neumann semigroup
  for bounded measurable data.  This removes the unnecessary source
  continuity assumption from the older spectral continuity interface.
-/
import ShenWork.PDE.IntervalFullKernelSecondDerivLinfty

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain (intervalMeasure intervalMeasure_univ_lt_top)

/-- For fixed `y`, the full-kernel Hessian is continuous in its first spatial
variable on the physical interval. -/
theorem continuousOn_secondDeriv_intervalNeumannFullKernel_fst_in_x
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ContinuousOn
      (fun x : ℝ ↦ deriv (fun z ↦ deriv
        (fun w ↦ intervalNeumannFullKernel t w y) z) x)
      (Set.Icc (0 : ℝ) 1) := by
  have hcd := continuous_secondDeriv_heatKernel ht
  have hfun :
      (fun x : ℝ ↦ deriv (fun z ↦ deriv
        (fun w ↦ intervalNeumannFullKernel t w y) z) x) =
      fun x : ℝ ↦
        (∑' k : ℤ, deriv (fun z ↦ deriv (fun w ↦ heatKernel t w) z)
          (x - y + 2 * (k : ℝ))) +
        (∑' k : ℤ, deriv (fun z ↦ deriv (fun w ↦ heatKernel t w) z)
          (x + y + 2 * (k : ℝ))) := by
    funext x
    exact (hasDerivAt_deriv_intervalNeumannFullKernel_fst ht x y).deriv
  rw [hfun]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_tsum
      (fun k ↦ (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatHessWindowBound ht (-y) 1) (fun k x hx ↦ ?_)
    rw [Real.norm_eq_abs]
    refine abs_secondDeriv_heatKernel_le_windowShift ht (-y) 1 k ?_
    rw [show x - y + 2 * (k : ℝ) - (-y + 2 * (k : ℝ)) = x by ring]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · refine continuousOn_tsum
      (fun k ↦ (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatHessWindowBound ht y 1) (fun k x hx ↦ ?_)
    rw [Real.norm_eq_abs]
    refine abs_secondDeriv_heatKernel_le_windowShift ht y 1 k ?_
    rw [show x + y + 2 * (k : ℝ) - (y + 2 * (k : ℝ)) = x by ring]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Bounded measurable source data already suffice for continuity of the
semigroup Hessian on `[0,1]`. -/
theorem intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1))
    {C : ℝ} (hf_bound : ∀ y, |f y| ≤ C) :
    ContinuousOn
      (fun x : ℝ ↦ deriv (fun z ↦ deriv
        (fun w ↦ intervalFullSemigroupOperator t f w) z) x)
      (Set.Icc (0 : ℝ) 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨intervalMeasure_univ_lt_top 1⟩
  have hC : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hf_bound 0)
  set B : ℝ := ∑' k : ℤ,
    (heatHessWindowBound t 0 2 k + heatHessWindowBound t 0 2 k) with hB
  have hB_nn : 0 ≤ B := by
    rw [hB]
    exact tsum_nonneg fun k ↦ by
      unfold heatHessWindowBound heatHessPointwiseBound
      positivity
  have hcont_int : ContinuousOn (fun x : ℝ ↦
      ∫ y, deriv (fun z ↦ deriv
        (fun w ↦ intervalNeumannFullKernel t w y) z) x * f y
          ∂(intervalMeasure 1)) (Set.Icc (0 : ℝ) 1) := by
    refine MeasureTheory.continuousOn_of_dominated
      (μ := intervalMeasure 1)
      (F := fun x : ℝ ↦ fun y : ℝ ↦
        deriv (fun z ↦ deriv
          (fun w ↦ intervalNeumannFullKernel t w y) z) x * f y)
      (bound := fun _ : ℝ ↦ B * C) ?hF_meas ?h_bound ?h_bound_int ?h_cont
    · intro x _hx
      exact ((continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x).aestronglyMeasurable
        measurableSet_Icc).mul hf_int.aestronglyMeasurable
    · intro x hx
      change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ‖deriv (fun z ↦ deriv
          (fun w ↦ intervalNeumannFullKernel t w y) z) x * f y‖ ≤ B * C
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy ↦ ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hx_abs : |x| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hy_abs : |y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hK : |deriv (fun z ↦ deriv
          (fun w ↦ intervalNeumannFullKernel t w y) z) x| ≤ B := by
        simpa [hB] using
          (abs_secondDeriv_intervalNeumannFullKernel_fst_le_const
            ht 0 (z := x) (y := y) (by simpa using hx_abs) hy_abs)
      exact mul_le_mul hK (hf_bound y) (abs_nonneg _) hB_nn
    · exact integrable_const _
    · change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ContinuousOn (fun x : ℝ ↦
          deriv (fun z ↦ deriv
            (fun w ↦ intervalNeumannFullKernel t w y) z) x * f y)
          (Set.Icc (0 : ℝ) 1)
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y _hy ↦ ?_
      exact (continuousOn_secondDeriv_intervalNeumannFullKernel_fst_in_x ht y).mul
        continuousOn_const
  exact hcont_int.congr (fun x _hx ↦
    (intervalFullSemigroupOperator_hasDerivAt_deriv_fst
      ht hf_int.aestronglyMeasurable hf_bound x).deriv)

end ShenWork.IntervalNeumannFullKernel
