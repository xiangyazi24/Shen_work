/-
  ShenWork/PDE/IntervalFullKernelGradEstimate.lean

  **T2 — full-kernel Duhamel gradient estimates.**

  Full-Neumann-kernel analogues of the zeroth-reflection
  `intervalCoupledDuhamel_grad_*` lemmas (in `IntervalCoupledClassicalBallEstimates.
  lean`), built on the unconditional full-kernel gradient `L∞→L∞` estimate
  `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` (T1).  These are the
  source-integral gradient bounds the `_clean` chain consumes — now on the FULL
  Neumann kernel (genuine two-endpoint Neumann), so the `hGradEq` boundary identity
  holds end-to-end (including `x = 1`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- **Per-slice full-kernel gradient bound.**  At each interior time slice the
full-Neumann-kernel propagator derivative obeys the `(t−s)^{−1/2}` envelope
(`intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`, T1). -/
theorem intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
    {t s : ℝ} (hs0 : 0 ≤ s) (hst : s < t)
    {F : ℝ → ℝ}
    (hF_int : MeasureTheory.Integrable F (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ y : ℝ, |F y| ≤ C_source) (x : ℝ) :
    |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) F z) x| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
        * (t - s) ^ (-(1 / 2) : ℝ) * C_source := by
  have htmS_pos : 0 < t - s := sub_pos.mpr hst
  exact intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
    (t := t - s) htmS_pos (f := F) hF_int.aestronglyMeasurable (Cf := C_source) hF_sup x

/-- **Full-kernel source-integral gradient bound (under a Leibniz interchange).**
The analogue of `intervalCoupledDuhamel_grad_integral_bound_of_leibniz` for the
full Neumann kernel: given the differentiation-under-the-integral identity
`hLeibniz` and the interval-integrability data, the source-integral gradient is
uniformly bounded by `Cgrad · 2√T · C_source` (uniformly as `t → 0⁺`).  Same proof
shape as the zeroth-reflection version, with the per-slice bound supplied by
`intervalFullCoupledDuhamel_grad_integrand_pointwise_bound`. -/
theorem intervalFullCoupledDuhamel_grad_integral_bound_of_leibniz
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hLeibniz :
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x₀)
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1 / 2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x) x₀| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant with hCgrad_def
  have hCgrad_nn : 0 ≤ Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hpt_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      |deriv (fun z : ℝ =>
        intervalFullSemigroupOperator (t - s) (F s) z) x₀| ≤
      Cgrad * C_source * (t - s) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    have h1 := intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
      (t := t) (s := s) hs.1.le hs.2 (F := F s) (hF_int s)
      (C_source := C_source) hC_source_nn (hF_sup s) x₀
    calc |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀|
        ≤ Cgrad * (t - s) ^ (-(1 / 2 : ℝ)) * C_source := h1
      _ = Cgrad * C_source * (t - s) ^ (-(1 / 2 : ℝ)) := by ring
  rw [hLeibniz]
  have habs_le :
      |∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (F s) z) x₀| ≤
        ∫ s in (0 : ℝ)..t,
          |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (F s) z) x₀| :=
    intervalIntegral.abs_integral_le_integral_abs ht.le
  have hmono :
      ∫ s in (0 : ℝ)..t,
        |deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x₀| ≤
      ∫ s in (0 : ℝ)..t, Cgrad * C_source * (t - s) ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo ht.le hGrad_int.abs hDom_int ?_
    intro s hs
    exact hpt_bound s hs
  have hint_eq :
      ∫ s in (0 : ℝ)..t, Cgrad * C_source * (t - s) ^ (-(1 / 2 : ℝ)) =
        Cgrad * C_source * (2 * Real.sqrt t) := by
    rw [intervalIntegral.integral_const_mul,
      ShenWork.IntervalCoupledClassicalBallEstimates.intervalIntegral_inv_sqrt_sub_eq_two_sqrt ht]
  have hC_nn : 0 ≤ Cgrad * C_source := mul_nonneg hCgrad_nn hC_source_nn
  have hT_bound :
      Cgrad * C_source * (2 * Real.sqrt t) ≤
        Cgrad * C_source * (2 * Real.sqrt T) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htT) (by norm_num)) hC_nn
  calc
    |∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x₀|
        ≤ ∫ s in (0 : ℝ)..t,
            |deriv (fun z : ℝ =>
              intervalFullSemigroupOperator (t - s) (F s) z) x₀| := habs_le
    _ ≤ ∫ s in (0 : ℝ)..t,
            Cgrad * C_source * (t - s) ^ (-(1 / 2 : ℝ)) := hmono
    _ = Cgrad * C_source * (2 * Real.sqrt t) := hint_eq
    _ ≤ Cgrad * C_source * (2 * Real.sqrt T) := hT_bound
    _ = Cgrad * (2 * Real.sqrt T) * C_source := by ring

end ShenWork.IntervalNeumannFullKernel
