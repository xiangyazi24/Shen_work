/-
  ShenWork/PDE/IntervalFullKernelGradEstimateFull.lean

  **T2 — complete full-kernel Duhamel gradient estimate (initial + source).**

  Combines the full-kernel initial-data IBP bound
  (`intervalFullCoupledDuhamel_grad_initial_bound`, T2-f) with the source-integral
  combiner (`intervalFullCoupledDuhamel_grad_estimate_of_leibniz`, T2-b) into the
  full-kernel analogue of `intervalCoupledDuhamel_grad_estimate_full_dirichlet`:

    `|deriv (S_full(t)u₀ + ∫₀ᵗ S_full(t−s)F) x₀| ≤ G_init + Cgrad·2√T·C_source`,

  with NO abstract `hInit_grad` hypothesis — the initial bound is discharged.  This
  is the complete gradient prerequisite of the C¹_x Duhamel ball, now end-to-end on
  the full Neumann kernel.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelGradEstimate
import ShenWork.PDE.IntervalFullKernelInitialIBP

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- **Complete full-kernel Duhamel gradient estimate.**  Full-Neumann-kernel
analogue of `intervalCoupledDuhamel_grad_estimate_full_dirichlet`, with the
initial-data gradient bound discharged internally by the IBP bound (T2-f). -/
theorem intervalFullCoupledDuhamel_grad_estimate_full
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {u₀ u₀' : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable u₀ (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |u₀ y| ≤ Cu₀)
    (hu₀ : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀ (u₀' y) y)
    (hu₀'_int : IntervalIntegrable u₀' MeasureTheory.volume 0 1)
    (hu₀_one : u₀ 1 = 0)
    {G_init : ℝ} (hG_init_nn : 0 ≤ G_init)
    (hu₀'_sup : ∀ y, |u₀' y| ≤ G_init)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hSplit :
      deriv (fun x : ℝ =>
        intervalFullSemigroupOperator t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x) x₀ =
      deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀ z) x₀ +
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x) x₀)
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
        intervalFullSemigroupOperator t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x) x₀| ≤
      G_init +
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt T) * C_source := by
  have hInit :
      |deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀ z) x₀| ≤ G_init :=
    intervalFullCoupledDuhamel_grad_initial_bound ht hu₀_meas hu₀_bound hu₀ hu₀'_int
      hu₀_one hG_init_nn hu₀'_sup x₀
  exact intervalFullCoupledDuhamel_grad_estimate_of_leibniz ht htT hF_int hC_source_nn
    hF_sup x₀ hG_init_nn hInit hSplit hLeibniz hGrad_int hDom_int

end ShenWork.IntervalNeumannFullKernel
