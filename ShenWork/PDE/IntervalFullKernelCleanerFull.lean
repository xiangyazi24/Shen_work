/-
  ShenWork/PDE/IntervalFullKernelCleanerFull.lean

  **T2 — `_cleaner_full`: discharge the Leibniz bridges on the full kernel.**

  Full-Neumann-kernel mirror of
  `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner`:
  the bookkeeping bridges `hSplit` (via `deriv_add`), `hLeibniz`
  (`intervalFullCoupledDuhamel_grad_leibniz`, T2-k) and `hGrad_int`
  (`intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable`, T2-k) are
  discharged internally, taking only the per-slice joint measurability
  (`hF_meas`/`hF'_meas`) — exactly the analytic input `_cleaner` takes via
  `hF_ae` + the `s_dependent` measurability lemmas.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelCleanFull
import ShenWork.PDE.IntervalFullKernelLeibniz
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain ShenWork.IntervalDomainExistence
open ShenWork.IntervalCoupledClassicalBallEstimates ShenWork.Paper2

/-- **`_cleaner_full`.** -/
theorem intervalFullKernelClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H Cu₀ : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext (intervalMeasure 1))
    (hu₀_ext_bound : ∀ y, |u₀_ext y| ≤ Cu₀)
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 < t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalFullSemigroupOperator (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (intervalMeasure 1))
    (hF_ae :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
            MeasureTheory.AEStronglyMeasurable
              (Function.uncurry
                (fun (s : ℝ) (y : ℝ) =>
                  intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y))
              ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ)).prod
                (intervalMeasure 1))) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p R u₀ u t x) v := by
  refine intervalFullKernelClassicalC1BallEstimates_hmap_dirichlet_initial_clean
    (p := p) (R := R) (u₀ := u₀) (u₀_ext := u₀_ext) (u₀'_ext := u₀'_ext)
    (T := T) (M := M) (G_u := G_u) (G_u_init := G_u_init)
    (C_source := C_source) (H := H) (Cu₀ := Cu₀)
    hT hH_nn hC_nn hG_init_nn hM_eq hG_u_eq hu₀_sup hext_eq
    hu₀_ext_int hu₀_ext_bound hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one hu₀_ext'_sup
    hSol hSource_sup_local hSource_sup_global hint hSource_int_global ?_ ?_ ?_
  · -- hSplit via `deriv_add`.
    intro u v hsnap τ x hτ hxIcc
    have hF_aeτ := hF_ae u v hsnap τ hτ
    have hFm := fun x' : ℝ =>
      intervalFullSemigroupOperator_s_dependent_aestronglyMeasurable_x hτ.1 hF_aeτ x'
    have hFd :=
      intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀ hτ.1 hF_aeτ
        (fun s => hSource_int_global u v hsnap s)
        (fun s y => hSource_sup_global u v hsnap s y) x
    have hInit_diff :
        DifferentiableAt ℝ (fun z : ℝ => intervalFullSemigroupOperator τ u₀_ext z) x :=
      (intervalFullSemigroupOperator_hasDerivAt_fst hτ.1
        hu₀_ext_int.aestronglyMeasurable (Cf := Cu₀) hu₀_ext_bound x).differentiableAt
    have hIntegral_diff :
        DifferentiableAt ℝ
          (fun y : ℝ =>
            ∫ s in (0 : ℝ)..τ,
              intervalFullSemigroupOperator (τ - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) y) x :=
      (intervalFullCoupledDuhamel_grad_integral_hasDerivAt (t := τ) hτ.1
        (F := fun s y => intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)
        (fun s => hSource_int_global u v hsnap s) hC_nn
        (fun s y => hSource_sup_global u v hsnap s y) x
        hFm hFd
        (intervalCoupledDuhamel_grad_envelope_intervalIntegrable hτ.1 C_source)).differentiableAt
    exact deriv_add hInit_diff hIntegral_diff
  · -- hLeibniz.
    intro u v hsnap τ x hτ hxIcc
    have hF_aeτ := hF_ae u v hsnap τ hτ
    have hFm := fun x' : ℝ =>
      intervalFullSemigroupOperator_s_dependent_aestronglyMeasurable_x hτ.1 hF_aeτ x'
    have hFd :=
      intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀ hτ.1 hF_aeτ
        (fun s => hSource_int_global u v hsnap s)
        (fun s y => hSource_sup_global u v hsnap s y) x
    exact intervalFullCoupledDuhamel_grad_leibniz (t := τ) hτ.1
      (F := fun s y => intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)
      (fun s => hSource_int_global u v hsnap s) hC_nn
      (fun s y => hSource_sup_global u v hsnap s y) x
      hFm hFd
      (intervalCoupledDuhamel_grad_envelope_intervalIntegrable hτ.1 C_source)
  · -- hGrad_int.
    intro u v hsnap τ x hτ hxIcc
    have hF_aeτ := hF_ae u v hsnap τ hτ
    have hFd :=
      intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀ hτ.1 hF_aeτ
        (fun s => hSource_int_global u v hsnap s)
        (fun s y => hSource_sup_global u v hsnap s y) x
    exact intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable (t := τ) hτ.1
      (F := fun s y => intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)
      (fun s => hSource_int_global u v hsnap s) hC_nn
      (fun s y => hSource_sup_global u v hsnap s y) x
      hFd
      (intervalCoupledDuhamel_grad_envelope_intervalIntegrable hτ.1 C_source)

end ShenWork.IntervalNeumannFullKernel
