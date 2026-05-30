/-
  ShenWork/PDE/IntervalFullKernelMass.lean

  **T2 — mass conservation of the full Neumann kernel.**

  `∫₀¹ K_full(t,x,y) dy = 1` for `t > 0`, every `x`.  The period-2 image lattice
  tiles the line, so the `[0,1]` mass of the periodised kernel equals the full-line
  heat mass `∫_ℝ heat = 1`.  Tonelli interchange (`integral_tsum_of_summable_
  integral_norm`) + the kernel-shaped tiling identity `tsum_cell_integral_eq_integral`
  (with `g = heatKernel t`) + `heatKernel_integral_eq_one`.

  This is the bound `∫₀¹ |K̃| ≤ ∫₀¹ K_full = 1` input for the full-kernel
  initial-data IBP gradient bound (T2).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelGradientLinfty

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- Cell-integral summability for the heat kernel (mass analogue of
`summable_cell_heatGrad_interval_integral`). -/
theorem summable_cell_heat_interval_integral {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
        (∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)))
          + (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))) := by
  have hg : Integrable (fun w : ℝ => heatKernel t w) := heatKernel_integrable ht
  have hint : IntegrableOn (fun w : ℝ => heatKernel t w)
      (⋃ k : ℤ, Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)) := by
    rw [ShenWork.iUnion_Ioc_offset_eq_univ]
    exact hg.integrableOn
  have hsum := (hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ioc)
    (ShenWork.pairwise_disjoint_Ioc_offset (x - 1)) hint).summable
  refine hsum.congr (fun k => ?_)
  have hset : Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)
      = Set.Ioc (x + 2 * (k : ℝ) - 1) (x + 2 * (k : ℝ) + 1) := by
    congr 1 <;> ring
  rw [hset]
  exact (ShenWork.cell_integral_eq hg x k).symm

/-- **Mass conservation of the full Neumann kernel.**  `∫₀¹ K_full(t,x,y) dy = 1`
for `t > 0`.  The `[0,1]` mass of the periodised image kernel equals the full-line
heat mass via the tiling identity. -/
theorem intervalNeumannFullKernel_integral_eq_one {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, intervalNeumannFullKernel t x y) = 1 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hg : Integrable (fun w : ℝ => heatKernel t w) := heatKernel_integrable ht
  have hhc : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  set hk : ℤ → ℝ → ℝ := fun k y =>
    heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)) with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y =>
    add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _)
  have hAii : ∀ k : ℤ,
      IntervalIntegrable (fun y : ℝ => heatKernel t (x - y + 2 * (k : ℝ))) volume 0 1 :=
    fun k => (hhc.comp (by fun_prop)).intervalIntegrable 0 1
  have hBii : ∀ k : ℤ,
      IntervalIntegrable (fun y : ℝ => heatKernel t (x + y + 2 * (k : ℝ))) volume 0 1 :=
    fun k => (hhc.comp (by fun_prop)).intervalIntegrable 0 1
  have hμint : ∀ k : ℤ, Integrable (hk k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    rw [hk_def]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp ((hAii k).add (hBii k))
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)))
            + (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ))) := by
    intro k
    have e1 : (∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ y in (0 : ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
    rw [e1]
    exact intervalIntegral.integral_add (hAii k) (hBii k)
  have hμsum : Summable
      (fun k : ℤ => ∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (summable_cell_heat_interval_integral ht x).congr (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := hk) hμint hμsum
  have hKeq : (fun y : ℝ => intervalNeumannFullKernel t x y) = fun y => ∑' k : ℤ, hk k y := rfl
  calc (∫ y in (0 : ℝ)..1, intervalNeumannFullKernel t x y)
      = ∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y := by rw [hKeq]
    _ = ∫ y, (∑' k : ℤ, hk k y) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        intervalIntegral.integral_of_le h01
    _ = ∑' k : ℤ, ∫ y, hk k y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
    _ = ∑' k : ℤ,
          ((∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)))
            + (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))) := by
        refine tsum_congr (fun k => ?_)
        rw [← intervalIntegral.integral_of_le h01]
        exact intervalIntegral.integral_add (hAii k) (hBii k)
    _ = ∫ w : ℝ, heatKernel t w := ShenWork.tsum_cell_integral_eq_integral hg x
    _ = 1 := heatKernel_integral_eq_one ht

end ShenWork.IntervalNeumannFullKernel
