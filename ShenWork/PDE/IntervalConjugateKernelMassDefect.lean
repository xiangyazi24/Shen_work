import ShenWork.PDE.IntervalFullKernelSourceIBP
import ShenWork.PDE.IntervalSemigroupUniform

/-!
# Reflected half-kernel for conjugate-kernel mass defects

This file starts the non-circular mass-defect route for the conjugate/Dirichlet
approximate identity.  The key algebraic observation is that `-Ktilde` is the
full Neumann kernel minus twice the reflected image half.
-/

open MeasureTheory Filter Topology
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

noncomputable section

/-- The reflected image half of the full Neumann image kernel. -/
def intervalNeumannReflectedKernelPart (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ))

/-- Summability of the reflected half-kernel lattice. -/
theorem reflectedKernelPart_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun k : ℤ => heatKernel t (x + y + 2 * (k : ℝ))) :=
  latticeGaussianSummable ht (x + y)

/-- The reflected half-kernel is nonnegative. -/
theorem reflectedKernelPart_nonneg {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    0 ≤ intervalNeumannReflectedKernelPart t x y := by
  rw [intervalNeumannReflectedKernelPart]
  exact tsum_nonneg (fun k => heatKernel_nonneg ht _)

/-- On an interior strip, every reflected image is separated from the origin. -/
theorem reflectedKernelPart_image_abs_ge
    {η x y : ℝ} (hη0 : 0 < η)
    (hx : x ∈ Set.Icc η (1 - η)) (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    η ≤ |x + y + 2 * (k : ℝ)| := by
  by_cases hk : (0 : ℤ) ≤ k
  · have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    have hnonneg : 0 ≤ x + y + 2 * (k : ℝ) := by linarith [hx.1, hy.1, hkr]
    rw [abs_of_nonneg hnonneg]
    linarith [hx.1, hy.1, hkr]
  · have hkneg : k ≤ (-1 : ℤ) := by omega
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg
    have hnonpos : x + y + 2 * (k : ℝ) ≤ 0 := by
      linarith [hx.2, hy.2, hkr]
    rw [abs_of_nonpos hnonpos]
    linarith [hx.2, hy.2, hkr]

/-- Integrability of the first absolute moment of the whole-line heat kernel. -/
theorem heatKernel_abs_mul_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℝ => |z| * heatKernel t z) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hfun : (fun z : ℝ => |z| * heatKernel t z) =
      fun z => 1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2)) := by
    ext z
    unfold heatKernel
    rw [show -z ^ 2 / (4 * t) = -(1 / (4 * t)) * z ^ 2 by ring]
    ring
  have habs : (fun z : ℝ =>
      1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2))) =
      fun z => 1 / Real.sqrt (4 * Real.pi * t) *
        ‖z * Real.exp (-(1 / (4 * t)) * z ^ 2)‖ := by
    ext z
    congr 1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun, habs]
  exact (integrable_mul_exp_neg_mul_sq hb).norm.const_mul _

/-- Cell-integral summability for the heat-kernel first absolute moment. -/
theorem summable_cell_heat_abs_moment_interval_integral {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
      (∫ y in (0 : ℝ)..1,
        |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)))
      + (∫ y in (0 : ℝ)..1,
        |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))) := by
  have hg := heatKernel_abs_mul_integrable ht
  have hint : IntegrableOn (fun w : ℝ => |w| * heatKernel t w)
      (⋃ k : ℤ, Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)) := by
    rw [ShenWork.iUnion_Ioc_offset_eq_univ]
    exact hg.integrableOn
  exact (hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ioc)
    (ShenWork.pairwise_disjoint_Ioc_offset (x - 1)) hint).summable.congr (fun k => by
      have hset : Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)
          = Set.Ioc (x + 2 * (k : ℝ) - 1) (x + 2 * (k : ℝ) + 1) := by
        congr 1 <;> ring
      rw [hset]
      exact (ShenWork.cell_integral_eq hg x k).symm)

/-- Summability of the reflected half-kernel cell masses. -/
theorem reflectedKernelPart_integral_summable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (summable_cell_heat_interval_integral ht x)
  · exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun y => heatKernel_nonneg ht _)
  · have hleft : 0 ≤ ∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)) :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num)
        (fun y => heatKernel_nonneg ht _)
    exact le_add_of_nonneg_left hleft

/-- Summability of the reflected half-kernel first absolute moments. -/
theorem reflectedKernelPart_abs_moment_summable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1,
        |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (summable_cell_heat_abs_moment_interval_integral ht x)
  · exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun y => mul_nonneg (abs_nonneg _) (heatKernel_nonneg ht _))
  · have hleft : 0 ≤ ∫ y in (0 : ℝ)..1,
        |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)) :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num)
        (fun y => mul_nonneg (abs_nonneg _) (heatKernel_nonneg ht _))
    exact le_add_of_nonneg_left hleft

/-- The reflected half-kernel integral is the sum of its reflected cell masses. -/
theorem reflectedKernelPart_integral_eq_tsum {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
      = ∑' k : ℤ, ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hhc : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  set hk : ℤ → ℝ → ℝ := fun k y => heatKernel t (x + y + 2 * (k : ℝ)) with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y => by
    rw [hk_def]
    exact heatKernel_nonneg ht _
  have hBii : ∀ k : ℤ, IntervalIntegrable (hk k) volume 0 1 := by
    intro k
    rw [hk_def]
    exact (hhc.comp (by fun_prop)).intervalIntegrable 0 1
  have hμint : ∀ k : ℤ, Integrable (hk k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp (hBii k)
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)) := by
    intro k
    calc
      (∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
          = ∫ y in (0 : ℝ)..1, hk k y := by
        rw [intervalIntegral.integral_of_le h01]
        exact integral_congr_ae
          (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
      _ = ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)) := by
        rw [hk_def]
  have hμsum : Summable
      (fun k : ℤ => ∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (reflectedKernelPart_integral_summable ht x).congr (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := hk) hμint hμsum
  calc
    (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
        = ∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y := by
      apply intervalIntegral.integral_congr
      intro y _
      rw [intervalNeumannReflectedKernelPart]
    _ = ∫ y, (∑' k : ℤ, hk k y) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      intervalIntegral.integral_of_le h01
    _ = ∑' k : ℤ, ∫ y, hk k y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
    _ = ∑' k : ℤ, ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)) := by
      refine tsum_congr (fun k => ?_)
      rw [← intervalIntegral.integral_of_le h01, hk_def]

/-- The reflected first absolute moment is bounded by the whole-line heat first moment. -/
theorem reflectedKernelPart_abs_moment_tsum_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∑' k : ℤ, ∫ y in (0 : ℝ)..1,
        |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))
      ≤ 4 * t / Real.sqrt (4 * Real.pi * t) := by
  have hB := reflectedKernelPart_abs_moment_summable ht x
  have hfull := summable_cell_heat_abs_moment_interval_integral ht x
  have hle :
      (∑' k : ℤ, ∫ y in (0 : ℝ)..1,
          |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))
        ≤ ∑' k : ℤ,
          ((∫ y in (0 : ℝ)..1,
              |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)))
            + (∫ y in (0 : ℝ)..1,
              |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))) :=
    hB.tsum_mono hfull (fun k => by
      have hleft : 0 ≤ ∫ y in (0 : ℝ)..1,
          |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)) :=
        intervalIntegral.integral_nonneg_of_forall (by norm_num)
          (fun y => mul_nonneg (abs_nonneg _) (heatKernel_nonneg ht _))
      exact le_add_of_nonneg_left hleft)
  calc
    (∑' k : ℤ, ∫ y in (0 : ℝ)..1,
        |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))
        ≤ ∑' k : ℤ,
          ((∫ y in (0 : ℝ)..1,
              |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)))
            + (∫ y in (0 : ℝ)..1,
              |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))) := hle
    _ = ∫ w : ℝ, |w| * heatKernel t w :=
      ShenWork.tsum_cell_integral_eq_integral (heatKernel_abs_mul_integrable ht) x
    _ = 4 * t / Real.sqrt (4 * Real.pi * t) :=
      ShenWork.IntervalSemigroupUniform.heatKernel_first_abs_moment ht

/-- Interior reflected mass is controlled by the whole-line first moment divided by
the interior distance to the absorbing endpoint. -/
theorem reflectedKernelPart_integral_le_first_abs_moment_div
    {t η x : ℝ} (ht : 0 < t) (hη0 : 0 < η)
    (hx : x ∈ Set.Icc η (1 - η)) :
    (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
      ≤ (4 * t / Real.sqrt (4 * Real.pi * t)) / η := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hmass := reflectedKernelPart_integral_summable ht x
  have hmoment := reflectedKernelPart_abs_moment_summable ht x
  have hcell : ∀ k : ℤ,
      (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))
        ≤ (1 / η) * (∫ y in (0 : ℝ)..1,
          |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ))) := by
    intro k
    have hhc : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
    have hBii : IntervalIntegrable
        (fun y : ℝ => heatKernel t (x + y + 2 * (k : ℝ))) volume 0 1 :=
      (hhc.comp (by fun_prop)).intervalIntegrable 0 1
    have hWii : IntervalIntegrable
        (fun y : ℝ => |x + y + 2 * (k : ℝ)| *
          heatKernel t (x + y + 2 * (k : ℝ))) volume 0 1 :=
      ((continuous_abs.comp (by fun_prop)).mul (hhc.comp (by fun_prop))).intervalIntegrable 0 1
    calc
      (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))
          ≤ ∫ y in (0 : ℝ)..1,
              (1 / η) * (|x + y + 2 * (k : ℝ)| *
                heatKernel t (x + y + 2 * (k : ℝ))) := by
        refine intervalIntegral.integral_mono_on h01 hBii (hWii.const_mul (1 / η))
          (fun y hy => ?_)
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, hy.2⟩
        have hdist := reflectedKernelPart_image_abs_ge hη0 hx hyIcc k
        have hcoeff : 1 ≤ (1 / η) * |x + y + 2 * (k : ℝ)| := by
          rw [one_div_mul_eq_div]
          exact (le_div_iff₀ hη0).mpr (by simpa using hdist)
        calc
          heatKernel t (x + y + 2 * (k : ℝ))
              = 1 * heatKernel t (x + y + 2 * (k : ℝ)) := by ring
          _ ≤ ((1 / η) * |x + y + 2 * (k : ℝ)|) *
                heatKernel t (x + y + 2 * (k : ℝ)) :=
              mul_le_mul_of_nonneg_right hcoeff (heatKernel_nonneg ht _)
          _ = (1 / η) * (|x + y + 2 * (k : ℝ)| *
                heatKernel t (x + y + 2 * (k : ℝ))) := by ring
      _ = (1 / η) * (∫ y in (0 : ℝ)..1,
          |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ))) := by
        rw [intervalIntegral.integral_const_mul]
  calc
    (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
        = ∑' k : ℤ, ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)) :=
      reflectedKernelPart_integral_eq_tsum ht x
    _ ≤ ∑' k : ℤ, (1 / η) * (∫ y in (0 : ℝ)..1,
          |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ))) :=
      hmass.tsum_mono (hmoment.mul_left (1 / η)) hcell
    _ = (1 / η) * (∑' k : ℤ, ∫ y in (0 : ℝ)..1,
          |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ))) := by
      rw [tsum_mul_left]
    _ ≤ (1 / η) * (4 * t / Real.sqrt (4 * Real.pi * t)) :=
      mul_le_mul_of_nonneg_left (reflectedKernelPart_abs_moment_tsum_le ht x) (by positivity)
    _ = (4 * t / Real.sqrt (4 * Real.pi * t)) / η := by
      rw [one_div_mul_eq_div]

/-- A square-root form of the interior reflected-mass bound. -/
theorem reflectedKernelPart_integral_le_two_sqrt_div
    {t η x : ℝ} (ht : 0 < t) (hη0 : 0 < η)
    (hx : x ∈ Set.Icc η (1 - η)) :
    (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
      ≤ (2 * Real.sqrt t) / η := by
  have hbase := reflectedKernelPart_integral_le_first_abs_moment_div ht hη0 hx
  have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
  have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by nlinarith [Real.pi_gt_three]
  have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
    have h4t_eq : (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
      have := Real.mul_self_sqrt ht.le
      nlinarith
    rw [show (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) from h4t_eq,
      Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
  have hmoment_le : 4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
    calc
      4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
        rw [hsqrt4t]
        nlinarith [Real.mul_self_sqrt ht.le]
      _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
  calc
    (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
        ≤ (4 * t / Real.sqrt (4 * Real.pi * t)) / η := hbase
    _ = (1 / η) * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
      rw [one_div_mul_eq_div]
    _ ≤ (1 / η) * (2 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hmoment_le (by positivity)
    _ = (2 * Real.sqrt t) / η := by
      rw [one_div_mul_eq_div]

/-- The reflected half-kernel mass tends to zero uniformly on every interior
strip away from the absorbing endpoints. -/
theorem reflectedKernelPart_integral_tendstoUniformlyOn_interior
    {η : ℝ} (hη0 : 0 < η) :
    TendstoUniformlyOn
      (fun t x : ℝ =>
        ∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y)
      (fun _ : ℝ => 0) (𝓝[>] (0 : ℝ)) (Set.Icc η (1 - η)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset]
  let δ : ℝ := (ε * η / 2) ^ 2
  have hδ_pos : 0 < δ := by positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro t htmem x hx
  rcases htmem with ⟨ht, htδ⟩
  have hmass_nonneg :
      0 ≤ ∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun y => reflectedKernelPart_nonneg ht x y)
  have hmass_le := reflectedKernelPart_integral_le_two_sqrt_div ht hη0 hx
  have htarget_nonneg : 0 ≤ ε * η / 2 := by positivity
  have hsqrt_bound : Real.sqrt t < ε * η / 2 := by
    rw [← Real.sqrt_sq htarget_nonneg]
    exact Real.sqrt_lt_sqrt ht.le htδ
  have hscaled : (2 * Real.sqrt t) / η < ε := by
    have hnum : 2 * Real.sqrt t < ε * η := by linarith
    rw [div_lt_iff₀ hη0]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  rw [Real.dist_eq]
  conv_lhs => rw [show (0 : ℝ) - (∫ y in (0 : ℝ)..1,
      intervalNeumannReflectedKernelPart t x y)
        = -(∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) by ring]
  rw [abs_neg, abs_of_nonneg hmass_nonneg]
  exact lt_of_le_of_lt hmass_le hscaled

/-- Continuity in the integration variable of the reflected half-kernel. -/
theorem continuousOn_reflectedKernelPart_snd {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (fun y : ℝ => intervalNeumannReflectedKernelPart t x y) (Set.Icc 0 1) := by
  have hh : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  have hsum : Summable (fun k : ℤ => heatKernelWindowBound t x 1 k) :=
    summable_heatKernelWindowBound ht x 1
  change ContinuousOn (fun y : ℝ => ∑' k : ℤ,
    heatKernel t (x + y + 2 * (k : ℝ))) (Set.Icc 0 1)
  refine continuousOn_tsum (fun k => (hh.comp (by fun_prop)).continuousOn) hsum
    (fun k y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht _)]
  exact heatKernel_le_windowShift ht x 1 k
    (by
      rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
      exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)

/-- Pointwise algebra: `-Ktilde = Kfull - 2 * reflectedHalf`. -/
theorem neg_conjugateKernel_eq_full_sub_two_reflected
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    -intervalNeumannConjugateKernel t x y =
      intervalNeumannFullKernel t x y - 2 * intervalNeumannReflectedKernelPart t x y := by
  have hA : Summable (fun k : ℤ => heatKernel t (x - y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x - y)
  have hB : Summable (fun k : ℤ => heatKernel t (x + y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x + y)
  rw [intervalNeumannConjugateKernel, intervalNeumannFullKernel,
    intervalNeumannReflectedKernelPart]
  rw [Summable.tsum_add hA.neg hB, Summable.tsum_add hA hB, tsum_neg]
  ring

/-- Algebraic mass-defect identity for the conjugate kernel. -/
theorem conjugateKernel_massDefect_eq_neg_two_reflectedMass
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (-(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) - 1)
      = -2 * (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hK_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannConjugateKernel t x y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_conjugateKernel_snd ht x
  have hF_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannFullKernel t x y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_intervalNeumannFullKernel_snd ht x
  have hR_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannReflectedKernelPart t x y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_reflectedKernelPart_snd ht x
  have hneg :
      (∫ y in (0 : ℝ)..1, -intervalNeumannConjugateKernel t x y)
        = -(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) := by
    rw [intervalIntegral.integral_neg]
  have hcongr :
      (∫ y in (0 : ℝ)..1, -intervalNeumannConjugateKernel t x y)
        = ∫ y in (0 : ℝ)..1,
          intervalNeumannFullKernel t x y - 2 * intervalNeumannReflectedKernelPart t x y := by
    apply intervalIntegral.integral_congr
    intro y _
    exact neg_conjugateKernel_eq_full_sub_two_reflected ht x y
  calc
    (-(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) - 1)
        = (∫ y in (0 : ℝ)..1, -intervalNeumannConjugateKernel t x y) - 1 := by
      rw [hneg]
    _ = (∫ y in (0 : ℝ)..1,
          intervalNeumannFullKernel t x y - 2 * intervalNeumannReflectedKernelPart t x y) - 1 := by
      rw [hcongr]
    _ = (∫ y in (0 : ℝ)..1, intervalNeumannFullKernel t x y)
          - 2 * (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) - 1 := by
      rw [intervalIntegral.integral_sub hF_int (hR_int.const_mul 2),
        intervalIntegral.integral_const_mul]
    _ = -2 * (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) := by
      rw [intervalNeumannFullKernel_integral_eq_one ht x]
      ring

end

end ShenWork.IntervalNeumannFullKernel
