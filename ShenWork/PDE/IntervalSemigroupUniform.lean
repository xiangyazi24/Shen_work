import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelGradientTiling
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform approximate-identity limit: `S(t)f → f` on `[0,1]` for continuous `f`

No `sorry`/`admit`/custom axiom.
-/

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupUniform

noncomputable section

open scoped Real

/-! ## Part A: tiling inequalities -/

theorem sq_sub_le_sq_shift_sub {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (y - x) ^ 2 ≤ (x - y + 2 * (k : ℝ)) ^ 2 := by
  suffices h : 0 ≤ (↑k : ℝ) * (↑k + x - y) by nlinarith
  by_cases hk1 : (1 : ℤ) ≤ k
  · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    exact mul_nonneg (by linarith) (by linarith [hx.1, hy.2])
  · by_cases hkn : k ≤ (-1 : ℤ)
    · have hknr : (k : ℝ) ≤ -1 := by exact_mod_cast hkn
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hx.2, hy.1])
    · push_neg at hk1 hkn; interval_cases k; simp

theorem sq_sub_le_sq_shift_add {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (y - x) ^ 2 ≤ (x + y + 2 * (k : ℝ)) ^ 2 := by
  suffices h : 0 ≤ (x + ↑k) * (y + ↑k) by nlinarith
  by_cases hk : (0 : ℤ) ≤ k
  · have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    exact mul_nonneg (by linarith [hx.1]) (by linarith [hy.1])
  · push_neg at hk
    have hk1 : (k : ℤ) ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hx.2]) (by linarith [hy.2])

theorem abs_sub_le_abs_shift_sub {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    |y - x| ≤ |x - y + 2 * (k : ℝ)| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_sub_le_sq_shift_sub hx hy k)

theorem abs_sub_le_abs_shift_add {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    |y - x| ≤ |x + y + 2 * (k : ℝ)| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_sub_le_sq_shift_add hx hy k)

/-! ## Part B: heat kernel first absolute moment -/

theorem heatKernel_first_abs_moment {t : ℝ} (ht : 0 < t) :
    ∫ z : ℝ, |z| * heatKernel t z = 4 * t / Real.sqrt (4 * Real.pi * t) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt (by positivity)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hkey : ∀ z : ℝ, |z| * heatKernel t z =
      1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2)) := by
    intro z; unfold heatKernel
    rw [show -z ^ 2 / (4 * t) = -(1 / (4 * t)) * z ^ 2 from by ring]
    rw [mul_left_comm]
  simp_rw [hkey]
  rw [integral_const_mul, integral_abs_mul_exp_neg_mul_sq hb]
  field_simp [hsqrt_ne, ht_ne]

/-! ## Part C: first-moment tiling bound -/

private theorem abs_mul_heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℝ => |z| * heatKernel t z) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hfun : (fun z : ℝ => |z| * heatKernel t z) =
      fun z => 1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2)) := by
    ext z; unfold heatKernel
    rw [show -z ^ 2 / (4 * t) = -(1 / (4 * t)) * z ^ 2 from by ring]; ring
  have habs : (fun z : ℝ =>
      1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2))) =
      fun z => 1 / Real.sqrt (4 * Real.pi * t) *
        ‖z * Real.exp (-(1 / (4 * t)) * z ^ 2)‖ := by
    ext z; congr 1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun, habs]; exact (integrable_mul_exp_neg_mul_sq hb).norm.const_mul _

private theorem summable_cell_abs_shift {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
      (∫ y in (0 : ℝ)..1,
        |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)))
      + (∫ y in (0 : ℝ)..1,
        |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ)))) := by
  have hg := abs_mul_heatKernel_integrable ht
  have hint : IntegrableOn (fun w : ℝ => |w| * heatKernel t w)
      (⋃ k : ℤ, Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)) := by
    rw [ShenWork.iUnion_Ioc_offset_eq_univ]; exact hg.integrableOn
  exact (hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ioc)
    (ShenWork.pairwise_disjoint_Ioc_offset (x - 1)) hint).summable.congr (fun k => by
      have hset : Set.Ioc ((x - 1) + 2 * (k : ℝ)) ((x - 1) + 2 * (k : ℝ) + 2)
          = Set.Ioc (x + 2 * (k : ℝ) - 1) (x + 2 * (k : ℝ) + 1) := by congr 1 <;> ring
      rw [hset]; exact (ShenWork.cell_integral_eq hg x k).symm)

private theorem summable_cell_abs_moment {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun k : ℤ =>
      (∫ y in (0 : ℝ)..1, |y - x| * heatKernel t (x - y + 2 * (k : ℝ)))
      + (∫ y in (0 : ℝ)..1, |y - x| * heatKernel t (x + y + 2 * (k : ℝ)))) := by
  have hhc : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  refine (summable_cell_abs_shift ht x).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · exact add_nonneg
      (intervalIntegral.integral_nonneg_of_forall (by norm_num)
        (fun y => mul_nonneg (abs_nonneg _) (heatKernel_nonneg ht _)))
      (intervalIntegral.integral_nonneg_of_forall (by norm_num)
        (fun y => mul_nonneg (abs_nonneg _) (heatKernel_nonneg ht _)))
  · apply add_le_add
    · exact intervalIntegral.integral_mono_on (by norm_num)
        (((continuous_abs.comp (continuous_id.sub continuous_const)).mul
          (hhc.comp ((continuous_const.sub continuous_id).add continuous_const))).intervalIntegrable 0 1)
        (((continuous_abs.comp ((continuous_const.sub continuous_id).add continuous_const)).mul
          (hhc.comp ((continuous_const.sub continuous_id).add continuous_const))).intervalIntegrable 0 1)
        (fun y hy => mul_le_mul_of_nonneg_right (abs_sub_le_abs_shift_sub hx ⟨hy.1, hy.2⟩ k) (heatKernel_nonneg ht _))
    · exact intervalIntegral.integral_mono_on (by norm_num)
        (((continuous_abs.comp (continuous_id.sub continuous_const)).mul
          (hhc.comp ((continuous_const.add continuous_id).add continuous_const))).intervalIntegrable 0 1)
        (((continuous_abs.comp ((continuous_const.add continuous_id).add continuous_const)).mul
          (hhc.comp ((continuous_const.add continuous_id).add continuous_const))).intervalIntegrable 0 1)
        (fun y hy => mul_le_mul_of_nonneg_right (abs_sub_le_abs_shift_add hx ⟨hy.1, hy.2⟩ k) (heatKernel_nonneg ht _))

set_option maxHeartbeats 800000 in
theorem intervalNeumannFullKernel_abs_moment_le {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ y in (0 : ℝ)..1, |y - x| * intervalNeumannFullKernel t x y ≤
      4 * t / Real.sqrt (4 * Real.pi * t) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hg := abs_mul_heatKernel_integrable ht
  have hhc : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  set hk : ℤ → ℝ → ℝ := fun k y =>
    |y - x| * (heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)))
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y =>
    mul_nonneg (abs_nonneg _) (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
  have hAii : ∀ k : ℤ, IntervalIntegrable
      (fun y : ℝ => |y - x| * heatKernel t (x - y + 2 * (k : ℝ))) volume 0 1 := fun k =>
    ((continuous_abs.comp (continuous_id.sub continuous_const)).mul
      (hhc.comp ((continuous_const.sub continuous_id).add continuous_const))).intervalIntegrable 0 1
  have hBii : ∀ k : ℤ, IntervalIntegrable
      (fun y : ℝ => |y - x| * heatKernel t (x + y + 2 * (k : ℝ))) volume 0 1 := fun k =>
    ((continuous_abs.comp (continuous_id.sub continuous_const)).mul
      (hhc.comp ((continuous_const.add continuous_id).add continuous_const))).intervalIntegrable 0 1
  have hμint : ∀ k : ℤ, Integrable (hk k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp
      (((hAii k).add (hBii k)).congr (fun y _ => by simp [hk]; ring))
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = (∫ y in (0 : ℝ)..1, |y - x| * heatKernel t (x - y + 2 * (k : ℝ)))
        + (∫ y in (0 : ℝ)..1, |y - x| * heatKernel t (x + y + 2 * (k : ℝ))) := by
    intro k
    have e1 : (∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ y in (0 : ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
        Real.norm_of_nonneg (hk_nonneg k y))
    rw [e1]
    show (∫ y in (0 : ℝ)..1, |y - x| *
        (heatKernel t (x - y + 2 * ↑k) + heatKernel t (x + y + 2 * ↑k))) = _
    rw [show (fun y : ℝ => |y - x| * (heatKernel t (x - y + 2 * ↑k) +
          heatKernel t (x + y + 2 * ↑k)))
        = (fun y : ℝ => |y - x| * heatKernel t (x - y + 2 * ↑k) +
            |y - x| * heatKernel t (x + y + 2 * ↑k)) from by ext y; ring]
    exact intervalIntegral.integral_add (hAii k) (hBii k)
  have hμsum : Summable (fun k : ℤ =>
      ∫ y, ‖hk k y‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (summable_cell_abs_moment ht x hx).congr (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := hk) hμint hμsum
  have hKeq : (fun y : ℝ => |y - x| * intervalNeumannFullKernel t x y)
      = fun y => ∑' k : ℤ, hk k y := by
    ext y; simp only [hk]; rw [intervalNeumannFullKernel, ← tsum_mul_left]
  have hA'ii : ∀ k : ℤ, IntervalIntegrable
      (fun y : ℝ => |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ))) volume 0 1 := fun k =>
    ((continuous_abs.comp ((continuous_const.sub continuous_id).add continuous_const)).mul
      (hhc.comp ((continuous_const.sub continuous_id).add continuous_const))).intervalIntegrable 0 1
  have hB'ii : ∀ k : ℤ, IntervalIntegrable
      (fun y : ℝ => |x + y + 2 * (k : ℝ)| * heatKernel t (x + y + 2 * (k : ℝ))) volume 0 1 := fun k =>
    ((continuous_abs.comp ((continuous_const.add continuous_id).add continuous_const)).mul
      (hhc.comp ((continuous_const.add continuous_id).add continuous_const))).intervalIntegrable 0 1
  calc ∫ y in (0 : ℝ)..1, |y - x| * intervalNeumannFullKernel t x y
      = ∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y := by rw [hKeq]
    _ = ∫ y, (∑' k : ℤ, hk k y) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        intervalIntegral.integral_of_le h01
    _ = ∑' k : ℤ, ∫ y, hk k y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
    _ = ∑' k : ℤ,
        ((∫ y in (0 : ℝ)..1, |y - x| * heatKernel t (x - y + 2 * (k : ℝ)))
          + (∫ y in (0 : ℝ)..1, |y - x| * heatKernel t (x + y + 2 * (k : ℝ)))) := by
        refine tsum_congr (fun k => ?_)
        rw [← intervalIntegral.integral_of_le h01]
        show (∫ y in (0 : ℝ)..1, |y - x| * (heatKernel t (x - y + 2 * ↑k) +
            heatKernel t (x + y + 2 * ↑k))) = _
        rw [show (fun y : ℝ => |y - x| * (heatKernel t (x - y + 2 * ↑k) +
              heatKernel t (x + y + 2 * ↑k)))
            = (fun y : ℝ => |y - x| * heatKernel t (x - y + 2 * ↑k) +
                |y - x| * heatKernel t (x + y + 2 * ↑k)) from by ext y; ring]
        exact intervalIntegral.integral_add (hAii k) (hBii k)
    _ ≤ ∑' k : ℤ,
        ((∫ y in (0 : ℝ)..1, |x - y + 2 * (k : ℝ)| * heatKernel t (x - y + 2 * (k : ℝ)))
          + (∫ y in (0 : ℝ)..1, |x + y + 2 * (k : ℝ)| *
              heatKernel t (x + y + 2 * (k : ℝ)))) :=
        (summable_cell_abs_moment ht x hx).tsum_mono (summable_cell_abs_shift ht x) (fun k =>
          add_le_add
            (intervalIntegral.integral_mono_on (by norm_num) (hAii k) (hA'ii k) (fun y hy =>
              mul_le_mul_of_nonneg_right (abs_sub_le_abs_shift_sub hx ⟨hy.1, hy.2⟩ k) (heatKernel_nonneg ht _)))
            (intervalIntegral.integral_mono_on (by norm_num) (hBii k) (hB'ii k) (fun y hy =>
              mul_le_mul_of_nonneg_right (abs_sub_le_abs_shift_add hx ⟨hy.1, hy.2⟩ k) (heatKernel_nonneg ht _))))
    _ = ∫ w : ℝ, |w| * heatKernel t w := ShenWork.tsum_cell_integral_eq_integral hg x
    _ = 4 * t / Real.sqrt (4 * Real.pi * t) := heatKernel_first_abs_moment ht

/-! ## Part D: main theorem -/

set_option maxHeartbeats 400000 in
theorem intervalFullSemigroup_tendstoUniformlyOn
    (f : ℝ → ℝ) (hf : Continuous f) :
    TendstoUniformlyOn (fun t x => intervalFullSemigroupOperator t f x) f
      (𝓝[>] (0 : ℝ)) (Set.Icc 0 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM_pos, hfM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ M := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨max B 1, by positivity, fun y hy => ?_⟩
    exact (Real.norm_eq_abs (f y) ▸ hB y hy).trans (le_max_left B 1)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc (0 : ℝ) 1) hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδf⟩ := huc (ε / 2) (by linarith)
  set C := 2 * M / δ
  have hC_pos : 0 < C := by positivity
  have hlinmod : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f y - f x| ≤ ε / 2 + C * |y - x| := by
    intro x hx y hy
    by_cases hclose : dist y x < δ
    · have h1 := hδf y hy x hx hclose
      rw [Real.dist_eq] at h1
      linarith [mul_nonneg hC_pos.le (abs_nonneg (y - x))]
    · push_neg at hclose
      have hyx : δ ≤ |y - x| := by rwa [Real.dist_eq] at hclose
      have hab : |f y - f x| ≤ 2 * M := by
        have hfy := abs_le.mp (hfM y hy)
        have hfx := abs_le.mp (hfM x hx)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      linarith [mul_le_mul_of_nonneg_left hyx hC_pos.le,
        show C * δ = 2 * M by simp [C]; field_simp]
  set τ := (ε / (4 * C)) ^ 2
  have hτ_pos : 0 < τ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hτ_pos] with t ht
  intro x hx
  have ht_pos : 0 < t := ht.1
  have ht_lt : t < τ := ht.2
  rw [Real.dist_eq]
  have hmass := intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht_pos x
  have hKnn : ∀ y, 0 ≤ intervalNeumannFullKernel t x y :=
    fun y => intervalNeumannFullKernel_nonneg ht_pos x y
  have hKint := intervalNeumannFullKernel_integrable ht_pos x
  have hKf_int : Integrable (fun y => intervalNeumannFullKernel t x y * f y)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact ((continuousOn_intervalNeumannFullKernel_snd ht_pos x).mul hf.continuousOn).integrableOn_Icc
  have hfx_K_int : Integrable (fun y => f x * intervalNeumannFullKernel t x y)
      (intervalMeasure 1) := hKint.const_mul (f x)
  have hrewrite : f x - intervalFullSemigroupOperator t f x =
      ∫ y, intervalNeumannFullKernel t x y * (f x - f y) ∂(intervalMeasure 1) := by
    unfold intervalFullSemigroupOperator
    have h1 : f x = ∫ y, f x * intervalNeumannFullKernel t x y ∂(intervalMeasure 1) := by
      rw [MeasureTheory.integral_const_mul, hmass, mul_one]
    conv_lhs => rw [h1]
    rw [← MeasureTheory.integral_sub hfx_K_int hKf_int]
    congr 1; ext y; ring
  have hKmod_int : Integrable (fun y => intervalNeumannFullKernel t x y * (ε / 2 + C * |y - x|))
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact ((continuousOn_intervalNeumannFullKernel_snd ht_pos x).mul
      ((continuous_const.add (continuous_const.mul
        (continuous_abs.comp (continuous_id.sub continuous_const)))).continuousOn)).integrableOn_Icc
  have hKabs_int : Integrable (fun y => intervalNeumannFullKernel t x y * |y - x|)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact ((continuousOn_intervalNeumannFullKernel_snd ht_pos x).mul
      ((continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn)).integrableOn_Icc
  -- Assemble the bound
  have habs_bound :
      |∫ y, intervalNeumannFullKernel t x y * (f x - f y) ∂(intervalMeasure 1)| ≤
      ∫ y, intervalNeumannFullKernel t x y * |f x - f y| ∂(intervalMeasure 1) := by
    calc |∫ y, intervalNeumannFullKernel t x y * (f x - f y) ∂(intervalMeasure 1)|
        = ‖∫ y, intervalNeumannFullKernel t x y * (f x - f y) ∂(intervalMeasure 1)‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ ∫ y, ‖intervalNeumannFullKernel t x y * (f x - f y)‖ ∂(intervalMeasure 1) :=
          norm_integral_le_integral_norm _
      _ = ∫ y, intervalNeumannFullKernel t x y * |f x - f y| ∂(intervalMeasure 1) := by
          congr 1; ext y; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnn y)]
  have hmod_bound :
      ∫ y, intervalNeumannFullKernel t x y * |f x - f y| ∂(intervalMeasure 1) ≤
      ∫ y, intervalNeumannFullKernel t x y * (ε / 2 + C * |y - x|) ∂(intervalMeasure 1) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y => mul_nonneg (hKnn y) (abs_nonneg _)
    · exact hKmod_int
    · simp only [intervalMeasure, intervalSet]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact mul_le_mul_of_nonneg_left (abs_sub_comm (f x) (f y) ▸ hlinmod x hx y hy) (hKnn y)
  have hsplit :
      ∫ y, intervalNeumannFullKernel t x y * (ε / 2 + C * |y - x|) ∂(intervalMeasure 1) =
      ε / 2 + C * ∫ y, intervalNeumannFullKernel t x y * |y - x| ∂(intervalMeasure 1) := by
    conv_lhs => rw [show (fun y => intervalNeumannFullKernel t x y *
        (ε / 2 + C * |y - x|)) = (fun y => ε / 2 * intervalNeumannFullKernel t x y +
          C * (intervalNeumannFullKernel t x y * |y - x|)) from by ext y; ring]
    rw [MeasureTheory.integral_add (hKint.const_mul (ε / 2)) (hKabs_int.const_mul C),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hmass, mul_one]
  have hmoment_bound :
      ∫ y, intervalNeumannFullKernel t x y * |y - x| ∂(intervalMeasure 1) ≤
      4 * t / Real.sqrt (4 * Real.pi * t) := by
    have hconv : ∫ y, intervalNeumannFullKernel t x y * |y - x| ∂(intervalMeasure 1) =
        ∫ y in (0 : ℝ)..1, |y - x| * intervalNeumannFullKernel t x y := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp only [intervalMeasure, intervalSet]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      congr 1; ext y; ring
    rw [hconv]; exact intervalNeumannFullKernel_abs_moment_le ht_pos x hx
  have htail_bound : C * (4 * t / Real.sqrt (4 * Real.pi * t)) < ε / 2 := by
    have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
    have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by nlinarith [Real.pi_gt_three]
    have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      have h4t_eq : (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
        have := Real.mul_self_sqrt ht_pos.le; nlinarith
      rw [show (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) from h4t_eq,
        Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
    have hmoment_le : 4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
      calc 4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
              rw [hsqrt4t]; nlinarith [Real.mul_self_sqrt ht_pos.le]
        _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
    have hsqrt_bound : Real.sqrt t < ε / (4 * C) := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ε / (4 * C) by positivity)]
      exact Real.sqrt_lt_sqrt ht_pos.le ht_lt
    calc C * (4 * t / Real.sqrt (4 * Real.pi * t))
        ≤ C * (2 * Real.sqrt t) := mul_le_mul_of_nonneg_left hmoment_le hC_pos.le
      _ < C * (2 * (ε / (4 * C))) := mul_lt_mul_of_pos_left (by linarith) hC_pos
      _ = ε / 2 := by field_simp; ring
  -- Final assembly
  calc |f x - intervalFullSemigroupOperator t f x|
      = |∫ y, intervalNeumannFullKernel t x y * (f x - f y) ∂(intervalMeasure 1)| := by
          rw [hrewrite]
    _ ≤ ∫ y, intervalNeumannFullKernel t x y * |f x - f y| ∂(intervalMeasure 1) := habs_bound
    _ ≤ ∫ y, intervalNeumannFullKernel t x y * (ε / 2 + C * |y - x|) ∂(intervalMeasure 1) := hmod_bound
    _ = ε / 2 + C * ∫ y, intervalNeumannFullKernel t x y * |y - x| ∂(intervalMeasure 1) := hsplit
    _ ≤ ε / 2 + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
          linarith [mul_le_mul_of_nonneg_left hmoment_bound hC_pos.le]
    _ < ε := by linarith

end

end ShenWork.IntervalSemigroupUniform
