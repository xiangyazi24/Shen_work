import ShenWork.PDE.IntervalSemigroupUniform

/-!
# A uniform approximate identity for a Hölder family

The Neumann heat semigroup converges to the identity uniformly not only for a
single continuous function, but for any family with a common Hölder modulus.
This is the homogeneous term needed in time-translate compactness arguments.
-/

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupHolderFamilyApprox

noncomputable section

open scoped Real

set_option maxHeartbeats 400000 in
theorem intervalFullSemigroup_eventually_uniform_family_of_holder
    {ι : Type*} (f : ι → ℝ → ℝ) (G : ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Set.Icc (0 : ℝ) 1))
    (hholder : ∀ i x, x ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, y ∈ Set.Icc (0 : ℝ) 1 →
        |f i y - f i x| ≤ G * Real.sqrt |y - x|) :
    ∀ ε > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ i x, x ∈ Set.Icc (0 : ℝ) 1 →
        dist (intervalFullSemigroupOperator t (f i) x) (f i x) < ε := by
  intro ε hε
  set C := G ^ 2 / (2 * ε) + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ G ^ 2 / (2 * ε) := div_nonneg (sq_nonneg G) (by positivity)
    dsimp [C]
    linarith
  have hlinmod : ∀ i x, x ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, y ∈ Set.Icc (0 : ℝ) 1 →
        |f i y - f i x| ≤ ε / 2 + C * |y - x| := by
    intro i x hx y hy
    have hr : 0 ≤ |y - x| := abs_nonneg _
    have hsqrt : 0 ≤ Real.sqrt |y - x| := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt |y - x|) ^ 2 = |y - x| :=
      Real.sq_sqrt hr
    have hsq : 0 ≤ (G * Real.sqrt |y - x| - ε) ^ 2 := sq_nonneg _
    have hyoung :
        G * Real.sqrt |y - x| ≤
          ε / 2 + (G ^ 2 / (2 * ε)) * |y - x| := by
      have hD_mul : (G ^ 2 / (2 * ε)) * (2 * ε) = G ^ 2 := by
        field_simp
      nlinarith
    calc
      |f i y - f i x| ≤ G * Real.sqrt |y - x| := hholder i x hx y hy
      _ ≤ ε / 2 + (G ^ 2 / (2 * ε)) * |y - x| := hyoung
      _ ≤ ε / 2 + C * |y - x| := by
        have hcoef : G ^ 2 / (2 * ε) ≤ C := by
          change G ^ 2 / (2 * ε) ≤ G ^ 2 / (2 * ε) + 1
          linarith
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hcoef hr) (ε / 2)
  set τ := (ε / (4 * C)) ^ 2
  have hτ_pos : 0 < τ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hτ_pos] with t ht
  intro i x hx
  have ht_pos : 0 < t := ht.1
  have ht_lt : t < τ := ht.2
  rw [Real.dist_eq, abs_sub_comm]
  have hmass := intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht_pos x
  have hKnn : ∀ y, 0 ≤ intervalNeumannFullKernel t x y :=
    fun y => intervalNeumannFullKernel_nonneg ht_pos x y
  have hKint := intervalNeumannFullKernel_integrable ht_pos x
  have hKf_int : Integrable
      (fun y => intervalNeumannFullKernel t x y * f i y)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact ((continuousOn_intervalNeumannFullKernel_snd ht_pos x).mul
      (hf i)).integrableOn_Icc
  have hfx_K_int : Integrable
      (fun y => f i x * intervalNeumannFullKernel t x y)
      (intervalMeasure 1) := hKint.const_mul (f i x)
  have hrewrite : f i x - intervalFullSemigroupOperator t (f i) x =
      ∫ y, intervalNeumannFullKernel t x y * (f i x - f i y)
        ∂(intervalMeasure 1) := by
    unfold intervalFullSemigroupOperator
    have h1 : f i x =
        ∫ y, f i x * intervalNeumannFullKernel t x y
          ∂(intervalMeasure 1) := by
      rw [MeasureTheory.integral_const_mul, hmass, mul_one]
    conv_lhs => rw [h1]
    rw [← MeasureTheory.integral_sub hfx_K_int hKf_int]
    congr 1
    ext y
    ring
  have hKmod_int : Integrable
      (fun y => intervalNeumannFullKernel t x y *
        (ε / 2 + C * |y - x|)) (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact ((continuousOn_intervalNeumannFullKernel_snd ht_pos x).mul
      ((continuous_const.add (continuous_const.mul
        (continuous_abs.comp
          (continuous_id.sub continuous_const)))).continuousOn)).integrableOn_Icc
  have hKabs_int : Integrable
      (fun y => intervalNeumannFullKernel t x y * |y - x|)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact ((continuousOn_intervalNeumannFullKernel_snd ht_pos x).mul
      ((continuous_abs.comp
        (continuous_id.sub continuous_const)).continuousOn)).integrableOn_Icc
  have habs_bound :
      |∫ y, intervalNeumannFullKernel t x y * (f i x - f i y)
          ∂(intervalMeasure 1)| ≤
        ∫ y, intervalNeumannFullKernel t x y * |f i x - f i y|
          ∂(intervalMeasure 1) := by
    calc
      |∫ y, intervalNeumannFullKernel t x y * (f i x - f i y)
          ∂(intervalMeasure 1)| =
          ‖∫ y, intervalNeumannFullKernel t x y * (f i x - f i y)
            ∂(intervalMeasure 1)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ y, ‖intervalNeumannFullKernel t x y * (f i x - f i y)‖
          ∂(intervalMeasure 1) := norm_integral_le_integral_norm _
      _ = ∫ y, intervalNeumannFullKernel t x y * |f i x - f i y|
          ∂(intervalMeasure 1) := by
        congr 1
        ext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnn y)]
  have hmod_bound :
      (∫ y, intervalNeumannFullKernel t x y * |f i x - f i y|
          ∂(intervalMeasure 1)) ≤
        ∫ y, intervalNeumannFullKernel t x y *
          (ε / 2 + C * |y - x|) ∂(intervalMeasure 1) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y =>
        mul_nonneg (hKnn y) (abs_nonneg _)
    · exact hKmod_int
    · simp only [intervalMeasure, intervalSet]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact mul_le_mul_of_nonneg_left
        (abs_sub_comm (f i x) (f i y) ▸ hlinmod i x hx y hy) (hKnn y)
  have hsplit :
      (∫ y, intervalNeumannFullKernel t x y *
          (ε / 2 + C * |y - x|) ∂(intervalMeasure 1)) =
        ε / 2 + C *
          ∫ y, intervalNeumannFullKernel t x y * |y - x|
            ∂(intervalMeasure 1) := by
    conv_lhs => rw [show
      (fun y => intervalNeumannFullKernel t x y *
        (ε / 2 + C * |y - x|)) =
      (fun y => ε / 2 * intervalNeumannFullKernel t x y +
        C * (intervalNeumannFullKernel t x y * |y - x|)) from by
          ext y
          ring]
    rw [MeasureTheory.integral_add (hKint.const_mul (ε / 2))
      (hKabs_int.const_mul C), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, hmass, mul_one]
  have hmoment_bound :
      (∫ y, intervalNeumannFullKernel t x y * |y - x|
          ∂(intervalMeasure 1)) ≤
        4 * t / Real.sqrt (4 * Real.pi * t) := by
    have hconv :
        (∫ y, intervalNeumannFullKernel t x y * |y - x|
            ∂(intervalMeasure 1)) =
          ∫ y in (0 : ℝ)..1,
            |y - x| * intervalNeumannFullKernel t x y := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp only [intervalMeasure, intervalSet]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      congr 1
      ext y
      ring
    rw [hconv]
    exact
      ShenWork.IntervalSemigroupUniform.intervalNeumannFullKernel_abs_moment_le
        ht_pos x hx
  have htail_bound :
      C * (4 * t / Real.sqrt (4 * Real.pi * t)) < ε / 2 := by
    have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
    have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by
      nlinarith [Real.pi_gt_three]
    have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      have h4t_eq : (4 : ℝ) * t =
          (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
        have := Real.mul_self_sqrt ht_pos.le
        nlinarith
      rw [h4t_eq, Real.sqrt_mul_self
        (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
    have hmoment_le :
        4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
      calc
        4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
          rw [hsqrt4t]
          nlinarith [Real.mul_self_sqrt ht_pos.le]
        _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
    have hsqrt_bound : Real.sqrt t < ε / (4 * C) := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ε / (4 * C) by positivity)]
      exact Real.sqrt_lt_sqrt ht_pos.le ht_lt
    calc
      C * (4 * t / Real.sqrt (4 * Real.pi * t)) ≤
          C * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hmoment_le hC_pos.le
      _ < C * (2 * (ε / (4 * C))) :=
        mul_lt_mul_of_pos_left (by linarith) hC_pos
      _ = ε / 2 := by field_simp; ring
  calc
    |f i x - intervalFullSemigroupOperator t (f i) x| =
        |∫ y, intervalNeumannFullKernel t x y * (f i x - f i y)
          ∂(intervalMeasure 1)| := by rw [hrewrite]
    _ ≤ ∫ y, intervalNeumannFullKernel t x y * |f i x - f i y|
        ∂(intervalMeasure 1) := habs_bound
    _ ≤ ∫ y, intervalNeumannFullKernel t x y *
        (ε / 2 + C * |y - x|) ∂(intervalMeasure 1) := hmod_bound
    _ = ε / 2 + C *
        ∫ y, intervalNeumannFullKernel t x y * |y - x|
          ∂(intervalMeasure 1) := hsplit
    _ ≤ ε / 2 + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
      linarith [mul_le_mul_of_nonneg_left hmoment_bound hC_pos.le]
    _ < ε := by linarith

end

end ShenWork.IntervalSemigroupHolderFamilyApprox

#print axioms
  ShenWork.IntervalSemigroupHolderFamilyApprox.intervalFullSemigroup_eventually_uniform_family_of_holder
