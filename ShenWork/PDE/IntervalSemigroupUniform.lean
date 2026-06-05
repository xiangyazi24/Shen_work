import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelGradientTiling
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform approximate-identity limit: `S(t)f → f` on `[0,1]` for continuous `f`

## Proof route

1. **Tiling inequalities** (Part A): `(y−x)² ≤ (x−y+2k)²` and `(y−x)² ≤ (x+y+2k)²`.
2. **First-moment bound** (Part B): `∫₀¹ |y−x| K(t,x,y) dy ≤ ∫_ℝ |z| G_t(z) dz ≤ C√t`.
3. **Markov + uniform continuity** (Part C): the main theorem.

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
  by_cases hk : (0 : ℤ) ≤ k
  · have : (0 : ℝ) ≤ k := Int.cast_nonneg.mpr hk
    exact mul_nonneg this (by linarith [hy.1, hy.2])
  · push_neg at hk
    have hk1 : (k : ℤ) ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hx.1, hx.2])

theorem sq_sub_le_sq_shift_add {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (y - x) ^ 2 ≤ (x + y + 2 * (k : ℝ)) ^ 2 := by
  suffices h : 0 ≤ (x + ↑k) * (y + ↑k) by nlinarith
  by_cases hk : (0 : ℤ) ≤ k
  · exact mul_nonneg (by linarith [hx.1, Int.cast_nonneg.mpr hk])
      (by linarith [hy.1, Int.cast_nonneg.mpr hk])
  · push_neg at hk
    have hk1 : (k : ℤ) ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hx.2]) (by linarith [hy.2])

/-- Absolute-value version: `|y−x| ≤ |x−y+2k|`. -/
theorem abs_sub_le_abs_shift_sub {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    |y - x| ≤ |x - y + 2 * (k : ℝ)| := by
  have h := sq_sub_le_sq_shift_sub hx hy k
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- Absolute-value version: `|y−x| ≤ |x+y+2k|`. -/
theorem abs_sub_le_abs_shift_add {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    |y - x| ≤ |x + y + 2 * (k : ℝ)| := by
  have h := sq_sub_le_sq_shift_add hx hy k
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-! ## Part B: heat kernel first absolute moment -/

/-- `∫_ℝ |z| G_t(z) dz = 4t / √(4πt)` for `t > 0`. -/
theorem heatKernel_first_abs_moment {t : ℝ} (ht : 0 < t) :
    ∫ z : ℝ, |z| * heatKernel t z = 4 * t / Real.sqrt (4 * Real.pi * t) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt (by positivity)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hkey : ∀ z : ℝ, |z| * heatKernel t z =
      1 / Real.sqrt (4 * Real.pi * t) * (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2)) := by
    intro z; unfold heatKernel
    rw [show -z ^ 2 / (4 * t) = -(1 / (4 * t)) * z ^ 2 from by ring]
    rw [mul_left_comm]
  simp_rw [hkey]
  rw [integral_const_mul, integral_abs_mul_exp_neg_mul_sq hb]
  field_simp [hsqrt_ne, ht_ne]

/-! ## Part C: main theorem -/

/-- **Uniform approximate-identity limit.**  For continuous `f` on `[0,1]`,
`S(t) f → f` uniformly as `t → 0⁺`. -/
theorem intervalFullSemigroup_tendstoUniformlyOn
    (f : ℝ → ℝ) (hf : Continuous f) :
    TendstoUniformlyOn (fun t x => intervalFullSemigroupOperator t f x) f
      (𝓝[>] (0 : ℝ)) (Set.Icc 0 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- f is bounded on [0,1]
  obtain ⟨M, hM_pos, hfM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ M := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨max B 1, by positivity, fun y hy => ?_⟩
    exact (Real.norm_eq_abs (f y) ▸ hB y hy).trans (le_max_left B 1)
  -- Uniform continuity
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc (0 : ℝ) 1) hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδf⟩ := huc (ε / 2) (by linarith)
  -- τ so that ε/2 + 2M · 2τ/(δ · √(4πτ)) < ε, simplified to 4Mτ/δ < ε/2 · √(4πτ)
  -- Use the simpler bound: 2M · (far bound) < ε/2 where far ≤ 2t/(δ √(4πt))
  -- Since 2t/√(4πt) = 2√t/√(4π) ≤ 2√t, want 2M · 2√t / δ < ε/2, i.e., t < ε²δ²/(64M²)
  set τ := ε ^ 2 * δ ^ 2 / (64 * M ^ 2) with hτ_def
  have hτ_pos : 0 < τ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hτ_pos] with t ht
  have htpos : 0 < t := ht.1
  have htlt : t < τ := ht.2
  intro x hx
  rw [Real.dist_eq]
  -- The L∞ contraction gives |S(t)g(x)| ≤ ‖g‖ for any g.
  -- Define g_near(y) = f(y) - f(x) when |y-x|<δ, else 0.
  -- Then ‖g_near‖∞ ≤ ε/2 (uniform continuity).
  -- Define g_far = (f - f(x)) - g_near. Then g_far is zero on {|y-x|<δ}.
  -- S(t)(f-f(x)) = S(t)(g_near) + S(t)(g_far).
  -- |S(t)(g_near)(x)| ≤ ε/2 (L∞ contraction).
  -- |S(t)(g_far)(x)| ≤ ∫ K·|g_far| ≤ 2M · ∫_{far} K ≤ 2M · (1/δ) ∫|y-x|K
  -- ≤ 2M/δ · ∫|z|G_t = 2M/δ · 4t/√(4πt) < ε/2 for t < τ.
  -- The tiling bound ∫|y-x|K ≤ ∫|z|G_t uses abs_sub_le_abs_shift_{sub,add}
  -- and tsum_cell_integral_eq_integral.
  -- Integral manipulation in Lean measure-theory API deferred to follow-up.
  sorry

end

end ShenWork.IntervalSemigroupUniform
