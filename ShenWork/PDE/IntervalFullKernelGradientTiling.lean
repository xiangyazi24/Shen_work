/-
  ShenWork/PDE/IntervalFullKernelGradientTiling.lean

  **Toward the full-kernel gradient L∞→L∞ estimate (ROUND-17 route).**

  The full Neumann semigroup gradient bound
  `|deriv (intervalFullSemigroupOperator t f) x| ≤ (1/√π) t^(−1/2) ‖f‖∞`
  requires the real-space method-of-images tiling — there is no spectral
  shortcut (spectral gives non-integrable `1/t`).  This file builds the tiling
  in small, independently-verified steps.

  Step 1 (this commit): the heat-gradient L¹ norm in `t^(−1/2)` form (the power
  the Duhamel envelope needs), restating the existing closed form
  `∫_ℝ |∂ₓ heat(t,·)| = 2/√(4πt)`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.HeatKernelGradientEstimates

open MeasureTheory
open scoped Topology

namespace ShenWork

open ShenWork.IntervalDomain

/-- **Heat-gradient `L¹` norm in `t^(−1/2)` form.**  `∫_ℝ |∂ₓ heat(t,·)|` equals
`heatGradientLinftyLinftyConstant · t^(−1/2)` (`= (1/√π) t^(−1/2)`), the
envelope-integrable power.  Restates `heatKernel_deriv_abs_integral` (`= 2/√(4πt)`). -/
theorem heatKernel_deriv_abs_integral_sqrt_form {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, |deriv (fun z : ℝ => heatKernel t z) x|
      = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * t ^ (-(1 / 2) : ℝ) := by
  rw [heatKernel_deriv_abs_integral ht]
  unfold ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  -- `√(4πt) = 2 · √π · √t`.
  have hsqrt : Real.sqrt (4 * Real.pi * t) = 2 * (Real.sqrt Real.pi * Real.sqrt t) := by
    rw [show (4 * Real.pi * t : ℝ) = (2 : ℝ) ^ 2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul hpi]
  -- `t^(−1/2) = (√t)⁻¹`.
  have hrpow : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  rw [hsqrt, hrpow]
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hst : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  field_simp

/-! ### Step 2: the period-`2` cell partition of `ℝ`.

The half-open cells `Ioc (2k) (2k+2)`, `k ∈ ℤ`, partition `ℝ` — they cover it
and are pairwise disjoint.  This is the index family for the tiling
`∫_ℝ G = ∑ₖ ∫_{cell k} G`. -/

/-- The period-`2` half-open cells with offset `a` cover `ℝ`. -/
theorem iUnion_Ioc_offset_eq_univ (a : ℝ) :
    ⋃ k : ℤ, Set.Ioc (a + 2 * (k : ℝ)) (a + 2 * (k : ℝ) + 2) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  rw [Set.mem_iUnion]
  refine ⟨⌈(w - a) / 2⌉ - 1, ?_⟩
  have h1 : (⌈(w - a) / 2⌉ : ℝ) < (w - a) / 2 + 1 := Int.ceil_lt_add_one ((w - a) / 2)
  have h2 : ((w - a) / 2 : ℝ) ≤ (⌈(w - a) / 2⌉ : ℝ) := Int.le_ceil ((w - a) / 2)
  rw [Set.mem_Ioc]
  push_cast
  constructor <;> linarith

/-- The period-`2` half-open cells with offset `a` are pairwise disjoint. -/
theorem pairwise_disjoint_Ioc_offset (a : ℝ) :
    Pairwise (Function.onFun Disjoint
      (fun k : ℤ => Set.Ioc (a + 2 * (k : ℝ)) (a + 2 * (k : ℝ) + 2))) := by
  intro i j hij
  simp only [Function.onFun, Set.disjoint_left, Set.mem_Ioc]
  rintro w ⟨hwi_lo, hwi_hi⟩ ⟨hwj_lo, hwj_hi⟩
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith
  · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith

/-- **Step 3: tiling integral split (arbitrary offset).**  For an integrable
`G : ℝ → ℝ`, the full-line integral is the sum of the integrals over the
period-`2` cells with any offset `a`. -/
theorem integral_eq_tsum_integral_Ioc_offset (a : ℝ)
    {G : ℝ → ℝ} (hG : MeasureTheory.Integrable G) :
    ∫ w : ℝ, G w
      = ∑' k : ℤ, ∫ w in Set.Ioc (a + 2 * (k : ℝ)) (a + 2 * (k : ℝ) + 2), G w := by
  have hmeas : ∀ k : ℤ,
      MeasurableSet (Set.Ioc (a + 2 * (k : ℝ)) (a + 2 * (k : ℝ) + 2)) :=
    fun _ => measurableSet_Ioc
  have hint_univ : MeasureTheory.IntegrableOn G
      (⋃ k : ℤ, Set.Ioc (a + 2 * (k : ℝ)) (a + 2 * (k : ℝ) + 2)) := by
    rw [iUnion_Ioc_offset_eq_univ]; exact hG.integrableOn
  rw [← MeasureTheory.setIntegral_univ, ← iUnion_Ioc_offset_eq_univ a]
  exact MeasureTheory.integral_iUnion hmeas (pairwise_disjoint_Ioc_offset a) hint_univ

end ShenWork
