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

/-! ### Step 4: per-cell change of variables.

The two `[0,1]` images `y ↦ x−y+2k` and `y ↦ x+y+2k` fill the cell
`Ioc (x+2k−1) (x+2k+1)`. -/

/-- **Per-cell change of variables.**  The reflected and direct `[0,1]` images
assemble to the integral over one period-`2` cell centered at `x+2k`. -/
theorem cell_integral_eq {g : ℝ → ℝ} (hg : MeasureTheory.Integrable g) (x : ℝ) (k : ℤ) :
    (∫ y in (0 : ℝ)..1, g (x - y + 2 * (k : ℝ)))
        + (∫ y in (0 : ℝ)..1, g (x + y + 2 * (k : ℝ)))
      = ∫ y in Set.Ioc (x + 2 * (k : ℝ) - 1) (x + 2 * (k : ℝ) + 1), g y := by
  -- reflected image: `g (x - y + 2k) = g ((x+2k) - y)`, then `integral_comp_sub_left`.
  have hcov1 : (∫ y in (0 : ℝ)..1, g (x - y + 2 * (k : ℝ)))
      = ∫ y in (x + 2 * (k : ℝ) - 1)..(x + 2 * (k : ℝ)), g y := by
    rw [show (∫ y in (0 : ℝ)..1, g (x - y + 2 * (k : ℝ)))
          = ∫ y in (0 : ℝ)..1, g ((x + 2 * (k : ℝ)) - y) from by
        apply intervalIntegral.integral_congr; intro y _; congr 1; ring,
      intervalIntegral.integral_comp_sub_left g (x + 2 * (k : ℝ))]
    simp only [sub_zero]
  -- direct image: `g (x + y + 2k) = g ((x+2k) + y)`, then `integral_comp_add_left`.
  have hcov2 : (∫ y in (0 : ℝ)..1, g (x + y + 2 * (k : ℝ)))
      = ∫ y in (x + 2 * (k : ℝ))..(x + 2 * (k : ℝ) + 1), g y := by
    rw [show (∫ y in (0 : ℝ)..1, g (x + y + 2 * (k : ℝ)))
          = ∫ y in (0 : ℝ)..1, g ((x + 2 * (k : ℝ)) + y) from by
        apply intervalIntegral.integral_congr; intro y _; congr 1; ring,
      intervalIntegral.integral_comp_add_left g (x + 2 * (k : ℝ))]
    simp only [add_zero]
  rw [hcov1, hcov2,
    intervalIntegral.integral_add_adjacent_intervals
      hg.intervalIntegrable hg.intervalIntegrable,
    intervalIntegral.integral_of_le (by linarith)]

/-- **Step 5: kernel-shaped tiling.**  Summing the reflected+direct `[0,1]`
images over all lattice cells recovers the full-line integral of any integrable
`g`. -/
theorem tsum_cell_integral_eq_integral {g : ℝ → ℝ} (hg : MeasureTheory.Integrable g) (x : ℝ) :
    (∑' k : ℤ,
        ((∫ y in (0 : ℝ)..1, g (x - y + 2 * (k : ℝ)))
          + (∫ y in (0 : ℝ)..1, g (x + y + 2 * (k : ℝ)))))
      = ∫ w : ℝ, g w := by
  rw [integral_eq_tsum_integral_Ioc_offset (x - 1) hg]
  refine tsum_congr (fun k => ?_)
  rw [cell_integral_eq hg x k]
  congr 1 <;> ring

/-- **Step 5′ (kernel-shaped tiling applied to `|heat'|`).**  The lattice sum of
the reflected+direct `[0,1]` heat-gradient `L¹` masses equals the full-line
heat-gradient `L¹` norm, in `t^(−1/2)` form:

  `∑ₖ [∫₀¹|∂ₓheat(x−y+2k)| + ∫₀¹|∂ₓheat(x+y+2k)|] = (1/√π)·t^(−1/2)`.

Step 5 (`tsum_cell_integral_eq_integral`) with `g = |∂ₓheat|`
(integrable by `heatKernel_deriv_abs_integrable`) followed by Step 1
(`heatKernel_deriv_abs_integral_sqrt_form`).  This is the exact constant the
full-kernel gradient `L¹` integrand is to be bounded by. -/
theorem tsum_cell_heatGrad_abs_integral_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∑' k : ℤ,
        ((∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
          + (∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|)))
      = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * t ^ (-(1 / 2) : ℝ) := by
  rw [tsum_cell_integral_eq_integral (heatKernel_deriv_abs_integrable ht) x,
    heatKernel_deriv_abs_integral_sqrt_form ht]

end ShenWork
