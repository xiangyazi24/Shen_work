/-
  ShenWork/PDE/IntervalFullKernelGradientLinfty.lean

  **Step 6.5b / 6.6 — the full-kernel gradient `L∞→L∞` estimate assembly.**

  Combines the summability + termwise-differentiation core
  (`IntervalNeumannFullKernel.lean`, Steps 6.1–6.5b-pre) with the real-space
  tiling (`IntervalFullKernelGradientTiling.lean`, Steps 1–5/5a) to produce the
  `t^(−1/2)`-integrable full-Neumann-kernel gradient bound, the prerequisite for
  wiring the full operator into the Duhamel `_clean` chain.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.IntervalFullKernelGradientTiling

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

/-- **Step 6.5b-1: cell-integral summability.**  The reflected+direct `[0,1]`
heat-gradient `L¹` masses are summable over the lattice.  Each pair equals the
mass over one period-`2` cell (`cell_integral_eq`), and the cell masses of the
integrable `|∂heat|` sum (countable additivity, `hasSum_integral_iUnion`). -/
theorem summable_cell_heatGrad_interval_integral {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ =>
        (∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
          + (∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|)) := by
  have hg : Integrable (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) w|) :=
    heatKernel_deriv_abs_integrable ht
  have hint : IntegrableOn (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) w|)
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

/-- Uniform majorant constant for the lattice gradient over a unit shift around
`x + 2k` (the lattice point seen as `y` ranges over a unit window). -/
noncomputable def heatGradUnitBound (t x : ℝ) (k : ℤ) : ℝ :=
  heatGradPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
    * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))

/-- The unit-window majorant is summable over the lattice (`latticeExpSummable (4t)`). -/
theorem summable_heatGradUnitBound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ => heatGradUnitBound t x k) := by
  have h4t : (0 : ℝ) < 4 * t := by linarith
  exact (latticeExpSummable h4t x).mul_left _

/-- **Uniform gradient bound over a unit window.**  Whenever the lattice argument
`w` lies within distance `1` of the centre `x + 2k`, the heat-gradient is bounded
by the summable constant `heatGradUnitBound t x k`.  Pointwise bound
`abs_deriv_heatKernel_le` + Young `(A+B)² ≥ ½A² − B²` (`B = w − (x+2k)`, `|B| ≤ 1`).
This is the uniform majorant feeding `continuousOn_tsum` on `[0,1]`. -/
theorem abs_deriv_heatKernel_le_unitShift {t : ℝ} (ht : 0 < t) (x : ℝ) (k : ℤ)
    {w : ℝ} (hw : |w - (x + 2 * (k : ℝ))| ≤ 1) :
    |deriv (fun z : ℝ => heatKernel t z) w| ≤ heatGradUnitBound t x k := by
  refine (abs_deriv_heatKernel_le ht w).trans ?_
  rw [heatGradUnitBound]
  have hP : (1 / 2) * (x + 2 * (k : ℝ)) ^ 2 - 1 ≤ w ^ 2 := by
    have hB : (w - (x + 2 * (k : ℝ))) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [hw, abs_nonneg (w - (x + 2 * (k : ℝ)))]
    nlinarith [sq_nonneg (2 * w - (x + 2 * (k : ℝ))), hB]
  have hexp : Real.exp (-w ^ 2 / (4 * (2 * t)))
      ≤ Real.exp (1 / (4 * (2 * t))) * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htne : t ≠ 0 := ne_of_gt ht
    have e1 : -w ^ 2 / (4 * (2 * t)) = (-2 * w ^ 2) / (4 * (4 * t)) := by
      field_simp
      ring
    have e2 : 1 / (4 * (2 * t)) + -(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))
        = (2 - (x + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by
      field_simp
      ring
    rw [e1, e2]
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * (4 * t))).mpr
    nlinarith [hP]
  calc heatGradPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t)))
      ≤ heatGradPointwiseBound t * (Real.exp (1 / (4 * (2 * t)))
          * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))) :=
        mul_le_mul_of_nonneg_left hexp (by unfold heatGradPointwiseBound; positivity)
    _ = heatGradPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
          * Real.exp (-(x + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by ring

end ShenWork.IntervalNeumannFullKernel
