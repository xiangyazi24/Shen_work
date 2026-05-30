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

end ShenWork.IntervalNeumannFullKernel
