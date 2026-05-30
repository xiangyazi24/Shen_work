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

/-- The heat-kernel spatial derivative `w ↦ ∂heat w` is continuous. -/
theorem continuous_deriv_heatKernel {t : ℝ} (ht : 0 < t) :
    Continuous (fun w : ℝ => deriv (fun z : ℝ => heatKernel t z) w) := by
  have heq : (fun w : ℝ => deriv (fun z : ℝ => heatKernel t z) w)
      = fun w : ℝ => -(w / (2 * t)) * heatKernel t w := by
    funext w; rw [deriv_heatKernel ht]
  rw [heq]; unfold heatKernel; fun_prop

/-- **Step 6.5b-2b: continuity of the full-kernel `x`-derivative in `y` on `[0,1]`.**
`y ↦ ∂ₓ K_full(t,x,y)` is continuous on `[0,1]`: by `hasDerivAt_intervalNeumann
FullKernel_fst` it is the sum of two lattice series, each continuous on the unit
window by `continuousOn_tsum` with the uniform majorant `heatGradUnitBound`. -/
theorem continuousOn_deriv_intervalNeumannFullKernel_fst {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (fun y : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x)
      (Set.Icc 0 1) := by
  have hcd := continuous_deriv_heatKernel ht
  have hfun : (fun y : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x)
      = fun y : ℝ => (∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))) := by
    funext y; exact (hasDerivAt_intervalNeumannFullKernel_fst ht x y).deriv
  rw [hfun]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatGradUnitBound ht x) (fun k y hy => ?_)
    rw [Real.norm_eq_abs]
    refine abs_deriv_heatKernel_le_unitShift ht x k ?_
    rw [show x - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = -y by ring, abs_neg]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatGradUnitBound ht x) (fun k y hy => ?_)
    rw [Real.norm_eq_abs]
    refine abs_deriv_heatKernel_le_unitShift ht x k ?_
    rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- The full-kernel `x`-derivative is interval-integrable in `y` on `[0,1]`. -/
theorem intervalIntegrable_deriv_intervalNeumannFullKernel_fst {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_deriv_intervalNeumannFullKernel_fst ht x

/-- **Step 6.5b: the full-kernel gradient `L¹` bound.**  The `[0,1]` mass of the
full-Neumann-kernel `x`-derivative is the envelope-integrable constant:

  `∫₀¹ |∂ₓ K_full(t,x,y)| dy ≤ (1/√π)·t^(−1/2)`.

Monotone bound by the dominating lattice series (`abs_deriv_intervalNeumannFull
Kernel_fst_le`), Tonelli interchange `∫₀¹ ∑ₖ = ∑ₖ ∫₀¹`
(`integral_tsum_of_summable_integral_norm`, summable cell masses), and the tiling
value `tsum_cell_heatGrad_abs_integral_eq`. -/
theorem intervalNeumannFullKernel_deriv_abs_interval_integral_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, |deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x|)
      ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * t ^ (-(1 / 2) : ℝ) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hcd := continuous_deriv_heatKernel ht
  have hAcont : ∀ k : ℤ,
      Continuous (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hBcont : ∀ k : ℤ,
      Continuous (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hAii : ∀ k : ℤ,
      IntervalIntegrable (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
        MeasureTheory.volume 0 1 := fun k => (hAcont k).intervalIntegrable 0 1
  have hBii : ∀ k : ℤ,
      IntervalIntegrable (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|)
        MeasureTheory.volume 0 1 := fun k => (hBcont k).intervalIntegrable 0 1
  set hk : ℤ → ℝ → ℝ := fun k y =>
    |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
      + |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))| with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y => by rw [hk_def]; positivity
  have hu2 : Summable (fun k : ℤ => 2 * heatGradUnitBound t x k) :=
    (summable_heatGradUnitBound ht x).mul_left 2
  have hk_bound : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 → ‖hk k y‖ ≤ 2 * heatGradUnitBound t x k := by
    intro k y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hk_nonneg k y)]
    have h1 := abs_deriv_heatKernel_le_unitShift ht x k (w := x - y + 2 * (k : ℝ))
      (by rw [show x - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = -y by ring, abs_neg]
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have h2 := abs_deriv_heatKernel_le_unitShift ht x k (w := x + y + 2 * (k : ℝ))
      (by rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    rw [hk_def]; linarith [h1, h2]
  have hDii : IntervalIntegrable (fun y : ℝ => ∑' k : ℤ, hk k y) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_tsum (fun k => ((hAcont k).add (hBcont k)).continuousOn) hu2 hk_bound
  -- Step 1: dominate by the lattice series.
  have hmono : (∫ y in (0 : ℝ)..1, |deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x|)
      ≤ ∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y := by
    refine intervalIntegral.integral_mono_on h01
      (intervalIntegrable_deriv_intervalNeumannFullKernel_fst ht x).abs hDii (fun y _ => ?_)
    rw [hk_def]
    exact abs_deriv_intervalNeumannFullKernel_fst_le ht x y
  refine hmono.trans (le_of_eq ?_)
  -- Step 2: Tonelli + the tiling value.
  have hμint : ∀ k : ℤ, Integrable (hk k) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    rw [hk_def]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp ((hAii k).add (hBii k))
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
            + (∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) := by
    intro k
    have e1 : (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ y in (0 : ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
    rw [e1]
    exact intervalIntegral.integral_add (hAii k) (hBii k)
  have hμsum : Summable
      (fun k : ℤ => ∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (summable_cell_heatGrad_interval_integral ht x).congr (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := hk) hμint hμsum
  calc (∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y)
      = ∫ y, (∑' k : ℤ, hk k y) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        intervalIntegral.integral_of_le h01
    _ = ∑' k : ℤ, ∫ y, hk k y ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
    _ = ∑' k : ℤ,
          ((∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
            + (∫ y in (0 : ℝ)..1, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|)) := by
        refine tsum_congr (fun k => ?_)
        rw [← intervalIntegral.integral_of_le h01]
        exact intervalIntegral.integral_add (hAii k) (hBii k)
    _ = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * t ^ (-(1 / 2) : ℝ) := ShenWork.tsum_cell_heatGrad_abs_integral_eq ht x

end ShenWork.IntervalNeumannFullKernel
