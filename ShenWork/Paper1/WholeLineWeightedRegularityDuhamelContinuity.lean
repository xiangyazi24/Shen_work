import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Continuity of exact-weight Duhamel histories

The forcing trajectory in the weighted Henry argument is naturally only
strongly measurable in time, with a uniform `L²` bound on compact positive
windows.  Strong continuity of the heat semigroup is enough to make its
Duhamel history continuous.  In particular, no time continuity of the
weighted population derivative is used here.
-/

/-- Away from the totalization seam at lag zero, every orbit of the
totalized weighted heat semigroup is continuous. -/
theorem weightedMovingHeatL2Semigroup_orbit_continuousAt_of_ne_zero
    {eta c r : ℝ} (Z : WholeLineRealL2) (hr : r ≠ 0) :
    ContinuousAt
      (fun q : ℝ => weightedMovingHeatL2Semigroup eta c q Z) r := by
  rcases lt_or_gt_of_ne hr with hrneg | hrpos
  · have hevent : ∀ᶠ q : ℝ in 𝓝 r, q < 0 := Iio_mem_nhds hrneg
    have heq :
        (fun q : ℝ => weightedMovingHeatL2Semigroup eta c q Z) =ᶠ[𝓝 r]
          fun _ => 0 := by
      filter_upwards [hevent] with q hq
      simp only [weightedMovingHeatL2Semigroup, dif_neg (not_lt.mpr hq.le),
        if_neg (ne_of_lt hq), ContinuousLinearMap.zero_apply]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · exact (weightedMovingHeatL2Semigroup_orbit_hasDerivAt
      (eta := eta) (c := c) hrpos Z).continuousAt

/-- Uniform operator bound for the totalized weighted heat semigroup when
both time variables lie in one compact interval. -/
theorem weightedMovingHeatL2Semigroup_norm_apply_le_compact_lag
    {eta c L R r q : ℝ} (hLR : L ≤ R)
    (hr : r ∈ Set.Icc L R) (hq : q ∈ Set.Icc L R)
    (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Semigroup eta c (r - q) Z‖ ≤
      Real.exp (|eta ^ 2 - c * eta| * (R - L)) * ‖Z‖ := by
  by_cases hpos : 0 < r - q
  · calc
      ‖weightedMovingHeatL2Semigroup eta c (r - q) Z‖ ≤
          weightedMovingHeatGrowth eta c (r - q) * ‖Z‖ := by
        rw [weightedMovingHeatL2Semigroup_of_pos hpos]
        exact weightedMovingHeatL2Fun_norm_le hpos Z
      _ ≤ Real.exp (|eta ^ 2 - c * eta| * (R - L)) * ‖Z‖ := by
        gcongr
        unfold weightedMovingHeatGrowth
        apply Real.exp_le_exp.mpr
        calc
          (eta ^ 2 - c * eta) * (r - q) ≤
              |eta ^ 2 - c * eta| * (r - q) := by
            exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
          _ ≤ |eta ^ 2 - c * eta| * (R - L) := by
            exact mul_le_mul_of_nonneg_left
              (by linarith [hr.2, hq.1]) (abs_nonneg _)
  · rcases (not_lt.mp hpos).eq_or_lt with hzero | hneg
    · have hz : r - q = 0 := hzero
      rw [hz, weightedMovingHeatL2Semigroup_zero,
        ContinuousLinearMap.one_apply]
      have hK : (1 : ℝ) ≤
          Real.exp (|eta ^ 2 - c * eta| * (R - L)) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hLR)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hK (norm_nonneg Z)
    · have hne : r - q ≠ 0 := ne_of_lt hneg
      simp only [weightedMovingHeatL2Semigroup,
        dif_neg (not_lt.mpr hneg.le), if_neg hne,
        ContinuousLinearMap.zero_apply, norm_zero]
      exact mul_nonneg (Real.exp_nonneg _) (norm_nonneg Z)

/-- A strongly measurable, uniformly bounded `L²` forcing has a continuous
weighted-heat Duhamel trajectory at every interior time.  The apparent seam
at `q = t` is a singleton and is discarded by dominated convergence. -/
theorem weightedMovingHeatL2Semigroup_duhamel_continuousAt_of_uniform_norm_bound
    {eta c L R a t C : ℝ}
    (hLR : L < R) (ha : a ∈ Set.Ioo L R) (ht : t ∈ Set.Ioo L R)
    {F : ℝ → WholeLineRealL2}
    (hC : 0 ≤ C)
    (hFbound : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ C)
    (hhist_meas : ∀ r : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      (volume.restrict (Set.uIoc L R))) :
    ContinuousAt
      (fun r : ℝ => ∫ q in a..r,
        weightedMovingHeatL2Semigroup eta c (r - q) (F q)) t := by
  let K : ℝ := Real.exp (|eta ^ 2 - c * eta| * (R - L)) * C
  have hK0 : 0 ≤ K :=
    mul_nonneg (Real.exp_nonneg _) hC
  have hparam := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (μ := volume)
    (F := fun r q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
    (bound := fun _ => K) L R (a₀ := a) (b₀ := t) (x₀ := t)
    (fun r => hhist_meas r)
    (by
      have hrmem : ∀ᶠ r : ℝ in 𝓝 t, r ∈ Set.Icc L R :=
        mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
      filter_upwards [hrmem] with r hr
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with q hq
      have hqIcc : q ∈ Set.Icc L R := by
        rw [Set.uIoc_of_le hLR.le] at hq
        exact ⟨hq.1.le, hq.2⟩
      calc
        ‖weightedMovingHeatL2Semigroup eta c (r - q) (F q)‖ ≤
            Real.exp (|eta ^ 2 - c * eta| * (R - L)) * ‖F q‖ :=
          weightedMovingHeatL2Semigroup_norm_apply_le_compact_lag
            hLR.le hr hqIcc (F q)
        _ ≤ K := by
          dsimp only [K]
          exact mul_le_mul_of_nonneg_left (hFbound q hqIcc)
            (Real.exp_nonneg _))
    intervalIntegrable_const
    (by
      have hne : ∀ᵐ q ∂(volume.restrict (Set.uIoc L R)), q ≠ t :=
        (Measure.ae_ne volume t).filter_mono ae_restrict_le
      filter_upwards [hne] with q hqt
      have hlag : t - q ≠ 0 := sub_ne_zero.mpr hqt.symm
      exact
        ContinuousAt.comp (f := fun r : ℝ => r - q)
          (weightedMovingHeatL2Semigroup_orbit_continuousAt_of_ne_zero
            (F q) hlag)
          (continuousAt_id.sub continuousAt_const))
    ha ht (MeasureTheory.measure_singleton t)
  have hdiag : ContinuousAt (fun r : ℝ => (r, r)) t :=
    continuousAt_id.prodMk continuousAt_id
  have hcomp := ContinuousAt.comp
    (f := fun r : ℝ => (r, r)) hparam hdiag
  simpa only [Function.comp_apply] using hcomp

section AxiomAudit

#print axioms weightedMovingHeatL2Semigroup_orbit_continuousAt_of_ne_zero
#print axioms weightedMovingHeatL2Semigroup_norm_apply_le_compact_lag
#print axioms
  weightedMovingHeatL2Semigroup_duhamel_continuousAt_of_uniform_norm_bound

end AxiomAudit

end ShenWork.Paper1
