import ShenWork.Paper3.IntervalDomainPersistenceSpatialMinContinuity
import ShenWork.Paper2.IntervalDomainSliceMinSlope
import Mathlib.Order.Filter.IsBounded

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomainSpatialMin_slope_isBoundedUnder_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ t ∈ Set.Ioi (0 : ℝ),
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h) := by
  intro t ht
  have htpos : 0 < t := ht
  have hTpos : 0 < t + 1 := by linarith
  have hclass := hsol.classical.classical (T := t + 1) hTpos
  obtain ⟨_, hTime, _, _, _, hJDt, hField⟩ := hclass.regularity
  set F : ℝ → ℝ → ℝ := fun s y => intervalDomainLift (u s) y
  have hslab : Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) (t + 1) ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, y⟩ hsy
    exact ⟨⟨lt_of_lt_of_le htpos hsy.1.1, by linarith [hsy.1.2]⟩, hsy.2⟩
  have hdFc : ContinuousOn
      (Function.uncurry
        (fun s y => deriv (fun r => intervalDomainLift (u r) y) s))
      (Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hJDt.1.mono hslab
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hdFc
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
  refine isBoundedUnder_of_eventually_ge (a := -M) ?_
  filter_upwards [hev] with h hh
  have hh0 : 0 < h := hh.1
  have hhle : h ≤ 1 / 2 := hh.2.le
  have hFcont : ContinuousOn (Function.uncurry F)
      (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hField.1.mono ?_
    rintro ⟨s, y⟩ hsy
    exact ⟨⟨lt_of_lt_of_le htpos hsy.1.1, by linarith [hsy.1.2, hh.2]⟩, hsy.2⟩
  have hslice_cont : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc t (t + h)) := by
    intro y hy
    have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc t (t + h))
        (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) := fun r hr => ⟨hr, hy⟩
    exact hFcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
  have hslice_diff : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Ioo t (t + h),
      HasDerivAt (fun r => F r y)
        (deriv (fun r => F r y) s) s := by
    intro y hy s hs
    have hsInt : s ∈ Set.Ioo (0 : ℝ) (t + 1) :=
      ⟨lt_trans htpos hs.1, by linarith [hs.2, hh.2]⟩
    have hfun : (fun r => F r y) = fun r => u r ⟨y, hy⟩ := by
      funext r
      simp only [F, intervalDomainLift]
      rw [dif_pos hy]
    rw [hfun]
    exact ((hTime ⟨y, hy⟩ s hsInt).1.1).hasDerivAt
  obtain ⟨ξ, hξ, xh, hxh, harg, hslope⟩ :=
    sliceMin_diff_le_slope (F := F) (a := t) (b := t + h)
      (x := t) (z := t + h)
      (by exact ⟨by linarith, le_rfl⟩) (by exact ⟨le_rfl, by linarith⟩)
      (by linarith) hFcont hslice_cont hslice_diff
  have hξK : (ξ, xh) ∈ Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hξ.1.le, by linarith [hξ.2, hhle]⟩, hxh⟩
  have hderiv_lb : -M ≤ deriv (fun r => F r xh) ξ := by
    have hb := hM (ξ, xh) hξK
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).1
  have hm_t := (intervalDomainSpatialMin_eq_lift_sInf u t).symm
  have hm_th := (intervalDomainSpatialMin_eq_lift_sInf u (t + h)).symm
  rw [← hm_t, ← hm_th]
  have : -M * h ≤
      sInf (F (t + h) '' Set.Icc (0 : ℝ) 1) -
        sInf (F t '' Set.Icc (0 : ℝ) 1) := by
    nlinarith [hslope, hderiv_lb, hh0]
  exact (le_div_iff₀ hh0).mpr this

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainSpatialMin_slope_isBoundedUnder_of_positiveGlobalBoundedSolution
