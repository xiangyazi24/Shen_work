import ShenWork.Paper3.IntervalDomainPersistenceGeneralMCompactFamily
import ShenWork.Paper3.IntervalDomainPersistenceSpatialMinContinuity
import ShenWork.Paper2.IntervalDomainSliceMinSlope
import Mathlib.Order.Filter.IsBounded

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

/-! Local boundedness of faithful general-`m` spatial-minimum difference quotients. -/

theorem intervalDomainM_spatialMin_slope_isBoundedUnder
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
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
    exact ⟨⟨lt_of_lt_of_le htpos hsy.1.1,
      by linarith [hsy.1.2, hh.2]⟩, hsy.2⟩
  have hslice_cont : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc t (t + h)) := by
    intro y hy
    have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc t (t + h))
        (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun r hr => ⟨hr, hy⟩
    exact hFcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
  have hslice_diff : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Ioo t (t + h),
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s := by
    intro y hy s hs
    have hsInt : s ∈ Set.Ioo (0 : ℝ) (t + 1) :=
      ⟨lt_trans htpos hs.1, by linarith [hs.2, hh.2]⟩
    have hfun : (fun r => F r y) = fun r => u r ⟨y, hy⟩ := by
      funext r
      simp only [F, intervalDomainLift]
      rw [dif_pos hy]
    rw [hfun]
    exact ((hTime ⟨y, hy⟩ s hsInt).1.1).hasDerivAt
  obtain ⟨ξ, hξ, xh, hxh, _, hslope⟩ :=
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

theorem intervalDomainM_spatialMin_slope_isCoboundedUnder
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t ∈ Set.Ioi (0 : ℝ),
      IsCoboundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h) := by
  intro t ht
  have htpos : 0 < t := ht
  have hTpos : 0 < t + 1 := by linarith
  have hclass := hsol.classical.classical (T := t + 1) hTpos
  obtain ⟨_, hTime, _, _, _, hJDt, hField⟩ := hclass.regularity
  set F : ℝ → ℝ → ℝ := fun s x => intervalDomainLift (u s) x
  set dF : ℝ → ℝ → ℝ := fun s x => deriv (fun r => F r x) s
  have hslab : Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) (t + 1) ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, x⟩ hsx
    exact ⟨⟨lt_of_lt_of_le htpos hsx.1.1, by linarith [hsx.1.2]⟩, hsx.2⟩
  have hdFc : ContinuousOn (Function.uncurry dF)
      (Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hJDt.1.mono hslab
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hdFc
  have H := intervalDomainM_generalM_compactMinFamily (p := p) (v := v) hsol
  rcases H.exists_min t with ⟨x0, hx0K, hx0eq⟩
  have hx0arg : F t x0 = intervalDomainSpatialMin u t := by
    simpa [F, intervalDomainActualLinearDanskinF, htpos] using hx0eq
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
  refine isCoboundedUnder_ge_of_eventually_le (𝓝[>] (0 : ℝ)) (x := M) ?_
  filter_upwards [hev] with h hh
  have hh0 : 0 < h := hh.1
  have hhhalf : h < 1 / 2 := hh.2
  have hFcont : ContinuousOn (Function.uncurry F)
      (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hField.1.mono ?_
    rintro ⟨s, y⟩ hsy
    exact ⟨⟨lt_of_lt_of_le htpos hsy.1.1,
      by linarith [hsy.1.2, hhhalf]⟩, hsy.2⟩
  have hslice_cont : ContinuousOn (fun r => F r x0) (Set.Icc t (t + h)) := by
    have hmaps : Set.MapsTo (fun r : ℝ => (r, x0)) (Set.Icc t (t + h))
        (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun r hr => ⟨hr, hx0K⟩
    exact hFcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
  have hslice_diff : ∀ s ∈ Set.Ioo t (t + h),
      HasDerivAt (fun r => F r x0) (deriv (fun r => F r x0) s) s := by
    intro s hs
    have hsInt : s ∈ Set.Ioo (0 : ℝ) (t + 1) :=
      ⟨lt_trans htpos hs.1, by linarith [hs.2, hhhalf]⟩
    have hfun : (fun r => F r x0) = fun r => u r ⟨x0, hx0K⟩ := by
      funext r
      simp only [F, intervalDomainLift]
      rw [dif_pos hx0K]
    rw [hfun]
    exact ((hTime ⟨x0, hx0K⟩ s hsInt).1.1).hasDerivAt
  obtain ⟨ξ, hξ, hξ_eq⟩ := exists_hasDerivAt_eq_slope
    (fun r => F r x0) (deriv (fun r => F r x0))
    (by linarith : t < t + h) hslice_cont hslice_diff
  have hξK : (ξ, x0) ∈ Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hξ.1.le, by linarith [hξ.2, hhhalf]⟩, hx0K⟩
  have hderiv_ub : deriv (fun r => F r x0) ξ ≤ M := by
    have hb := hM (ξ, x0) hξK
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).2
  have hslice_quot : (F (t + h) x0 - F t x0) / h ≤ M := by
    have hq : (F (t + h) x0 - F t x0) / h =
        deriv (fun r => F r x0) ξ := by
      rw [hξ_eq]
      ring_nf
    rw [hq]
    exact hderiv_ub
  have hpos_th : 0 < t + h := add_pos htpos hh0
  have hzle := H.z_le (t + h) x0 hx0K
  have hnum : intervalDomainSpatialMin u (t + h) -
      intervalDomainSpatialMin u t ≤ F (t + h) x0 - F t x0 := by
    have hzleF : intervalDomainSpatialMin u (t + h) ≤ F (t + h) x0 := by
      simpa [F, intervalDomainActualLinearDanskinF, hpos_th] using hzle
    rw [hx0arg]
    linarith
  exact (div_le_div_of_nonneg_right hnum hh0.le).trans hslice_quot

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_spatialMin_slope_isBoundedUnder
#print axioms ShenWork.Paper3.intervalDomainM_spatialMin_slope_isCoboundedUnder
