import ShenWork.Paper3.IntervalDomainPersistenceGeneralMCompactFamily

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-! Regularity inputs for the faithful general-`m` compact-minimum theorem. -/

theorem intervalDomainM_generalM_uniformRightDerivLower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t ∈ Set.Ioi (0 : ℝ),
      UniformRightDerivLowerOnCompact (Set.Icc (0 : ℝ) 1)
        (intervalDomainActualLinearDanskinF u)
        (intervalDomainActualLinearDanskinFt u) t := by
  intro t ht eps heps
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
  have huc :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hdFc
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc eps heps with ⟨δ, hδ, hmod⟩
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), ?_⟩
  intro h hh0 hhη x hx
  have hhδ : h < δ := lt_of_lt_of_le hhη (min_le_left _ _)
  have hhhalf : h < 1 / 2 := lt_of_lt_of_le hhη (min_le_right _ _)
  have hFcont : ContinuousOn (Function.uncurry F)
      (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hField.1.mono ?_
    rintro ⟨s, y⟩ hsy
    exact ⟨⟨lt_of_lt_of_le htpos hsy.1.1,
      by linarith [hsy.1.2, hhhalf]⟩, hsy.2⟩
  have hslice_cont : ContinuousOn (fun r => F r x) (Set.Icc t (t + h)) := by
    have hmaps : Set.MapsTo (fun r : ℝ => (r, x)) (Set.Icc t (t + h))
        (Set.Icc t (t + h) ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun r hr => ⟨hr, hx⟩
    exact hFcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
  have hslice_diff : ∀ s ∈ Set.Ioo t (t + h),
      HasDerivAt (fun r => F r x) (deriv (fun r => F r x) s) s := by
    intro s hs
    have hsInt : s ∈ Set.Ioo (0 : ℝ) (t + 1) :=
      ⟨lt_trans htpos hs.1, by linarith [hs.2, hhhalf]⟩
    have hfun : (fun r => F r x) = fun r => u r ⟨x, hx⟩ := by
      funext r
      simp only [F, intervalDomainLift]
      rw [dif_pos hx]
    rw [hfun]
    exact ((hTime ⟨x, hx⟩ s hsInt).1.1).hasDerivAt
  obtain ⟨ξ, hξ, hξ_eq⟩ := exists_hasDerivAt_eq_slope
    (fun r => F r x) (deriv (fun r => F r x)) (by linarith : t < t + h)
    hslice_cont hslice_diff
  have hξK : (ξ, x) ∈ Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hξ.1.le, by linarith [hξ.2, hhhalf]⟩, hx⟩
  have htK : (t, x) ∈ Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨le_rfl, by linarith⟩, hx⟩
  have hdist : dist (t, x) (ξ, x) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self]
    rw [max_eq_left dist_nonneg]
    have : dist t ξ < δ := by
      rw [dist_comm, Real.dist_eq]
      have hξt : 0 < ξ - t := sub_pos.mpr hξ.1
      have hξh : ξ - t < h := by linarith [hξ.2]
      simpa [abs_of_pos hξt] using lt_trans hξh hhδ
    exact this
  have hclose := hmod (t, x) htK (ξ, x) hξK hdist
  have hlo : dF t x - eps ≤ dF ξ x := by
    have hlt : dF t x - dF ξ x < eps := by
      simpa [Function.uncurry, Real.dist_eq] using (abs_lt.mp hclose).2
    linarith
  have hquot : dF ξ x = (F (t + h) x - F t x) / h := by
    dsimp [dF]
    rw [hξ_eq]
    ring_nf
  have hpos_th : 0 < t + h := add_pos htpos hh0
  simpa [dF, F, intervalDomainActualLinearDanskinF,
    intervalDomainActualLinearDanskinFt, htpos, hpos_th, hquot] using hlo

theorem intervalDomainM_generalM_uniformTimeContinuity
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t ∈ Set.Ioi (0 : ℝ),
      UniformTimeContinuityOnCompact (Set.Icc (0 : ℝ) 1)
        (intervalDomainActualLinearDanskinF u) t := by
  intro t ht eps heps
  have htpos : 0 < t := ht
  have hTpos : 0 < t + 1 := by linarith
  have hclass := hsol.classical.classical (T := t + 1) hTpos
  obtain ⟨_, _, _, _, _, _, hField⟩ := hclass.regularity
  set F : ℝ → ℝ → ℝ := fun s x => intervalDomainLift (u s) x
  have hslab : Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) (t + 1) ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, x⟩ hsx
    exact ⟨⟨lt_of_lt_of_le htpos hsx.1.1, by linarith [hsx.1.2]⟩, hsx.2⟩
  have hF : ContinuousOn (Function.uncurry F)
      (Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hField.1.mono hslab
  have huc :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc eps heps with ⟨δ, hδ, hmod⟩
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), ?_⟩
  intro h hh0 hhη x hx
  have hhδ : h < δ := lt_of_lt_of_le hhη (min_le_left _ _)
  have hhhalf : h < 1 / 2 := lt_of_lt_of_le hhη (min_le_right _ _)
  have hp1 : (t + h, x) ∈
      Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨by linarith, by linarith⟩, hx⟩
  have hp0 : (t, x) ∈
      Set.Icc t (t + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨le_rfl, by linarith⟩, hx⟩
  have hdist : dist (t + h, x) (t, x) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self]
    rw [max_eq_left dist_nonneg]
    simpa [Real.dist_eq, abs_of_pos hh0] using hhδ
  have hlt := hmod (t + h, x) hp1 (t, x) hp0 hdist
  have hpos_th : 0 < t + h := add_pos htpos hh0
  have hle : |F (t + h) x - F t x| ≤ eps := by
    simpa [Function.uncurry, Real.dist_eq] using le_of_lt hlt
  simpa [F, intervalDomainActualLinearDanskinF, htpos, hpos_th] using hle

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_generalM_uniformRightDerivLower
#print axioms ShenWork.Paper3.intervalDomainM_generalM_uniformTimeContinuity
