import ShenWork.Paper3.IntervalDomainPersistenceActualLinearCompactFamily

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_actualLinear_uniformTimeContinuity
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
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

#print axioms ShenWork.Paper3.intervalDomain_actualLinear_uniformTimeContinuity
