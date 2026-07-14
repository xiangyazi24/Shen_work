import ShenWork.Paper3.IntervalDomainPersistenceGeneralMDini
import ShenWork.Paper3.IntervalDomainPersistenceElliptic
import ShenWork.Paper3.IntervalDomainPersistenceFaithfulUV

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

/-! Geometry and elliptic-transfer inputs for the faithful general-`m` branch. -/

theorem intervalDomainM_abs_lift_le_supNorm
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |intervalDomainLift (u t) y| ≤ intervalDomainSupNorm (u t) := by
  classical
  have hcont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u t x|)) := by
    obtain ⟨B, hB⟩ :=
      (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hBx := hB ⟨x.1, x.2, rfl⟩
    have hlift : intervalDomainLift (u t) x.1 = u t x := by
      simp [intervalDomainLift, x.2]
    simpa only [hlift] using hBx
  have hle : |u t ⟨y, hy⟩| ≤ intervalDomainSupNorm (u t) :=
    le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩
  simpa [intervalDomainLift, hy] using hle

theorem intervalDomainM_spatialMin_continuousOn
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 T : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hT0 : 0 < T0) (hT0T : T0 ≤ T) :
    ContinuousOn (intervalDomainSpatialMin u) (Set.Icc T0 T) := by
  have hTbig : 0 < T + 1 := by linarith
  have hclass := hsol.classical.classical (T := T + 1) hTbig
  have hsub : Set.Icc T0 T ⊆ Set.Ioo (0 : ℝ) (T + 1) := by
    intro s hs
    exact ⟨lt_of_lt_of_le hT0 hs.1, by linarith [hs.2]⟩
  have hsubprod : Set.Icc T0 T ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) (T + 1) ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hsub (le_refl _)
  obtain ⟨_, _, _, _, _, _, hField⟩ := hclass.regularity
  set F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y
  have hF : ContinuousOn (Function.uncurry F)
      (Set.Icc T0 T ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F] using hField.1.mono hsubprod
  have hm : ContinuousOn
      (fun t => sInf (F t '' Set.Icc (0 : ℝ) 1)) (Set.Icc T0 T) :=
    sliceMin_continuousOn hF
  refine hm.congr ?_
  intro t _ht
  simpa [F] using intervalDomainSpatialMin_eq_lift_sInf u t

theorem intervalDomainM_spatialMin_pos
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hT0 : 0 < T0) :
    0 < intervalDomainSpatialMin u T0 := by
  have hTbig : 0 < T0 + 1 := by linarith
  have hclass := hsol.classical.classical (T := T0 + 1) hTbig
  have hslice_cont : ContinuousOn (intervalDomainLift (u T0))
      (Set.Icc (0 : ℝ) 1) :=
    (hclass.regularity.2.2.2.2.1 T0 ⟨hT0, by linarith⟩).1.1.continuousOn
  have himg : IsCompact
      (intervalDomainLift (u T0) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice_cont
  have hne : (intervalDomainLift (u T0) '' Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨intervalDomainLift (u T0) 0,
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  obtain ⟨x0, hx0_mem, hx0_eq⟩ := himg.sInf_mem hne
  rw [intervalDomainSpatialMin_eq_lift_sInf, ← hx0_eq,
    intervalDomainLift, dif_pos hx0_mem]
  exact hclass.u_pos' hT0 (by linarith)

theorem intervalDomainM_infValue_isBoundedUnder
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    IsBoundedUnder GE.ge atTop
      (fun t => intervalDomainM.infValue (u t)) := by
  rcases hsol.bounded with ⟨M, hM⟩
  have hfloor : ∀ᶠ t in atTop, -M ≤ intervalDomainM.infValue (u t) := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with t hMt ht1
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hclass := hsol.classical.classical (T := t + 1) (by linarith)
    have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htpos, by linarith⟩
    change -M ≤ sInf (Set.range (u t))
    refine le_csInf ?_ ?_
    · exact ⟨u t ⟨0, ⟨le_rfl, zero_le_one⟩⟩,
        ⟨⟨0, ⟨le_rfl, zero_le_one⟩⟩, rfl⟩⟩
    · rintro y ⟨x, rfl⟩
      have habs : |u t x| ≤ M := by
        have hlift : intervalDomainLift (u t) x.1 = u t x := by
          simp [intervalDomainLift]
        have h := (intervalDomainM_abs_lift_le_supNorm hclass htmem x.2).trans hMt
        simpa [hlift] using h
      exact (abs_le.mp habs).1
  exact isBoundedUnder_of_eventually_ge hfloor

theorem intervalDomainM_infValue_isCoboundedUnder
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomainM.infValue (u t)) := by
  rcases hsol.bounded with ⟨M, hM⟩
  have hceil : ∀ᶠ t in atTop, intervalDomainM.infValue (u t) ≤ M := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with t hMt ht1
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hclass := hsol.classical.classical (T := t + 1) (by linarith)
    have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htpos, by linarith⟩
    let x0 : intervalDomain.Point := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    have hbound : ∀ x : intervalDomain.Point, |u t x| ≤ M := by
      intro x
      have hlift : intervalDomainLift (u t) x.1 = u t x := by
        simp [intervalDomainLift]
      have h := (intervalDomainM_abs_lift_le_supNorm hclass htmem x.2).trans hMt
      simpa [hlift] using h
    change sInf (Set.range (u t)) ≤ M
    have hbdd : BddBelow (Set.range (u t)) := by
      refine ⟨-M, ?_⟩
      rintro y ⟨x, rfl⟩
      exact (abs_le.mp (hbound x)).1
    exact (csInf_le hbdd ⟨x0, rfl⟩).trans (abs_le.mp (hbound x0)).2
  exact isCoboundedUnder_ge_of_eventually_le atTop hceil

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_spatialMin_continuousOn
#print axioms ShenWork.Paper3.intervalDomainM_abs_lift_le_supNorm
#print axioms ShenWork.Paper3.intervalDomainM_spatialMin_pos
#print axioms ShenWork.Paper3.intervalDomainM_infValue_isBoundedUnder
#print axioms ShenWork.Paper3.intervalDomainM_infValue_isCoboundedUnder
