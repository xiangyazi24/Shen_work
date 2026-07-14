/-
  Positive-floor persistence for faithful general-m interval solutions.
-/
import ShenWork.Paper2.IntervalDomainMBoundaryHamilton
import ShenWork.Paper2.IntervalDomainMinPersistCore

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMMinPersistence

private theorem abs_lift_le_supNorm_M
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
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

/-- At any closed-interval spatial minimizer, a faithful general-`m`
classical solution retains the positive linear reaction after the remaining
terms are bounded by a common slice ceiling. -/
theorem hbound_closed_M_allChi_with_growth
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_bd : ∀ y, |intervalDomainLift (u s) y| ≤ M)
    {ys : ℝ} (hys : ys ∈ Set.Icc (0 : ℝ) 1)
    (hargmin : intervalDomainLift (u s) ys =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    generalMMinGrowthRate p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) ys) s := by
  have hu_le : ∀ x : intervalDomainPoint, u s x ≤ M := by
    intro x
    have hx : |u s x| ≤ M := by
      simpa [intervalDomainLift, x.property] using hu_bd x.1
    exact (le_abs_self _).trans hx
  rcases eq_or_lt_of_le hys.1 with hy0 | hy0
  · subst ys
    exact hbdry_left_M_of_classicalSolution_with_growth
      hm hsol hs0 hsT hM hu_le hargmin
  · rcases eq_or_lt_of_le hys.2 with hy1 | hy1
    · subst ys
      exact hbdry_right_M_of_classicalSolution_with_growth
        hm hsol hs0 hsT hM hu_le hargmin
    · exact hbound_interior_M_allChi_with_growth
        hm hsol hs0 hsT hM hu_bd ⟨hy0, hy1⟩ hargmin

/-- Hamilton persistence from the regularity conjuncts of a faithful
general-`m` classical solution. -/
theorem solution_minPersist_M_of_conjuncts
    {p : CM2Params} {T a b Kp : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : 0 < a) (hbT : b < T) (hab : a ≤ b)
    (hbound : ∀ s ∈ Set.Icc a b, ∀ ys ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u s) ys =
          sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
        -Kp * sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
          deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∀ t ∈ Set.Icc a b, ∀ x : intervalDomainPoint,
      sInf (intervalDomainLift (u a) '' Set.Icc (0 : ℝ) 1) *
          Real.exp (-Kp * (t - a)) ≤ u t x := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hsubprod : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hsub (le_refl _)
  obtain ⟨_, h4, _, _, _, h8, h9⟩ := hsol.regularity
  have hF : ContinuousOn
      (Function.uncurry (fun t y => intervalDomainLift (u t) y))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := h9.1.mono hsubprod
  have hdF_cont : ContinuousOn
      (Function.uncurry
        (fun s y => deriv (fun r => intervalDomainLift (u r) y) s))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := h8.1.mono hsubprod
  have hslice_cont : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun r => intervalDomainLift (u r) y) (Set.Icc a b) := by
    intro y hy
    have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc a b)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := fun w hw => ⟨hw, hy⟩
    exact hF.comp (Continuous.continuousOn (by fun_prop)) hmaps
  have hslice_diff : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => intervalDomainLift (u r) y)
        (deriv (fun r => intervalDomainLift (u r) y) s) s := by
    intro y hy s hs
    have hsInt : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le ha0 hs.1.le, lt_of_lt_of_le hs.2 hbT.le⟩
    have hfun : (fun r => intervalDomainLift (u r) y) =
        fun r => u r ⟨y, hy⟩ := by
      funext r
      rw [intervalDomainLift, dif_pos hy]
    rw [hfun]
    obtain ⟨⟨hdU, _⟩, _, _⟩ := h4 ⟨y, hy⟩ s hsInt
    exact hdU.hasDerivAt
  exact ShenWork.MinPersistenceAtoms.solution_minPersist_core
    hF hslice_cont hslice_diff hdF_cont hbound

/-- The spatial minimum of a faithful classical solution is positive at every
positive interior time. -/
theorem sliceMin_M_pos_of_solution
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 < sInf (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1) := by
  have hslice_cont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) := by
    obtain ⟨_, _, _, _, h7, _, _⟩ := hsol.regularity
    exact (h7 t ⟨ht0, htT⟩).1.1.continuousOn
  have himg : IsCompact
      (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice_cont
  have hne : (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨intervalDomainLift (u t) 0,
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  obtain ⟨x0, hx0_mem, hx0_eq⟩ := himg.sInf_mem hne
  rw [← hx0_eq, intervalDomainLift, dif_pos hx0_mem]
  exact hsol.u_pos' ht0 htT

/-- A bounded faithful general-`m` solution with `m ≥ 1` has a uniform positive
floor on the terminal half of every finite horizon. -/
theorem minimumPersistenceM_of_bounded
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hbdd : IsPaper2BoundedBefore intervalDomainM T u) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t, T / 2 ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x := by
  obtain ⟨B, hB⟩ := hbdd
  let M : ℝ := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hSup : ∀ s ∈ Set.Ico (T / 2 / 2) T, ∀ y,
      |intervalDomainLift (u s) y| ≤ M := by
    intro s hs y
    have hquarter : 0 < T / 2 / 2 :=
      div_pos (div_pos hsol.T_pos (by norm_num)) (by norm_num)
    have hs0 : 0 < s := lt_of_lt_of_le hquarter hs.1
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have habs := abs_lift_le_supNorm_M hsol ⟨hs0, hs.2⟩ hy
      exact (habs.trans (hB s hs0 hs.2)).trans (le_max_left _ _)
    · simp [intervalDomainLift, hy, hM]
  have hbound : ∀ s ∈ Set.Ico (T / 2 / 2) T,
      ∀ ys ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (u s) ys =
            sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
          -generalMMinSlopeConst p M *
              sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
            deriv (fun r => intervalDomainLift (u r) ys) s := by
    intro s hs ys hys harg
    have hquarter : 0 < T / 2 / 2 :=
      div_pos (div_pos hsol.T_pos (by norm_num)) (by norm_num)
    have hs0 : 0 < s := lt_of_lt_of_le hquarter hs.1
    have hu_le : ∀ x : intervalDomainPoint, u s x ≤ M := by
      intro x
      have hx := hSup s hs x.1
      have hx' : |u s x| ≤ M := by
        simpa [intervalDomainLift, x.property] using hx
      exact (le_abs_self _).trans hx'
    rcases eq_or_lt_of_le hys.1 with hy0 | hy0
    · subst ys
      exact hbdry_left_M_of_classicalSolution
        hm hsol hs0 hs.2 hM hu_le harg
    · rcases eq_or_lt_of_le hys.2 with hy1 | hy1
      · subst ys
        exact hbdry_right_M_of_classicalSolution
          hm hsol hs0 hs.2 hM hu_le harg
      · exact hbound_interior_M_allChi
          hm hsol hs0 hs.2 hM (hSup s hs) ⟨hy0, hy1⟩ harg
  let Kp : ℝ := generalMMinSlopeConst p M
  have hKp : 0 ≤ Kp := by
    dsimp [Kp, generalMMinSlopeConst]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hM _)
          (ShenWork.MinPersistenceAtoms.fluxCoeffConst_nonneg p.hβ
            (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))))
      (mul_nonneg p.hb (Real.rpow_nonneg hM _))
  let a : ℝ := T / 2
  have ha0 : 0 < a := by dsimp [a]; linarith [hsol.T_pos]
  have haT : a < T := by dsimp [a]; linarith [hsol.T_pos]
  let m0 : ℝ :=
    sInf (intervalDomainLift (u a) '' Set.Icc (0 : ℝ) 1)
  have hm0 : 0 < m0 := sliceMin_M_pos_of_solution hsol ha0 haT
  refine ⟨m0 * Real.exp (-Kp * (T - a)), by positivity, ?_⟩
  intro t hta htT x
  have hpersist := solution_minPersist_M_of_conjuncts
    (a := a) (b := t) (Kp := Kp) hsol ha0 htT hta
    (fun s hs ys hys harg =>
      hbound s ⟨by
          have hquarter_le_half : T / 2 / 2 ≤ T / 2 := by
            linarith [hsol.T_pos]
          exact hquarter_le_half.trans (by simpa [a] using hs.1),
        lt_of_le_of_lt hs.2 htT⟩
        ys hys harg)
    t (Set.right_mem_Icc.mpr hta) x
  have hexp : Real.exp (-Kp * (T - a)) ≤
      Real.exp (-Kp * (t - a)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hKp]
  calc
    m0 * Real.exp (-Kp * (T - a)) ≤
        m0 * Real.exp (-Kp * (t - a)) :=
      mul_le_mul_of_nonneg_left hexp hm0.le
    _ ≤ u t x := hpersist

section AxiomAudit

#print axioms solution_minPersist_M_of_conjuncts
#print axioms sliceMin_M_pos_of_solution
#print axioms hbound_closed_M_allChi_with_growth
#print axioms minimumPersistenceM_of_bounded

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMMinPersistence
