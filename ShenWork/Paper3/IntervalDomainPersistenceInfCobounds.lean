import ShenWork.Paper3.IntervalDomainPersistenceLiminfBounds

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- A positive global bounded interval solution has an eventually upper-bounded
spatial infimum trajectory. -/
theorem intervalDomain_infValue_isCoboundedUnder_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (u t)) := by
  rcases hsol.bounded with ⟨M, hM⟩
  have hceil :
      ∀ᶠ t in atTop, intervalDomain.infValue (u t) ≤ M := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with t hMt ht1
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hTpos : 0 < t + 1 := by linarith
    have hclass := hsol.classical.classical (T := t + 1) hTpos
    have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := by
      exact ⟨htpos, by linarith⟩
    let x0 : intervalDomain.Point := ⟨0, by exact ⟨le_rfl, by norm_num⟩⟩
    have hbound : ∀ x : intervalDomain.Point, |u t x| ≤ M := by
      intro x
      have hlift : intervalDomainLift (u t) x.1 = u t x := by
        simp [intervalDomainLift]
      have h := (abs_lift_le_supNorm hclass htmem x.2).trans hMt
      simpa [hlift] using h
    change sInf (Set.range (u t)) ≤ M
    have hbdd : BddBelow (Set.range (u t)) := by
      refine ⟨-M, ?_⟩
      rintro y ⟨x, rfl⟩
      exact (abs_le.mp (hbound x)).1
    exact (csInf_le hbdd ⟨x0, rfl⟩).trans (abs_le.mp (hbound x0)).2
  exact isCoboundedUnder_ge_of_eventually_le atTop hceil

#print axioms intervalDomain_infValue_isCoboundedUnder_of_positiveGlobalBoundedSolution

end

end ShenWork.Paper3
