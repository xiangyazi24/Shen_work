import ShenWork.Paper1.WholeLineWeightedRegularityLeftTailBarrierNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# The patched lower barrier at zero sensitivity

When `p.χ = 0`, the paper and divergence-form frozen wave operators agree
for every pair of profiles.  Consequently the patched lower barrier is a
subsolution away from its `C¹` splice without any wave-trap hypothesis on the
frozen population profile.
-/

/-- At zero sensitivity the paper and frozen wave operators agree off the
diagonal as well as on it. -/
theorem paperWaveOperator_eq_frozenWaveOperator_of_chi_zero
    (p : CMParams) {c : ℝ} {u W : ℝ → ℝ} (hχ : p.χ = 0) :
    paperWaveOperator p c u W = frozenWaveOperator p c u W := by
  funext x
  simp [paperWaveOperator, frozenWaveOperator, hχ]

/-- For zero sensitivity, the patched lower barrier is a paper subsolution
away from its `C¹` splice.  Only boundedness and nonnegativity of the frozen
profile are used on the constant branch; no wave trap is required. -/
theorem paperWaveOperator_lowerBarrierPlateau_nonneg_chi_zero_away
    (p : CMParams) {c M κ κtilde D : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau κ κtilde D x ≤
      constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : IsCUnifBdd u) (hu0 : ∀ x, 0 ≤ u x)
    {x : ℝ} (hx : x ≠ lowerBarrierXPlus κ κtilde D) :
    0 ≤ paperWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x := by
  have hDold :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D := by
    simpa [hχ, paperDMin, subsolutionDThreshold, paperSpeedDenominator] using hD
  rcases lt_or_gt_of_ne hx with hxlt | hxgt
  · let d := lowerBarrierRaw κ κtilde D
        (lowerBarrierXPlus κ κtilde D)
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
    have hd0 : 0 < d := by
      dsimp [d]
      exact lowerBarrierRaw_pos_at_xplus hcond.hκ0
        (sub_pos.mpr hcond.hgap) hDpos
    have hd : d ≤ constantSubsolutionThreshold p.χ κ κtilde D := by
      simpa [d, lowerBarrierPlateau_eq_const_of_le
        (le_refl (lowerBarrierXPlus κ κtilde D))] using
          hplateau (lowerBarrierXPlus κ κtilde D)
    have hconst := constant_subsolution_frozenWaveOperator_nonneg_of_chi_zero
      p (c := c) (u := u) ( κ := κ) (κtilde := κtilde) (D := D)
        hχ hd0 hd hu hu0 x (Set.mem_univ x)
    have heq := lowerBarrierPlateau_eventuallyEq_const_of_lt hxlt
    have hval : lowerBarrierPlateau κ κtilde D x = d := by
      rw [lowerBarrierPlateau_eq_const_of_le hxlt.le]
    have hderiv : deriv (lowerBarrierPlateau κ κtilde D) x = 0 := by
      rw [heq.deriv_eq]
      simp
    have hderiv2 : iteratedDeriv 2 (lowerBarrierPlateau κ κtilde D) x = 0 := by
      rw [heq.iteratedDeriv_eq 2]
      simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
        ite_false]
    have hconst2 : iteratedDeriv 2 (fun _ : ℝ => d) x = 0 := by
      simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
        ite_false]
    have hopEq :
        paperWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x =
          paperWaveOperator p c u (fun _ => d) x := by
      unfold paperWaveOperator
      dsimp only
      rw [hval, hderiv, hderiv2, hconst2]
      simp
    rw [hopEq, paperWaveOperator_eq_frozenWaveOperator_of_chi_zero p hχ]
    exact hconst
  · have hregion : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D) := by
      exact lt_trans
        (lowerBarrierXMinus_lt_xplus hcond.hκ0
          (sub_pos.mpr hcond.hgap) (lt_of_lt_of_le zero_lt_one hD1)) hxgt
    have hraw :=
      lowerBarrierRaw_frozenSubSolution_chi_zero_of_threshold_of_D_ge_one
        p (u := u) hχ hcond.hκ0 hcond.hκ1 hcond.hgap hcond.hrange
          hD1 hcond.hc hDold x hregion
    have heq := lowerBarrierPlateau_eventuallyEq_raw_of_gt hxgt
    have hval : lowerBarrierPlateau κ κtilde D x =
        lowerBarrierRaw κ κtilde D x :=
      lowerBarrierPlateau_eq_raw_of_xplus_lt hxgt
    have hderiv : deriv (lowerBarrierPlateau κ κtilde D) x =
        deriv (lowerBarrierRaw κ κtilde D) x := heq.deriv_eq
    have hderiv2 : iteratedDeriv 2 (lowerBarrierPlateau κ κtilde D) x =
        iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x :=
      heq.iteratedDeriv_eq 2
    have hopEq :
        paperWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x =
          paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x := by
      unfold paperWaveOperator
      dsimp only
      rw [hval, hderiv, hderiv2]
    rw [hopEq, paperWaveOperator_eq_frozenWaveOperator_of_chi_zero p hχ]
    exact hraw

section AxiomAudit

#print axioms paperWaveOperator_eq_frozenWaveOperator_of_chi_zero
#print axioms paperWaveOperator_lowerBarrierPlateau_nonneg_chi_zero_away

end AxiomAudit

end ShenWork.Paper1
