import ShenWork.Paper1.WavePositivePlateauComparison

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- The height of the two-exponential lower barrier at its critical point is
the second scalar entry in `constantSubsolutionThreshold`. -/
theorem lowerBarrierRaw_xplus_eq_constantSubsolutionTail
    {κ κtilde D : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) =
      (κ / (κtilde * D)) ^ (κ / (κtilde - κ)) *
        (1 - κ / κtilde) := by
  have hκtilde : 0 < κtilde := by linarith
  have hbase : 0 < κ / (κtilde * D) := by positivity
  have harg : 0 < κtilde * D / κ := by positivity
  have hinv : κtilde * D / κ = (κ / (κtilde * D))⁻¹ := by
    field_simp [ne_of_gt hκ, ne_of_gt hκtilde, ne_of_gt hD]
  have hX :
      lowerBarrierXPlus κ κtilde D =
        Real.log (κtilde * D / κ) / (κtilde - κ) := rfl
  have hgapX :
      Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) =
        κ / (κtilde * D) := by
    rw [hX]
    have hexponent :
        -(κtilde - κ) *
            (Real.log (κtilde * D / κ) / (κtilde - κ)) =
          Real.log (κ / (κtilde * D)) := by
      rw [hinv, Real.log_inv]
      field_simp [ne_of_gt hgap]
    rw [hexponent, Real.exp_log hbase]
  have hκX :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) =
        (κ / (κtilde * D)) ^ (κ / (κtilde - κ)) := by
    rw [Real.rpow_def_of_pos hbase]
    rw [hX, hinv, Real.log_inv]
    congr 1
    field_simp [ne_of_gt hgap]
  rw [lowerBarrierRaw_eq_exp_mul, hκX]
  rw [hgapX]
  field_simp [ne_of_gt hκtilde, ne_of_gt hD]

/-- The patched barrier never exceeds its constant left-hand height. -/
theorem lowerBarrierPlateau_le_value_at_xplus
    {κ κtilde D x : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    lowerBarrierPlateau κ κtilde D x ≤
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
  · have hxgt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxgt]
    exact lowerBarrierRaw_antitoneOn_Ici_xplus hκ hgap hD
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hxgt.le) hxgt.le

/-- The paper lower-barrier coefficient can be chosen so that its plateau is
small enough for the nonpositive-sensitivity constant subsolution estimate. -/
theorem exists_chiNonposPlateau_D
    (p : CMParams) {c M κ κtilde : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) :
    ∃ D : ℝ,
      1 ≤ D ∧
      paperDMin p.χ M κ κtilde p.m p.γ c < D ∧
      ∀ x, lowerBarrierPlateau κ κtilde D x ≤
        constantSubsolutionThreshold p.χ κ κtilde D := by
  let B := max 1 (paperDMin p.χ M κ κtilde p.m p.γ c)
  obtain ⟨D, hDB, hexp⟩ :=
    exists_D_gt_with_exp_xplus_le
      (B := B) hκ hgap (show 0 < 1 / (1 + |p.χ|) by positivity)
  have hD1 : 1 ≤ D := (le_max_left 1 _).trans hDB.le
  have hDmin : paperDMin p.χ M κ κtilde p.m p.γ c < D :=
    lt_of_le_of_lt (le_max_right 1 _) hDB
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  refine ⟨D, hD1, hDmin, ?_⟩
  intro x
  unfold constantSubsolutionThreshold
  apply le_min
  · exact (lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x).trans hexp
  · rw [← lowerBarrierRaw_xplus_eq_constantSubsolutionTail hκ hgap hD]
    exact lowerBarrierPlateau_le_value_at_xplus hκ hgap hD

/-- For nonpositive sensitivity, the patched positive lower barrier is a
paper subsolution at every point away from its `C¹` splice. -/
theorem paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_away
    (p : CMParams) {c M κ κtilde D : ℝ} {u : ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau κ κtilde D x ≤
      constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : InWaveTrapSet κ M u)
    {x : ℝ} (hx : x ≠ lowerBarrierXPlus κ κtilde D) :
    0 ≤ paperWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x := by
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
    have hconst := paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos
      p (c := c) (κ := κ) (κtilde := κtilde) (D := D)
        hcond.hχ hu.cunif_bdd hu.nonneg hd0 hd x
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
    rw [hopEq]
    exact hconst
  · have hregion : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D) := by
      exact lt_trans
        (lowerBarrierXMinus_lt_xplus hcond.hκ0
          (sub_pos.mpr hcond.hgap) (lt_of_lt_of_le zero_lt_one hD1)) hxgt
    have hraw := PaperLemma_4_2_paperWaveOperator_of_conditions
      hcond hD hD1 u hu x hregion
    have heq := lowerBarrierPlateau_eventuallyEq_raw_of_gt hxgt
    have hval : lowerBarrierPlateau κ κtilde D x =
        lowerBarrierRaw κ κtilde D x :=
      lowerBarrierPlateau_eq_raw_of_xplus_lt hxgt
    have hderiv : deriv (lowerBarrierPlateau κ κtilde D) x =
        deriv (lowerBarrierRaw κ κtilde D) x := heq.deriv_eq
    have hderiv2 : iteratedDeriv 2 (lowerBarrierPlateau κ κtilde D) x =
        iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x :=
      heq.iteratedDeriv_eq 2
    unfold paperWaveOperator at hraw ⊢
    dsimp only
    rw [hval, hderiv, hderiv2]
    exact hraw

section AxiomAudit

#print axioms lowerBarrierRaw_xplus_eq_constantSubsolutionTail
#print axioms lowerBarrierPlateau_le_value_at_xplus
#print axioms exists_chiNonposPlateau_D
#print axioms paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_away

end AxiomAudit

end ShenWork.Paper1
