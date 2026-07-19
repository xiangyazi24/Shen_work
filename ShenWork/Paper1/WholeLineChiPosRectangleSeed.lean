import ShenWork.Paper1.WholeLineCauchyChiPosRangeBound

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Algebraic seed for the positive-sensitivity rectangle iteration

At the critical exponent, the only obstruction to starting a floor barrier
at a small positive value occurs when `m = 1`.  In that case the exact
`MChi` identity and `chi < 1 / 2` leave a strict margin.  Continuity first
preserves this margin at a ceiling strictly above `MChi`, and then gives a
small positive floor for that ceiling.
-/

/-- In the critical `m = 1` case, the canonical ceiling lies strictly below
the threshold at which the zero-floor reaction margin vanishes. -/
theorem chi_mul_MChi_rpow_gamma_lt_one_of_m_eq_one
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1) (hm : p.m = 1) :
    p.χ * (MChi p) ^ p.γ < 1 := by
  have hchi_one : p.χ < 1 := by linarith
  have halpha_gamma : p.α = p.γ := by
    rw [hm] at hcritical
    linarith
  have hpow : (MChi p) ^ p.α = 1 / (1 - p.χ) :=
    MChi_rpow_alpha_eq_one_div_one_sub_chi p hchi.le hchi_one
  have hden : 0 < 1 - p.χ := sub_pos.mpr hchi_one
  calc
    p.χ * (MChi p) ^ p.γ = p.χ * (1 / (1 - p.χ)) := by
      rw [← halpha_gamma, hpow]
    _ = p.χ / (1 - p.χ) := by ring
    _ < 1 := (div_lt_one hden).2 (by linarith)

/-- There is a ceiling strictly above both `MChi` and `1` which retains the
zero-floor margin required in the exceptional case `m = 1`. -/
theorem exists_M_gt_MChi_with_m_one_margin
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1) :
    ∃ M : ℝ,
      MChi p < M ∧ 1 < M ∧
        (p.m = 1 → p.χ * M ^ p.γ < 1) := by
  have hchi_one : p.χ < 1 := by linarith
  have hMChi_one : 1 ≤ MChi p :=
    one_le_MChi_of_chi_nonneg_lt_one p hchi.le hchi_one
  by_cases hm : p.m = 1
  · let f : ℝ → ℝ := fun R => p.χ * R ^ p.γ
    have hbase : f (MChi p) < 1 := by
      simpa [f] using
        chi_mul_MChi_rpow_gamma_lt_one_of_m_eq_one
          p hchi hchi_half hcritical hm
    have hgamma_nonneg : 0 ≤ p.γ := zero_le_one.trans p.hγ
    have hcont : ContinuousAt f (MChi p) := by
      dsimp [f]
      exact continuousAt_const.mul
        (Real.continuous_rpow_const hgamma_nonneg).continuousAt
    have hpre : f ⁻¹' Iio 1 ∈ 𝓝 (MChi p) :=
      hcont (Iio_mem_nhds hbase)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨delta, hdelta, hball⟩
    let M : ℝ := MChi p + delta / 2
    have hMChi_lt : MChi p < M := by
      dsimp [M]
      linarith
    have hMmem : M ∈ Metric.ball (MChi p) delta := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [M]
      rw [abs_of_nonneg (by linarith : 0 ≤ MChi p + delta / 2 - MChi p)]
      linarith
    refine ⟨M, hMChi_lt, hMChi_one.trans_lt hMChi_lt, ?_⟩
    intro _hm
    exact hball hMmem
  · refine ⟨MChi p + 1, by linarith, by linarith, ?_⟩
    intro hm'
    exact (hm hm').elim

/-- Every ceiling strictly above `MChi` has a strict critical ceiling-gap
margin, for any nonnegative resolver floor. -/
theorem chiPos_rectangle_ceiling_margin_pos_of_MChi_lt
    (p : CMParams) (hchi : 0 < p.χ) (hchi_one : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    {M ell : ℝ} (hMChi_lt : MChi p < M) (hell : 0 ≤ ell) :
    0 < M ^ p.α - 1 -
      p.χ * M ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ) := by
  have hMChi_pos : 0 < MChi p :=
    MChi_pos_of_chi_lt_one p hchi_one
  have hM_pos : 0 < M := hMChi_pos.trans hMChi_lt
  have halpha_pos : 0 < p.α := zero_lt_one.trans_le p.hα
  have hden_pos : 0 < 1 - p.χ := sub_pos.mpr hchi_one
  have hMChi_pow : (MChi p) ^ p.α = 1 / (1 - p.χ) :=
    MChi_rpow_alpha_eq_one_div_one_sub_chi p hchi.le hchi_one
  have hpow_lt : (MChi p) ^ p.α < M ^ p.α :=
    Real.rpow_lt_rpow hMChi_pos.le hMChi_lt halpha_pos
  have hroot : (1 - p.χ) * (MChi p) ^ p.α = 1 := by
    rw [hMChi_pow]
    field_simp
  have hlead : 1 < (1 - p.χ) * M ^ p.α := by
    have := mul_lt_mul_of_pos_left hpow_lt hden_pos
    linarith
  have hpow_combine :
      M ^ (p.m - 1) * M ^ p.γ = M ^ p.α := by
    rw [← Real.rpow_add hM_pos]
    congr 1
    linarith
  have htail : 0 ≤ p.χ * M ^ (p.m - 1) * ell ^ p.γ :=
    mul_nonneg
      (mul_nonneg hchi.le (Real.rpow_nonneg hM_pos.le _))
      (Real.rpow_nonneg hell _)
  have hpow_scaled :
      p.χ * M ^ (p.m - 1) * M ^ p.γ = p.χ * M ^ p.α := by
    calc
      p.χ * M ^ (p.m - 1) * M ^ p.γ =
          p.χ * (M ^ (p.m - 1) * M ^ p.γ) := mul_assoc _ _ _
      _ = p.χ * M ^ p.α := by rw [hpow_combine]
  calc
    0 < (1 - p.χ) * M ^ p.α - 1 +
        p.χ * M ^ (p.m - 1) * ell ^ p.γ := by linarith
    _ = M ^ p.α - 1 -
        p.χ * M ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ) := by
      rw [mul_sub, hpow_scaled]
      ring

/-- Any ceiling with the exceptional `m = 1` margin admits a small positive
floor on which the weighted rectangle reaction margin is strictly positive. -/
theorem exists_ell_with_positive_rectangle_floor_margin
    (p : CMParams) {M : ℝ}
    (hm_one_margin : p.m = 1 → p.χ * M ^ p.γ < 1) :
    ∃ ell : ℝ,
      0 < ell ∧ ell < 1 ∧
        0 < 1 - ell ^ p.α -
          p.χ * ell ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ) := by
  let phi : ℝ → ℝ := fun ell =>
    1 - ell ^ p.α -
      p.χ * ell ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ)
  have halpha_pos : 0 < p.α := zero_lt_one.trans_le p.hα
  have hgamma_pos : 0 < p.γ := zero_lt_one.trans_le p.hγ
  have hm_sub_nonneg : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hphi_zero : 0 < phi 0 := by
    by_cases hm : p.m = 1
    · have hmargin := sub_pos.mpr (hm_one_margin hm)
      simpa [phi, hm, Real.zero_rpow halpha_pos.ne',
        Real.zero_rpow hgamma_pos.ne'] using hmargin
    · have hm_sub_pos : 0 < p.m - 1 :=
        sub_pos.mpr (lt_of_le_of_ne p.hm (Ne.symm hm))
      simp [phi, Real.zero_rpow halpha_pos.ne',
        Real.zero_rpow hgamma_pos.ne', Real.zero_rpow hm_sub_pos.ne']
  have hpow_alpha : ContinuousAt (fun ell : ℝ => ell ^ p.α) 0 :=
    (Real.continuous_rpow_const halpha_pos.le).continuousAt
  have hpow_m_sub_one :
      ContinuousAt (fun ell : ℝ => ell ^ (p.m - 1)) 0 :=
    (Real.continuous_rpow_const hm_sub_nonneg).continuousAt
  have hpow_gamma : ContinuousAt (fun ell : ℝ => ell ^ p.γ) 0 :=
    (Real.continuous_rpow_const hgamma_pos.le).continuousAt
  have hcont : ContinuousAt phi 0 := by
    dsimp [phi]
    exact (continuousAt_const.sub hpow_alpha).sub
      ((continuousAt_const.mul hpow_m_sub_one).mul
        (continuousAt_const.sub hpow_gamma))
  have hpre : phi ⁻¹' Ioi 0 ∈ 𝓝 0 :=
    hcont (Ioi_mem_nhds hphi_zero)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨delta, hdelta, hball⟩
  let ell : ℝ := min (delta / 2) (1 / 2)
  have hell_pos : 0 < ell := by
    dsimp [ell]
    exact lt_min (by linarith) (by norm_num)
  have hell_delta : ell < delta :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hell_one : ell < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hell_mem : ell ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hell_pos]
    exact hell_delta
  exact ⟨ell, hell_pos, hell_one, hball hell_mem⟩

/-- Combined algebraic/topological seed for the first positive-sensitivity
rectangle round. -/
theorem exists_chiPos_rectangle_seed
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1) :
    ∃ M ell : ℝ,
      MChi p < M ∧ 1 < M ∧
      (p.m = 1 → p.χ * M ^ p.γ < 1) ∧
      0 < ell ∧ ell < 1 ∧
      0 < 1 - ell ^ p.α -
        p.χ * ell ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ) := by
  rcases exists_M_gt_MChi_with_m_one_margin
      p hchi hchi_half hcritical with ⟨M, hMChi, hM_one, hm_margin⟩
  rcases exists_ell_with_positive_rectangle_floor_margin
      p hm_margin with ⟨ell, hell_pos, hell_one, hell_margin⟩
  exact ⟨M, ell, hMChi, hM_one, hm_margin,
    hell_pos, hell_one, hell_margin⟩

section WholeLineChiPosRectangleSeedAxiomAudit

#print axioms chi_mul_MChi_rpow_gamma_lt_one_of_m_eq_one
#print axioms exists_M_gt_MChi_with_m_one_margin
#print axioms chiPos_rectangle_ceiling_margin_pos_of_MChi_lt
#print axioms exists_ell_with_positive_rectangle_floor_margin
#print axioms exists_chiPos_rectangle_seed

end WholeLineChiPosRectangleSeedAxiomAudit

end ShenWork.Paper1
