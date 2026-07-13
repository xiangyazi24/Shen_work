/-
  Lower-barrier comparison data for the positive-attraction construction.

  The paper's positive trap is not spatially monotone.  Its lower barrier is
  the positive plateau followed by the two-exponential tail.  The smallness
  `chi < 1/2` supplies the constant-plateau subsolution even though the frozen
  elliptic field is only bounded by `MChi^gamma`.
-/
import ShenWork.Paper1.WavePositiveLocalStep
import ShenWork.Paper1.WaveLowerRawTailfree
import ShenWork.Paper1.StatementAssembly

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- A conservative positive height for the constant part of the positive
lower barrier. -/
def paper1PositivePlateauFloor (p : CMParams) : ℝ :=
  min 1 ((1 - 2 * p.χ) / (2 * (1 - p.χ) ^ 2))

theorem paper1PositivePlateauFloor_pos
    (p : CMParams) (hχ : p.χ < (1 / 2 : ℝ)) :
    0 < paper1PositivePlateauFloor p := by
  unfold paper1PositivePlateauFloor
  have hden : 0 < 1 - p.χ := by linarith
  apply lt_min one_pos
  exact div_pos (by linarith) (by positivity)

/-- In the positive headline regime the normalized elliptic source-box bound
obeys `MChi^gamma <= 1/(1-chi)`.  The exponent inequality is exactly
`gamma <= alpha = m+gamma-1`. -/
theorem MChi_rpow_gamma_le_one_div_one_sub_chi
    (p : CMParams)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1) :
    (MChi p) ^ p.γ ≤ 1 / (1 - p.χ) := by
  let b : ℝ := 1 / (1 - p.χ)
  have hden : 0 < 1 - p.χ := by linarith
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hden]
    linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγleα : p.γ ≤ p.α := by
    rw [hα]
    linarith [p.hm]
  have hexp : (1 / p.α) * p.γ ≤ 1 := by
    rw [one_div_mul_eq_div]
    exact (div_le_one hαpos).2 hγleα
  rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ0 hχ1]
  change (b ^ (1 / p.α)) ^ p.γ ≤ b
  rw [← Real.rpow_mul hbpos.le (1 / p.α) p.γ]
  calc
    b ^ ((1 / p.α) * p.γ) ≤ b ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ = b := Real.rpow_one b

/-- The small positive plateau is a genuine paper-expanded frozen
subsolution for every frozen profile in the nonmonotone positive trap. -/
theorem paperWaveOperator_const_subsolution_nonneg_pos_MChi
    (p : CMParams) {c κ d : ℝ} {u : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < (1 / 2 : ℝ))
    (hα : p.α = p.m + p.γ - 1)
    (hd0 : 0 < d) (hd : d ≤ paper1PositivePlateauFloor p)
    (hu : InWaveTrapSet κ (MChi p) u) :
    ∀ x, 0 ≤ paperWaveOperator p c u (fun _ => d) x := by
  intro x
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  apply mul_nonneg hd0.le
  have hχ1 : p.χ < 1 := by linarith
  have hden : 0 < 1 - p.χ := by linarith
  have hMpos : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ1
  have hV0 : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg_of_inWaveTrapSet p hu x
  have hVle : frozenElliptic p u x ≤ (MChi p) ^ p.γ :=
    frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu x
  have hMγ : (MChi p) ^ p.γ ≤ 1 / (1 - p.χ) :=
    MChi_rpow_gamma_le_one_div_one_sub_chi p hχ0 hχ1 hα
  have hd1 : d ≤ 1 :=
    hd.trans (min_le_left _ _)
  have hdm1 : d ^ (p.m - 1) ≤ 1 :=
    Real.rpow_le_one hd0.le hd1 (sub_nonneg.mpr p.hm)
  have hdm10 : 0 ≤ d ^ (p.m - 1) :=
    Real.rpow_nonneg hd0.le _
  have hchem :
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤
        p.χ / (1 - p.χ) := by
    calc
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤
          p.χ * 1 * (1 / (1 - p.χ)) := by
        gcongr
        exact hVle.trans hMγ
      _ = p.χ / (1 - p.χ) := by ring
  have hdα : d ^ p.α ≤ d := by
    calc
      d ^ p.α ≤ d ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hd0 hd1 p.hα
      _ = d := Real.rpow_one d
  have hdfloor :
      d ≤ (1 - 2 * p.χ) / (2 * (1 - p.χ) ^ 2) :=
    hd.trans (min_le_right _ _)
  have hlogistic :
      (1 - p.χ) * d ^ p.α ≤
        (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
    have h1 := mul_le_mul_of_nonneg_left hdα hden.le
    have h2 := mul_le_mul_of_nonneg_left hdfloor hden.le
    have hdenne : 1 - p.χ ≠ 0 := ne_of_gt hden
    calc
      (1 - p.χ) * d ^ p.α ≤ (1 - p.χ) * d := h1
      _ ≤ (1 - p.χ) *
          ((1 - 2 * p.χ) / (2 * (1 - p.χ) ^ 2)) := h2
      _ = (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
        field_simp [hdenne]
  have hmargin :
      0 < (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
    exact div_pos (by linarith) (by positivity)
  have hbudget :
      p.χ / (1 - p.χ) +
          (1 - 2 * p.χ) / (2 * (1 - p.χ)) < 1 := by
    have hdenne : 1 - p.χ ≠ 0 := ne_of_gt hden
    have heq :
        p.χ / (1 - p.χ) +
            (1 - 2 * p.χ) / (2 * (1 - p.χ)) =
          1 - (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
      field_simp [hdenne]
      ring
    rw [heq]
    linarith
  have hpow : d ^ (p.m + p.γ - 1) = d ^ p.α := by
    rw [hα]
  rw [hpow]
  nlinarith [hchem, hlogistic, hbudget]

/-- Choose the lower-barrier coefficient far enough past the Lemma 4.2
threshold that its entire plateau lies below the positive constant-floor
budget. -/
theorem exists_positivePlateau_D
    (p : CMParams) {c κ κtilde : ℝ}
    (hχhalf : p.χ < (1 / 2 : ℝ))
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) :
    ∃ D : ℝ,
      1 ≤ D ∧
      paperDMin p.χ (MChi p) κ κtilde p.m p.γ c < D ∧
      ∀ x, lowerBarrierPlateau κ κtilde D x ≤
        paper1PositivePlateauFloor p := by
  let B : ℝ := max 1 (paperDMin p.χ (MChi p) κ κtilde p.m p.γ c)
  obtain ⟨D, hDB, htail⟩ :=
    exists_D_gt_with_exp_xplus_le
      (B := B) hκ hgap (paper1PositivePlateauFloor_pos p hχhalf)
  have hD1 : 1 ≤ D :=
    (le_max_left 1 _).trans hDB.le
  have hDmin :
      paperDMin p.χ (MChi p) κ κtilde p.m p.γ c < D :=
    lt_of_le_of_lt (le_max_right 1 _) hDB
  refine ⟨D, hD1, hDmin, ?_⟩
  intro x
  exact (lowerBarrierPlateau_le_exp_xplus hκ.le
    (lt_of_lt_of_le zero_lt_one hD1).le x).trans htail

section AxiomAudit

#print axioms MChi_rpow_gamma_le_one_div_one_sub_chi
#print axioms paperWaveOperator_const_subsolution_nonneg_pos_MChi
#print axioms exists_positivePlateau_D

end AxiomAudit

end ShenWork.Paper1
