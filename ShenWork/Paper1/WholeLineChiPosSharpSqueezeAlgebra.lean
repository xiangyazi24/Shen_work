import Mathlib.Analysis.MeanInequalities
import ShenWork.Paper1.WholeLineChiPosHalfLineRectangle

/-!
# A sharper critical positive-sensitivity squeeze

The floor term in the positive rectangle iteration carries the small-endpoint
factor `ell'^(m - 1)`.  When `m > 1`, retaining that factor gains the exact
coefficient `gamma / alpha` at the critical exponent.  Keeping the ceiling
term on the new gap then gives the affine ratio

`chi * gamma / (alpha * (1 - chi))`.

Thus the scalar iteration contracts under

`chi * gamma < alpha * (1 - chi)`,

equivalently `chi < alpha / (alpha + gamma)`.  This is strictly wider than
`chi < 1 / 2` whenever `m > 1` and `alpha = m + gamma - 1`.
-/

open Real Set

noncomputable section

namespace ShenWork.Paper1

/-- Sharp small-endpoint absorption.  The coefficient is optimal as
`L / U -> 1`. -/
theorem rpow_small_prefactor_gap_le_ratio
    {L U s a : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hs : 0 ≤ s) (ha : 0 < a) :
    L ^ s * (U ^ a - L ^ a) ≤
      (a / (a + s)) * (U ^ (a + s) - L ^ (a + s)) := by
  have hU : 0 < U := hL.trans_le hLU
  have hsum : 0 < a + s := add_pos_of_pos_of_nonneg ha hs
  let wa : ℝ := a / (a + s)
  let ws : ℝ := s / (a + s)
  have hwa : 0 ≤ wa := by
    dsimp [wa]
    positivity
  have hws : 0 ≤ ws := by
    dsimp [ws]
    positivity
  have hweights : wa + ws = 1 := by
    dsimp [wa, ws]
    field_simp [ne_of_gt hsum]
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    (p₁ := U ^ (a + s)) (p₂ := L ^ (a + s))
    hwa hws (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hL.le _) hweights
  have hUw : (U ^ (a + s)) ^ wa = U ^ a := by
    dsimp [wa]
    rw [← Real.rpow_mul hU.le]
    congr 1
    field_simp [ne_of_gt hsum]
  have hLw : (L ^ (a + s)) ^ ws = L ^ s := by
    dsimp [ws]
    rw [← Real.rpow_mul hL.le]
    congr 1
    field_simp [ne_of_gt hsum]
  rw [hUw, hLw] at hamgm
  have hws_eq : ws = 1 - wa := by linarith [hweights]
  rw [hws_eq] at hamgm
  have hLas : L ^ (a + s) = L ^ a * L ^ s := Real.rpow_add hL a s
  change L ^ s * (U ^ a - L ^ a) ≤
    wa * (U ^ (a + s) - L ^ (a + s))
  rw [hLas] at hamgm ⊢
  nlinarith

/-- One critical rectangle round with the small-endpoint coefficient retained.
The chemotactic coupling enters exactly as `chi * gamma / alpha`; the
ceiling contribution is absorbed into the left-hand side. -/
theorem chiPos_squeeze_gap_step_m_gt_one
    {m gamma alpha chi ell ell' M M' delta : ℝ}
    (hm : 1 < m) (hgamma : 1 ≤ gamma)
    (hcritical : alpha = m + gamma - 1)
    (hchi : 0 ≤ chi)
    (hell : 0 < ell) (hellell' : ell ≤ ell') (hell'one : ell' ≤ 1)
    (honeM' : 1 ≤ M') (hM'M : M' ≤ M)
    (hfloor : 1 - ell' ^ alpha ≤
      chi * (ell' ^ (m - 1) * (M ^ gamma - ell' ^ gamma)) + delta)
    (hceiling : M' ^ alpha - 1 ≤
      chi * (M' ^ (m - 1) * (M' ^ gamma - ell' ^ gamma)) + delta) :
    (1 - chi) * (M' ^ alpha - ell' ^ alpha) ≤
      chi * (gamma / alpha) * (M ^ alpha - ell ^ alpha) + 2 * delta := by
  have hell' : 0 < ell' := hell.trans_le hellell'
  have honeM : (1 : ℝ) ≤ M := honeM'.trans hM'M
  have hs : 0 < m - 1 := sub_pos.mpr hm
  have ha : 0 < gamma := zero_lt_one.trans_le hgamma
  have halpha : 0 < alpha := by rw [hcritical]; linarith
  have hexp : gamma + (m - 1) = alpha := by rw [hcritical]; ring
  have hfloorAbsorb :
      ell' ^ (m - 1) * (M ^ gamma - ell' ^ gamma) ≤
        (gamma / alpha) * (M ^ alpha - ell' ^ alpha) := by
    have h := rpow_small_prefactor_gap_le_ratio
      hell' (hell'one.trans honeM) hs.le ha
    rwa [hexp] at h
  have hceilingAbsorb :
      M' ^ (m - 1) * (M' ^ gamma - ell' ^ gamma) ≤
        M' ^ alpha - ell' ^ alpha := by
    have h := ShenWork.Paper3.rpow_mul_gap_le_gap_add
      hell' hell'one honeM' hs.le ha.le
    rwa [hexp] at h
  have hfloorMono : ell ^ alpha ≤ ell' ^ alpha :=
    Real.rpow_le_rpow hell.le hellell' halpha.le
  have hgapMono : M ^ alpha - ell' ^ alpha ≤ M ^ alpha - ell ^ alpha := by
    linarith
  have hratio0 : 0 ≤ gamma / alpha := div_nonneg ha.le halpha.le
  have hchiFloor :
      chi * (ell' ^ (m - 1) * (M ^ gamma - ell' ^ gamma)) ≤
        chi * (gamma / alpha) * (M ^ alpha - ell ^ alpha) := by
    have h := hfloorAbsorb.trans
      (mul_le_mul_of_nonneg_left hgapMono hratio0)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hchi
  have hchiCeiling :
      chi * (M' ^ (m - 1) * (M' ^ gamma - ell' ^ gamma)) ≤
        chi * (M' ^ alpha - ell' ^ alpha) :=
    mul_le_mul_of_nonneg_left hceilingAbsorb hchi
  nlinarith [hfloor, hceiling, hchiFloor, hchiCeiling]

/-- The sharp ratio condition is genuinely weaker than `chi < 1 / 2` at every
critical exponent with `m > 1`. -/
theorem half_mul_gamma_lt_alpha_mul_one_sub_half_of_m_gt_one
    {m gamma alpha : ℝ} (hm : 1 < m) (_hgamma : 1 ≤ gamma)
    (hcritical : alpha = m + gamma - 1) :
    (1 / 2 : ℝ) * gamma < alpha * (1 - 1 / 2) := by
  rw [hcritical]
  linarith

/-- Quotient form of the exact sharp contraction condition. -/
theorem chi_mul_gamma_lt_alpha_mul_one_sub_iff
    {chi gamma alpha : ℝ} (halpha : 0 < alpha) (hgamma : 0 < gamma) :
    chi * gamma < alpha * (1 - chi) ↔
      chi < alpha / (alpha + gamma) := by
  rw [lt_div_iff₀ (add_pos halpha hgamma)]
  constructor <;> intro h <;> nlinarith

/-- The critical sharp threshold is strictly larger than one half exactly
when the mobility exponent is genuinely larger than one. -/
theorem one_half_lt_critical_sharp_threshold
    {m gamma alpha : ℝ} (hm : 1 < m) (hgamma : 1 ≤ gamma)
    (hcritical : alpha = m + gamma - 1) :
    (1 / 2 : ℝ) < alpha / (alpha + gamma) := by
  have halpha : 0 < alpha := by rw [hcritical]; linarith
  rw [lt_div_iff₀ (add_pos halpha (zero_lt_one.trans_le hgamma))]
  rw [hcritical]
  linarith

section AxiomAudit

#print axioms rpow_small_prefactor_gap_le_ratio
#print axioms chiPos_squeeze_gap_step_m_gt_one
#print axioms half_mul_gamma_lt_alpha_mul_one_sub_half_of_m_gt_one
#print axioms chi_mul_gamma_lt_alpha_mul_one_sub_iff
#print axioms one_half_lt_critical_sharp_threshold

end AxiomAudit

end ShenWork.Paper1
