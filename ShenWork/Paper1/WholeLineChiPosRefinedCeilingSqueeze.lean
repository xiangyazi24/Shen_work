import ShenWork.Paper1.WholeLineChiPosSharpSqueezeAlgebra

/-!
# Refined ceiling absorption in the positive-sensitivity squeeze

`chiPos_squeeze_gap_step_m_gt_one` absorbs the ceiling budget with the crude
bound

`M' ^ (m - 1) * (M' ^ γ - ell' ^ γ) ≤ M' ^ α - ell' ^ α`   (coefficient `1`),

which is what produces the `(1 - chi)` factor on the left of the gap recursion
and caps the method at `chi < alpha / (alpha + gamma)`.

That coefficient is not optimal.  By homogeneity, with `t = ell' / M'`,

`M' ^ (m - 1) * (M' ^ γ - ell' ^ γ) = c t * (M' ^ α - ell' ^ α)`,
`c t = (1 - t ^ γ) / (1 - t ^ α)`,

and `c` is non-increasing on `(0, 1)` with `c 0⁺ = 1` and `c 1⁻ = γ / α`.  So
any *a priori* lower bound `t₀` on the rectangle's aspect ratio `ell / M`
upgrades the coefficient from `1` to `c t₀ < 1`.

Crucially `t₀` comes from the SEED rectangle (`ell` increases and `M`
decreases along the iteration, so `t` only increases), i.e. from the
`chi < 1` equilibrium-height trap — **not** from the contraction one is trying
to prove.  There is therefore no circularity.

This file isolates the algebra with the ceiling coefficient `c0` carried as a
hypothesis; the producer for `c0 = c t₀` is
`ShenWork/Paper1/WholeLineChiPosCeilingRatio.lean`.

Resulting contraction ratio: `rho = chi * (gamma / alpha) / (1 - chi * c0)`,
so the iteration closes under

`chi * gamma / alpha + chi * c0 < 1`,

which at `c0 = 1` recovers `chi < alpha / (alpha + gamma)` and at the limiting
`c0 = gamma / alpha` gives `chi < alpha / (2 * gamma)` — strictly wider for
every `m > 1`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The squeeze step with the ceiling absorbed at a general coefficient `c0`.
Taking `c0 = 1` recovers `chiPos_squeeze_gap_step_m_gt_one`. -/
theorem chiPos_squeeze_gap_step_refined_ceiling
    {m gamma alpha chi ell ell' M M' delta c0 : ℝ}
    (hm : 1 < m) (hgamma : 1 ≤ gamma)
    (hcritical : alpha = m + gamma - 1)
    (hchi : 0 ≤ chi)
    (hell : 0 < ell) (hellell' : ell ≤ ell') (hell'one : ell' ≤ 1)
    (honeM' : 1 ≤ M') (hM'M : M' ≤ M)
    (hceilAbsorb : M' ^ (m - 1) * (M' ^ gamma - ell' ^ gamma) ≤
      c0 * (M' ^ alpha - ell' ^ alpha))
    (hfloor : 1 - ell' ^ alpha ≤
      chi * (ell' ^ (m - 1) * (M ^ gamma - ell' ^ gamma)) + delta)
    (hceiling : M' ^ alpha - 1 ≤
      chi * (M' ^ (m - 1) * (M' ^ gamma - ell' ^ gamma)) + delta) :
    (1 - chi * c0) * (M' ^ alpha - ell' ^ alpha) ≤
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
        chi * (c0 * (M' ^ alpha - ell' ^ alpha)) :=
    mul_le_mul_of_nonneg_left hceilAbsorb hchi
  nlinarith [hfloor, hceiling, hchiFloor, hchiCeiling]

/-- The refined contraction condition, in quotient form. -/
theorem chiPos_refined_contraction_iff
    {chi gamma alpha c0 : ℝ} (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hc0 : 0 < c0) :
    chi * (gamma / alpha) < 1 - chi * c0 ↔
      chi < alpha / (gamma + alpha * c0) := by
  have hden : 0 < gamma + alpha * c0 := by positivity
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;>
    · field_simp at h ⊢
      nlinarith [h]

/-- At the limiting coefficient `c0 = gamma / alpha` the refined threshold is
`alpha / (2 * gamma)`, strictly larger than the current `alpha / (alpha + gamma)`
for every `m > 1` (i.e. whenever `gamma < alpha`). -/
theorem refined_threshold_gt_sharp_threshold
    {gamma alpha : ℝ} (hgamma : 0 < gamma) (hlt : gamma < alpha) :
    alpha / (alpha + gamma) < alpha / (2 * gamma) := by
  have halpha : 0 < alpha := hgamma.trans hlt
  have h1 : 0 < alpha + gamma := by linarith
  have h2 : 0 < 2 * gamma := by linarith
  exact div_lt_div_of_pos_left halpha h2 (by linarith)

/-- The ceiling ratio never exceeds `1`, so the refinement is never a
regression: it recovers the crude coefficient in the worst case. -/
theorem ceilingRatio_le_one {g a t : ℝ} (hg : 0 < g) (hga : g ≤ a)
    (ht : 0 < t) (ht1 : t < 1) :
    (1 - t ^ g) / (1 - t ^ a) ≤ 1 := by
  have hag : t ^ a ≤ t ^ g :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1.le hga
  have hlt : t ^ a < 1 := Real.rpow_lt_one ht.le ht1 (hg.trans_le hga)
  have hpos : 0 < 1 - t ^ a := sub_pos.mpr hlt
  rw [div_le_one hpos]
  linarith

/-- Consequently the refined contraction condition is implied by the crude
one: anything the `c0 = 1` threshold covers, the refined threshold covers. -/
theorem refined_contraction_of_sharp
    {chi gamma alpha c0 : ℝ} (hchi : 0 ≤ chi) (halpha : 0 < alpha)
    (hc0 : c0 ≤ 1) (h : chi * gamma < alpha * (1 - chi)) :
    chi * gamma < alpha * (1 - chi * c0) := by
  have : chi * c0 ≤ chi := by nlinarith
  nlinarith

/-- **Exact coverage at the limiting threshold.**  `chiStar p ≤ alpha / (2 γ)`
precisely when the cubic `Q (m, γ) = m ^ 3 + γ m ^ 2 - (γ + 1) m - 2 γ ^ 2 - 2 γ`
is nonnegative.  Its root in `m` is strictly below the root of the `c0 = 1`
cubic `P` (e.g. `1.6590` versus `2.2695` at `γ = 1`), which is the quantitative
content of the refinement. -/
theorem chiStar_le_limitThreshold_of_poly (p : CMParams)
    (hcritical : p.α = p.m + p.γ - 1)
    (hQ : 0 ≤ p.m ^ 3 + p.γ * p.m ^ 2 - (p.γ + 1) * p.m - 2 * p.γ ^ 2
      - 2 * p.γ)
    (hm : 1 < p.m) :
    chiStar p ≤ p.α / (2 * p.γ) := by
  have hg1 : (1 : ℝ) ≤ p.γ := p.hγ
  have hg : 0 < p.γ := zero_lt_one.trans_le hg1
  have hden2 : 0 < p.m ^ 2 + p.m + 2 * p.γ := by nlinarith
  have hden3 : 0 < 2 * p.γ := by linarith
  refine (min_le_right _ _).trans ?_
  rw [div_le_div_iff₀ hden2 hden3, hcritical]
  nlinarith [hQ]

/-- When `γ + 1 ≤ m` the limiting threshold exceeds `1`, so it covers the whole
window trivially (`chiStar ≤ 1` by definition). -/
theorem chiStar_le_limitThreshold_of_gamma_add_one_le (p : CMParams)
    (hcritical : p.α = p.m + p.γ - 1) (hmg : p.γ + 1 ≤ p.m) :
    chiStar p ≤ p.α / (2 * p.γ) := by
  have hg1 : (1 : ℝ) ≤ p.γ := p.hγ
  have hg : 0 < p.γ := zero_lt_one.trans_le hg1
  have hone : (1 : ℝ) ≤ p.α / (2 * p.γ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * p.γ), hcritical]
    linarith
  exact (min_le_left _ _).trans hone

section AxiomAudit

#print axioms ceilingRatio_le_one
#print axioms refined_contraction_of_sharp
#print axioms chiStar_le_limitThreshold_of_poly
#print axioms chiStar_le_limitThreshold_of_gamma_add_one_le
#print axioms chiPos_squeeze_gap_step_refined_ceiling
#print axioms chiPos_refined_contraction_iff
#print axioms refined_threshold_gt_sharp_threshold

end AxiomAudit

end ShenWork.Paper1
