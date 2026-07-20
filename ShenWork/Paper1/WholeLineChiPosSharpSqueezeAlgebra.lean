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
    (hL : 0 < L) (hLU : L ≤ U) (hs : 0 < s) (ha : 0 < a) :
    L ^ s * (U ^ a - L ^ a) ≤
      (a / (a + s)) * (U ^ (a + s) - L ^ (a + s)) := by
  let f : ℝ → ℝ := fun x =>
    a * (x ^ (a + s) - L ^ (a + s)) -
      (a + s) * L ^ s * (x ^ a - L ^ a)
  have hcont : ContinuousOn f (Set.Icc L U) := by
    unfold f
    fun_prop
  have hmono : MonotoneOn f (Set.Icc L U) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc L U) hcont
    intro x hx
    have hxpos : 0 < x := hL.trans_le hx.1
    have hderiv : HasDerivAt f
        (a * (a + s) * x ^ (a + s - 1) -
          (a + s) * L ^ s * (a * x ^ (a - 1))) x := by
      unfold f
      fun_prop
    rw [hderiv.deriv]
    have hLs : L ^ s ≤ x ^ s :=
      Real.rpow_le_rpow hL.le hx.1 hs.le
    have hxa : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxpos.le _
    have hsplit : x ^ (a + s - 1) = x ^ (a - 1) * x ^ s := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    rw [hsplit]
    nlinarith
  have hbase : f L ≤ f U := hmono (by simp) (by simp) hLU
  have hfL : f L = 0 := by simp [f]
  have hraw :
      (a + s) * (L ^ s * (U ^ a - L ^ a)) ≤
        a * (U ^ (a + s) - L ^ (a + s)) := by
    rw [hfL] at hbase
    dsimp [f] at hbase
    linarith
  have has : 0 < a + s := add_pos ha hs
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ has).2
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
      hell' (hell'one.trans honeM) hs ha
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
    exact mul_le_mul_of_nonneg_left h hchi
  have hchiCeiling :
      chi * (M' ^ (m - 1) * (M' ^ gamma - ell' ^ gamma)) ≤
        chi * (M' ^ alpha - ell' ^ alpha) :=
    mul_le_mul_of_nonneg_left hceilingAbsorb hchi
  nlinarith [hfloor, hceiling, hchiFloor, hchiCeiling]

/-- The sharp ratio condition is genuinely weaker than `chi < 1 / 2` at every
critical exponent with `m > 1`. -/
theorem half_mul_gamma_lt_alpha_mul_one_sub_half_of_m_gt_one
    {m gamma alpha : ℝ} (hm : 1 < m) (hgamma : 1 ≤ gamma)
    (hcritical : alpha = m + gamma - 1) :
    (1 / 2 : ℝ) * gamma < alpha * (1 - 1 / 2) := by
  rw [hcritical]
  linarith

section AxiomAudit

#print axioms rpow_small_prefactor_gap_le_ratio
#print axioms chiPos_squeeze_gap_step_m_gt_one
#print axioms half_mul_gamma_lt_alpha_mul_one_sub_half_of_m_gt_one

end AxiomAudit

end ShenWork.Paper1
