import ShenWork.Paper1.WholeLineChiPosSupercriticalAtoms

/-!
# The supercritical positive-sensitivity relaxing ceiling

Mirror of `wholeLineCauchyChiPosCeiling` for the branch
`q := m + γ - 1 < α`, based at the explicit parameter threshold
`wholeLineCauchyParameterCeiling p` and relaxing at the parameter-only rate
`d := α - q > 0`.

The worst-case scalar field at an approximate spatial maximum is
`F(s) = χ * s ^ (m + γ) + reactionFun α s`: after expanding the flux and using
`v_xx = v - u^γ`, the favorable zeroth-order piece `-χ u^m v ≤ 0` is discarded
and the adverse piece is exactly `+χ u^{m+γ}` (the resolver upper bound is only
used for the first-order drift coefficient, which vanishes at the contact
point).  No smallness condition on `χ > 0` is needed here — the only
load-bearing hypothesis is `d > 0`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The parameter-only relaxation rate of the supercritical ceiling. -/
def wholeLineCauchyChiPosSupercriticalRate (p : CMParams) : ℝ :=
  p.α - (p.m + p.γ - 1)

theorem wholeLineCauchyChiPosSupercriticalRate_pos
    {p : CMParams} (hsuper : p.m + p.γ - 1 < p.α) :
    0 < wholeLineCauchyChiPosSupercriticalRate p := by
  unfold wholeLineCauchyChiPosSupercriticalRate
  linarith

/-- The relaxing supercritical ceiling started at height `C`. -/
def wholeLineCauchyChiPosSupercriticalCeiling
    (p : CMParams) (C t : ℝ) : ℝ :=
  wholeLineCauchyParameterCeiling p +
    (C - wholeLineCauchyParameterCeiling p) *
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t)

theorem wholeLineCauchyChiPosSupercriticalCeiling_zero
    (p : CMParams) (C : ℝ) :
    wholeLineCauchyChiPosSupercriticalCeiling p C 0 = C := by
  simp [wholeLineCauchyChiPosSupercriticalCeiling]

theorem wholeLineCauchyChiPosSupercriticalCeiling_hasDerivAt
    (p : CMParams) (C t : ℝ) :
    HasDerivAt (wholeLineCauchyChiPosSupercriticalCeiling p C)
      (-wholeLineCauchyChiPosSupercriticalRate p *
        ((C - wholeLineCauchyParameterCeiling p) *
          Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t))) t := by
  have hlin : HasDerivAt
      (fun s : ℝ => -wholeLineCauchyChiPosSupercriticalRate p * s)
      (-wholeLineCauchyChiPosSupercriticalRate p) t := by
    simpa using (hasDerivAt_id t).const_mul
      (-wholeLineCauchyChiPosSupercriticalRate p)
  have hexp := hlin.exp
  have := (hexp.const_mul (C - wholeLineCauchyParameterCeiling p)).const_add
    (wholeLineCauchyParameterCeiling p)
  convert this using 1
  · ring

/-- The ceiling stays above its parameter base when started above it. -/
theorem wholeLineCauchyChiPosSupercriticalCeiling_base_le
    {p : CMParams} {C : ℝ}
    (hC : wholeLineCauchyParameterCeiling p ≤ C) (t : ℝ) :
    wholeLineCauchyParameterCeiling p ≤
      wholeLineCauchyChiPosSupercriticalCeiling p C t := by
  unfold wholeLineCauchyChiPosSupercriticalCeiling
  have hexp : 0 < Real.exp
      (-wholeLineCauchyChiPosSupercriticalRate p * t) := Real.exp_pos _
  nlinarith [sub_nonneg.mpr hC, hexp.le]

/-- The ceiling never exceeds its initial height (for `t ≥ 0`). -/
theorem wholeLineCauchyChiPosSupercriticalCeiling_le
    {p : CMParams} {C t : ℝ}
    (hC : wholeLineCauchyParameterCeiling p ≤ C)
    (hsuper : p.m + p.γ - 1 < p.α) (ht : 0 ≤ t) :
    wholeLineCauchyChiPosSupercriticalCeiling p C t ≤ C := by
  unfold wholeLineCauchyChiPosSupercriticalCeiling
  have hrate := wholeLineCauchyChiPosSupercriticalRate_pos hsuper
  have hexp_le : Real.exp
      (-wholeLineCauchyChiPosSupercriticalRate p * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  nlinarith [sub_nonneg.mpr hC]

/-- The restart identity: relaxing from the height reached at time `a` for a
further time `s` is the same as relaxing from `C` for time `a + s`. -/
theorem wholeLineCauchyChiPosSupercriticalCeiling_restart
    (p : CMParams) (C a s : ℝ) :
    wholeLineCauchyChiPosSupercriticalCeiling p
        (wholeLineCauchyChiPosSupercriticalCeiling p C a) s =
      wholeLineCauchyChiPosSupercriticalCeiling p C (a + s) := by
  unfold wholeLineCauchyChiPosSupercriticalCeiling
  have hexp : Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * a) *
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * s) =
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * (a + s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- The explicit supercritical parameter threshold is at least one. -/
theorem one_le_wholeLineCauchyParameterCeiling_of_supercritical
    (p : CMParams) (hsuper : p.m + p.γ - 1 < p.α) :
    1 ≤ wholeLineCauchyParameterCeiling p := by
  unfold wholeLineCauchyParameterCeiling
  rw [if_pos hsuper]
  exact le_max_left _ _

/-- Above the explicit threshold the `d`-power exceeds `1 + χ`.  This is the
scalar margin that pays for the relaxation rate. -/
theorem wholeLineCauchyParameterCeiling_pow_gap_of_supercritical
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM : wholeLineCauchyParameterCeiling p ≤ M) :
    1 + p.χ ≤ M ^ (p.α - (p.m + p.γ - 1)) := by
  have hd : 0 < p.α - (p.m + p.γ - 1) := by linarith
  have hbase : (0 : ℝ) ≤ 1 + max p.χ 0 := by positivity
  have hthreshold :
      max 1 ((1 + max p.χ 0) ^ (1 / (p.α - (p.m + p.γ - 1)))) ≤ M := by
    have := hM
    unfold wholeLineCauchyParameterCeiling at this
    rwa [if_pos hsuper] at this
  have hrootM : (1 + max p.χ 0) ^ (1 / (p.α - (p.m + p.γ - 1))) ≤ M :=
    (le_max_right _ _).trans hthreshold
  have hroot :
      ((1 + max p.χ 0) ^ (1 / (p.α - (p.m + p.γ - 1)))) ^
          (p.α - (p.m + p.γ - 1)) = 1 + max p.χ 0 := by
    rw [one_div, Real.rpow_inv_rpow hbase hd.ne']
  have hstep := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hrootM hd.le
  rw [hroot] at hstep
  simpa [max_eq_left hχ] using hstep

/-- The supersolution inequality at the ceiling value.  For every
`B ≥ wholeLineCauchyParameterCeiling p`, the worst-case scalar field plus the
relaxation rate term is nonpositive. -/
theorem chiPosSupercriticalCeiling_supersolution
    {p : CMParams} (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {B : ℝ} (hB : wholeLineCauchyParameterCeiling p ≤ B) :
    p.χ * B ^ (p.m + p.γ) + reactionFun p.α B +
        wholeLineCauchyChiPosSupercriticalRate p *
          (B - wholeLineCauchyParameterCeiling p) ≤ 0 := by
  have hq : (1 : ℝ) ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hq0 : (0 : ℝ) ≤ p.m + p.γ - 1 := by linarith
  have hd : 0 < p.α - (p.m + p.γ - 1) := by linarith
  have hM1 : (1 : ℝ) ≤ wholeLineCauchyParameterCeiling p :=
    one_le_wholeLineCauchyParameterCeiling_of_supercritical p hsuper
  have hM0 : (0 : ℝ) < wholeLineCauchyParameterCeiling p :=
    zero_lt_one.trans_le hM1
  have hB1 : (1 : ℝ) ≤ B := hM1.trans hB
  have hB0 : (0 : ℝ) < B := zero_lt_one.trans_le hB1
  have hgapM : 1 + p.χ ≤
      (wholeLineCauchyParameterCeiling p) ^ (p.α - (p.m + p.γ - 1)) :=
    wholeLineCauchyParameterCeiling_pow_gap_of_supercritical p hχ hsuper (le_refl (wholeLineCauchyParameterCeiling p))
  -- power algebra
  have hpowB : B ^ (p.m + p.γ) = B ^ (p.m + p.γ - 1) * B := by
    rw [show B ^ (p.m + p.γ - 1) * B
        = B ^ (p.m + p.γ - 1) * B ^ (1 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hB0]
    congr 1; ring
  have hpowAlpha :
      B ^ p.α = B ^ (p.m + p.γ - 1) * B ^ (p.α - (p.m + p.γ - 1)) := by
    rw [← Real.rpow_add hB0]; congr 1; ring
  have hBq1 : (1 : ℝ) ≤ B ^ (p.m + p.γ - 1) := Real.one_le_rpow hB1 hq0
  have hBqpos : (0 : ℝ) < B ^ (p.m + p.γ - 1) :=
    Real.rpow_pos_of_pos hB0 _
  -- the scaled gap pays for the relaxation rate
  have hgap := rpow_supercritical_scaled_gap hM0 hB hq0 hd
  have hMalpha : (1 : ℝ) ≤
      (wholeLineCauchyParameterCeiling p) ^
        ((p.m + p.γ - 1) + (p.α - (p.m + p.γ - 1))) :=
    Real.one_le_rpow hM1 (by linarith)
  have hBM : 0 ≤ B - wholeLineCauchyParameterCeiling p := by linarith
  have hrate :
      (p.α - (p.m + p.γ - 1)) *
          (B - wholeLineCauchyParameterCeiling p) ≤
        B ^ ((p.m + p.γ - 1) + 1) *
          (B ^ (p.α - (p.m + p.γ - 1)) -
            (wholeLineCauchyParameterCeiling p) ^
              (p.α - (p.m + p.γ - 1))) := by
    refine le_trans ?_ hgap
    nlinarith [mul_nonneg hd.le hBM]
  have hBq1' : B ^ ((p.m + p.γ - 1) + 1) = B ^ (p.m + p.γ - 1) * B := by
    rw [Real.rpow_add hB0, Real.rpow_one]
  rw [hBq1'] at hrate
  -- the base margin turns the ceiling power into the χ budget
  have hkey :
      B ^ (p.m + p.γ - 1) * B *
          (B ^ (p.α - (p.m + p.γ - 1)) -
            (wholeLineCauchyParameterCeiling p) ^
              (p.α - (p.m + p.γ - 1))) ≤
        B ^ (p.m + p.γ - 1) * B *
          (B ^ (p.α - (p.m + p.γ - 1)) - 1 - p.χ) := by
    have hstep : B ^ (p.α - (p.m + p.γ - 1)) -
        (wholeLineCauchyParameterCeiling p) ^ (p.α - (p.m + p.γ - 1)) ≤
        B ^ (p.α - (p.m + p.γ - 1)) - 1 - p.χ := by linarith
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  have hrateDef : wholeLineCauchyChiPosSupercriticalRate p =
      p.α - (p.m + p.γ - 1) := rfl
  rw [hrateDef]
  unfold reactionFun
  rw [hpowB, hpowAlpha]
  nlinarith [hrate, hkey, hBq1, hB0.le]

section AxiomAudit

#print axioms wholeLineCauchyChiPosSupercriticalRate_pos
#print axioms wholeLineCauchyChiPosSupercriticalCeiling_zero
#print axioms wholeLineCauchyChiPosSupercriticalCeiling_hasDerivAt
#print axioms wholeLineCauchyChiPosSupercriticalCeiling_base_le
#print axioms wholeLineCauchyChiPosSupercriticalCeiling_le
#print axioms wholeLineCauchyChiPosSupercriticalCeiling_restart
#print axioms one_le_wholeLineCauchyParameterCeiling_of_supercritical
#print axioms wholeLineCauchyParameterCeiling_pow_gap_of_supercritical
#print axioms chiPosSupercriticalCeiling_supersolution

end AxiomAudit

end ShenWork.Paper1
