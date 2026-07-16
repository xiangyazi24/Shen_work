/- Uniform positive-strip power bounds for the faithful general-`m` Route-A estimate. -/
import ShenWork.Paper2.IntervalPositiveFloorNonlinearLipschitz
import ShenWork.Paper3.IntervalDomainEliminatedNonlinearity

namespace ShenWork.Paper3

open Set Real
open ShenWork.IntervalPositiveFloorNonlinearLipschitz

noncomputable section

/-- A fixed factor which controls both the value increment of `u ^ m` and
the chain-rule coefficient `m u^(m-1)` on the standard positive strip. -/
def paper3RouteAPowerFactor (p : CM2Params) (uStar : ℝ) : ℝ :=
  max 1 (powerLip p.m (uStar / 2) (3 * uStar / 2))

/-- A fixed absolute ceiling for `u ^ m` on the standard positive strip. -/
def paper3RouteAPowerCeiling (p : CM2Params) (uStar : ℝ) : ℝ :=
  1 + (3 * uStar / 2) ^ p.m

theorem paper3RouteAPowerFactor_one_le (p : CM2Params) (uStar : ℝ) :
    1 ≤ paper3RouteAPowerFactor p uStar := by
  exact le_max_left _ _

theorem paper3RouteAPowerFactor_nonneg (p : CM2Params) (uStar : ℝ) :
    0 ≤ paper3RouteAPowerFactor p uStar :=
  zero_le_one.trans (paper3RouteAPowerFactor_one_le p uStar)

theorem paper3RouteAPowerCeiling_pos
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    0 < paper3RouteAPowerCeiling p uStar := by
  unfold paper3RouteAPowerCeiling
  have hR : 0 ≤ 3 * uStar / 2 := by positivity
  linarith [Real.rpow_nonneg hR p.m]

/-- The positive-strip power increment is controlled by the fixed Route-A
factor times the underlying population increment. -/
theorem paper3RouteAPower_sub_le_factor_mul
    (p : CM2Params) {uStar x M : ℝ} (huStar : 0 < uStar)
    (hx : x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hxM : |x - uStar| ≤ M) :
    |x ^ p.m - uStar ^ p.m| ≤ paper3RouteAPowerFactor p uStar * M := by
  have hc : 0 < uStar / 2 := by linarith
  have huI : uStar ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    constructor <;> linarith
  have hlip := ShenWork.Paper2.rpow_lipschitz_on_pos_Icc
    p.hm hc hx huI
  have hpower :
      powerLip p.m (uStar / 2) (3 * uStar / 2) ≤
        paper3RouteAPowerFactor p uStar := by
    exact le_max_right _ _
  calc
    |x ^ p.m - uStar ^ p.m| ≤
        powerLip p.m (uStar / 2) (3 * uStar / 2) * |x - uStar| := by
      simpa [powerLip] using hlip
    _ ≤ paper3RouteAPowerFactor p uStar * |x - uStar| :=
      mul_le_mul_of_nonneg_right hpower (abs_nonneg _)
    _ ≤ paper3RouteAPowerFactor p uStar * M :=
      mul_le_mul_of_nonneg_left hxM
        (paper3RouteAPowerFactor_nonneg p uStar)

/-- The real-power chain-rule coefficient is uniformly bounded by the same
fixed factor on the positive strip. -/
theorem paper3RouteAPower_derivativeCoeff_le_factor
    (p : CM2Params) {uStar x : ℝ} (huStar : 0 < uStar)
    (hx : x ∈ Set.Icc (uStar / 2) (3 * uStar / 2)) :
    |p.m * x ^ (p.m - 1)| ≤ paper3RouteAPowerFactor p uStar := by
  have hc : 0 < uStar / 2 := by linarith
  have hxpos : 0 < x := hc.trans_le hx.1
  have hRpos : 0 < 3 * uStar / 2 := by positivity
  have hpow : x ^ (p.m - 1) ≤
      (uStar / 2) ^ (p.m - 1) + (3 * uStar / 2) ^ (p.m - 1) := by
    rcases le_or_gt 1 p.m with hm1 | hm1
    · have hmono : x ^ (p.m - 1) ≤ (3 * uStar / 2) ^ (p.m - 1) :=
        Real.rpow_le_rpow hxpos.le hx.2 (by linarith)
      linarith [Real.rpow_nonneg hc.le (p.m - 1)]
    · have hmono : x ^ (p.m - 1) ≤ (uStar / 2) ^ (p.m - 1) :=
        Real.rpow_le_rpow_of_nonpos hc hx.1 (by linarith)
      linarith [Real.rpow_nonneg hRpos.le (p.m - 1)]
  calc
    |p.m * x ^ (p.m - 1)| =
        p.m * x ^ (p.m - 1) := by
      rw [abs_of_nonneg]
      exact mul_nonneg p.hm.le (Real.rpow_nonneg hxpos.le _)
    _ ≤ powerLip p.m (uStar / 2) (3 * uStar / 2) := by
      exact mul_le_mul_of_nonneg_left hpow p.hm.le
    _ ≤ paper3RouteAPowerFactor p uStar := le_max_right _ _

/-- Multiplying the chain-rule coefficient by a derivative bounded by `M`
costs only the fixed Route-A power factor. -/
theorem paper3RouteAPower_derivative_le_factor_mul
    (p : CM2Params) {uStar x ux M : ℝ} (huStar : 0 < uStar)
    (hx : x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hux : |ux| ≤ M) :
    |p.m * x ^ (p.m - 1) * ux| ≤
      paper3RouteAPowerFactor p uStar * M := by
  rw [abs_mul]
  exact mul_le_mul
    (paper3RouteAPower_derivativeCoeff_le_factor p huStar hx) hux
    (abs_nonneg _) (paper3RouteAPowerFactor_nonneg p uStar)

/-- The physical power itself stays under the fixed Route-A ceiling. -/
theorem paper3RouteAPower_abs_le_ceiling
    (p : CM2Params) {uStar x : ℝ} (huStar : 0 < uStar)
    (hx : x ∈ Set.Icc (uStar / 2) (3 * uStar / 2)) :
    |x ^ p.m| ≤ paper3RouteAPowerCeiling p uStar := by
  have hxpos : 0 < x := (by linarith [huStar, hx.1])
  have hR0 : 0 ≤ 3 * uStar / 2 := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  unfold paper3RouteAPowerCeiling
  have hmono : x ^ p.m ≤ (3 * uStar / 2) ^ p.m :=
    Real.rpow_le_rpow hxpos.le hx.2 p.hm.le
  linarith [Real.rpow_nonneg hR0 p.m]

#print axioms paper3RouteAPower_sub_le_factor_mul
#print axioms paper3RouteAPower_derivative_le_factor_mul
#print axioms paper3RouteAPower_abs_le_ceiling

end

end ShenWork.Paper3
