import ShenWork.Paper3.IntervalDomainMMinimalGoodSlice
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.PoincareInequality
import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassConvergence

/-!
# Negative-power boxes from minimal good slices

For `m > 1`, the entropy dissipation is the squared `L²` norm of the
derivative of `u^(1-m)`, up to the factor `(m-1)²`.  On the unit interval this
gives the endpoint-safe oscillation estimate

`osc (u^(1-m)) ≤ (m-1) sqrt G`.

Mass conservation supplies a point at which `u = uStar`, so a sufficiently
small oscillation places the whole slice in any prescribed positive sup
neighborhood of `uStar`.  The final theorem combines this static fact with
the arbitrarily late good slices from `IntervalDomainMMinimalGoodSlice`.
-/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- Endpoint-safe oscillation estimate for a positive real power of a `C²`
interval profile. -/
theorem intervalDomainLift_rpow_oscillation_le
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Icc (0 : ℝ) 1))
    {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |(intervalDomainLift f x) ^ (q / 2) -
        (intervalDomainLift f z) ^ (q / 2)| ≤
      Real.sqrt
        ((q ^ 2 / 4) *
          intervalDomain.integral
            (fun y => f y ^ (q - 2) * (intervalDomain.gradNorm f y) ^ 2)) := by
  let Y : ℝ → ℝ := fun y => (intervalDomainLift f y) ^ (q / 2)
  let Y' : ℝ → ℝ := fun y =>
    (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      deriv (intervalDomainLift f) y
  have hYcont : ContinuousOn Y (Icc (0 : ℝ) 1) := by
    simpa [Y] using
      intervalDomainLift_rpow_continuousOn_Icc (q := q) hf_pos hfC2
  have hYderiv : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt Y (Y' y) (Ioi y) y := by
    simpa [Y, Y'] using
      intervalDomainLift_rpow_hasDerivWithinAt_Ioi (q := q) hf_pos hfC2
  have hY'int : IntervalIntegrable Y' volume (0 : ℝ) 1 := by
    simpa [Y'] using
      intervalDomainLift_rpow_deriv_intervalIntegrable (q := q) hf_pos hfC2
  have hY'sqint : IntervalIntegrable (fun y => (Y' y) ^ 2)
      volume (0 : ℝ) 1 := by
    simpa [Y'] using
      intervalDomainLift_rpow_deriv_sq_intervalIntegrable (q := q) hf_pos hfC2
  have hftc :
      ∫ y in z..x, Y' y = Y x - Y z := by
    have hsub : uIcc z x ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc hz hx
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (hcont := hYcont.mono hsub)
      (hderiv := by
        intro y hy
        have hy_uIoo : y ∈ uIoo z x := by
          simpa [Ioo_min_max] using hy
        exact hYderiv y (uIoo_subset_Ioo hz hx hy_uIoo))
      (hint := hY'int.mono
        (uIcc_subset_uIcc (Icc_subset_uIcc hz) (Icc_subset_uIcc hx))
        le_rfl)
  have hY'absint : IntervalIntegrable (fun y => |Y' y|)
      volume (0 : ℝ) 1 := by
    simpa only [Real.norm_eq_abs] using hY'int.norm
  have hsegment :
      |∫ y in z..x, Y' y| ≤ ∫ y in (0 : ℝ)..1, |Y' y| := by
    rcases le_or_gt z x with hzx | hxz
    · calc
        |∫ y in z..x, Y' y| ≤ ∫ y in z..x, |Y' y| :=
          intervalIntegral.abs_integral_le_integral_abs hzx
        _ ≤ ∫ y in (0 : ℝ)..1, |Y' y| :=
          intervalIntegral.integral_mono_interval hz.1 hzx hx.2
            (Filter.Eventually.of_forall fun _ => abs_nonneg _) hY'absint
    · rw [intervalIntegral.integral_symm, abs_neg]
      calc
        |∫ y in x..z, Y' y| ≤ ∫ y in x..z, |Y' y| :=
          intervalIntegral.abs_integral_le_integral_abs hxz.le
        _ ≤ ∫ y in (0 : ℝ)..1, |Y' y| :=
          intervalIntegral.integral_mono_interval hx.1 hxz.le hz.2
            (Filter.Eventually.of_forall fun _ => abs_nonneg _) hY'absint
  have hcs :
      (∫ y in (0 : ℝ)..1, |Y' y|) ≤
        Real.sqrt (∫ y in (0 : ℝ)..1, (Y' y) ^ 2) := by
    have hprod : IntervalIntegrable (fun y => |Y' y * (1 : ℝ)|)
        volume (0 : ℝ) 1 := by
      simpa only [mul_one] using hY'absint
    have hraw := ShenWork.GagliardoNirenberg.integral_abs_mul_le_sqrt
      (L := 1) (by norm_num : (0 : ℝ) < 1)
      hY'sqint intervalIntegrable_const hprod
    simpa only [mul_one, one_pow, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, Real.sqrt_one] using hraw
  have hsq :
      (∫ y in (0 : ℝ)..1, (Y' y) ^ 2) =
        (q ^ 2 / 4) *
          intervalDomain.integral
            (fun y => f y ^ (q - 2) * (intervalDomain.gradNorm f y) ^ 2) := by
    simpa [Y'] using
      intervalDomainLift_rpow_deriv_sq_integral_eq (q := q) hf_pos
  rw [← hftc]
  exact hsegment.trans (hcs.trans_eq (congrArg Real.sqrt hsq))

/-- The negative-power oscillation radius associated with one dissipation
slice. -/
def minimalMNegativePowerOscillationRadius
    (p : CM2Params) (G : ℝ) : ℝ :=
  (p.m - 1) * Real.sqrt G

/-- The explicit negative-power radius which guarantees entry into the
`delta` sup neighborhood of a positive equilibrium. -/
def minimalMNegativePowerBasinRadius
    (p : CM2Params) (uStar delta : ℝ) : ℝ :=
  min
    (uStar ^ (1 - p.m) - (uStar + delta) ^ (1 - p.m))
    (((uStar - delta) ^ (1 - p.m) - uStar ^ (1 - p.m)) / 2)

/-- Positivity of the explicit negative-power basin radius. -/
theorem minimalMNegativePowerBasinRadius_pos
    (p : CM2Params) {uStar delta : ℝ}
    (hm : 1 < p.m) (huStar : 0 < uStar)
    (hdelta : 0 < delta) (hdeltaStar : delta < uStar) :
    0 < minimalMNegativePowerBasinRadius p uStar delta := by
  have hexp : 1 - p.m < 0 := by linarith
  have hplus : 0 < uStar + delta := by linarith
  have hminus : 0 < uStar - delta := by linarith
  have hupPow :
      (uStar + delta) ^ (1 - p.m) < uStar ^ (1 - p.m) := by
    exact (Real.rpow_lt_rpow_iff_of_neg hplus huStar hexp).2 (by linarith)
  have hlowPow :
      uStar ^ (1 - p.m) < (uStar - delta) ^ (1 - p.m) := by
    exact (Real.rpow_lt_rpow_iff_of_neg huStar hminus hexp).2 (by linarith)
  unfold minimalMNegativePowerBasinRadius
  exact lt_min (sub_pos.mpr hupPow) (div_pos (sub_pos.mpr hlowPow) (by norm_num))

/-- On a classical slice, the entropy dissipation controls the oscillation of
`u^(1-m)` with the exact coefficient `m-1`. -/
theorem intervalDomainM_negativePower_oscillation_le
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 < p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (x z : intervalDomainPoint) :
    |(u t x) ^ (1 - p.m) - (u t z) ^ (1 - p.m)| ≤
      minimalMNegativePowerOscillationRadius p
        (intervalDomainLpWeightedGradientDissipation
          (2 - 2 * p.m) u t) := by
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hpos : ∀ y : intervalDomainPoint, 0 < u t y :=
    fun y => u_pos hsol ht0 htT y
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hraw := intervalDomainLift_rpow_oscillation_le
    (q := 2 - 2 * p.m) hpos hC2 x.property z.property
  have hG :
      intervalDomain.integral
          (fun y => (u t y) ^ ((2 - 2 * p.m) - 2) *
            (intervalDomain.gradNorm (u t) y) ^ 2) =
        intervalDomainLpWeightedGradientDissipation
          (2 - 2 * p.m) u t := rfl
  have hcoef : (2 - 2 * p.m) ^ 2 / 4 = (p.m - 1) ^ 2 := by ring
  have hm1 : 0 ≤ p.m - 1 := by linarith
  change
    |(intervalDomainLift (u t) x.1) ^ ((2 - 2 * p.m) / 2) -
        (intervalDomainLift (u t) z.1) ^ ((2 - 2 * p.m) / 2)| ≤
      Real.sqrt
        (((2 - 2 * p.m) ^ 2 / 4) *
          intervalDomain.integral
            (fun y => (u t y) ^ ((2 - 2 * p.m) - 2) *
              (intervalDomain.gradNorm (u t) y) ^ 2)) at hraw
  rw [hcoef, hG, Real.sqrt_mul (sq_nonneg (p.m - 1)),
    Real.sqrt_sq hm1] at hraw
  simpa [minimalMNegativePowerOscillationRadius, intervalDomainLift,
    x.property, z.property, show (2 - 2 * p.m) / 2 = 1 - p.m by ring] using hraw

/-- A continuous interval profile which is pointwise strictly below a fixed
absolute bound is strictly below it in the concrete interval supremum norm. -/
theorem intervalDomain_supNorm_lt_of_continuous_pointwise_abs_lt
    {f : intervalDomainPoint → ℝ} {K : ℝ}
    (hf : Continuous f) (hpoint : ∀ x, |f x| < K) :
    intervalDomain.supNorm f < K := by
  letI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : Nonempty intervalDomainPoint :=
    ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
  obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
    Set.univ_nonempty hf.abs.continuousOn
  have hsup : intervalDomain.supNorm f ≤ |f xmax| :=
    intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => hmax (Set.mem_univ x))
  exact hsup.trans_lt (hpoint xmax)

/-- A negative-power oscillation below the explicit radius puts the entire
mass-constrained slice in the prescribed sup neighborhood. -/
theorem intervalDomainM_supClose_of_negativePower_oscillation
    {p : CM2Params} {T t uStar delta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 < p.m) (huStar : 0 < uStar)
    (hdelta : 0 < delta) (hdeltaStar : delta < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmass : intervalDomainM.integral (u t) = uStar)
    (hradius :
      minimalMNegativePowerOscillationRadius p
          (intervalDomainLpWeightedGradientDissipation
            (2 - 2 * p.m) u t) <
        minimalMNegativePowerBasinRadius p uStar delta) :
    SupCloseToConstant intervalDomainM (u t) uStar delta := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Icc (0 : ℝ) 1) := by
    simpa [U] using solution_lift_continuousOn_Icc hsol ht
  have hUint : IntervalIntegrable U volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hUcont
  have hmassLift : (∫ y in (0 : ℝ)..1, U y) = uStar := by
    simpa [U, intervalDomainM] using hmass
  have hzero : (∫ y in (0 : ℝ)..1, (U y - uStar)) = 0 := by
    rw [intervalIntegral.integral_sub hUint intervalIntegrable_const,
      intervalIntegral.integral_const, hmassLift]
    norm_num [smul_eq_mul]
  obtain ⟨z, hz, hzroot⟩ :=
    ShenWork.Poincare.continuous_zero_integral_has_root
      (L := 1) (by norm_num) (hUcont.sub continuousOn_const) hzero
  let zPoint : intervalDomainPoint := ⟨z, hz⟩
  have hzval : u t zPoint = uStar := by
    have : U z = uStar := by linarith
    simpa [U, zPoint, intervalDomainLift, hz] using this
  have hexp : 1 - p.m < 0 := by linarith
  have hminus : 0 < uStar - delta := by linarith
  have hplus : 0 < uStar + delta := by linarith
  have hsliceCont : Continuous (u t) :=
    solutionSlice_continuous hsol ht
  apply intervalDomain_supNorm_lt_of_continuous_pointwise_abs_lt
    (hf := hsliceCont.sub continuous_const)
  intro x
  have hosc := intervalDomainM_negativePower_oscillation_le
    hm hsol ht0 htT x zPoint
  rw [hzval] at hosc
  have hpowClose :
      |(u t x) ^ (1 - p.m) - uStar ^ (1 - p.m)| <
        minimalMNegativePowerBasinRadius p uStar delta :=
    hosc.trans_lt hradius
  have hpowBounds := (abs_lt.mp hpowClose)
  have hrLeft :
      minimalMNegativePowerBasinRadius p uStar delta ≤
        uStar ^ (1 - p.m) - (uStar + delta) ^ (1 - p.m) :=
    min_le_left _ _
  have hrRight :
      minimalMNegativePowerBasinRadius p uStar delta ≤
        ((uStar - delta) ^ (1 - p.m) - uStar ^ (1 - p.m)) / 2 :=
    min_le_right _ _
  have hupPow :
      (uStar + delta) ^ (1 - p.m) < (u t x) ^ (1 - p.m) := by
    linarith
  have hlowPow :
      (u t x) ^ (1 - p.m) < (uStar - delta) ^ (1 - p.m) := by
    have hgapPos :
        0 < (uStar - delta) ^ (1 - p.m) - uStar ^ (1 - p.m) := by
      exact sub_pos.mpr
        ((Real.rpow_lt_rpow_iff_of_neg huStar hminus hexp).2 (by linarith))
    linarith
  have hux : 0 < u t x := u_pos hsol ht0 htT x
  have hupper : u t x < uStar + delta :=
    (Real.rpow_lt_rpow_iff_of_neg hplus hux hexp).1 hupPow
  have hlower : uStar - delta < u t x :=
    (Real.rpow_lt_rpow_iff_of_neg hux hminus hexp).1 hlowPow
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The exact small-sensitivity threshold associated with a prescribed local
sup basin radius `delta`. -/
def supercriticalSmallSensitivityThresholdM
    (p : CM2Params) (uStar delta : ℝ) : ℝ :=
  minimalMNegativePowerBasinRadius p uStar delta /
    ((p.m - 1) * Real.sqrt p.μ * signalSaturationFactor p.β)

/-- Equivalent product form of the explicit small-sensitivity condition. -/
theorem chi_lt_supercriticalSmallSensitivityThresholdM_iff
    (p : CM2Params) {uStar delta : ℝ}
    (hm : 1 < p.m) (hbeta : 1 ≤ p.β) :
    p.χ₀ < supercriticalSmallSensitivityThresholdM p uStar delta ↔
      (p.m - 1) * p.χ₀ * Real.sqrt p.μ *
          signalSaturationFactor p.β <
        minimalMNegativePowerBasinRadius p uStar delta := by
  have hden :
      0 < (p.m - 1) * Real.sqrt p.μ * signalSaturationFactor p.β :=
    mul_pos
      (mul_pos (sub_pos.mpr hm) (Real.sqrt_pos.2 p.hμ))
      (signalSaturationFactor_pos hbeta)
  unfold supercriticalSmallSensitivityThresholdM
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- Under the explicit small-`chi₀` condition, every minimal global orbit
with equilibrium mass has an arbitrarily late slice in the prescribed local
sup basin. -/
theorem intervalDomainM_minimal_exists_late_supClose_smallSensitivity
    (p : CM2Params) (hm : 1 < p.m)
    {uStar vStar delta : ℝ}
    (hb0 : p.b = 0) (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hdelta : 0 < delta) (hdeltaStar : delta < uStar)
    (hsmall :
      p.χ₀ < supercriticalSmallSensitivityThresholdM p uStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    {T : ℝ} (hT : 0 < T) :
    ∃ t, T ≤ t ∧
      SupCloseToConstant intervalDomainM (u t) uStar delta := by
  let r : ℝ := minimalMNegativePowerBasinRadius p uStar delta
  let a : ℝ :=
    p.χ₀ * Real.sqrt p.μ * signalSaturationFactor p.β
  let b : ℝ := r / (p.m - 1)
  have hr : 0 < r := by
    exact minimalMNegativePowerBasinRadius_pos
      p hm heq.u_pos hdelta hdeltaStar
  have ha : 0 < a := by
    exact mul_pos
      (mul_pos hchi (Real.sqrt_pos.2 p.hμ))
      (signalSaturationFactor_pos hbeta)
  have hb : 0 < b := div_pos hr (sub_pos.mpr hm)
  have hproduct :
      (p.m - 1) * p.χ₀ * Real.sqrt p.μ *
          signalSaturationFactor p.β < r := by
    simpa [r] using
      (chi_lt_supercriticalSmallSensitivityThresholdM_iff
        p hm hbeta).1 hsmall
  have hab : a < b := by
    rw [show a = p.χ₀ * Real.sqrt p.μ *
        signalSaturationFactor p.β by rfl,
      show b = r / (p.m - 1) by rfl]
    exact (lt_div_iff₀ (sub_pos.mpr hm)).2 (by
      nlinarith [hproduct])
  have hfloor :
      minimalMGoodSliceDissipationFloor p = a ^ 2 := by
    unfold minimalMGoodSliceDissipationFloor
    dsimp [a]
    rw [mul_pow, mul_pow, Real.sq_sqrt p.hμ.le]
  let eps : ℝ := b ^ 2 - minimalMGoodSliceDissipationFloor p
  have heps : 0 < eps := by
    rw [show eps = b ^ 2 - minimalMGoodSliceDissipationFloor p by rfl,
      hfloor, sub_pos]
    exact (sq_lt_sq₀ ha.le hb.le).2 hab
  obtain ⟨t, htT, hgood⟩ :=
    intervalDomainM_minimal_exists_late_goodSlice
      p hm hb0 hbeta heq huv hT heps
  have ht0 : 0 < t := lt_of_lt_of_le hT htT
  have hH : 0 < t + 1 := by linarith
  let G : ℝ :=
    intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t
  have hGlt : G < b ^ 2 := by
    change G < minimalMGoodSliceDissipationFloor p + eps at hgood
    dsimp [eps] at hgood
    linarith
  have hsqrt : Real.sqrt G < b :=
    (Real.sqrt_lt' hb).2 hGlt
  have hrb : r = (p.m - 1) * b := by
    dsimp [b]
    field_simp [ne_of_gt (sub_pos.mpr hm)]
  have hoscRadius :
      minimalMNegativePowerOscillationRadius p G < r := by
    unfold minimalMNegativePowerOscillationRadius
    rw [hrb]
    exact mul_lt_mul_of_pos_left hsqrt (sub_pos.mpr hm)
  have hmassT : intervalDomainM.integral (u t) = uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomainM] using
      hmass t ht0
  refine ⟨t, htT, ?_⟩
  apply intervalDomainM_supClose_of_negativePower_oscillation
    hm heq.u_pos hdelta hdeltaStar
      (huv.classical (t + 1) hH) ht0 (by linarith) hmassT
  simpa [G, r] using hoscRadius

#print axioms intervalDomainLift_rpow_oscillation_le
#print axioms minimalMNegativePowerBasinRadius_pos
#print axioms intervalDomainM_negativePower_oscillation_le
#print axioms intervalDomainM_supClose_of_negativePower_oscillation
#print axioms chi_lt_supercriticalSmallSensitivityThresholdM_iff
#print axioms intervalDomainM_minimal_exists_late_supClose_smallSensitivity

end

end ShenWork.Paper3
