import ShenWork.Paper1.WholeLineWeightedRegularityRestart
import ShenWork.Paper1.WholeLineWeightedRegularityUnweightedSecondBound

open Filter Topology MeasureTheory Real Set
open scoped Interval Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical bounded-window drift restart

This file discharges the concrete bounded-joint hypotheses of the whole-line
drift restart theorem from the positive-time regularity of the canonical BUC
fixed point.  No differentiated nonlinear-flux or stronger exponential weight
is used.
-/

/-- Separate time differentiability and a jointly continuous spatial
derivative give the full derivative on a product.  Only the spatial partial
has to be continuous: the proof splits an increment first in space at the new
time and then in time at the fixed base point. -/
theorem hasFDerivAt_prod_of_time_slice_of_spatial_continuousAt
    {f ft fx : ℝ → ℝ → ℝ} {t x : ℝ}
    (htime : HasDerivAt (fun r => f r x) (ft t x) t)
    (hspace : ∀ᶠ r in 𝓝 t, ∀ y, HasDerivAt (f r) (fx r y) y)
    (hfx : ContinuousAt (fun q : ℝ × ℝ => fx q.1 q.2) (t, x)) :
    HasFDerivAt
      (fun q : ℝ × ℝ => f q.1 q.2)
      (ft t x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        fx t x • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, x) := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  have htimeO := htime.hasFDerivAt.isLittleO
  have htimeBound := htimeO.bound (half_pos heps)
  have htimeProd : ∀ᶠ q in 𝓝 (t, x),
      ‖f q.1 x - f t x - (ft t x) * (q.1 - t)‖ ≤
        (eps / 2) * ‖q.1 - t‖ := by
    have hfst : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝 (t, x)) (𝓝 t) :=
      continuousAt_fst
    filter_upwards [hfst.eventually htimeBound] with q hq
    simpa [mul_comm] using hq
  have hspaceProd : ∀ᶠ q : ℝ × ℝ in 𝓝 (t, x),
      ∀ y, HasDerivAt (f q.1) (fx q.1 y) y :=
    (show Tendsto (fun q : ℝ × ℝ => q.1) (𝓝 (t, x)) (𝓝 t) from
      continuousAt_fst).eventually hspace
  rw [Metric.continuousAt_iff] at hfx
  obtain ⟨delta, hdelta, hfxClose⟩ := hfx (eps / 2) (half_pos heps)
  filter_upwards [htimeProd, hspaceProd,
    Metric.ball_mem_nhds (t, x) hdelta] with q htimeQ hspaceQ hq
  have hqdist : dist q (t, x) < delta := Metric.mem_ball.mp hq
  have hqt : dist q.1 t < delta := by
    exact (le_max_left _ _).trans_lt (by simpa [Prod.dist_eq] using hqdist)
  have hqx : dist q.2 x < delta := by
    exact (le_max_right _ _).trans_lt (by simpa [Prod.dist_eq] using hqdist)
  let g : ℝ → ℝ := fun z => f q.1 z - fx t x * z
  have hg : ∀ z, HasDerivAt g (fx q.1 z - fx t x) z := by
    intro z
    have hlin : HasDerivAt (fun w : ℝ => fx t x * w) (fx t x) z := by
      simpa using (hasDerivAt_id z).const_mul (fx t x)
    exact (hspaceQ z).sub hlin
  have hspatial : ‖g q.2 - g x‖ ≤ (eps / 2) * ‖q.2 - x‖ := by
    apply (convex_uIcc x q.2).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun z => fx q.1 z - fx t x)
      (fun z _ => (hg z).hasDerivWithinAt) _ left_mem_uIcc right_mem_uIcc
    intro z hz
    have hzx : dist z x ≤ dist q.2 x := by
      simpa [dist_comm] using Real.dist_left_le_of_mem_uIcc hz
    have hpair : dist (q.1, z) (t, x) < delta := by
      simp only [Prod.dist_eq]
      exact max_lt hqt (hzx.trans_lt hqx)
    have hclose := hfxClose hpair
    simpa [Real.dist_eq, Real.norm_eq_abs] using hclose.le
  have hcoordT : ‖q.1 - t‖ ≤ ‖q - (t, x)‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hcoordX : ‖q.2 - x‖ ≤ ‖q - (t, x)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  change
    ‖f q.1 q.2 - f t x -
        (ft t x • ContinuousLinearMap.fst ℝ ℝ ℝ +
          fx t x • ContinuousLinearMap.snd ℝ ℝ ℝ) (q - (t, x))‖ ≤
      eps * ‖q - (t, x)‖
  calc
    _ = ‖(g q.2 - g x) +
          (f q.1 x - f t x - ft t x * (q.1 - t))‖ := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
        Prod.fst_sub, Prod.snd_sub]
      dsimp [g]
      congr 1
      ring
    _ ≤ ‖g q.2 - g x‖ +
          ‖f q.1 x - f t x - ft t x * (q.1 - t)‖ := norm_add_le _ _
    _ ≤ (eps / 2) * ‖q.2 - x‖ +
          (eps / 2) * ‖q.1 - t‖ := add_le_add hspatial htimeQ
    _ ≤ (eps / 2) * ‖q - (t, x)‖ +
          (eps / 2) * ‖q - (t, x)‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcoordX (half_pos heps).le)
        (mul_le_mul_of_nonneg_left hcoordT (half_pos heps).le)
    _ = eps * ‖q - (t, x)‖ := by ring

#print axioms hasFDerivAt_prod_of_time_slice_of_spatial_continuousAt

/-- On every strictly positive canonical slice, BUC continuity together with
the compact-window Holder bound on `u_x` upgrades to uniform-in-space time
continuity of `u_x`. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_deriv_uniformContinuousAt_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1) (hzT : z.1 < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta) :
    ∀ eps > 0, ∃ delta > 0, ∀ s,
      |s - z.1| < delta → ∀ x,
      |deriv
          (fun y : ℝ =>
            (wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 y) x -
        deriv
          (fun y : ℝ =>
            (wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) z.1).1 y) x| < eps := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let E : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT U
  let a : ℝ := z.1 / 2
  let b : ℝ := (z.1 + T) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith [z.2.2]
  have hbT : b ≤ T := by dsimp [b]; linarith
  have hztWindow : z.1 ∈ Set.Icc a b := by
    dsimp [a, b]
    constructor <;> linarith
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel with
    ⟨H, hH, hholder⟩
  have hEcont : Continuous E := by
    simpa [E] using wholeLineBUCTrajectoryExtend_continuous hT U
  intro eps heps
  let r : ℝ := (eps / (8 * (H + 1))) ^ (1 / eta)
  have hden : 0 < 8 * (H + 1) := by positivity
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (div_pos heps hden) _
  have hrpow : r ^ eta = eps / (8 * (H + 1)) := by
    dsimp [r]
    rw [← Real.rpow_mul (div_pos heps hden).le, one_div,
      inv_mul_cancel₀ (ne_of_gt heta0), Real.rpow_one]
  let d : ℝ := eps * r / 8
  have hd : 0 < d := by dsimp [d]; positivity
  have hEAt : ContinuousAt E z.1 := hEcont.continuousAt
  rw [Metric.continuousAt_iff] at hEAt
  obtain ⟨deltaE, hdeltaE, hclose⟩ := hEAt d hd
  let delta : ℝ := min deltaE (min (z.1 - a) (b - z.1))
  have hza : 0 < z.1 - a := by dsimp [a]; linarith
  have hbz : 0 < b - z.1 := by dsimp [b]; linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdeltaE (lt_min hza hbz)
  refine ⟨delta, hdelta, ?_⟩
  intro s hs x
  have hsE : dist s z.1 < deltaE := by
    rw [Real.dist_eq]
    exact hs.trans_le (min_le_left _ _)
  have hsWindow : s ∈ Set.Icc a b := by
    have hsInner : |s - z.1| < min (z.1 - a) (b - z.1) :=
      hs.trans_le (min_le_right deltaE _)
    have hsa : |s - z.1| < z.1 - a :=
      hsInner.trans_le (min_le_left _ _)
    have hsb : |s - z.1| < b - z.1 :=
      hsInner.trans_le (min_le_right _ _)
    constructor
    · have := neg_abs_le (s - z.1)
      linarith
    · have := le_abs_self (s - z.1)
      linarith
  have hspos : 0 < s := ha.trans_le hsWindow.1
  have hsT : s ≤ T := hsWindow.2.trans hbT
  let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT⟩
  have hexts : E s = U zs := by
    exact wholeLineBUCTrajectoryExtend_eq hT U zs.2
  have hextz : E z.1 = U z := by
    exact wholeLineBUCTrajectoryExtend_eq hT U z.2
  have hEs : ∀ y, HasDerivAt (E s).1 (deriv (E s).1 y) y := by
    intro y
    have h := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall zs hspos y
    rw [hexts]
    exact h.differentiableAt.hasDerivAt
  have hEz : ∀ y, HasDerivAt (E z.1).1 (deriv (E z.1).1 y) y := by
    intro y
    have h := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz y
    rw [hextz]
    exact h.differentiableAt.hasDerivAt
  have hdist : dist (E s) (E z.1) < d := hclose hsE
  have hval : ∀ y, |(E s).1 y - (E z.1).1 y| ≤ dist (E s) (E z.1) := by
    intro y
    calc
      |(E s).1 y - (E z.1).1 y| = |(E s - E z.1).1 y| := rfl
      _ ≤ ‖E s - E z.1‖ := WholeLineBUC.abs_apply_le_norm (E s - E z.1) y
      _ = dist (E s) (E z.1) :=
        (WholeLineBUC.dist_eq_norm_sub (E s) (E z.1)).symm
  have hinterp := deriv_sub_abs_le_of_common_holder
    hH heta0 hr hEs hEz (hholder s hsWindow) (hholder z.1 hztWindow)
      hval x
  have hfirst : 2 * H * r ^ eta < eps / 2 := by
    rw [hrpow]
    have hfrac : H / (H + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    calc
      2 * H * (eps / (8 * (H + 1))) =
          eps / 4 * (H / (H + 1)) := by field_simp; ring
      _ < eps / 4 * 1 :=
        mul_lt_mul_of_pos_left hfrac (by positivity)
      _ < eps / 2 := by linarith
  have hsecond : 2 * dist (E s) (E z.1) / r < eps / 2 := by
    have hnum : 2 * dist (E s) (E z.1) < eps * r / 4 := by
      dsimp [d] at hdist
      linarith
    rw [div_lt_iff₀ hr]
    nlinarith
  simpa [E, U] using hinterp.trans_lt (by linarith)

#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_deriv_uniformContinuousAt_positive

/-- The spatial derivative of the canonical population is jointly continuous
at every positive interior space-time point. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_deriv_jointContinuousAt_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1) (hzT : z.1 < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta) (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    ContinuousAt
      (fun q : ℝ × ℝ => deriv
        (fun y : ℝ => (wholeLineBUCTrajectoryExtend hT U q.1).1 y) q.2)
      (z.1, x) := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let a : ℝ := z.1 / 2
  let b : ℝ := (z.1 + T) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith [z.2.2]
  have hbT : b ≤ T := by dsimp [b]; linarith
  have hzWindow : z.1 ∈ Set.Icc a b := by
    dsimp [a, b]
    constructor <;> linarith
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel with
    ⟨H, hH, hholder⟩
  rw [Metric.continuousAt_iff]
  intro eps heps
  obtain ⟨deltaT, hdeltaT, htime⟩ :=
    wholeLineCauchyBUCMildFixedPoint_spatial_deriv_uniformContinuousAt_positive
      p hM hT u₀ hsmall z hz hzT htheta0 htheta1
        heta0 heta1 hrel (eps / 2) (half_pos heps)
  let deltaX : ℝ := (eps / (2 * (H + 1))) ^ (1 / eta)
  have hden : 0 < 2 * (H + 1) := by positivity
  have hdeltaX : 0 < deltaX := by
    dsimp [deltaX]
    exact Real.rpow_pos_of_pos (div_pos heps hden) _
  have hdeltaXpow : deltaX ^ eta = eps / (2 * (H + 1)) := by
    dsimp [deltaX]
    rw [← Real.rpow_mul (div_pos heps hden).le, one_div,
      inv_mul_cancel₀ (ne_of_gt heta0), Real.rpow_one]
  let delta : ℝ := min deltaT
    (min deltaX (min (z.1 - a) (b - z.1)))
  have hza : 0 < z.1 - a := by dsimp [a]; linarith
  have hbz : 0 < b - z.1 := by dsimp [b]; linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdeltaT
      (lt_min hdeltaX (lt_min hza hbz))
  refine ⟨delta, hdelta, ?_⟩
  intro q hq
  have hqmax : max (dist q.1 z.1) (dist q.2 x) < delta := by
    simpa [Prod.dist_eq] using hq
  have hqtDelta : dist q.1 z.1 < delta :=
    (le_max_left _ _).trans_lt hqmax
  have hqxDelta : dist q.2 x < delta :=
    (le_max_right _ _).trans_lt hqmax
  have hqt : |q.1 - z.1| < deltaT := by
    rw [← Real.dist_eq]
    exact hqtDelta.trans_le (min_le_left _ _)
  have hqx : |q.2 - x| < deltaX := by
    rw [← Real.dist_eq]
    exact hqxDelta.trans_le
      ((min_le_right deltaT _).trans (min_le_left _ _))
  have hqWindow : q.1 ∈ Set.Icc a b := by
    have hinner : dist q.1 z.1 < min (z.1 - a) (b - z.1) :=
      hqtDelta.trans_le
        ((min_le_right deltaT _).trans (min_le_right deltaX _))
    rw [Real.dist_eq] at hinner
    have hleft : |q.1 - z.1| < z.1 - a :=
      hinner.trans_le (min_le_left _ _)
    have hright : |q.1 - z.1| < b - z.1 :=
      hinner.trans_le (min_le_right _ _)
    constructor
    · have := neg_abs_le (q.1 - z.1)
      linarith
    · have := le_abs_self (q.1 - z.1)
      linarith
  have htimeAt := htime q.1 hqt x
  have hspace :
      |deriv
          (fun y : ℝ =>
            (wholeLineBUCTrajectoryExtend hT U q.1).1 y) q.2 -
        deriv
          (fun y : ℝ =>
            (wholeLineBUCTrajectoryExtend hT U q.1).1 y) x| ≤ eps / 2 := by
    have hpow : |q.2 - x| ^ eta < deltaX ^ eta :=
      Real.rpow_lt_rpow (abs_nonneg _) hqx heta0
    have hraw := hholder q.1 hqWindow q.2 x
    calc
      _ ≤ H * |q.2 - x| ^ eta := hraw
      _ ≤ H * deltaX ^ eta :=
        mul_le_mul_of_nonneg_left hpow.le hH
      _ = eps / 2 * (H / (H + 1)) := by
        rw [hdeltaXpow]
        field_simp
      _ ≤ eps / 2 := by
        have hfrac : H / (H + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        simpa using mul_le_mul_of_nonneg_left hfrac (half_pos heps).le
  rw [Real.dist_eq]
  exact (abs_sub_le _ _ _).trans_lt (by
    simpa [U] using add_lt_add_of_le_of_lt hspace htimeAt)

#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_deriv_jointContinuousAt_positive

/-- Full space-time derivative of the canonical population at a positive
interior point.  The time component is the already proved physical PDE
derivative; the product differentiability is supplied by joint continuity of
the spatial derivative, not by differentiating the nonlinear flux. -/
theorem wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1) (hzT : z.1 < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ w : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall w).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    HasFDerivAt
      (fun q : ℝ × ℝ =>
        (wholeLineBUCTrajectoryExtend hT U q.1).1 q.2)
      (deriv (fun r : ℝ =>
          (wholeLineBUCTrajectoryExtend hT U r).1 x) z.1 •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (fun y : ℝ =>
          (wholeLineBUCTrajectoryExtend hT U z.1).1 y) x •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      (z.1, x) := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let f : ℝ → ℝ → ℝ := fun r y =>
    (wholeLineBUCTrajectoryExtend hT U r).1 y
  let ft : ℝ → ℝ → ℝ := fun r y => deriv (fun q => f q y) r
  let fx : ℝ → ℝ → ℝ := fun r y => deriv (f r) y
  have htimeRaw :=
    wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
      p hM hT u₀ hsmall hz hzT htheta0 htheta1
        heta0 heta1 hrel hstrip x
  have htime : HasDerivAt (fun r => f r x) (ft z.1 x) z.1 := by
    simpa [f, ft, U] using htimeRaw.differentiableAt.hasDerivAt
  have hspace : ∀ᶠ r in 𝓝 z.1, ∀ y,
      HasDerivAt (f r) (fx r y) y := by
    filter_upwards [Ioo_mem_nhds hz hzT] with r hr
    intro y
    let zr : Set.Icc (0 : ℝ) T := ⟨r, hr.1.le, hr.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT U r = U zr :=
      wholeLineBUCTrajectoryExtend_eq hT U zr.2
    have hs := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall zr hr.1 y
    simpa [f, fx, hext] using hs.differentiableAt.hasDerivAt
  have hfx : ContinuousAt (fun q : ℝ × ℝ => fx q.1 q.2) (z.1, x) := by
    simpa [fx, f, U] using
      wholeLineCauchyBUCMildFixedPoint_spatial_deriv_jointContinuousAt_positive
        p hM hT u₀ hsmall z hz hzT htheta0 htheta1
          heta0 heta1 hrel x
  simpa [f, ft, fx, U] using
    hasFDerivAt_prod_of_time_slice_of_spatial_continuousAt
      htime hspace hfx

#print axioms wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive

/-- The undamped drift heat operator preserves a pointwise uniform bound.
The zero-lag value of the integral realization is zero; at positive lag this
is the ordinary heat-semigroup contraction applied to a translated input. -/
theorem wholeLineDriftHeatOp_abs_le_of_bounded
    {d t M : ℝ} {f : ℝ → ℝ}
    (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hf : ∀ y, |f y| ≤ M) (hf_cont : Continuous f) (x : ℝ) :
    |wholeLineDriftHeatOp d t f x| ≤ M := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa [wholeLineDriftHeatOp, wholeLineCauchyMovingHeatOp,
      wholeLineCauchyHeatOp, modifiedSemigroup, heatSemigroup, heatKernel]
      using hM
  · rw [wholeLineDriftHeatOp_eq_translated_integral ht]
    change |heatSemigroup t (fun y : ℝ => f (y + d * t)) x| ≤ M
    exact heatSemigroup_abs_bound
      (fun y => hf (y + d * t)) ht hM
      ((hf_cont.comp (continuous_id.add continuous_const)).aestronglyMeasurable) x

#print axioms wholeLineDriftHeatOp_abs_le_of_bounded

/-- The time integrability premise of the bounded-joint drift restart is
automatic.  On the open window the source path is the derivative of the
backward orbit, hence measurable.  Its uniform bound follows from the heat
contraction; the two endpoints are discarded as a null set. -/
theorem wholeLineDrift_sourcePath_intervalIntegrable_of_bounded_joint
    {a b d x CW CWt CWx CWxx : ℝ}
    {W : ℝ → WholeLineBUC} {Wt Wx Wxx : ℝ → ℝ → ℝ}
    (hab : a < b)
    (hCW : 0 ≤ CW) (hCWt : 0 ≤ CWt) (hCWx : 0 ≤ CWx)
    (hCWxx : 0 ≤ CWxx)
    (hW : ∀ r ∈ Set.Ioo a b, ∀ y, |(W r).1 y| ≤ CW)
    (hWt : ∀ r ∈ Set.Ioo a b, ∀ y, |Wt r y| ≤ CWt)
    (hWx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wx r y| ≤ CWx)
    (hWxx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wxx r y| ≤ CWxx)
    (hWt_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r))
    (hWx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r))
    (hWxx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r))
    (hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (W r).1 (Wx r y) y)
    (hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y)
    (hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => (W q.1).1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y)) :
    IntervalIntegrable
      (fun s => wholeLineDriftHeatOp d (b - s)
        (fun y => Wt s y - Wxx s y - d * Wx s y) x)
      volume a b := by
  let path : ℝ → ℝ := fun r =>
    wholeLineDriftHeatOp d (b - r) (W r).1 x
  let sourcePath : ℝ → ℝ := fun r =>
    wholeLineDriftHeatOp d (b - r)
      (fun y => Wt r y - Wxx r y - d * Wx r y) x
  let g : ℝ → ℝ := Set.Ioo a b |>.indicator (deriv path)
  let C : ℝ := CWt + CWxx + |d| * CWx
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg hCWt hCWxx)
      (mul_nonneg (abs_nonneg d) hCWx)
  have hderiv : ∀ r ∈ Set.Ioo a b,
      HasDerivAt path (sourcePath r) r := by
    intro r hr
    exact wholeLineDriftBackwardOrbit_hasDerivAt_of_bounded_joint
      hr.1 hr.2 hCW hCWt hCWx hW hWt hWx hWxx
      (fun q _ => (W q).1.continuous) hWt_cont hWx_cont hWxx_cont
      hspace1 hspace2 hjoint
  have hg_meas : AEStronglyMeasurable g volume := by
    exact (measurable_deriv path).aestronglyMeasurable.indicator measurableSet_Ioo
  have hg_bound : ∀ r ∈ Set.Icc a b, ‖g r‖ ≤ C := by
    intro r hr
    by_cases hri : r ∈ Set.Ioo a b
    · have hgr : g r = deriv path r := by simp [g, hri]
      rw [hgr]
      rw [(hderiv r hri).deriv]
      rw [Real.norm_eq_abs]
      apply wholeLineDriftHeatOp_abs_le_of_bounded
      · exact sub_nonneg.mpr hri.2.le
      · exact hC
      · intro y
        calc
          |Wt r y - Wxx r y - d * Wx r y| ≤
              |Wt r y - Wxx r y| + |d * Wx r y| := abs_sub _ _
          _ ≤ (|Wt r y| + |Wxx r y|) + |d * Wx r y| :=
            add_le_add (abs_sub _ _) le_rfl
          _ ≤ CWt + CWxx + |d| * CWx := by
            rw [abs_mul]
            exact add_le_add
              (add_le_add (hWt r hri y) (hWxx r hri y))
              (mul_le_mul_of_nonneg_left (hWx r hri y) (abs_nonneg d))
          _ = C := rfl
      · exact ((hWt_cont r hri).sub (hWxx_cont r hri)).sub
          (continuous_const.mul (hWx_cont r hri))
    · simp [g, hri, hC]
  have hg_int : IntervalIntegrable g volume a b :=
    intervalIntegrable_of_aestronglyMeasurable_of_norm_le
      hab.le hg_meas hg_bound
  have hsource_g : sourcePath =ᵐ[volume.restrict (Set.uIoc a b)] g := by
    rw [Set.uIoc_of_le hab.le]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards
      [(MeasureTheory.Ioo_ae_eq_Ioc
        (a := a) (b := b) (μ := volume)).symm] with r hr hrIoc
    have hri : r ∈ Set.Ioo a b := hr.mp hrIoc
    have hgr : g r = deriv path r := by simp [g, hri]
    rw [hgr]
    exact (hderiv r hri).deriv.symm
  exact hg_int.congr_ae hsource_g.symm

#print axioms
  wholeLineDrift_sourcePath_intervalIntegrable_of_bounded_joint

/-- Bounded-joint drift restart with no separately carried time-integrability
premise. -/
theorem wholeLineDrift_restart_identity_of_bounded_joint_auto
    {a b d x CW CWt CWx CWxx : ℝ}
    {W : ℝ → WholeLineBUC} {Wt Wx Wxx : ℝ → ℝ → ℝ}
    (hab : a < b)
    (hW_left : Tendsto W (𝓝[>] a) (𝓝 (W a)))
    (hW_right : Tendsto W (𝓝[<] b) (𝓝 (W b)))
    (hCW : 0 ≤ CW) (hCWt : 0 ≤ CWt) (hCWx : 0 ≤ CWx)
    (hCWxx : 0 ≤ CWxx)
    (hW : ∀ r ∈ Set.Ioo a b, ∀ y, |(W r).1 y| ≤ CW)
    (hWt : ∀ r ∈ Set.Ioo a b, ∀ y, |Wt r y| ≤ CWt)
    (hWx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wx r y| ≤ CWx)
    (hWxx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wxx r y| ≤ CWxx)
    (hWt_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r))
    (hWx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r))
    (hWxx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r))
    (hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (W r).1 (Wx r y) y)
    (hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y)
    (hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => (W q.1).1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y)) :
    (W b).1 x = wholeLineDriftHeatOp d (b - a) (W a).1 x +
      ∫ s in a..b, wholeLineDriftHeatOp d (b - s)
        (fun y => Wt s y - Wxx s y - d * Wx s y) x := by
  apply wholeLineDrift_restart_identity_of_bounded_joint
    hab hW_left hW_right hCW hCWt hCWx hW hWt hWx hWxx
      hWt_cont hWx_cont hWxx_cont hspace1 hspace2 hjoint
  exact wholeLineDrift_sourcePath_intervalIntegrable_of_bounded_joint
    hab hCW hCWt hCWx hCWxx hW hWt hWx hWxx hWt_cont hWx_cont hWxx_cont
      hspace1 hspace2 hjoint

#print axioms wholeLineDrift_restart_identity_of_bounded_joint_auto

/-- Canonical positive-window restart for the full pointwise generator in an
arbitrary drift frame.  Every boundedness, continuity, differentiability and
time-integrability premise is supplied by the canonical fixed-point
regularity.  In particular, no derivative of the nonlinear flux is assumed
as input. -/
theorem wholeLineCauchyBUCMildFixedPoint_drift_restart_identity_positive_window
    (p : CMParams) {M T a b theta eta d : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let E := wholeLineBUCTrajectoryExtend hT U
    (E b).1 x = wholeLineDriftHeatOp d (b - a) (E a).1 x +
      ∫ s in a..b, wholeLineDriftHeatOp d (b - s)
        (fun y =>
          deriv (fun r : ℝ => (E r).1 y) s -
            deriv (fun q : ℝ => deriv (fun w : ℝ => (E s).1 w) q) y -
            d * deriv (fun w : ℝ => (E s).1 w) y) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let E : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT U
  let Wt : ℝ → ℝ → ℝ := fun r y => deriv (fun q : ℝ => (E q).1 y) r
  let Wx : ℝ → ℝ → ℝ := fun r y => deriv (fun q : ℝ => (E r).1 q) y
  let Wxx : ℝ → ℝ → ℝ := fun r y =>
    deriv (fun q : ℝ => deriv (fun w : ℝ => (E r).1 w) q) y
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  have hstripHalf : ∀ s ∈ Set.Icc (a / 2) b, ∀ y,
      (E s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hs0 : 0 ≤ s := (half_pos ha).le.trans hs.1
    have hsT : s ≤ T := hs.2.trans hbT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
    rw [show E s = U zs by
      exact wholeLineBUCTrajectoryExtend_eq hT U zs.2]
    exact hstrip zs y
  have hstripWindow : ∀ s ∈ Set.Icc a b, ∀ y,
      (E s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    exact hstripHalf s
      ⟨(div_le_self ha.le (by norm_num)).trans hs.1, hs.2⟩ y
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
      p hM hT ha hab.le hbT.le u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel (by simpa [E, U] using hstripWindow) with
    ⟨Bx, hBx, hxBound⟩
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive_window
      p hM hT ha hab.le hbT.le u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel (by simpa [E, U] using hstripHalf) with
    ⟨Bxx, hBxx, hxxBound⟩
  rcases wholeLineCauchyBUCMildFixedPoint_time_deriv_bounded_positive_window
      p hM hT ha hab.le hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstrip with
    ⟨Bt, hBt, htBound⟩
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT ha hab.le hbT.le u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel (by simpa [E, U] using hstripWindow) with
    ⟨rho, HF, hrho, _hrho1, hHF, hfluxHolder⟩
  have hEcont : Continuous E := by
    simpa [E] using wholeLineBUCTrajectoryExtend_continuous hT U
  have hE_left : Tendsto E (𝓝[>] a) (𝓝 (E a)) :=
    hEcont.continuousAt.mono_left nhdsWithin_le_nhds
  have hE_right : Tendsto E (𝓝[<] b) (𝓝 (E b)) :=
    hEcont.continuousAt.mono_left nhdsWithin_le_nhds
  have hvalue : ∀ r ∈ Set.Ioo a b, ∀ y, |(E r).1 y| ≤ M := by
    intro r hr y
    have hmem := hstripWindow r ⟨hr.1.le, hr.2.le⟩ y
    rw [abs_of_nonneg hmem.1]
    exact hmem.2
  have htbound : ∀ r ∈ Set.Ioo a b, ∀ y, |Wt r y| ≤ Bt := by
    intro r hr y
    simpa [Wt, E, U] using htBound r ⟨hr.1.le, hr.2.le⟩ y
  have hxbound : ∀ r ∈ Set.Ioo a b, ∀ y, |Wx r y| ≤ Bx := by
    intro r hr y
    simpa [Wx, E, U] using hxBound r ⟨hr.1.le, hr.2.le⟩ y
  have hxxbound : ∀ r ∈ Set.Ioo a b, ∀ y, |Wxx r y| ≤ Bxx := by
    intro r hr y
    simpa [Wxx, E, U] using hxxBound r ⟨hr.1.le, hr.2.le⟩ y
  have hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (E r).1 (Wx r y) y := by
    intro r hr y
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hext : E r = U zr := wholeLineBUCTrajectoryExtend_eq hT U zr.2
    have hs := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) y
    have hdiff : DifferentiableAt ℝ (E r).1 y := by
      simpa [hext] using hs.differentiableAt
    simpa [Wx] using hdiff.hasDerivAt
  have hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y := by
    intro r hr y
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hext : E r = U zr := wholeLineBUCTrajectoryExtend_eq hT U zr.2
    have hstripR : ∀ s ∈ Set.Icc (r / 2) r, ∀ q,
        (E s).1 q ∈ Set.Icc (0 : ℝ) M := by
      intro s hs q
      have hs0 : 0 ≤ s := (half_pos (ha.trans hr.1)).le.trans hs.1
      have hsT : s ≤ T := hs.2.trans (hr.2.trans hbT).le
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      rw [show E s = U zs by
        exact wholeLineBUCTrajectoryExtend_eq hT U zs.2]
      exact hstrip zs q
    have hs := wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) htheta0 htheta1
        heta0 heta1 hrel (by simpa [E, U] using hstripR) y
    have hraw := hs.differentiableAt.hasDerivAt
    simpa [Wx, Wxx, E, hext] using hraw
  have hxcont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r) := by
    intro r hr
    rw [continuous_iff_continuousAt]
    intro y
    exact (hspace2 r hr y).continuousAt
  have hxxcont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r) := by
    intro r hr
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hext : E r = U zr := wholeLineBUCTrajectoryExtend_eq hT U zr.2
    have hstripR : ∀ s ∈ Set.Icc (r / 2) r, ∀ q,
        (E s).1 q ∈ Set.Icc (0 : ℝ) M := by
      intro s hs q
      have hs0 : 0 ≤ s := (half_pos (ha.trans hr.1)).le.trans hs.1
      have hsT : s ≤ T := hs.2.trans (hr.2.trans hbT).le
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      rw [show E s = U zs by
        exact wholeLineBUCTrajectoryExtend_eq hT U zs.2]
      exact hstrip zs q
    have hc := wholeLineCauchyBUCMildFixedPoint_spatial_second_continuous_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) htheta0 htheta1
        heta0 heta1 hrel (by simpa [E, U] using hstripR)
    simpa [Wxx, E, hext] using hc
  have htcont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r) := by
    intro r hr
    have hfluxCont : Continuous (fun y => deriv (F r).1 y) :=
      wholeLineContinuous_of_holder hrho hHF
        (fun y q => hfluxHolder r ⟨hr.1.le, hr.2.le⟩ y q)
    have hformula : Wt r = fun y =>
        Wxx r y - (E r).1 y + (-p.χ) * deriv (F r).1 y + (R r).1 y := by
      funext y
      have ht0 : 0 < r := ha.trans hr.1
      have htT : r < T := hr.2.trans hbT
      have htderiv := wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
        p hM hT u₀ hsmall ht0 htT htheta0 htheta1
          heta0 heta1 hrel hstrip y
      simpa [Wt, Wxx, E, U, F, R] using htderiv.deriv
    rw [hformula]
    exact ((hxxcont r hr).sub (E r).1.continuous).add
      (continuous_const.mul hfluxCont) |>.add (R r).1.continuous
  have hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => (E q.1).1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y) := by
    intro r hr y
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hj := wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) (hr.2.trans hbT)
        htheta0 htheta1 heta0 heta1 hrel hstrip y
    simpa [Wt, Wx, E, U] using hj
  simpa [Wt, Wx, Wxx, E] using
    (wholeLineDrift_restart_identity_of_bounded_joint_auto
      (a := a) (b := b) (d := d) (x := x)
      (W := E) (Wt := Wt) (Wx := Wx) (Wxx := Wxx)
      hab hE_left hE_right hM hBt hBx hBxx hvalue htbound hxbound hxxbound
        htcont hxcont hxxcont hspace1 hspace2 hjoint)

#print axioms
  wholeLineCauchyBUCMildFixedPoint_drift_restart_identity_positive_window

/-- PDE form of the canonical drift restart.  The second spatial derivative
cancels against the diffusion term in `u_t`; the remaining source is the
physical reaction/chemotaxis generator together with the chosen drift. -/
theorem wholeLineCauchyBUCMildFixedPoint_drift_pde_restart_identity_positive_window
    (p : CMParams) {M T a b theta eta d : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let E := wholeLineBUCTrajectoryExtend hT U
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    (E b).1 x = wholeLineDriftHeatOp d (b - a) (E a).1 x +
      ∫ s in a..b, wholeLineDriftHeatOp d (b - s)
        (fun y =>
          -(E s).1 y + (-p.χ) * deriv (F s).1 y + (R s).1 y -
            d * deriv (fun w : ℝ => (E s).1 w) y) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let E : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT U
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  calc
    (E b).1 x = wholeLineDriftHeatOp d (b - a) (E a).1 x +
        ∫ s in a..b, wholeLineDriftHeatOp d (b - s)
          (fun y =>
            deriv (fun r : ℝ => (E r).1 y) s -
              deriv (fun q : ℝ => deriv (fun w : ℝ => (E s).1 w) q) y -
              d * deriv (fun w : ℝ => (E s).1 w) y) x := by
      simpa [E, U] using
        wholeLineCauchyBUCMildFixedPoint_drift_restart_identity_positive_window
          p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
            heta0 heta1 hrel hstrip x
    _ = wholeLineDriftHeatOp d (b - a) (E a).1 x +
        ∫ s in a..b, wholeLineDriftHeatOp d (b - s)
          (fun y =>
            -(E s).1 y + (-p.χ) * deriv (F s).1 y + (R s).1 y -
              d * deriv (fun w : ℝ => (E s).1 w) y) x := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hab.le] at hs
      apply congrArg (fun f : ℝ → ℝ => wholeLineDriftHeatOp d (b - s) f x)
      funext y
      have hs0 : 0 < s := ha.trans_le hs.1
      have hsT : s < T := hs.2.trans_lt hbT
      have htderiv := wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
        p hM hT u₀ hsmall hs0 hsT htheta0 htheta1
          heta0 heta1 hrel hstrip y
      have heq := htderiv.deriv
      change
        deriv (fun r : ℝ => (E r).1 y) s -
            deriv (fun q : ℝ => deriv (fun w : ℝ => (E s).1 w) q) y -
            d * deriv (fun w : ℝ => (E s).1 w) y =
          -(E s).1 y + (-p.χ) * deriv (F s).1 y + (R s).1 y -
            d * deriv (fun w : ℝ => (E s).1 w) y
      have heq' :
          deriv (fun r : ℝ => (E r).1 y) s =
            deriv (fun q : ℝ => deriv (fun w : ℝ => (E s).1 w) q) y -
              (E s).1 y + (-p.χ) * deriv (F s).1 y + (R s).1 y := by
        simpa [E, U, F, R] using heq
      rw [heq']
      ring

#print axioms
  wholeLineCauchyBUCMildFixedPoint_drift_pde_restart_identity_positive_window

end ShenWork.Paper1
