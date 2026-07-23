import ShenWork.Paper1.WholeLineChiPosSharpEntropyDissipation
import ShenWork.Paper1.WholeLineResolverSharpGradient

/-!
# Weighted sharp entropy dissipation on a bounded interval

This file localizes the sharp periodic entropy calculation with a strictly
positive, slowly varying weight.  All weight and resolver boundary fluxes are
kept explicitly.
-/

open MeasureTheory intervalIntegral Set Real
open scoped Topology Interval

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

/-- One smooth positive time slice with a strictly positive localization
weight on a bounded interval. -/
structure ChiOneWeightedEntropySlice
    (a b c chi ell : ℝ) (w w' : ℝ → ℝ)
    (u ux uxx r rx rxx ut : ℝ → ℝ) : Prop where
  hab : a ≤ b
  hell : 0 < ell
  u_pos : ∀ x, 0 < u x
  w_pos : ∀ x, 0 < w x
  w_deriv : ∀ x, HasDerivAt w (w' x) x
  w'_cont : Continuous w'
  w_slow : ∀ x, |w' x| ≤ (1 / ell) * w x
  u_deriv : ∀ x, HasDerivAt u (ux x) x
  ux_deriv : ∀ x, HasDerivAt ux (uxx x) x
  r_deriv : ∀ x, HasDerivAt r (rx x) x
  rx_deriv : ∀ x, HasDerivAt rx (rxx x) x
  uxx_continuous : Continuous uxx
  rxx_continuous : Continuous rxx
  ut_continuous : Continuous ut
  population_pde : ∀ x,
    ut x = uxx x + c * ux x -
      chi * (ux x * rx x + u x * rxx x) + u x * (1 - u x)
  resolver_pde : ∀ x, -rxx x + r x = u x - 1

namespace ChiOneWeightedEntropySlice

variable {a b c chi ell : ℝ} {w w' : ℝ → ℝ}
    {u ux uxx r rx rxx ut : ℝ → ℝ}
    (d : ChiOneWeightedEntropySlice a b c chi ell w w'
      u ux uxx r rx rxx ut)

include d

theorem w_continuous : Continuous w := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.w_deriv x).continuousAt

theorem u_continuous : Continuous u := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.u_deriv x).continuousAt

theorem ux_continuous : Continuous ux := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.ux_deriv x).continuousAt

theorem r_continuous : Continuous r := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.r_deriv x).continuousAt

theorem rx_continuous : Continuous rx := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.rx_deriv x).continuousAt

/-! ## Stage 1: weighted sharp resolver estimate -/

/-- Weighted real-space resolver estimate.  The sharp source coefficient is
`1 / 4`; the slowly varying weight and both endpoint fluxes remain explicit. -/
theorem weighted_resolver_le :
    (∫ x in a..b, w x * (rx x) ^ 2) ≤
      (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
        (1 / (2 * ell)) *
          ((∫ x in a..b, w x * (r x) ^ 2) +
            ∫ x in a..b, w x * (rx x) ^ 2) +
        |w b * r b * rx b - w a * r a * rx a| := by
  have hwr_deriv : ∀ x,
      HasDerivAt (fun y ↦ w y * r y)
        (w' x * r x + w x * rx x) x := by
    intro x
    exact (d.w_deriv x).mul (d.r_deriv x)
  have hwr_deriv_cont : Continuous
      (fun x ↦ w' x * r x + w x * rx x) :=
    (d.w'_cont.mul d.r_continuous).add
      (d.w_continuous.mul d.rx_continuous)
  have hI_cont : Continuous (fun x ↦ w x * (rx x) ^ 2) :=
    d.w_continuous.mul (d.rx_continuous.pow 2)
  have hV_cont : Continuous (fun x ↦ w x * (r x) ^ 2) :=
    d.w_continuous.mul (d.r_continuous.pow 2)
  have hVtwo_cont : Continuous (fun x ↦ w x * (rxx x) ^ 2) :=
    d.w_continuous.mul (d.rxx_continuous.pow 2)
  have hK_cont : Continuous (fun x ↦ w x * r x * rxx x) :=
    (d.w_continuous.mul d.r_continuous).mul d.rxx_continuous
  have hJ_cont : Continuous (fun x ↦ w' x * r x * rx x) :=
    (d.w'_cont.mul d.r_continuous).mul d.rx_continuous
  have hG_cont : Continuous (fun x ↦ w x * (u x - 1) ^ 2) :=
    d.w_continuous.mul ((d.u_continuous.sub continuous_const).pow 2)
  have hibp :
      (∫ x in a..b, w x * r x * rxx x) =
        w b * r b * rx b - w a * r a * rx a -
          ∫ x in a..b, (w' x * r x + w x * rx x) * rx x := by
    simpa only [Pi.zero_apply] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := a) (b := b) (u := fun x ↦ w x * r x) (v := rx)
        (u' := fun x ↦ w' x * r x + w x * rx x) (v' := rxx)
        (fun x _ ↦ hwr_deriv x)
        (fun x _ ↦ d.rx_deriv x)
        (hwr_deriv_cont.intervalIntegrable a b)
        (d.rxx_continuous.intervalIntegrable a b))
  have hibp_split :
      (∫ x in a..b, w x * r x * rxx x) =
        w b * r b * rx b - w a * r a * rx a -
          (∫ x in a..b, w' x * r x * rx x) -
          ∫ x in a..b, w x * (rx x) ^ 2 := by
    rw [hibp]
    rw [show (fun x ↦ (w' x * r x + w x * rx x) * rx x) =
        (fun x ↦ w' x * r x * rx x + w x * (rx x) ^ 2) by
      funext x
      ring]
    rw [intervalIntegral.integral_add
      (hJ_cont.intervalIntegrable a b) (hI_cont.intervalIntegrable a b)]
    ring
  have hyoung :
      -2 * (∫ x in a..b, w x * r x * rxx x) ≤
        (∫ x in a..b, w x * (r x) ^ 2) +
          ∫ x in a..b, w x * (rxx x) ^ 2 := by
    calc
      -2 * (∫ x in a..b, w x * r x * rxx x) =
          ∫ x in a..b, -2 * (w x * r x * rxx x) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in a..b,
          w x * (r x) ^ 2 + w x * (rxx x) ^ 2 := by
        apply intervalIntegral.integral_mono_on d.hab
          (hK_cont.const_mul (-2) |>.intervalIntegrable a b)
          ((hV_cont.add hVtwo_cont).intervalIntegrable a b)
        intro x _
        change -2 * (w x * r x * rxx x) ≤
          w x * (r x) ^ 2 + w x * (rxx x) ^ 2
        nlinarith [mul_nonneg (d.w_pos x).le
          (sq_nonneg (r x + rxx x))]
      _ = (∫ x in a..b, w x * (r x) ^ 2) +
          ∫ x in a..b, w x * (rxx x) ^ 2 := by
        rw [intervalIntegral.integral_add
          (hV_cont.intervalIntegrable a b)
          (hVtwo_cont.intervalIntegrable a b)]
  have hdecomp :
      (∫ x in a..b, w x * (u x - 1) ^ 2) =
        (∫ x in a..b, w x * (r x) ^ 2) -
          2 * (∫ x in a..b, w x * r x * rxx x) +
          ∫ x in a..b, w x * (rxx x) ^ 2 := by
    calc
      (∫ x in a..b, w x * (u x - 1) ^ 2) =
          ∫ x in a..b, w x * (-rxx x + r x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _
        change w x * (u x - 1) ^ 2 = w x * (-rxx x + r x) ^ 2
        rw [← d.resolver_pde x]
      _ = ∫ x in a..b,
          w x * (r x) ^ 2 - 2 * (w x * r x * rxx x) +
            w x * (rxx x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = (∫ x in a..b, w x * (r x) ^ 2) -
          2 * (∫ x in a..b, w x * r x * rxx x) +
          ∫ x in a..b, w x * (rxx x) ^ 2 := by
        rw [intervalIntegral.integral_add
          ((hV_cont.sub (hK_cont.const_mul 2)).intervalIntegrable a b)
          (hVtwo_cont.intervalIntegrable a b)]
        rw [intervalIntegral.integral_sub
          (hV_cont.intervalIntegrable a b)
          (hK_cont.const_mul 2 |>.intervalIntegrable a b)]
        rw [intervalIntegral.integral_const_mul]
  have hraw :
      (∫ x in a..b, w x * (rx x) ^ 2) ≤
        (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
          (w b * r b * rx b - w a * r a * rx a) -
          ∫ x in a..b, w' x * r x * rx x := by
    have hfour :
        4 * (∫ x in a..b, w x * (rx x) ^ 2) ≤
          (∫ x in a..b, w x * (u x - 1) ^ 2) +
            4 * (w b * r b * rx b - w a * r a * rx a) -
            4 * (∫ x in a..b, w' x * r x * rx x) := by
      nlinarith [hyoung, hdecomp, hibp_split]
    norm_num at hfour ⊢
    linarith [hfour]
  have hpoint : ∀ x,
      |w' x * r x * rx x| ≤
        (1 / (2 * ell)) *
          (w x * (r x) ^ 2 + w x * (rx x) ^ 2) := by
    intro x
    have hproduct :
        |r x * rx x| ≤ ((r x) ^ 2 + (rx x) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|r x| - |rx x|),
        sq_abs (r x), sq_abs (rx x)]
    calc
      |w' x * r x * rx x| = |w' x| * |r x * rx x| := by
        simp only [abs_mul, mul_assoc]
      _ ≤ ((1 / ell) * w x) * |r x * rx x| :=
        mul_le_mul_of_nonneg_right (d.w_slow x) (abs_nonneg _)
      _ ≤ ((1 / ell) * w x) *
          (((r x) ^ 2 + (rx x) ^ 2) / 2) := by
        exact mul_le_mul_of_nonneg_left hproduct
          (mul_nonneg (div_nonneg zero_le_one d.hell.le) (d.w_pos x).le)
      _ = (1 / (2 * ell)) *
          (w x * (r x) ^ 2 + w x * (rx x) ^ 2) := by ring
  have hJ_abs :
      |∫ x in a..b, w' x * r x * rx x| ≤
        (1 / (2 * ell)) *
          ((∫ x in a..b, w x * (r x) ^ 2) +
            ∫ x in a..b, w x * (rx x) ^ 2) := by
    calc
      |∫ x in a..b, w' x * r x * rx x| ≤
          ∫ x in a..b, |w' x * r x * rx x| :=
        intervalIntegral.abs_integral_le_integral_abs d.hab
      _ ≤ ∫ x in a..b, (1 / (2 * ell)) *
          (w x * (r x) ^ 2 + w x * (rx x) ^ 2) := by
        apply intervalIntegral.integral_mono_on d.hab
          (hJ_cont.abs.intervalIntegrable a b)
          (((hV_cont.add hI_cont).const_mul
            (1 / (2 * ell))).intervalIntegrable a b)
        intro x _
        exact hpoint x
      _ = (1 / (2 * ell)) *
          ((∫ x in a..b, w x * (r x) ^ 2) +
            ∫ x in a..b, w x * (rx x) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_add
          (hV_cont.intervalIntegrable a b)
          (hI_cont.intervalIntegrable a b)]
  calc
    (∫ x in a..b, w x * (rx x) ^ 2) ≤
        (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
          (w b * r b * rx b - w a * r a * rx a) -
          ∫ x in a..b, w' x * r x * rx x := hraw
    _ ≤ (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
        |w b * r b * rx b - w a * r a * rx a| +
        |∫ x in a..b, w' x * r x * rx x| := by
      have hboundary :=
        le_abs_self (w b * r b * rx b - w a * r a * rx a)
      have hcross :=
        neg_le_abs (∫ x in a..b, w' x * r x * rx x)
      calc
        (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
              (w b * r b * rx b - w a * r a * rx a) -
              ∫ x in a..b, w' x * r x * rx x ≤
            (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
              |w b * r b * rx b - w a * r a * rx a| -
              ∫ x in a..b, w' x * r x * rx x := by
          exact sub_le_sub_right
            (add_le_add_right hboundary _) _
        _ ≤ (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
            |w b * r b * rx b - w a * r a * rx a| +
            |∫ x in a..b, w' x * r x * rx x| := by
          simpa only [sub_eq_add_neg] using
            add_le_add_right hcross
              ((1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
                |w b * r b * rx b - w a * r a * rx a|)
    _ ≤ (1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
        (1 / (2 * ell)) *
          ((∫ x in a..b, w x * (r x) ^ 2) +
            ∫ x in a..b, w x * (rx x) ^ 2) +
        |w b * r b * rx b - w a * r a * rx a| := by
      have hadd := add_le_add_right hJ_abs
        ((1 / 4 : ℝ) * (∫ x in a..b, w x * (u x - 1) ^ 2) +
          |w b * r b * rx b - w a * r a * rx a|)
      simpa only [add_assoc, add_left_comm, add_comm] using hadd

/-! ## Stage 2: weighted entropy production identity -/

theorem multiplier_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y ↦ chiOneEntropyMultiplier (u y))
      (ux x / (u x) ^ 2) x :=
  chiOneEntropyMultiplier_comp_hasDerivAt
    (d.u_deriv x) (d.u_pos x).ne'

theorem entropy_comp_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y ↦ chiOneRelativeEntropy (u y))
      (chiOneEntropyMultiplier (u x) * ux x) x :=
  (chiOneRelativeEntropy_hasDerivAt (d.u_pos x).ne').comp x
    (d.u_deriv x)

/-- Weighted diffusion integration by parts, including both endpoint values. -/
theorem weighted_diffusion_integral :
    (∫ x in a..b, w x * chiOneEntropyMultiplier (u x) * uxx x) =
      (w b * chiOneEntropyMultiplier (u b) * ux b -
        w a * chiOneEntropyMultiplier (u a) * ux a) -
        (∫ x in a..b,
          w' x * chiOneEntropyMultiplier (u x) * ux x) -
        ∫ x in a..b, w x * (ux x / u x) ^ 2 := by
  have hmult_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hweighted_mult_deriv : ∀ x,
      HasDerivAt (fun y ↦ w y * chiOneEntropyMultiplier (u y))
        (w' x * chiOneEntropyMultiplier (u x) +
          w x * (ux x / (u x) ^ 2)) x := by
    intro x
    exact (d.w_deriv x).mul (d.multiplier_hasDerivAt x)
  have hweighted_mult_deriv_cont : Continuous
      (fun x ↦ w' x * chiOneEntropyMultiplier (u x) +
        w x * (ux x / (u x) ^ 2)) := by
    have hquot_cont : Continuous (fun x ↦ ux x / (u x) ^ 2) := by
      apply Continuous.div d.ux_continuous (d.u_continuous.pow 2)
      exact fun x ↦ pow_ne_zero 2 (d.u_pos x).ne'
    exact (d.w'_cont.mul hmult_cont).add
      (d.w_continuous.mul hquot_cont)
  have hflux_cont : Continuous
      (fun x ↦ w' x * chiOneEntropyMultiplier (u x) * ux x) :=
    (d.w'_cont.mul hmult_cont).mul d.ux_continuous
  have hA_cont : Continuous (fun x ↦ ux x / u x) := by
    apply Continuous.div d.ux_continuous d.u_continuous
    exact fun x ↦ (d.u_pos x).ne'
  have hA_sq_cont : Continuous
      (fun x ↦ w x * (ux x / u x) ^ 2) :=
    d.w_continuous.mul (hA_cont.pow 2)
  have hibp :
      (∫ x in a..b,
          (w x * chiOneEntropyMultiplier (u x)) * uxx x) =
        (w b * chiOneEntropyMultiplier (u b)) * ux b -
          (w a * chiOneEntropyMultiplier (u a)) * ux a -
          ∫ x in a..b,
            (w' x * chiOneEntropyMultiplier (u x) +
              w x * (ux x / (u x) ^ 2)) * ux x := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := b)
      (u := fun x ↦ w x * chiOneEntropyMultiplier (u x))
      (v := ux)
      (u' := fun x ↦ w' x * chiOneEntropyMultiplier (u x) +
        w x * (ux x / (u x) ^ 2))
      (v' := uxx)
      (fun x _ ↦ hweighted_mult_deriv x)
      (fun x _ ↦ d.ux_deriv x)
      (hweighted_mult_deriv_cont.intervalIntegrable a b)
      (d.uxx_continuous.intervalIntegrable a b)
  rw [show (fun x ↦ w x * chiOneEntropyMultiplier (u x) * uxx x) =
      (fun x ↦ (w x * chiOneEntropyMultiplier (u x)) * uxx x) by
    funext x
    ring]
  rw [hibp]
  rw [show (fun x ↦
      (w' x * chiOneEntropyMultiplier (u x) +
        w x * (ux x / (u x) ^ 2)) * ux x) =
      (fun x ↦ w' x * chiOneEntropyMultiplier (u x) * ux x +
        w x * (ux x / u x) ^ 2) by
    funext x
    field_simp [(d.u_pos x).ne']
    ]
  rw [intervalIntegral.integral_add
    (hflux_cont.intervalIntegrable a b)
    (hA_sq_cont.intervalIntegrable a b)]
  ring

/-- Weighted drift is an entropy flux plus the weight-derivative correction. -/
theorem weighted_drift_integral :
    (∫ x in a..b,
        w x * chiOneEntropyMultiplier (u x) * (c * ux x)) =
      c * (w b * chiOneRelativeEntropy (u b) -
        w a * chiOneRelativeEntropy (u a)) -
        c * ∫ x in a..b, w' x * chiOneRelativeEntropy (u x) := by
  have hent_cont : Continuous
      (fun x ↦ chiOneRelativeEntropy (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.entropy_comp_hasDerivAt x).continuousAt
  have hmult_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hentropy_deriv_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x) * ux x) :=
    hmult_cont.mul d.ux_continuous
  have hcore :
      (∫ x in a..b,
          w x * (chiOneEntropyMultiplier (u x) * ux x)) =
        w b * chiOneRelativeEntropy (u b) -
          w a * chiOneRelativeEntropy (u a) -
          ∫ x in a..b, w' x * chiOneRelativeEntropy (u x) := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := b) (u := w)
      (v := fun x ↦ chiOneRelativeEntropy (u x))
      (u' := w')
      (v' := fun x ↦ chiOneEntropyMultiplier (u x) * ux x)
      (fun x _ ↦ d.w_deriv x)
      (fun x _ ↦ d.entropy_comp_hasDerivAt x)
      (d.w'_cont.intervalIntegrable a b)
      (hentropy_deriv_cont.intervalIntegrable a b)
  rw [show (fun x ↦
      w x * chiOneEntropyMultiplier (u x) * (c * ux x)) =
      (fun x ↦ c *
        (w x * (chiOneEntropyMultiplier (u x) * ux x))) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul, hcore]
  ring

/-- Weighted chemotaxis integration by parts.  The endpoint flux and both
weight-gradient corrections are explicit. -/
theorem weighted_chemotaxis_integral :
    (∫ x in a..b, w x * chiOneEntropyMultiplier (u x) *
        (-chi * (ux x * rx x + u x * rxx x))) =
      -chi * (w b * (u b - 1) * rx b -
        w a * (u a - 1) * rx a) +
        chi * (∫ x in a..b, w' x * (u x - 1) * rx x) +
        chi * ∫ x in a..b, w x * (ux x / u x) * rx x := by
  have hmult_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hweighted_mult_deriv : ∀ x,
      HasDerivAt (fun y ↦ w y * chiOneEntropyMultiplier (u y))
        (w' x * chiOneEntropyMultiplier (u x) +
          w x * (ux x / (u x) ^ 2)) x := by
    intro x
    exact (d.w_deriv x).mul (d.multiplier_hasDerivAt x)
  have hweighted_mult_deriv_cont : Continuous
      (fun x ↦ w' x * chiOneEntropyMultiplier (u x) +
        w x * (ux x / (u x) ^ 2)) := by
    have hquot_cont : Continuous (fun x ↦ ux x / (u x) ^ 2) := by
      apply Continuous.div d.ux_continuous (d.u_continuous.pow 2)
      exact fun x ↦ pow_ne_zero 2 (d.u_pos x).ne'
    exact (d.w'_cont.mul hmult_cont).add
      (d.w_continuous.mul hquot_cont)
  have hsignal_flux_deriv : ∀ x,
      HasDerivAt (fun y ↦ u y * rx y)
        (ux x * rx x + u x * rxx x) x := by
    intro x
    exact (d.u_deriv x).mul (d.rx_deriv x)
  have hsignal_flux_deriv_cont : Continuous
      (fun x ↦ ux x * rx x + u x * rxx x) :=
    (d.ux_continuous.mul d.rx_continuous).add
      (d.u_continuous.mul d.rxx_continuous)
  have hweight_flux_cont : Continuous
      (fun x ↦ w' x * (u x - 1) * rx x) :=
    (d.w'_cont.mul (d.u_continuous.sub continuous_const)).mul
      d.rx_continuous
  have hA_cont : Continuous (fun x ↦ ux x / u x) := by
    apply Continuous.div d.ux_continuous d.u_continuous
    exact fun x ↦ (d.u_pos x).ne'
  have hcross_cont : Continuous
      (fun x ↦ w x * (ux x / u x) * rx x) :=
    (d.w_continuous.mul hA_cont).mul d.rx_continuous
  have hibp :
      (∫ x in a..b,
          (w x * chiOneEntropyMultiplier (u x)) *
            (ux x * rx x + u x * rxx x)) =
        (w b * chiOneEntropyMultiplier (u b)) * (u b * rx b) -
          (w a * chiOneEntropyMultiplier (u a)) * (u a * rx a) -
          ∫ x in a..b,
            (w' x * chiOneEntropyMultiplier (u x) +
              w x * (ux x / (u x) ^ 2)) * (u x * rx x) := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := b)
      (u := fun x ↦ w x * chiOneEntropyMultiplier (u x))
      (v := fun x ↦ u x * rx x)
      (u' := fun x ↦ w' x * chiOneEntropyMultiplier (u x) +
        w x * (ux x / (u x) ^ 2))
      (v' := fun x ↦ ux x * rx x + u x * rxx x)
      (fun x _ ↦ hweighted_mult_deriv x)
      (fun x _ ↦ hsignal_flux_deriv x)
      (hweighted_mult_deriv_cont.intervalIntegrable a b)
      (hsignal_flux_deriv_cont.intervalIntegrable a b)
  have hcore :
      (∫ x in a..b, w x * chiOneEntropyMultiplier (u x) *
          (ux x * rx x + u x * rxx x)) =
        (w b * (u b - 1) * rx b - w a * (u a - 1) * rx a) -
          (∫ x in a..b, w' x * (u x - 1) * rx x) -
          ∫ x in a..b, w x * (ux x / u x) * rx x := by
    rw [show (fun x ↦ w x * chiOneEntropyMultiplier (u x) *
        (ux x * rx x + u x * rxx x)) =
        (fun x ↦ (w x * chiOneEntropyMultiplier (u x)) *
          (ux x * rx x + u x * rxx x)) by
      funext x
      ring]
    rw [hibp]
    have hboundary_b :
        (w b * chiOneEntropyMultiplier (u b)) * (u b * rx b) =
          w b * (u b - 1) * rx b := by
      unfold chiOneEntropyMultiplier
      field_simp [(d.u_pos b).ne']
    have hboundary_a :
        (w a * chiOneEntropyMultiplier (u a)) * (u a * rx a) =
          w a * (u a - 1) * rx a := by
      unfold chiOneEntropyMultiplier
      field_simp [(d.u_pos a).ne']
    rw [hboundary_b, hboundary_a]
    rw [show (fun x ↦
        (w' x * chiOneEntropyMultiplier (u x) +
          w x * (ux x / (u x) ^ 2)) * (u x * rx x)) =
        (fun x ↦ w' x * (u x - 1) * rx x +
          w x * (ux x / u x) * rx x) by
      funext x
      unfold chiOneEntropyMultiplier
      field_simp [(d.u_pos x).ne']
      ]
    rw [intervalIntegral.integral_add
      (hweight_flux_cont.intervalIntegrable a b)
      (hcross_cont.intervalIntegrable a b)]
    ring
  rw [show (fun x ↦ w x * chiOneEntropyMultiplier (u x) *
      (-chi * (ux x * rx x + u x * rxx x))) =
      (fun x ↦ -chi *
        (w x * chiOneEntropyMultiplier (u x) *
          (ux x * rx x + u x * rxx x))) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul, hcore]
  ring

/-- The weighted logistic term remains exactly the displacement square. -/
theorem weighted_reaction_integral :
    (∫ x in a..b, w x * chiOneEntropyMultiplier (u x) *
        (u x * (1 - u x))) =
      -∫ x in a..b, w x * (u x - 1) ^ 2 := by
  calc
    (∫ x in a..b, w x * chiOneEntropyMultiplier (u x) *
        (u x * (1 - u x))) =
        ∫ x in a..b, -(w x * (u x - 1) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold chiOneEntropyMultiplier
      field_simp [(d.u_pos x).ne']
      ring
    _ = -∫ x in a..b, w x * (u x - 1) ^ 2 := by
      rw [intervalIntegral.integral_neg]

/-- Exact weighted entropy production identity with all interval fluxes. -/
theorem weighted_entropy_production_identity :
    (∫ x in a..b,
        w x * chiOneEntropyMultiplier (u x) * ut x) =
      (-(∫ x in a..b, w x * (ux x / u x) ^ 2) +
        chi * (∫ x in a..b, w x * (ux x / u x) * rx x) -
        (∫ x in a..b, w x * (u x - 1) ^ 2)) +
      (-(∫ x in a..b,
          w' x * chiOneEntropyMultiplier (u x) * ux x) -
        c * (∫ x in a..b,
          w' x * chiOneRelativeEntropy (u x)) +
        chi * (∫ x in a..b, w' x * (u x - 1) * rx x)) +
      ((w b * chiOneEntropyMultiplier (u b) * ux b -
          w a * chiOneEntropyMultiplier (u a) * ux a) +
        c * (w b * chiOneRelativeEntropy (u b) -
          w a * chiOneRelativeEntropy (u a)) -
        chi * (w b * (u b - 1) * rx b -
          w a * (u a - 1) * rx a)) := by
  let diffusion : ℝ → ℝ := fun x ↦
    w x * chiOneEntropyMultiplier (u x) * uxx x
  let drift : ℝ → ℝ := fun x ↦
    w x * chiOneEntropyMultiplier (u x) * (c * ux x)
  let chemotaxis : ℝ → ℝ := fun x ↦
    w x * chiOneEntropyMultiplier (u x) *
      (-chi * (ux x * rx x + u x * rxx x))
  let reaction : ℝ → ℝ := fun x ↦
    w x * chiOneEntropyMultiplier (u x) * (u x * (1 - u x))
  have hmult_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hweighted_mult_cont : Continuous
      (fun x ↦ w x * chiOneEntropyMultiplier (u x)) :=
    d.w_continuous.mul hmult_cont
  have hdiff_cont : Continuous diffusion :=
    hweighted_mult_cont.mul d.uxx_continuous
  have hdrift_cont : Continuous drift :=
    hweighted_mult_cont.mul (continuous_const.mul d.ux_continuous)
  have hchem_cont : Continuous chemotaxis := by
    exact hweighted_mult_cont.mul <|
      continuous_const.mul <|
        (d.ux_continuous.mul d.rx_continuous).add
          (d.u_continuous.mul d.rxx_continuous)
  have hreact_cont : Continuous reaction :=
    hweighted_mult_cont.mul <|
      d.u_continuous.mul (continuous_const.sub d.u_continuous)
  have hintegrand :
      (fun x ↦ w x * chiOneEntropyMultiplier (u x) * ut x) =
        diffusion + drift + chemotaxis + reaction := by
    funext x
    rw [d.population_pde x]
    dsimp [diffusion, drift, chemotaxis, reaction]
    ring
  rw [hintegrand]
  calc
    intervalIntegral (diffusion + drift + chemotaxis + reaction)
        a b volume =
        intervalIntegral (diffusion + drift + chemotaxis) a b volume +
          intervalIntegral reaction a b volume := by
      simpa only [Pi.add_apply] using intervalIntegral.integral_add
        (((hdiff_cont.add hdrift_cont).add hchem_cont).intervalIntegrable a b)
        (hreact_cont.intervalIntegrable a b)
    _ = (intervalIntegral (diffusion + drift) a b volume +
          intervalIntegral chemotaxis a b volume) +
        intervalIntegral reaction a b volume := by
      rw [show intervalIntegral (diffusion + drift + chemotaxis)
          a b volume =
          intervalIntegral (diffusion + drift) a b volume +
            intervalIntegral chemotaxis a b volume by
        simpa only [Pi.add_apply] using intervalIntegral.integral_add
          ((hdiff_cont.add hdrift_cont).intervalIntegrable a b)
          (hchem_cont.intervalIntegrable a b)]
    _ = ((intervalIntegral diffusion a b volume +
            intervalIntegral drift a b volume) +
          intervalIntegral chemotaxis a b volume) +
        intervalIntegral reaction a b volume := by
      rw [show intervalIntegral (diffusion + drift) a b volume =
          intervalIntegral diffusion a b volume +
            intervalIntegral drift a b volume by
        simpa only [Pi.add_apply] using intervalIntegral.integral_add
          (hdiff_cont.intervalIntegrable a b)
          (hdrift_cont.intervalIntegrable a b)]
    _ = _ := by
      dsimp [diffusion, drift, chemotaxis, reaction]
      rw [d.weighted_diffusion_integral, d.weighted_drift_integral,
        d.weighted_chemotaxis_integral, d.weighted_reaction_integral]
      ring

/-! ## Stage 3: weighted sharp entropy production inequality -/

omit d in
theorem chiOneRelativeEntropy_nonneg {z : ℝ} (hz : 0 < z) :
    0 ≤ chiOneRelativeEntropy z := by
  unfold chiOneRelativeEntropy
  linarith [Real.log_le_sub_one_of_pos hz]

/-- **Weighted sharp entropy production.**  The leading displacement-square
coefficient is exactly `1 - chi ^ 2 / 16`.  Weight errors and both kinds of
endpoint flux are displayed explicitly. -/
theorem weighted_sharp_entropy_production_le (hchi : 0 ≤ chi) :
    (∫ x in a..b,
        w x * chiOneEntropyMultiplier (u x) * ut x) ≤
      -(1 - chi ^ 2 / 16) *
          (∫ x in a..b, w x * (u x - 1) ^ 2) +
        ((|c| + chi + 2) / ell) *
          ((∫ x in a..b, w x * chiOneRelativeEntropy (u x)) +
            (∫ x in a..b,
              w x * ((ux x / u x) ^ 2 + (u x - 1) ^ 2))) +
        (chi ^ 2 / 4 + chi / (2 * ell)) *
          ((1 / (2 * ell)) *
              ((∫ x in a..b, w x * (r x) ^ 2) +
                ∫ x in a..b, w x * (rx x) ^ 2) +
            |w b * r b * rx b - w a * r a * rx a|) +
        ((w b * chiOneEntropyMultiplier (u b) * ux b -
            w a * chiOneEntropyMultiplier (u a) * ux a) +
          c * (w b * chiOneRelativeEntropy (u b) -
            w a * chiOneRelativeEntropy (u a)) -
          chi * (w b * (u b - 1) * rx b -
            w a * (u a - 1) * rx a)) := by
  let A : ℝ → ℝ := fun x ↦ ux x / u x
  let W : ℝ → ℝ := fun x ↦ u x - 1
  let X : ℝ := ∫ x in a..b, w x * (A x) ^ 2
  let Y : ℝ := ∫ x in a..b, w x * (W x) ^ 2
  let R : ℝ := ∫ x in a..b, w x * (rx x) ^ 2
  let V : ℝ := ∫ x in a..b, w x * (r x) ^ 2
  let E : ℝ := ∫ x in a..b, w x * chiOneRelativeEntropy (u x)
  let K : ℝ := ∫ x in a..b, w x * A x * rx x
  let Jdiff : ℝ := ∫ x in a..b,
    w' x * chiOneEntropyMultiplier (u x) * ux x
  let Jentropy : ℝ := ∫ x in a..b,
    w' x * chiOneRelativeEntropy (u x)
  let Jchem : ℝ := ∫ x in a..b, w' x * W x * rx x
  let Bresolver : ℝ :=
    |w b * r b * rx b - w a * r a * rx a|
  let Q : ℝ := (1 / (2 * ell)) * (V + R) + Bresolver
  let Bentropy : ℝ :=
    (w b * chiOneEntropyMultiplier (u b) * ux b -
      w a * chiOneEntropyMultiplier (u a) * ux a) +
    c * (w b * chiOneRelativeEntropy (u b) -
      w a * chiOneRelativeEntropy (u a)) -
    chi * (w b * (u b - 1) * rx b -
      w a * (u a - 1) * rx a)
  let P : ℝ := ∫ x in a..b,
    w x * chiOneEntropyMultiplier (u x) * ut x
  let C : ℝ := |c| + chi + 2
  have hA_cont : Continuous A := by
    dsimp [A]
    apply Continuous.div d.ux_continuous d.u_continuous
    exact fun x ↦ (d.u_pos x).ne'
  have hW_cont : Continuous W := by
    exact d.u_continuous.sub continuous_const
  have hphi_cont : Continuous
      (fun x ↦ chiOneRelativeEntropy (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.entropy_comp_hasDerivAt x).continuousAt
  have hmult_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hX_cont : Continuous (fun x ↦ w x * (A x) ^ 2) :=
    d.w_continuous.mul (hA_cont.pow 2)
  have hY_cont : Continuous (fun x ↦ w x * (W x) ^ 2) :=
    d.w_continuous.mul (hW_cont.pow 2)
  have hR_cont : Continuous (fun x ↦ w x * (rx x) ^ 2) :=
    d.w_continuous.mul (d.rx_continuous.pow 2)
  have hV_cont : Continuous (fun x ↦ w x * (r x) ^ 2) :=
    d.w_continuous.mul (d.r_continuous.pow 2)
  have hE_cont : Continuous
      (fun x ↦ w x * chiOneRelativeEntropy (u x)) :=
    d.w_continuous.mul hphi_cont
  have hK_cont : Continuous (fun x ↦ w x * A x * rx x) :=
    (d.w_continuous.mul hA_cont).mul d.rx_continuous
  have hJdiff_cont : Continuous (fun x ↦
      w' x * chiOneEntropyMultiplier (u x) * ux x) :=
    (d.w'_cont.mul hmult_cont).mul d.ux_continuous
  have hJentropy_cont : Continuous
      (fun x ↦ w' x * chiOneRelativeEntropy (u x)) :=
    d.w'_cont.mul hphi_cont
  have hJchem_cont : Continuous (fun x ↦ w' x * W x * rx x) :=
    (d.w'_cont.mul hW_cont).mul d.rx_continuous
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact intervalIntegral.integral_nonneg d.hab
      (fun x _ ↦ mul_nonneg (d.w_pos x).le (sq_nonneg (A x)))
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    exact intervalIntegral.integral_nonneg d.hab
      (fun x _ ↦ mul_nonneg (d.w_pos x).le (sq_nonneg (W x)))
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact intervalIntegral.integral_nonneg d.hab (fun x _ ↦
      mul_nonneg (d.w_pos x).le
        (chiOneRelativeEntropy_nonneg (d.u_pos x)))
  have hcross_point : ∀ x,
      chi * (w x * A x * rx x) ≤
        w x * (A x) ^ 2 + (chi ^ 2 / 4) * (w x * (rx x) ^ 2) := by
    intro x
    nlinarith [mul_nonneg (d.w_pos x).le
      (sq_nonneg (A x - (chi / 2) * rx x))]
  have hcross : chi * K ≤ X + (chi ^ 2 / 4) * R := by
    dsimp [K, X, R]
    calc
      chi * (∫ x in a..b, w x * A x * rx x) =
          ∫ x in a..b, chi * (w x * A x * rx x) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in a..b,
          w x * (A x) ^ 2 +
            (chi ^ 2 / 4) * (w x * (rx x) ^ 2) := by
        apply intervalIntegral.integral_mono_on d.hab
          (hK_cont.const_mul chi |>.intervalIntegrable a b)
          ((hX_cont.add (hR_cont.const_mul
            (chi ^ 2 / 4))).intervalIntegrable a b)
        intro x _
        exact hcross_point x
      _ = (∫ x in a..b, w x * (A x) ^ 2) +
          (chi ^ 2 / 4) *
            (∫ x in a..b, w x * (rx x) ^ 2) := by
        rw [intervalIntegral.integral_add
          (hX_cont.intervalIntegrable a b)
          (hR_cont.const_mul (chi ^ 2 / 4) |>.intervalIntegrable a b)]
        rw [intervalIntegral.integral_const_mul]
  have hmult_ux : ∀ x,
      chiOneEntropyMultiplier (u x) * ux x = W x * A x := by
    intro x
    dsimp [W, A]
    unfold chiOneEntropyMultiplier
    field_simp [(d.u_pos x).ne']
  have hdiff_point : ∀ x,
      |w' x * chiOneEntropyMultiplier (u x) * ux x| ≤
        (1 / (2 * ell)) *
          (w x * (W x) ^ 2 + w x * (A x) ^ 2) := by
    intro x
    have hproduct :
        |W x * A x| ≤ ((W x) ^ 2 + (A x) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|W x| - |A x|),
        sq_abs (W x), sq_abs (A x)]
    have hrewrite :
        w' x * chiOneEntropyMultiplier (u x) * ux x =
          w' x * (W x * A x) := by
      rw [mul_assoc, hmult_ux x]
    rw [hrewrite]
    calc
      |w' x * (W x * A x)| = |w' x| * |W x * A x| := by
        rw [abs_mul]
      _ ≤ ((1 / ell) * w x) * |W x * A x| :=
        mul_le_mul_of_nonneg_right (d.w_slow x) (abs_nonneg _)
      _ ≤ ((1 / ell) * w x) *
          (((W x) ^ 2 + (A x) ^ 2) / 2) := by
        exact mul_le_mul_of_nonneg_left hproduct
          (mul_nonneg (div_nonneg zero_le_one d.hell.le) (d.w_pos x).le)
      _ = (1 / (2 * ell)) *
          (w x * (W x) ^ 2 + w x * (A x) ^ 2) := by ring
  have hJdiff_abs : |Jdiff| ≤ (1 / (2 * ell)) * (Y + X) := by
    dsimp [Jdiff, Y, X]
    calc
      |∫ x in a..b,
          w' x * chiOneEntropyMultiplier (u x) * ux x| ≤
          ∫ x in a..b,
            |w' x * chiOneEntropyMultiplier (u x) * ux x| :=
        intervalIntegral.abs_integral_le_integral_abs d.hab
      _ ≤ ∫ x in a..b, (1 / (2 * ell)) *
          (w x * (W x) ^ 2 + w x * (A x) ^ 2) := by
        apply intervalIntegral.integral_mono_on d.hab
          (hJdiff_cont.abs.intervalIntegrable a b)
          (((hY_cont.add hX_cont).const_mul
            (1 / (2 * ell))).intervalIntegrable a b)
        intro x _
        exact hdiff_point x
      _ = (1 / (2 * ell)) *
          ((∫ x in a..b, w x * (W x) ^ 2) +
            ∫ x in a..b, w x * (A x) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_add
          (hY_cont.intervalIntegrable a b)
          (hX_cont.intervalIntegrable a b)]
  have hentropy_point : ∀ x,
      |w' x * chiOneRelativeEntropy (u x)| ≤
        (1 / ell) * (w x * chiOneRelativeEntropy (u x)) := by
    intro x
    have hphi := chiOneRelativeEntropy_nonneg (d.u_pos x)
    calc
      |w' x * chiOneRelativeEntropy (u x)| =
          |w' x| * chiOneRelativeEntropy (u x) := by
        rw [abs_mul, abs_of_nonneg hphi]
      _ ≤ ((1 / ell) * w x) * chiOneRelativeEntropy (u x) :=
        mul_le_mul_of_nonneg_right (d.w_slow x) hphi
      _ = (1 / ell) * (w x * chiOneRelativeEntropy (u x)) := by
        ring
  have hJentropy_abs : |Jentropy| ≤ (1 / ell) * E := by
    dsimp [Jentropy, E]
    calc
      |∫ x in a..b, w' x * chiOneRelativeEntropy (u x)| ≤
          ∫ x in a..b, |w' x * chiOneRelativeEntropy (u x)| :=
        intervalIntegral.abs_integral_le_integral_abs d.hab
      _ ≤ ∫ x in a..b, (1 / ell) *
          (w x * chiOneRelativeEntropy (u x)) := by
        apply intervalIntegral.integral_mono_on d.hab
          (hJentropy_cont.abs.intervalIntegrable a b)
          (hE_cont.const_mul (1 / ell) |>.intervalIntegrable a b)
        intro x _
        exact hentropy_point x
      _ = (1 / ell) *
          ∫ x in a..b, w x * chiOneRelativeEntropy (u x) := by
        rw [intervalIntegral.integral_const_mul]
  have hchem_point : ∀ x,
      |w' x * W x * rx x| ≤
        (1 / (2 * ell)) *
          (w x * (W x) ^ 2 + w x * (rx x) ^ 2) := by
    intro x
    have hproduct :
        |W x * rx x| ≤ ((W x) ^ 2 + (rx x) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|W x| - |rx x|),
        sq_abs (W x), sq_abs (rx x)]
    calc
      |w' x * W x * rx x| = |w' x| * |W x * rx x| := by
        simp only [abs_mul, mul_assoc]
      _ ≤ ((1 / ell) * w x) * |W x * rx x| :=
        mul_le_mul_of_nonneg_right (d.w_slow x) (abs_nonneg _)
      _ ≤ ((1 / ell) * w x) *
          (((W x) ^ 2 + (rx x) ^ 2) / 2) := by
        exact mul_le_mul_of_nonneg_left hproduct
          (mul_nonneg (div_nonneg zero_le_one d.hell.le) (d.w_pos x).le)
      _ = (1 / (2 * ell)) *
          (w x * (W x) ^ 2 + w x * (rx x) ^ 2) := by ring
  have hJchem_abs : |Jchem| ≤ (1 / (2 * ell)) * (Y + R) := by
    dsimp [Jchem, Y, R]
    calc
      |∫ x in a..b, w' x * W x * rx x| ≤
          ∫ x in a..b, |w' x * W x * rx x| :=
        intervalIntegral.abs_integral_le_integral_abs d.hab
      _ ≤ ∫ x in a..b, (1 / (2 * ell)) *
          (w x * (W x) ^ 2 + w x * (rx x) ^ 2) := by
        apply intervalIntegral.integral_mono_on d.hab
          (hJchem_cont.abs.intervalIntegrable a b)
          (((hY_cont.add hR_cont).const_mul
            (1 / (2 * ell))).intervalIntegrable a b)
        intro x _
        exact hchem_point x
      _ = (1 / (2 * ell)) *
          ((∫ x in a..b, w x * (W x) ^ 2) +
            ∫ x in a..b, w x * (rx x) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_add
          (hY_cont.intervalIntegrable a b)
          (hR_cont.intervalIntegrable a b)]
  have hresolver := d.weighted_resolver_le
  change R ≤ (1 / 4 : ℝ) * Y +
    (1 / (2 * ell)) * (V + R) + Bresolver at hresolver
  have hresolverQ : R ≤ (1 / 4 : ℝ) * Y + Q := by
    dsimp [Q]
    linarith [hresolver]
  have hmain :
      -X + chi * K - Y ≤
        -(1 - chi ^ 2 / 16) * Y + (chi ^ 2 / 4) * Q := by
    calc
      -X + chi * K - Y ≤ -Y + (chi ^ 2 / 4) * R := by
        linarith [hcross]
      _ ≤ -Y + (chi ^ 2 / 4) * ((1 / 4 : ℝ) * Y + Q) := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hresolverQ
            (show 0 ≤ chi ^ 2 / 4 by positivity)) _
      _ = -(1 - chi ^ 2 / 16) * Y + (chi ^ 2 / 4) * Q := by
        ring
  have hJdiff_upper : -Jdiff ≤ (1 / (2 * ell)) * (Y + X) :=
    le_trans (neg_le_abs Jdiff) hJdiff_abs
  have hJentropy_upper :
      -c * Jentropy ≤ (|c| / ell) * E := by
    calc
      -c * Jentropy ≤ |-c * Jentropy| := le_abs_self _
      _ = |c| * |Jentropy| := by rw [abs_mul, abs_neg]
      _ ≤ |c| * ((1 / ell) * E) :=
        mul_le_mul_of_nonneg_left hJentropy_abs (abs_nonneg c)
      _ = (|c| / ell) * E := by ring
  have hJchem_upper :
      chi * Jchem ≤ (chi / (2 * ell)) * (Y + R) := by
    calc
      chi * Jchem ≤ chi * |Jchem| :=
        mul_le_mul_of_nonneg_left (le_abs_self Jchem) hchi
      _ ≤ chi * ((1 / (2 * ell)) * (Y + R)) :=
        mul_le_mul_of_nonneg_left hJchem_abs hchi
      _ = (chi / (2 * ell)) * (Y + R) := by ring
  have hchem_resolver :
      chi * Jchem ≤
        (chi / (2 * ell)) *
          (Y + (1 / 4 : ℝ) * Y + Q) := by
    calc
      chi * Jchem ≤ (chi / (2 * ell)) * (Y + R) :=
        hJchem_upper
      _ ≤ (chi / (2 * ell)) *
          (Y + ((1 / 4 : ℝ) * Y + Q)) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add_right hresolverQ Y)
          (div_nonneg hchi (mul_nonneg (by norm_num) d.hell.le))
      _ = (chi / (2 * ell)) *
          (Y + (1 / 4 : ℝ) * Y + Q) := by ring
  have hid := d.weighted_entropy_production_identity
  change P =
    (-X + chi * K - Y) +
      (-Jdiff - c * Jentropy + chi * Jchem) + Bentropy at hid
  have hdetail :
      P ≤ -(1 - chi ^ 2 / 16) * Y + (chi ^ 2 / 4) * Q +
        (1 / (2 * ell)) * (Y + X) + (|c| / ell) * E +
        (chi / (2 * ell)) * (Y + (1 / 4 : ℝ) * Y + Q) +
        Bentropy := by
    linarith [hmain, hJdiff_upper, hJentropy_upper, hchem_resolver]
  have hnum_X : (1 / 2 : ℝ) ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg c]
  have hcoef_X : 1 / (2 * ell) ≤ C / ell := by
    calc
      1 / (2 * ell) = (1 / 2 : ℝ) / ell := by
        field_simp [d.hell.ne']
      _ ≤ C / ell :=
        (div_le_div_iff_of_pos_right d.hell).2 hnum_X
  have hnum_E : |c| ≤ C := by
    dsimp [C]
    nlinarith [hchi]
  have hcoef_E : |c| / ell ≤ C / ell :=
    (div_le_div_iff_of_pos_right d.hell).2 hnum_E
  have hnum_Y :
      (1 / 2 : ℝ) + (5 / 8 : ℝ) * chi ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg c]
  have hcoef_Y :
      1 / (2 * ell) + (5 / 4 : ℝ) * (chi / (2 * ell)) ≤
        C / ell := by
    calc
      1 / (2 * ell) + (5 / 4 : ℝ) * (chi / (2 * ell)) =
          ((1 / 2 : ℝ) + (5 / 8 : ℝ) * chi) / ell := by
        field_simp [d.hell.ne']
        ring
      _ ≤ C / ell :=
        (div_le_div_iff_of_pos_right d.hell).2 hnum_Y
  have hX_budget := mul_le_mul_of_nonneg_right hcoef_X hX_nonneg
  have hE_budget := mul_le_mul_of_nonneg_right hcoef_E hE_nonneg
  have hY_budget := mul_le_mul_of_nonneg_right hcoef_Y hY_nonneg
  have hbudget :
      (1 / (2 * ell)) * (Y + X) + (|c| / ell) * E +
          (chi / (2 * ell)) * (Y + (1 / 4 : ℝ) * Y) ≤
        (C / ell) * (E + X + Y) := by
    calc
      (1 / (2 * ell)) * (Y + X) + (|c| / ell) * E +
          (chi / (2 * ell)) * (Y + (1 / 4 : ℝ) * Y) =
          (1 / (2 * ell)) * X + (|c| / ell) * E +
            (1 / (2 * ell) +
              (5 / 4 : ℝ) * (chi / (2 * ell))) * Y := by
        ring
      _ ≤ (C / ell) * X + (C / ell) * E + (C / ell) * Y := by
        linarith [hX_budget, hE_budget, hY_budget]
      _ = (C / ell) * (E + X + Y) := by ring
  have hXY :
      (∫ x in a..b, w x * ((A x) ^ 2 + (W x) ^ 2)) = X + Y := by
    dsimp [X, Y]
    rw [show (fun x ↦ w x * ((A x) ^ 2 + (W x) ^ 2)) =
        (fun x ↦ w x * (A x) ^ 2 + w x * (W x) ^ 2) by
      funext x
      ring]
    rw [intervalIntegral.integral_add
      (hX_cont.intervalIntegrable a b)
      (hY_cont.intervalIntegrable a b)]
  change P ≤ -(1 - chi ^ 2 / 16) * Y +
    (C / ell) *
      (E + ∫ x in a..b, w x * ((A x) ^ 2 + (W x) ^ 2)) +
    (chi ^ 2 / 4 + chi / (2 * ell)) * Q + Bentropy
  rw [hXY]
  calc
    P ≤ -(1 - chi ^ 2 / 16) * Y + (chi ^ 2 / 4) * Q +
        (1 / (2 * ell)) * (Y + X) + (|c| / ell) * E +
        (chi / (2 * ell)) * (Y + (1 / 4 : ℝ) * Y + Q) +
        Bentropy := hdetail
    _ = -(1 - chi ^ 2 / 16) * Y +
        ((1 / (2 * ell)) * (Y + X) + (|c| / ell) * E +
          (chi / (2 * ell)) * (Y + (1 / 4 : ℝ) * Y)) +
        (chi ^ 2 / 4 + chi / (2 * ell)) * Q + Bentropy := by
      ring
    _ ≤ -(1 - chi ^ 2 / 16) * Y +
        (C / ell) * (E + (X + Y)) +
        (chi ^ 2 / 4 + chi / (2 * ell)) * Q + Bentropy := by
      linarith [hbudget]

end ChiOneWeightedEntropySlice

section AxiomAudit

#print axioms ChiOneWeightedEntropySlice.weighted_resolver_le
#print axioms ChiOneWeightedEntropySlice.weighted_diffusion_integral
#print axioms ChiOneWeightedEntropySlice.weighted_drift_integral
#print axioms ChiOneWeightedEntropySlice.weighted_chemotaxis_integral
#print axioms ChiOneWeightedEntropySlice.weighted_reaction_integral
#print axioms ChiOneWeightedEntropySlice.weighted_entropy_production_identity
#print axioms ChiOneWeightedEntropySlice.chiOneRelativeEntropy_nonneg
#print axioms ChiOneWeightedEntropySlice.weighted_sharp_entropy_production_le

end AxiomAudit

end ShenWork.Paper1
