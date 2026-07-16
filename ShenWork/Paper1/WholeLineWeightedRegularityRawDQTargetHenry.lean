import ShenWork.Paper1.WholeLineWeightedRegularityH1VolterraAuto
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQShiftedIntegrability
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQTimeShift

open MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Target-time Henry closure for one fixed raw-DQ profile

The restart face must be chosen only after the short Henry window is known.
This theorem fixes one profile on the whole target interval, chooses the
window, moves the restart face to `t-H`, and closes the resulting scalar
Volterra inequality at the prescribed target time `t`.
-/

/-- A restart inequality valid on every positive subinterval yields a
step-independent raw-DQ norm bound at one prescribed positive target time,
on any fixed Henry window satisfying the scalar smallness condition.  Keeping
`H` explicit is essential when the same window must serve an entire family of
cap radii and difference-quotient steps. -/
theorem target_norm_bound_of_restart_henry_on_fixed_window
    {t H A0 A1 F D0 D1 C0 C1 X0 K0 K1 delta : ℝ}
    (ht : 0 < t)
    (hH : 0 < H) (hHt : H ≤ t / 2)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hX0 : 0 ≤ X0) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (hdelta : delta ≠ 0)
    (P : ℝ → WholeLineRealL2)
    (hPint : IntervalIntegrable P volume 0 t)
    (hPbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖P s‖ ≤ X0)
    (hXcrude : X0 ≤ K0 + |delta⁻¹| * K1)
    (hsmall : 2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1)
    (hrestart : ∀ a r : ℝ, 0 < a → a < r → r ≤ t →
      ‖P r‖ ≤
        A0 * (r - a) ^ (-(1 / 2 : ℝ)) + A1 +
          F * (D0 * (r - a) + 2 * D1 * Real.sqrt (r - a)) +
          ∫ s in a..r,
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖) :
    Real.sqrt H * ‖P t‖ ≤
      ((A0 + A1 + F * (D0 * H + 2 * D1 * Real.sqrt H)) *
        (1 + Real.sqrt H)) /
      (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  let a : ℝ := t - H
  let x : ℝ → ℝ := fun q => ‖P (a + q)‖
  let A : ℝ := A0 + A1 + F * (D0 * H + 2 * D1 * Real.sqrt H)
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have ha0 : 0 ≤ a := ha.le
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hx_nonneg : ∀ q ∈ Set.Ioc (0 : ℝ) H, 0 ≤ x q := by
    intro q _hq
    exact norm_nonneg _
  have hsegment : ∀ q ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable P volume a (a + q) := by
    intro q hq
    have hqH : q ≤ H := hq.2
    apply hPint.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hq.1.le),
      Set.uIcc_of_le ht.le]
    exact Set.Icc_subset_Icc ha0 (by
      dsimp only [a]
      linarith)
  have hx_int : ∀ q ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable x volume 0 q := by
    intro q hq
    simpa only [x, add_comm] using
      (wholeLineRealL2_norm_restart_intervalIntegrable (hsegment q hq))
  have hx_bound : ∀ q ∈ Set.Ioc (0 : ℝ) H,
      ∀ s ∈ Set.Icc (0 : ℝ) q, |x s| ≤ X0 := by
    intro q hq s hs
    have hqH : q ≤ H := hq.2
    have hsH : s ≤ H := hs.2.trans hqH
    have hast : a + s ∈ Set.Icc (0 : ℝ) t := by
      constructor
      · exact ha0.trans (le_add_of_nonneg_right hs.1)
      · dsimp only [a]
        linarith
    simp only [x, abs_of_nonneg (norm_nonneg _)]
    exact hPbound (a + s) hast
  have hconv_int : ∀ q ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable
        (fun s : ℝ => (q - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 q := by
    intro q hq
    exact intervalIntegrable_invSqrt_sub_mul_of_abs_le hq.1 hX0
      (hx_int q hq) (hx_bound q hq)
  have hineq : ∀ q ∈ Set.Ioc (0 : ℝ) H,
      x q ≤ A * (1 + q ^ (-(1 / 2 : ℝ))) +
        ∫ s in (0 : ℝ)..q,
          (C0 + C1 * (q - s) ^ (-(1 / 2 : ℝ))) * x s := by
    intro q hq
    have hqH : q ≤ H := hq.2
    have har : a < a + q := lt_add_of_pos_right _ hq.1
    have hart : a + q ≤ t := by
      dsimp only [a]
      linarith
    have hraw := hrestart a (a + q) ha har hart
    have hqHsqrt : Real.sqrt q ≤ Real.sqrt H :=
      Real.sqrt_le_sqrt hqH
    have hforce :
        A0 * q ^ (-(1 / 2 : ℝ)) + A1 +
            F * (D0 * q + 2 * D1 * Real.sqrt q) ≤
          A * (1 + q ^ (-(1 / 2 : ℝ))) := by
      have hDq : D0 * q + 2 * D1 * Real.sqrt q ≤
          D0 * H + 2 * D1 * Real.sqrt H := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqH hD0)
          (mul_le_mul_of_nonneg_left hqHsqrt
            (mul_nonneg (by norm_num) hD1))
      have hregular : A1 + F * (D0 * q + 2 * D1 * Real.sqrt q) ≤ A := by
        dsimp only [A]
        have hmul := mul_le_mul_of_nonneg_left hDq hF
        linarith
      have hA0A : A0 ≤ A := by
        have hextra : 0 ≤ A1 + F * (D0 * H + 2 * D1 * Real.sqrt H) :=
          add_nonneg hA1
            (mul_nonneg hF
              (add_nonneg (mul_nonneg hD0 hH.le)
                (mul_nonneg (mul_nonneg (by norm_num) hD1)
                  (Real.sqrt_nonneg _))))
        dsimp only [A]
        linarith
      have hrpow : 0 ≤ q ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg hq.1.le _
      have hsing := mul_le_mul_of_nonneg_right hA0A hrpow
      calc
        A0 * q ^ (-(1 / 2 : ℝ)) + A1 +
            F * (D0 * q + 2 * D1 * Real.sqrt q) ≤
          A * q ^ (-(1 / 2 : ℝ)) + A := by linarith
        _ = A * (1 + q ^ (-(1 / 2 : ℝ))) := by ring
    have hint := intervalIntegral_restart_invSqrtKernel_eq a q C0 C1
      (fun s => ‖P s‖)
    dsimp only [x]
    rw [show a + q - a = q by ring] at hraw
    have hint' :
        (∫ s in a..a + q,
          (C0 + C1 * (a + q - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖) =
        ∫ s in (0 : ℝ)..q,
          (C0 + C1 * (q - s) ^ (-(1 / 2 : ℝ))) * ‖P (a + s)‖ := by
      simpa only [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] using hint
    rw [hint'] at hraw
    linarith
  have hcrude : ∀ q ∈ Set.Ioc (0 : ℝ) H,
      x q ≤ K0 + |delta⁻¹| * K1 := by
    intro q hq
    have hqH : q ≤ H := hq.2
    have haq : a + q ∈ Set.Icc (0 : ℝ) t := by
      constructor
      · exact ha0.trans (le_add_of_nonneg_right hq.1.le)
      · dsimp only [a]
        linarith
    exact (hPbound (a + q) haq).trans hXcrude
  have hclosed := volterra_one_add_invSqrt_profile_bound_of_fixed_step_bound
    hH hA hC0 hC1 hK0 hK1 hdelta hx_nonneg hx_int hconv_int hineq
      hsmall hcrude H ⟨hH, le_rfl⟩
  simpa only [x, a, A, sub_add_cancel] using hclosed

/-- Coefficient-only selection of a short Henry window.  Applications to a
family should choose this witness once and then use
`target_norm_bound_of_restart_henry_on_fixed_window` for every member. -/
theorem exists_shortWindow_target_norm_bound_of_restart_henry
    {t A0 A1 F D0 D1 C0 C1 X0 K0 K1 delta : ℝ}
    (ht : 0 < t)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hX0 : 0 ≤ X0) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (hdelta : delta ≠ 0)
    (P : ℝ → WholeLineRealL2)
    (hPint : IntervalIntegrable P volume 0 t)
    (hPbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖P s‖ ≤ X0)
    (hXcrude : X0 ≤ K0 + |delta⁻¹| * K1)
    (hrestart : ∀ a r : ℝ, 0 < a → a < r → r ≤ t →
      ‖P r‖ ≤
        A0 * (r - a) ^ (-(1 / 2 : ℝ)) + A1 +
          F * (D0 * (r - a) + 2 * D1 * Real.sqrt (r - a)) +
          ∫ s in a..r,
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖) :
    ∃ H : ℝ, 0 < H ∧ H ≤ t / 2 ∧
      2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1 ∧
      Real.sqrt H * ‖P t‖ ≤
        ((A0 + A1 + F * (D0 * H + 2 * D1 * Real.sqrt H)) *
          (1 + Real.sqrt H)) /
        (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  have htHalf : 0 < t / 2 := by linarith
  rcases exists_pos_le_henryProfileMass_lt_one htHalf hC0 hC1 with
    ⟨H, hH, hHt, hsmall⟩
  refine ⟨H, hH, hHt, hsmall, ?_⟩
  exact target_norm_bound_of_restart_henry_on_fixed_window
    ht hH hHt hA0 hA1 hF hD0 hD1 hC0 hC1 hX0 hK0 hK1 hdelta
      P hPint hPbound hXcrude hsmall hrestart

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.target_norm_bound_of_restart_henry_on_fixed_window

#print axioms
  ShenWork.Paper1.exists_shortWindow_target_norm_bound_of_restart_henry
