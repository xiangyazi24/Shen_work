import ShenWork.Paper1.WholeLineWeightedRegularityVolterra

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# A single-history Henry closure

The cap-weighted spatial difference quotient of the canonical restarted mild
solution satisfies a Volterra inequality for one scalar history, rather than a
Picard recurrence.  This file records the scalar inverse-square-root closure
needed by that argument.  Every integral carries an explicit integrability
hypothesis.
-/

/-- Exact mass of the inverse-square-root profile based at the left endpoint. -/
theorem intervalIntegral_invSqrt_eq_two_sqrt
    {t : ℝ} (_ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, s ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt t := by
  have hrpow := integral_rpow
    (a := (0 : ℝ)) (b := t) (r := -(1 / 2 : ℝ))
    (Or.inl (by norm_num))
  rw [hrpow]
  have hzero : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 :=
    Real.zero_rpow (by norm_num)
  rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by ring,
    hzero, sub_zero, show t ^ (1 / 2 : ℝ) = Real.sqrt t by
      exact (Real.sqrt_eq_rpow t).symm]
  ring

/-- One scaled Henry step.  If a history is bounded by the tentative profile
`S / √t` on `(0,t]`, then its Volterra inequality improves the scaled value
at `t` by the explicit constant and inverse-square-root kernel masses. -/
theorem henry_invSqrt_scaled_step_of_majorant
    {T A C0 C1 S t : ℝ} {r : ℝ → ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) T)
    (_hA : 0 ≤ A) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hS : 0 ≤ S)
    (hr0 : r 0 ≤ 0)
    (hr_int : IntervalIntegrable r volume 0 t)
    (hconv_int : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ)) * r s) volume 0 t)
    (hmajor : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      r s ≤ S * s ^ (-(1 / 2 : ℝ)))
    (hself : r t ≤
      A * t ^ (-(1 / 2 : ℝ)) +
        C0 * (∫ s in (0 : ℝ)..t, r s) +
        C1 * (∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * r s)) :
    Real.sqrt t * r t ≤
      A + (2 * C0 * T + C1 * Real.pi * Real.sqrt T) * S := by
  have htpos : 0 < t := ht.1
  have htT : t ≤ T := ht.2
  have hmajor_closed : ∀ s ∈ Set.Icc (0 : ℝ) t,
      r s ≤ S * s ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa using hr0
    · exact hmajor s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
  have hinv : IntervalIntegrable
      (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hr_le :
      (∫ s in (0 : ℝ)..t, r s) ≤ 2 * S * Real.sqrt t := by
    calc
      (∫ s in (0 : ℝ)..t, r s) ≤
          ∫ s in (0 : ℝ)..t, S * s ^ (-(1 / 2 : ℝ)) := by
        exact intervalIntegral.integral_mono_on htpos.le hr_int
          (hinv.const_mul S) hmajor_closed
      _ = S * (2 * Real.sqrt t) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_invSqrt_eq_two_sqrt htpos]
      _ = 2 * S * Real.sqrt t := by ring
  have hconv_le :
      (∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * r s) ≤ S * Real.pi :=
    intervalIntegral_invSqrt_mul_le_of_invSqrt_majorant
      htpos hconv_int hmajor_closed
  have hinside :
      A * t ^ (-(1 / 2 : ℝ)) +
          C0 * (∫ s in (0 : ℝ)..t, r s) +
          C1 * (∫ s in (0 : ℝ)..t,
            (t - s) ^ (-(1 / 2 : ℝ)) * r s) ≤
        A * t ^ (-(1 / 2 : ℝ)) +
          C0 * (2 * S * Real.sqrt t) + C1 * (S * Real.pi) := by
    have h0 := mul_le_mul_of_nonneg_left hr_le hC0
    have h1 := mul_le_mul_of_nonneg_left hconv_le hC1
    linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hscaled :
      Real.sqrt t * r t ≤
        Real.sqrt t *
          (A * t ^ (-(1 / 2 : ℝ)) +
            C0 * (2 * S * Real.sqrt t) + C1 * (S * Real.pi)) := by
    exact (mul_le_mul_of_nonneg_left hself hsqrt_nonneg).trans
      (mul_le_mul_of_nonneg_left hinside hsqrt_nonneg)
  have hrpow : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg htpos.le, Real.sqrt_eq_rpow]
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hsqrt_rpow : Real.sqrt t * t ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [hrpow]
    exact mul_inv_cancel₀ hsqrt_ne
  have hsqrt_sq : Real.sqrt t * Real.sqrt t = t := by
    nlinarith [Real.sq_sqrt htpos.le]
  have hexact :
      Real.sqrt t *
          (A * t ^ (-(1 / 2 : ℝ)) +
            C0 * (2 * S * Real.sqrt t) + C1 * (S * Real.pi)) =
        A + (2 * C0 * t + C1 * Real.pi * Real.sqrt t) * S := by
    calc
      _ = A * (Real.sqrt t * t ^ (-(1 / 2 : ℝ))) +
          2 * C0 * S * (Real.sqrt t * Real.sqrt t) +
          C1 * Real.pi * Real.sqrt t * S := by ring
      _ = A + (2 * C0 * t + C1 * Real.pi * Real.sqrt t) * S := by
        rw [hsqrt_rpow, hsqrt_sq]
        ring
  have hsqrt_le : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hconst :
      2 * C0 * t + C1 * Real.pi * Real.sqrt t ≤
        2 * C0 * T + C1 * Real.pi * Real.sqrt T := by
    have hlin : 2 * C0 * t ≤ 2 * C0 * T :=
      mul_le_mul_of_nonneg_left htT (by positivity)
    have hsqrt_part : C1 * Real.pi * Real.sqrt t ≤
        C1 * Real.pi * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hsqrt_le
        (mul_nonneg hC1 Real.pi_pos.le)
    linarith
  calc
    Real.sqrt t * r t ≤
        A + (2 * C0 * t + C1 * Real.pi * Real.sqrt t) * S := by
      rw [← hexact]
      exact hscaled
    _ ≤ A + (2 * C0 * T + C1 * Real.pi * Real.sqrt T) * S := by
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hconst hS) A)

/-- Singular Gronwall--Henry closure for a single nonnegative history.  The
boundedness hypothesis is only for the scaled scalar profile; in the PDE
application it follows from the continuous finite-difference history on a
compact positive-time window. -/
theorem henry_invSqrt_bound_of_self_volterra
    {T A C0 C1 : ℝ} {r : ℝ → ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hq_lt : 2 * C0 * T + C1 * Real.pi * Real.sqrt T < 1)
    (hr0 : r 0 ≤ 0)
    (hr_nonneg : ∀ t ∈ Set.Ioc (0 : ℝ) T, 0 ≤ r t)
    (hr_int : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      IntervalIntegrable r volume 0 t)
    (hconv_int : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      IntervalIntegrable
        (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ)) * r s) volume 0 t)
    (hself : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      r t ≤ A * t ^ (-(1 / 2 : ℝ)) +
        C0 * (∫ s in (0 : ℝ)..t, r s) +
        C1 * (∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * r s))
    (hBdd : BddAbove
      ((fun t : ℝ => Real.sqrt t * r t) '' Set.Ioc (0 : ℝ) T)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) T,
      r t ≤
        (A / (1 - (2 * C0 * T + C1 * Real.pi * Real.sqrt T))) *
          t ^ (-(1 / 2 : ℝ)) := by
  let E : Set ℝ :=
    (fun t : ℝ => Real.sqrt t * r t) '' Set.Ioc (0 : ℝ) T
  let S : ℝ := sSup E
  have ht0 : T / 2 ∈ Set.Ioc (0 : ℝ) T := by
    constructor <;> linarith
  have hE_nonempty : E.Nonempty := by
    exact ⟨Real.sqrt (T / 2) * r (T / 2), ⟨T / 2, ht0, rfl⟩⟩
  have hBddE : BddAbove E := by simpa only [E] using hBdd
  have hS_nonneg : 0 ≤ S := by
    have hmember : Real.sqrt (T / 2) * r (T / 2) ∈ E :=
      ⟨T / 2, ht0, rfl⟩
    have hleS : Real.sqrt (T / 2) * r (T / 2) ≤ S := by
      exact le_csSup hBddE hmember
    have hleft : 0 ≤ Real.sqrt (T / 2) * r (T / 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (hr_nonneg (T / 2) ht0)
    exact hleft.trans hleS
  have hprofile : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      r t ≤ S * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have hmem : Real.sqrt t * r t ∈ E := ⟨t, ht, rfl⟩
    have hscaled_le : Real.sqrt t * r t ≤ S := le_csSup hBddE hmem
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
    have hdiv : r t ≤ S / Real.sqrt t := by
      apply (le_div_iff₀ hsqrt_pos).2
      simpa [mul_comm] using hscaled_le
    have hrpow : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht.1.le, Real.sqrt_eq_rpow]
    calc
      r t ≤ S / Real.sqrt t := hdiv
      _ = S * t ^ (-(1 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, hrpow]
  have hscaled_step : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      Real.sqrt t * r t ≤
        A + (2 * C0 * T + C1 * Real.pi * Real.sqrt T) * S := by
    intro t ht
    apply henry_invSqrt_scaled_step_of_majorant ht hA hC0 hC1 hS_nonneg
      hr0 (hr_int t ht) (hconv_int t ht)
    · intro s hs
      exact hprofile s ⟨hs.1, hs.2.trans ht.2⟩
    · exact hself t ht
  have hS_step :
      S ≤ A + (2 * C0 * T + C1 * Real.pi * Real.sqrt T) * S := by
    apply csSup_le hE_nonempty
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact hscaled_step t ht
  have hden_pos : 0 < 1 - (2 * C0 * T + C1 * Real.pi * Real.sqrt T) :=
    sub_pos.mpr hq_lt
  have hS_bound :
      S ≤ A / (1 - (2 * C0 * T + C1 * Real.pi * Real.sqrt T)) := by
    apply (le_div_iff₀ hden_pos).2
    nlinarith [hS_step]
  intro t ht
  have hscaled_le : Real.sqrt t * r t ≤ S :=
    le_csSup hBddE ⟨t, ht, rfl⟩
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  have hdiv : r t ≤
      (A / (1 - (2 * C0 * T + C1 * Real.pi * Real.sqrt T))) /
        Real.sqrt t := by
    apply (le_div_iff₀ hsqrt_pos).2
    simpa [mul_comm] using hscaled_le.trans hS_bound
  have hrpow : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.1.le, Real.sqrt_eq_rpow]
  calc
    r t ≤
        (A / (1 - (2 * C0 * T + C1 * Real.pi * Real.sqrt T))) /
          Real.sqrt t := hdiv
    _ =
        (A / (1 - (2 * C0 * T + C1 * Real.pi * Real.sqrt T))) *
          t ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, hrpow]

section AxiomAudit

#print axioms intervalIntegral_invSqrt_eq_two_sqrt
#print axioms henry_invSqrt_scaled_step_of_majorant
#print axioms henry_invSqrt_bound_of_self_volterra

end AxiomAudit

end ShenWork.Paper1
