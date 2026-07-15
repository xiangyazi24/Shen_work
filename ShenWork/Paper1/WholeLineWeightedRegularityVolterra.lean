import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalar Volterra closure for the weighted whole-line Picard scheme

The cap-weighted mild iteration is reduced to a nonnegative scalar history.
This file keeps the scalar induction separate from the spatial Schur estimates.
Every convolution used below carries an explicit `IntervalIntegrable`
hypothesis, so no conclusion relies on the convention for a non-integrable
integral.
-/

/-- Exact mass of the self-convolution of the heat-gradient kernel. -/
theorem intervalIntegral_betaHalf_kernel_eq_pi {r : ℝ} (hr : 0 < r) :
    ∫ s in (0 : ℝ)..r,
        (r - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) = Real.pi := by
  have htoC :
      ((∫ s in (0 : ℝ)..r,
          (r - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        ∫ s in (0 : ℝ)..r,
          (s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
            ((r : ℂ) - s) ^ ((1 / 2 : ℂ) - 1) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.le] at hs
    have hs0 : 0 ≤ s := hs.1
    have hrs0 : 0 ≤ r - s := sub_nonneg.mpr hs.2
    have h1 :
        (((r - s : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          ((r : ℂ) - s) ^ (-(2 : ℂ)⁻¹) := by
      simpa [Complex.ofReal_sub, one_div, neg_div] using
        Complex.ofReal_cpow hrs0 (-(1 / 2 : ℝ))
    have h2 :
        (((s : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          (s : ℂ) ^ (-(2 : ℂ)⁻¹) := by
      simpa [one_div, neg_div] using
        Complex.ofReal_cpow hs0 (-(1 / 2 : ℝ))
    calc
      (((r - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          (((r - s : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (((s : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
        Complex.ofReal_mul _ _
      _ = ((r : ℂ) - s) ^ (-(2 : ℂ)⁻¹) *
            (s : ℂ) ^ (-(2 : ℂ)⁻¹) := by rw [h1, h2]
      _ = (s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
            ((r : ℂ) - s) ^ ((1 / 2 : ℂ) - 1) := by
        norm_num [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
  apply Complex.ofReal_injective
  rw [htoC]
  have hscaled := Complex.betaIntegral_scaled
    (s := (1 / 2 : ℂ)) (t := (1 / 2 : ℂ)) (a := r) hr
  rw [show ((1 / 2 : ℂ) + (1 / 2 : ℂ) - 1) = 0 by norm_num,
    Complex.cpow_zero, one_mul] at hscaled
  rw [hscaled, Complex.betaIntegral_eq_Gamma_mul_div]
  · rw [show ((1 / 2 : ℂ) + (1 / 2 : ℂ)) = 1 by norm_num,
      Complex.Gamma_one, Complex.Gamma_one_half_eq, div_one,
      ← Complex.cpow_add]
    · norm_num
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · norm_num
  · norm_num

/-- The beta-half kernel is explicitly integrable; this hypothesis is kept
available to every later monotonicity estimate. -/
theorem intervalIntegrable_betaHalf_kernel {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable
      (fun s : ℝ =>
        (r - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) volume 0 r := by
  have hmid_pos : 0 < r / 2 := by linarith
  have h0mid : (0 : ℝ) ≤ r / 2 := hmid_pos.le
  have hmidr : r / 2 ≤ r := by linarith
  have hs_left :
      IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 (r / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hrsub_left_cont :
      ContinuousOn (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)))
        (Set.uIcc (0 : ℝ) (r / 2)) := by
    refine (continuous_const.sub continuous_id).continuousOn.rpow_const ?_
    intro s hs
    left
    rw [Set.uIcc_of_le h0mid] at hs
    have hrs : 0 < r - s := by nlinarith [hs.2, hr]
    simpa using ne_of_gt hrs
  have hleft :
      IntervalIntegrable
        (fun s : ℝ =>
          (r - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))
        volume 0 (r / 2) := by
    simpa [mul_comm] using
      hs_left.mul_continuousOn hrsub_left_cont
  have hrsub_right :
      IntervalIntegrable (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)))
        volume (r / 2) r := by
    refine intervalIntegrable_invSqrt_sub.mono_set (c := r / 2) (d := r) ?_
    intro x hx
    rw [Set.uIcc_of_le hmidr] at hx
    rw [Set.uIcc_of_le hr.le]
    exact ⟨h0mid.trans hx.1, hx.2⟩
  have hs_right_cont :
      ContinuousOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ)))
        (Set.uIcc (r / 2) r) := by
    refine continuous_id.continuousOn.rpow_const ?_
    intro s hs
    left
    rw [Set.uIcc_of_le hmidr] at hs
    exact ne_of_gt (hmid_pos.trans_le hs.1)
  have hright :
      IntervalIntegrable
        (fun s : ℝ =>
          (r - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))
        volume (r / 2) r :=
    hrsub_right.mul_continuousOn hs_right_cont
  exact hleft.trans hright

/-- A Volterra recurrence whose kernel has mass at most `q` preserves the
closed scalar ball of radius `B`, provided `A + q * B <= B`. -/
theorem volterraPicard_uniform_of_kernel_mass
    {T A B q : ℝ} {K : ℝ → ℝ} {r : ℕ → ℝ → ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (_hq_lt : q < 1) (hclose : A + q * B ≤ B)
    (hK_nonneg : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 ≤ K τ)
    (hK_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable (fun s : ℝ => K (t - s)) volume 0 t)
    (hK_mass : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, K (t - s)) ≤ q)
    (hr_int : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      IntervalIntegrable (fun s : ℝ => K (t - s) * r n s) volume 0 t)
    (hr0 : ∀ t ∈ Set.Icc (0 : ℝ) T, r 0 t ≤ B)
    (_hr_nonneg : ∀ n t, t ∈ Set.Icc (0 : ℝ) T → 0 ≤ r n t)
    (hstep : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      r (n + 1) t ≤ A + ∫ s in (0 : ℝ)..t, K (t - s) * r n s) :
    ∀ n t, t ∈ Set.Icc (0 : ℝ) T → r n t ≤ B := by
  intro n
  induction n with
  | zero => exact hr0
  | succ n ih =>
      intro t ht
      have h0t : (0 : ℝ) ≤ t := ht.1
      have hKt_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ K (t - s) := by
        intro s hs
        apply hK_nonneg (t - s)
        constructor
        · exact sub_nonneg.mpr hs.2
        · linarith [hs.1, ht.2]
      have hupper_int :
          IntervalIntegrable (fun s : ℝ => K (t - s) * B) volume 0 t := by
        simpa [mul_comm] using (hK_int t ht).const_mul B
      have hconv :
          (∫ s in (0 : ℝ)..t, K (t - s) * r n s) ≤
            ∫ s in (0 : ℝ)..t, K (t - s) * B := by
        apply intervalIntegral.integral_mono_on h0t (hr_int n t ht) hupper_int
        intro s hs
        exact mul_le_mul_of_nonneg_left
          (ih s ⟨hs.1, hs.2.trans ht.2⟩) (hKt_nonneg s hs)
      have hmassB :
          (∫ s in (0 : ℝ)..t, K (t - s) * B) ≤ q * B := by
        rw [show (fun s : ℝ => K (t - s) * B) =
            fun s : ℝ => B * K (t - s) by funext s; ring,
          intervalIntegral.integral_const_mul]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left (hK_mass t ht) hB)
      calc
        r (n + 1) t
            ≤ A + ∫ s in (0 : ℝ)..t, K (t - s) * r n s := hstep n t ht
        _ ≤ A + q * B := by linarith
        _ ≤ B := hclose

/-- The constant-plus-gradient kernel is integrable on every forward time
interval. -/
theorem intervalIntegrable_const_add_mul_invSqrt_sub
    {t C0 C1 : ℝ} :
    IntervalIntegrable
      (fun s : ℝ => C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  exact intervalIntegral.intervalIntegrable_const.add
    (intervalIntegrable_invSqrt_sub.const_mul C1)

/-- Exact mass of the constant-plus-gradient kernel. -/
theorem intervalIntegral_const_add_mul_invSqrt_sub
    {t C0 C1 : ℝ} (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t,
        (C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ)))) =
      C0 * t + 2 * C1 * Real.sqrt t := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegrable_invSqrt_sub.const_mul C1),
    intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral_invSqrt_sub_eq_two_sqrt ht]
  ring

/-- Uniform mass bound for the constant-plus-gradient kernel on `[0,T]`. -/
theorem intervalIntegral_const_add_mul_invSqrt_sub_le
    {t T C0 C1 : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    (∫ s in (0 : ℝ)..t,
        (C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ)))) ≤
      C0 * T + 2 * C1 * Real.sqrt T := by
  rw [intervalIntegral_const_add_mul_invSqrt_sub ht]
  have hT : 0 ≤ T := ht.le.trans htT
  have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  nlinarith

section AxiomAudit

#print axioms intervalIntegral_betaHalf_kernel_eq_pi
#print axioms intervalIntegrable_betaHalf_kernel
#print axioms volterraPicard_uniform_of_kernel_mass
#print axioms intervalIntegrable_const_add_mul_invSqrt_sub
#print axioms intervalIntegral_const_add_mul_invSqrt_sub
#print axioms intervalIntegral_const_add_mul_invSqrt_sub_le

end AxiomAudit

end ShenWork.Paper1
