import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel

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

#print axioms volterraPicard_uniform_of_kernel_mass
#print axioms intervalIntegrable_const_add_mul_invSqrt_sub
#print axioms intervalIntegral_const_add_mul_invSqrt_sub
#print axioms intervalIntegral_const_add_mul_invSqrt_sub_le

end AxiomAudit

end ShenWork.Paper1
