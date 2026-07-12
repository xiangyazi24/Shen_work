/-
  Singular Duhamel convolution at a reserved exponential rate.

  If the smoothing kernel and quadratic source both decay at rate `2d`, one
  factor of rate `d` can be reserved for the output.  The remaining singular
  kernel is integrable because `0 < theta < 1`; its exact `L¹` norm is a Gamma
  factor.  This is the scalar L6 estimate used by the weighted fixed point.
-/
import Mathlib.MeasureTheory.Integral.Gamma
import ShenWork.Paper3.IntervalDomainLinearizedSmoothing

namespace ShenWork.Paper3

open MeasureTheory Set Real

noncomputable section

/-- Positive singular kernel after reserving half of the exponential decay. -/
def reservedSingularKernel (theta d r : ℝ) : ℝ :=
  r ^ (-theta) * Real.exp (-d * r)

/-- The integrable Gamma constant for `reservedSingularKernel`. -/
def reservedSingularKernelMass (theta d : ℝ) : ℝ :=
  d ^ (theta - 1) * Real.Gamma (1 - theta)

theorem reservedSingularKernel_integrableOn_Ioi
    {theta d : ℝ} (_htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hd : 0 < d) :
    IntegrableOn (reservedSingularKernel theta d) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := -theta) (b := d)
    (by linarith) (by norm_num) hd
  change IntegrableOn
    (fun x : ℝ => x ^ (-theta) * Real.exp (-d * x)) (Set.Ioi 0)
  simpa only [Real.rpow_one, neg_mul] using h

theorem reservedSingularKernel_integral_Ioi
    {theta d : ℝ} (_htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hd : 0 < d) :
    (∫ r in Set.Ioi (0 : ℝ), reservedSingularKernel theta d r) =
      reservedSingularKernelMass theta d := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := -theta) (b := d)
    (by norm_num) (by linarith) hd
  change (∫ x in Set.Ioi (0 : ℝ),
      x ^ (-theta) * Real.exp (-d * x)) =
    d ^ (theta - 1) * Real.Gamma (1 - theta)
  have he1 : -1 + theta = theta - 1 := by ring
  have he2 : -theta + 1 = 1 - theta := by ring
  norm_num [Real.rpow_one] at h
  simpa only [neg_mul, he1, he2, show -(1 - theta) = theta - 1 by ring]
    using h

/-- L6: convolution of the order-`theta` smoothing singularity with a
quadratically decaying source retains exponential rate `d`. -/
theorem singular_quadratic_exponential_convolution_le
    {theta d t : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hd : 0 < d) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        (t - s) ^ (-theta) * Real.exp (-2 * d * (t - s)) *
          Real.exp (-2 * d * s)) ≤
      Real.exp (-d * t) * reservedSingularKernelMass theta d := by
  let base : ℝ → ℝ := reservedSingularKernel theta d
  let major : ℝ → ℝ := fun s => Real.exp (-d * t) * base (t - s)
  let source : ℝ → ℝ := fun s =>
    (t - s) ^ (-theta) * Real.exp (-2 * d * (t - s)) *
      Real.exp (-2 * d * s)
  have hbaseIoi : IntegrableOn base (Set.Ioi 0) := by
    simpa [base] using
      reservedSingularKernel_integrableOn_Ioi htheta0 htheta1 hd
  have hbaseIci : IntegrableOn base (Set.Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hbaseIoi
  have huIcc : Set.uIcc (0 : ℝ) t ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le ht]
    exact fun r hr => hr.1
  have hbaseInt : IntervalIntegrable base volume (0 : ℝ) t :=
    (hbaseIci.mono_set huIcc).intervalIntegrable
  have hcompInt : IntervalIntegrable (fun s => base (t - s)) volume (0 : ℝ) t := by
    simpa using (hbaseInt.comp_sub_left t).symm
  have hmajorInt : IntervalIntegrable major volume (0 : ℝ) t := by
    exact hcompInt.const_mul (Real.exp (-d * t))
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t, source s ≤ major s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hr0 : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hpow0 : 0 ≤ (t - s) ^ (-theta) := Real.rpow_nonneg hr0 _
    have hexps : Real.exp (-d * s) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hexpEq :
        Real.exp (-2 * d * (t - s)) * Real.exp (-2 * d * s) =
          Real.exp (-d * t) * Real.exp (-d * (t - s)) *
            Real.exp (-d * s) := by
      calc
        Real.exp (-2 * d * (t - s)) * Real.exp (-2 * d * s) =
            Real.exp ((-2 * d * (t - s)) + (-2 * d * s)) := by
          rw [Real.exp_add]
        _ = Real.exp ((-d * t) + (-d * (t - s)) + (-d * s)) := by
          congr 1
          ring
        _ = Real.exp (-d * t) * Real.exp (-d * (t - s)) *
            Real.exp (-d * s) := by
          rw [Real.exp_add, Real.exp_add]
    dsimp only [source, major, base, reservedSingularKernel]
    rw [show
      (t - s) ^ (-theta) * Real.exp (-2 * d * (t - s)) *
          Real.exp (-2 * d * s) =
        (t - s) ^ (-theta) *
          (Real.exp (-2 * d * (t - s)) * Real.exp (-2 * d * s)) by ring]
    rw [hexpEq]
    have hnonneg :
        0 ≤ (t - s) ^ (-theta) *
          (Real.exp (-d * t) * Real.exp (-d * (t - s))) :=
      mul_nonneg hpow0 (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    calc
      (t - s) ^ (-theta) *
            (Real.exp (-d * t) * Real.exp (-d * (t - s)) *
              Real.exp (-d * s))
          ≤ (t - s) ^ (-theta) *
              (Real.exp (-d * t) * Real.exp (-d * (t - s)) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexps
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) hpow0
      _ = Real.exp (-d * t) *
            ((t - s) ^ (-theta) * Real.exp (-d * (t - s))) := by ring
  have hsource_meas : AEStronglyMeasurable source
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [source]
    fun_prop
  have hsourceInt : IntervalIntegrable source volume (0 : ℝ) t := by
    apply hmajorInt.mono_fun
    · exact hsource_meas
    · refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
      refine Filter.Eventually.of_forall (fun s hs => ?_)
      have hsIcc : s ∈ Set.Icc (0 : ℝ) t := by
        rw [Set.uIoc_of_le ht] at hs
        exact ⟨le_of_lt hs.1, hs.2⟩
      have hsource0 : 0 ≤ source s := by
        dsimp [source]
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hsIcc.2) _)
            (Real.exp_nonneg _)) (Real.exp_nonneg _)
      have hmajor0 : 0 ≤ major s := by
        dsimp [major, base, reservedSingularKernel]
        exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hsIcc.2) _)
            (Real.exp_nonneg _))
      simpa [Real.norm_eq_abs, abs_of_nonneg hsource0,
        abs_of_nonneg hmajor0] using hpoint s hsIcc
  have hmono :
      (∫ s in (0 : ℝ)..t, source s) ≤
        ∫ s in (0 : ℝ)..t, major s :=
    intervalIntegral.integral_mono_on ht hsourceInt hmajorInt hpoint
  have hmajorEq :
      (∫ s in (0 : ℝ)..t, major s) =
        Real.exp (-d * t) * ∫ r in (0 : ℝ)..t, base r := by
    dsimp [major]
    rw [intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_comp_sub_left, sub_self, tsub_zero]
  have hbase_nonneg : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), 0 ≤ base r := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall (fun r hr => ?_)
    dsimp [base, reservedSingularKernel]
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _)
  have hbaseInterval_le :
      (∫ r in (0 : ℝ)..t, base r) ≤
        ∫ r in Set.Ioi (0 : ℝ), base r := by
    rw [intervalIntegral.integral_of_le ht]
    exact setIntegral_mono_set hbaseIoi hbase_nonneg
      (Filter.Eventually.of_forall (fun r hr => Set.Ioc_subset_Ioi_self hr))
  calc
    (∫ s in (0 : ℝ)..t,
        (t - s) ^ (-theta) * Real.exp (-2 * d * (t - s)) *
          Real.exp (-2 * d * s))
        = ∫ s in (0 : ℝ)..t, source s := rfl
    _ ≤ ∫ s in (0 : ℝ)..t, major s := hmono
    _ = Real.exp (-d * t) * ∫ r in (0 : ℝ)..t, base r := hmajorEq
    _ ≤ Real.exp (-d * t) * ∫ r in Set.Ioi (0 : ℝ), base r :=
      mul_le_mul_of_nonneg_left hbaseInterval_le (Real.exp_nonneg _)
    _ = Real.exp (-d * t) * reservedSingularKernelMass theta d := by
      rw [show (∫ r in Set.Ioi (0 : ℝ), base r) =
          reservedSingularKernelMass theta d by
        simpa [base] using
          reservedSingularKernel_integral_Ioi htheta0 htheta1 hd]

#print axioms reservedSingularKernel_integrableOn_Ioi
#print axioms reservedSingularKernel_integral_Ioi
#print axioms singular_quadratic_exponential_convolution_le

end

end ShenWork.Paper3
