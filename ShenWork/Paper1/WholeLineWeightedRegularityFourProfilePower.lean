import ShenWork.Paper1.WholeLineWeightedRegularitySpatialDifference

noncomputable section

namespace ShenWork.Paper1

/-- Exact matched-secant identity for two pairs of profiles. -/
theorem paper5_four_profile_power_sub_identity
    (beta a2 b2 a1 b1 : ℝ) :
    (a2 ^ beta - b2 ^ beta) - (a1 ^ beta - b1 ^ beta) =
      paper5MeanCoefficient beta a2 a1 *
          ((a2 - b2) - (a1 - b1)) +
        (paper5MeanCoefficient beta a2 a1 -
            paper5MeanCoefficient beta b2 b1) * (b2 - b1) := by
  have ha := paper5MeanCoefficient_mul_sub beta a2 a1
  have hb := paper5MeanCoefficient_mul_sub beta b2 b1
  calc
    (a2 ^ beta - b2 ^ beta) - (a1 ^ beta - b1 ^ beta) =
        (a2 ^ beta - a1 ^ beta) - (b2 ^ beta - b1 ^ beta) := by ring
    _ = paper5MeanCoefficient beta a2 a1 * (a2 - a1) -
          paper5MeanCoefficient beta b2 b1 * (b2 - b1) := by rw [ha, hb]
    _ = paper5MeanCoefficient beta a2 a1 *
          ((a2 - b2) - (a1 - b1)) +
        (paper5MeanCoefficient beta a2 a1 -
          paper5MeanCoefficient beta b2 b1) * (b2 - b1) := by ring

#print axioms paper5_four_profile_power_sub_identity

/-- In the subquadratic branch, the difference of the two spatial secants
is harmless after multiplication by a *relative* increment of the positive
reference profile.  This is the finite-increment version of the logarithmic
derivative cancellation in Paper 1 (5.23). -/
theorem paper5_four_profile_secant_relative_increment_bound
    {m M B h a2 b2 a1 b1 : ℝ}
    (hm1 : 1 < m) (hm2 : m < 2)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M)
    (hb2pos : 0 < b2) (hb1pos : 0 < b1)
    (hrelative : ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(b2 - b1) / h| ≤ B * (tau * b2 + (1 - tau) * b1)) :
    |paper5MeanCoefficient m a2 a1 -
        paper5MeanCoefficient m b2 b1| * |(b2 - b1) / h| ≤
      m * B * M ^ (m - 1) * (|a1 - b1| + |a2 - b2|) := by
  let au : ℝ → ℝ := fun tau => tau * a2 + (1 - tau) * a1
  let bu : ℝ → ℝ := fun tau => tau * b2 + (1 - tau) * b1
  let qbase : ℝ := (b2 - b1) / h
  let C : ℝ := m * B * M ^ (m - 1) * (|a1 - b1| + |a2 - b2|)
  have hm : 1 ≤ m := hm1.le
  have hq0 : 0 < m - 1 := by linarith
  have hq1 : m - 1 ≤ 1 := by linarith
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hMq0 : 0 ≤ M ^ (m - 1) := Real.rpow_nonneg hM _
  have hsum0 : 0 ≤ |a1 - b1| + |a2 - b2| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hseg (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      au tau ∈ Set.Icc (0 : ℝ) M ∧
        bu tau ∈ Set.Icc (0 : ℝ) M ∧ 0 < bu tau := by
    have hau := (convex_Icc (0 : ℝ) M).add_smul_sub_mem ha1 ha2 htau
    have hbu := (convex_Icc (0 : ℝ) M).add_smul_sub_mem hb1 hb2 htau
    have hau' : au tau ∈ Set.Icc (0 : ℝ) M := by
      have heq : au tau = a1 + tau * (a2 - a1) := by
        dsimp [au]
        ring
      rw [heq]
      exact hau
    have hbu' : bu tau ∈ Set.Icc (0 : ℝ) M := by
      have heq : bu tau = b1 + tau * (b2 - b1) := by
        dsimp [bu]
        ring
      rw [heq]
      exact hbu
    have hbminpos : 0 < min b1 b2 := lt_min hb1pos hb2pos
    have hb1min : b1 ∈ Set.Icc (min b1 b2) M :=
      ⟨min_le_left _ _, hb1.2⟩
    have hb2min : b2 ∈ Set.Icc (min b1 b2) M :=
      ⟨min_le_right _ _, hb2.2⟩
    have hbumin :=
      (convex_Icc (min b1 b2) M).add_smul_sub_mem hb1min hb2min htau
    have hbumin' : min b1 b2 ≤ bu tau := by
      have heq : bu tau = b1 + tau * (b2 - b1) := by
        dsimp [bu]
        ring
      rw [heq]
      exact hbumin.1
    exact ⟨hau', hbu', lt_of_lt_of_le hbminpos hbumin'⟩
  have hwu (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      |au tau - bu tau| ≤ |a1 - b1| + |a2 - b2| := by
    have ht0 : 0 ≤ tau := htau.1
    have ht1 : tau ≤ 1 := htau.2
    have h1t0 : 0 ≤ 1 - tau := sub_nonneg.mpr ht1
    calc
      |au tau - bu tau| =
          |tau * (a2 - b2) + (1 - tau) * (a1 - b1)| := by
            congr 1
            dsimp [au, bu]
            ring
      _ ≤ |tau * (a2 - b2)| + |(1 - tau) * (a1 - b1)| :=
        abs_add_le _ _
      _ = tau * |a2 - b2| + (1 - tau) * |a1 - b1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg h1t0]
      _ ≤ |a2 - b2| + |a1 - b1| := by
        exact add_le_add
          (mul_le_of_le_one_left (abs_nonneg _) ht1)
          (mul_le_of_le_one_left (abs_nonneg _) (by linarith))
      _ = |a1 - b1| + |a2 - b2| := add_comm _ _
  have hpoint (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      |m * (au tau ^ (m - 1) - bu tau ^ (m - 1)) * qbase| ≤ C := by
    rcases hseg tau htau with ⟨hau, hbu, hbupos⟩
    have hcoef := paper5MeanCoefficient_abs_mul_right_le_rpow
      (beta := m - 1) (s := au tau) (r := bu tau)
      hq0 hq1 hau.1 hbupos
    have hpowid := paper5MeanCoefficient_mul_sub (m - 1) (au tau) (bu tau)
    have habspow :
        |au tau ^ (m - 1) - bu tau ^ (m - 1)| =
          |paper5MeanCoefficient (m - 1) (au tau) (bu tau)| *
            |au tau - bu tau| := by
      rw [← hpowid, abs_mul]
    have hbuq : bu tau ^ (m - 1) ≤ M ^ (m - 1) :=
      Real.rpow_le_rpow hbu.1 hbu.2 hq0.le
    have hrel : |qbase| ≤ B * bu tau := by
      simpa [qbase, bu] using hrelative tau htau
    rw [abs_mul, abs_mul, abs_of_nonneg hm0, habspow]
    dsimp [C]
    calc
      m * (|paper5MeanCoefficient (m - 1) (au tau) (bu tau)| *
          |au tau - bu tau|) * |qbase| =
          m * (|paper5MeanCoefficient (m - 1) (au tau) (bu tau)| *
            bu tau) * |au tau - bu tau| * (|qbase| / bu tau) := by
              field_simp [ne_of_gt hbupos]
      _ ≤ m * (|paper5MeanCoefficient (m - 1) (au tau) (bu tau)| *
            bu tau) * |au tau - bu tau| * B := by
          have hdiv : |qbase| / bu tau ≤ B := (div_le_iff₀ hbupos).2 <| by
            simpa [mul_comm] using hrel
          gcongr
      _ ≤ m * (bu tau ^ (m - 1)) * |au tau - bu tau| * B := by
          gcongr
      _ ≤ m * (M ^ (m - 1)) *
            (|a1 - b1| + |a2 - b2|) * B := by
          gcongr
          exact hwu tau htau
      _ = m * B * M ^ (m - 1) * (|a1 - b1| + |a2 - b2|) := by ring
  have hinta : IntervalIntegrable
      (fun tau : ℝ => m * au tau ^ (m - 1)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · dsimp [au]
      fun_prop
    · intro _
      exact Or.inr hq0.le
  have hintb : IntervalIntegrable
      (fun tau : ℝ => m * bu tau ^ (m - 1)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · dsimp [bu]
      fun_prop
    · intro _
      exact Or.inr hq0.le
  have hcoefint :
      paper5MeanCoefficient m a2 a1 - paper5MeanCoefficient m b2 b1 =
        ∫ tau : ℝ in 0..1,
          (m * (au tau ^ (m - 1) - bu tau ^ (m - 1))) := by
    rw [← paper5IntegralMeanCoefficient_eq hm,
      ← paper5IntegralMeanCoefficient_eq hm]
    unfold paper5IntegralMeanCoefficient
    rw [← intervalIntegral.integral_sub hinta hintb]
    apply intervalIntegral.integral_congr
    intro tau _htau
    dsimp [au, bu]
    ring
  have hnorm :
      |∫ tau : ℝ in 0..1,
          (m * (au tau ^ (m - 1) - bu tau ^ (m - 1))) * qbase| ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := C)
        (f := fun tau : ℝ =>
          (m * (au tau ^ (m - 1) - bu tau ^ (m - 1))) * qbase)
        (fun tau htau => by
          rw [Real.norm_eq_abs]
          exact hpoint tau (by
            simpa [Set.uIcc_of_le zero_le_one] using
              (Set.uIoc_subset_uIcc htau))))
  rw [hcoefint]
  rw [← abs_mul, ← intervalIntegral.integral_mul_const]
  exact hnorm

#print axioms paper5_four_profile_secant_relative_increment_bound

/-- Matched four-profile finite-difference estimate for `1 < m < 2`.
The lower-order term is linear in the perturbation because the reference
increment is controlled relative to the positive reference segment. -/
theorem paper5_four_profile_power_quotient_bound
    {m M B h a2 b2 a1 b1 : ℝ}
    (hm1 : 1 < m) (hm2 : m < 2)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M)
    (hb2pos : 0 < b2) (hb1pos : 0 < b1)
    (hrelative : ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(b2 - b1) / h| ≤ B * (tau * b2 + (1 - tau) * b1)) :
    |((a2 ^ m - b2 ^ m) - (a1 ^ m - b1 ^ m)) / h| ≤
      m * M ^ (m - 1) *
          |((a2 - b2) - (a1 - b1)) / h| +
        m * B * M ^ (m - 1) * (|a1 - b1| + |a2 - b2|) := by
  have hm : 1 ≤ m := hm1.le
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hMq0 : 0 ≤ M ^ (m - 1) := Real.rpow_nonneg hM _
  have hA := paper5MeanCoefficient_abs_le
    (beta := m) (M := M) (s := a2) (r := a1) hm hM ha2 ha1
  have hsec := paper5_four_profile_secant_relative_increment_bound
    hm1 hm2 hM hB ha2 hb2 ha1 hb1 hb2pos hb1pos hrelative
  have hid := paper5_four_profile_power_sub_identity m a2 b2 a1 b1
  have hquot :
      ((a2 ^ m - b2 ^ m) - (a1 ^ m - b1 ^ m)) / h =
        paper5MeanCoefficient m a2 a1 *
            (((a2 - b2) - (a1 - b1)) / h) +
          (paper5MeanCoefficient m a2 a1 -
              paper5MeanCoefficient m b2 b1) * ((b2 - b1) / h) := by
    rw [hid]
    ring
  rw [hquot]
  calc
    |paper5MeanCoefficient m a2 a1 *
          (((a2 - b2) - (a1 - b1)) / h) +
        (paper5MeanCoefficient m a2 a1 -
            paper5MeanCoefficient m b2 b1) * ((b2 - b1) / h)|
        ≤ |paper5MeanCoefficient m a2 a1 *
              (((a2 - b2) - (a1 - b1)) / h)| +
            |(paper5MeanCoefficient m a2 a1 -
                paper5MeanCoefficient m b2 b1) * ((b2 - b1) / h)| :=
          abs_add_le _ _
    _ = |paper5MeanCoefficient m a2 a1| *
            |((a2 - b2) - (a1 - b1)) / h| +
          |paper5MeanCoefficient m a2 a1 -
              paper5MeanCoefficient m b2 b1| * |(b2 - b1) / h| := by
        rw [abs_mul, abs_mul]
    _ ≤ (m * M ^ (m - 1)) *
            |((a2 - b2) - (a1 - b1)) / h| +
          m * B * M ^ (m - 1) * (|a1 - b1| + |a2 - b2|) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) hsec

#print axioms paper5_four_profile_power_quotient_bound

/-- For `m ≥ 2`, the spatial secant coefficient is Lipschitz in the two
matched endpoint segments. -/
theorem paper5_four_profile_secant_difference_bound_of_two_le
    {m M a2 b2 a1 b1 : ℝ}
    (hm2 : 2 ≤ m) (hM : 0 ≤ M)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M) :
    |paper5MeanCoefficient m a2 a1 -
        paper5MeanCoefficient m b2 b1| ≤
      m * (m - 1) * M ^ (m - 2) *
        (|a1 - b1| + |a2 - b2|) := by
  let au : ℝ → ℝ := fun tau => tau * a2 + (1 - tau) * a1
  let bu : ℝ → ℝ := fun tau => tau * b2 + (1 - tau) * b1
  let C : ℝ := m * (m - 1) * M ^ (m - 2) *
    (|a1 - b1| + |a2 - b2|)
  have hm : 1 ≤ m := by linarith
  have hq : 1 ≤ m - 1 := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hq0 : 0 ≤ m - 1 := by linarith
  have hMq0 : 0 ≤ M ^ (m - 2) := Real.rpow_nonneg hM _
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hseg (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      au tau ∈ Set.Icc (0 : ℝ) M ∧ bu tau ∈ Set.Icc (0 : ℝ) M := by
    have hau := (convex_Icc (0 : ℝ) M).add_smul_sub_mem ha1 ha2 htau
    have hbu := (convex_Icc (0 : ℝ) M).add_smul_sub_mem hb1 hb2 htau
    have haueq : au tau = a1 + tau * (a2 - a1) := by
      dsimp [au]
      ring
    have hbueq : bu tau = b1 + tau * (b2 - b1) := by
      dsimp [bu]
      ring
    constructor
    · rw [haueq]
      exact hau
    · rw [hbueq]
      exact hbu
  have hwu (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      |au tau - bu tau| ≤ |a1 - b1| + |a2 - b2| := by
    have ht0 : 0 ≤ tau := htau.1
    have ht1 : tau ≤ 1 := htau.2
    have h1t0 : 0 ≤ 1 - tau := sub_nonneg.mpr ht1
    calc
      |au tau - bu tau| =
          |tau * (a2 - b2) + (1 - tau) * (a1 - b1)| := by
            congr 1
            dsimp [au, bu]
            ring
      _ ≤ |tau * (a2 - b2)| + |(1 - tau) * (a1 - b1)| :=
        abs_add_le _ _
      _ = tau * |a2 - b2| + (1 - tau) * |a1 - b1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg h1t0]
      _ ≤ |a2 - b2| + |a1 - b1| := by
        exact add_le_add
          (mul_le_of_le_one_left (abs_nonneg _) ht1)
          (mul_le_of_le_one_left (abs_nonneg _) (by linarith))
      _ = |a1 - b1| + |a2 - b2| := add_comm _ _
  have hpoint (tau : ℝ) (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
      |m * (au tau ^ (m - 1) - bu tau ^ (m - 1))| ≤ C := by
    rcases hseg tau htau with ⟨hau, hbu⟩
    have hA := paper5MeanCoefficient_abs_le
      (beta := m - 1) (M := M) (s := au tau) (r := bu tau)
      hq hM hau hbu
    have hA' :
        |paper5MeanCoefficient (m - 1) (au tau) (bu tau)| ≤
          (m - 1) * M ^ (m - 2) := by
      convert hA using 1 <;> ring
    have hpowid := paper5MeanCoefficient_mul_sub
      (m - 1) (au tau) (bu tau)
    have habspow :
        |au tau ^ (m - 1) - bu tau ^ (m - 1)| =
          |paper5MeanCoefficient (m - 1) (au tau) (bu tau)| *
            |au tau - bu tau| := by
      rw [← hpowid, abs_mul]
    rw [abs_mul, abs_of_nonneg hm0, habspow]
    dsimp [C]
    calc
      m * (|paper5MeanCoefficient (m - 1) (au tau) (bu tau)| *
          |au tau - bu tau|) ≤
          m * (((m - 1) * M ^ (m - 2)) * |au tau - bu tau|) := by
        gcongr
      _ ≤ m * (((m - 1) * M ^ (m - 2)) *
          (|a1 - b1| + |a2 - b2|)) := by
        gcongr
        exact hwu tau htau
      _ = m * (m - 1) * M ^ (m - 2) *
          (|a1 - b1| + |a2 - b2|) := by ring
  have hinta : IntervalIntegrable
      (fun tau : ℝ => m * au tau ^ (m - 1)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · dsimp [au]
      fun_prop
    · intro _
      exact Or.inr hq0
  have hintb : IntervalIntegrable
      (fun tau : ℝ => m * bu tau ^ (m - 1)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.rpow_const
    · dsimp [bu]
      fun_prop
    · intro _
      exact Or.inr hq0
  have hcoefint :
      paper5MeanCoefficient m a2 a1 - paper5MeanCoefficient m b2 b1 =
        ∫ tau : ℝ in 0..1,
          (m * (au tau ^ (m - 1) - bu tau ^ (m - 1))) := by
    rw [← paper5IntegralMeanCoefficient_eq hm,
      ← paper5IntegralMeanCoefficient_eq hm]
    unfold paper5IntegralMeanCoefficient
    rw [← intervalIntegral.integral_sub hinta hintb]
    apply intervalIntegral.integral_congr
    intro tau _htau
    dsimp [au, bu]
    ring
  rw [hcoefint]
  simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun tau : ℝ =>
        m * (au tau ^ (m - 1) - bu tau ^ (m - 1)))
      (fun tau htau => by
        rw [Real.norm_eq_abs]
        exact hpoint tau (by
          simpa [Set.uIcc_of_le zero_le_one] using
            (Set.uIoc_subset_uIcc htau))))

#print axioms paper5_four_profile_secant_difference_bound_of_two_le

/-- Matched four-profile quotient estimate in the `m ≥ 2` branch. -/
theorem paper5_four_profile_power_quotient_bound_of_two_le
    {m M DU h a2 b2 a1 b1 : ℝ}
    (hm2 : 2 ≤ m) (hM : 0 ≤ M) (hDU : 0 ≤ DU)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M)
    (hbase : |(b2 - b1) / h| ≤ DU) :
    |((a2 ^ m - b2 ^ m) - (a1 ^ m - b1 ^ m)) / h| ≤
      m * M ^ (m - 1) *
          |((a2 - b2) - (a1 - b1)) / h| +
        (m * (m - 1) * M ^ (m - 2) * DU) *
          (|a1 - b1| + |a2 - b2|) := by
  have hm : 1 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hA := paper5MeanCoefficient_abs_le
    (beta := m) (M := M) (s := a2) (r := a1) hm hM ha2 ha1
  have hsec := paper5_four_profile_secant_difference_bound_of_two_le
    hm2 hM ha2 hb2 ha1 hb1
  have hsecUpper0 :
      0 ≤ m * (m - 1) * M ^ (m - 2) *
        (|a1 - b1| + |a2 - b2|) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hm0 (by linarith))
        (Real.rpow_nonneg hM _))
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hid := paper5_four_profile_power_sub_identity m a2 b2 a1 b1
  have hquot :
      ((a2 ^ m - b2 ^ m) - (a1 ^ m - b1 ^ m)) / h =
        paper5MeanCoefficient m a2 a1 *
            (((a2 - b2) - (a1 - b1)) / h) +
          (paper5MeanCoefficient m a2 a1 -
              paper5MeanCoefficient m b2 b1) * ((b2 - b1) / h) := by
    rw [hid]
    ring
  rw [hquot]
  calc
    |paper5MeanCoefficient m a2 a1 *
          (((a2 - b2) - (a1 - b1)) / h) +
        (paper5MeanCoefficient m a2 a1 -
            paper5MeanCoefficient m b2 b1) * ((b2 - b1) / h)|
        ≤ |paper5MeanCoefficient m a2 a1| *
              |((a2 - b2) - (a1 - b1)) / h| +
            |paper5MeanCoefficient m a2 a1 -
                paper5MeanCoefficient m b2 b1| * |(b2 - b1) / h| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
    _ ≤ (m * M ^ (m - 1)) *
            |((a2 - b2) - (a1 - b1)) / h| +
          (m * (m - 1) * M ^ (m - 2) *
            (|a1 - b1| + |a2 - b2|)) * DU := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hA (abs_nonneg _))
          (mul_le_mul hsec hbase (abs_nonneg _)
            hsecUpper0)
    _ = m * M ^ (m - 1) *
            |((a2 - b2) - (a1 - b1)) / h| +
          (m * (m - 1) * M ^ (m - 2) * DU) *
            (|a1 - b1| + |a2 - b2|) := by ring

#print axioms paper5_four_profile_power_quotient_bound_of_two_le
/-- At `m = 1`, the matched power quotient is exactly the perturbation
difference quotient. -/
theorem paper5_four_profile_power_quotient_eq_of_m_eq_one
    {m h a2 b2 a1 b1 : ℝ} (hm : m = 1) :
    ((a2 ^ m - b2 ^ m) - (a1 ^ m - b1 ^ m)) / h =
      ((a2 - b2) - (a1 - b1)) / h := by
  subst m
  simp only [Real.rpow_one]

#print axioms paper5_four_profile_power_quotient_eq_of_m_eq_one

/-- Unified matched four-profile power quotient estimate for every `m ≥ 1`.
The subquadratic branch consumes the relative wave-increment estimate; the
superquadratic branch only consumes an absolute wave quotient bound. -/
theorem paper5_four_profile_power_quotient_bound_of_one_le
    {m M Brel DU h a2 b2 a1 b1 : ℝ}
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M)
    (hb2pos : 0 < b2) (hb1pos : 0 < b1)
    (hbase : |(b2 - b1) / h| ≤ DU)
    (hrelative : ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(b2 - b1) / h| ≤
        Brel * (tau * b2 + (1 - tau) * b1)) :
    |((a2 ^ m - b2 ^ m) - (a1 ^ m - b1 ^ m)) / h| ≤
      m * M ^ (m - 1) *
          |((a2 - b2) - (a1 - b1)) / h| +
        (if m < 2 then m * Brel * M ^ (m - 1)
          else m * (m - 1) * M ^ (m - 2) * DU) *
          (|a1 - b1| + |a2 - b2|) := by
  by_cases hmone : m = 1
  · have heq := paper5_four_profile_power_quotient_eq_of_m_eq_one
      (h := h) (a2 := a2) (b2 := b2) (a1 := a1) (b1 := b1) hmone
    subst m
    rw [heq]
    simp only [sub_self, Real.rpow_zero, one_mul, mul_one,
      if_pos (by norm_num : (1 : ℝ) < 2)]
    exact le_add_of_nonneg_right <|
      mul_nonneg hBrel (add_nonneg (abs_nonneg _) (abs_nonneg _))
  · have hm1 : 1 < m := lt_of_le_of_ne hm (Ne.symm hmone)
    by_cases hmlt : m < 2
    · rw [if_pos hmlt]
      exact paper5_four_profile_power_quotient_bound
        hm1 hmlt hM hBrel ha2 hb2 ha1 hb1 hb2pos hb1pos hrelative
    · have hm2 : 2 ≤ m := le_of_not_gt hmlt
      rw [if_neg hmlt]
      exact paper5_four_profile_power_quotient_bound_of_two_le
        hm2 hM hDU ha2 hb2 ha1 hb1 hbase

#print axioms paper5_four_profile_power_quotient_bound_of_one_le


theorem profile_shift_quotient_le_convex_of_logDerivative_bound
    {U : ℝ → ℝ} {B h x : ℝ}
    (hB : 0 ≤ B)
    (hUpos : ∀ y, 0 < U y)
    (hUdiff : Differentiable ℝ U)
    (hlog : ∀ y, |deriv U y / U y| ≤ B)
    (hh : h ≠ 0) :
    ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        (B * Real.exp (2 * B * |h|)) *
          (tau * U (x + h) + (1 - tau) * U x) := by
  intro tau htau
  let a : ℝ := B * |h|
  have ha : 0 ≤ a := mul_nonneg hB (abs_nonneg h)
  have hshift := profile_shift_sub_abs_le_mul_self_of_logDerivative_bound
    hB hUpos hUdiff hlog x h
  have hquot :
      |(U (x + h) - U x) / h| ≤ B * Real.exp a * U x := by
    rw [abs_div]
    have hhabs : 0 < |h| := abs_pos.mpr hh
    apply (div_le_iff₀ hhabs).2
    dsimp [a]
    calc
      |U (x + h) - U x| ≤
          B * Real.exp (B * |h|) * |h| * U x := hshift
      _ = (B * Real.exp (B * |h|) * U x) * |h| := by ring
  have hback :=
    profile_value_le_exp_mul_of_logDerivative_bound hUpos hUdiff hlog
      (x + h) x
  have habs : |x - (x + h)| = |h| := by
    rw [show x - (x + h) = -h by ring, abs_neg]
  rw [habs] at hback
  have hU2lower : Real.exp (-a) * U x ≤ U (x + h) := by
    calc
      Real.exp (-a) * U x ≤
          Real.exp (-a) * (Real.exp a * U (x + h)) :=
        mul_le_mul_of_nonneg_left hback (Real.exp_nonneg _)
      _ = U (x + h) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
        simp
  have hexp_le : Real.exp (-a) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hU1lower : Real.exp (-a) * U x ≤ U x := by
    simpa using mul_le_mul_of_nonneg_right hexp_le (hUpos x).le
  have hcombo :
      Real.exp (-a) * U x ≤
        tau * U (x + h) + (1 - tau) * U x := by
    calc
      Real.exp (-a) * U x =
          tau * (Real.exp (-a) * U x) +
            (1 - tau) * (Real.exp (-a) * U x) := by ring
      _ ≤ tau * U (x + h) + (1 - tau) * U x := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hU2lower htau.1)
          (mul_le_mul_of_nonneg_left hU1lower
            (sub_nonneg.mpr htau.2))
  calc
    |(U (x + h) - U x) / h| ≤ B * Real.exp a * U x := hquot
    _ = (B * Real.exp (2 * a)) * (Real.exp (-a) * U x) := by
      have he : Real.exp (2 * a) * Real.exp (-a) = Real.exp a := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show (B * Real.exp (2 * a)) * (Real.exp (-a) * U x) =
          B * (Real.exp (2 * a) * Real.exp (-a)) * U x by ring,
        he]
    _ ≤ (B * Real.exp (2 * a)) *
        (tau * U (x + h) + (1 - tau) * U x) := by
      exact mul_le_mul_of_nonneg_left hcombo
        (mul_nonneg hB (Real.exp_nonneg _))
    _ = (B * Real.exp (2 * B * |h|)) *
        (tau * U (x + h) + (1 - tau) * U x) := by
      dsimp [a]
      rw [show 2 * (B * |h|) = 2 * B * |h| by ring]

#print axioms profile_shift_quotient_le_convex_of_logDerivative_bound

end ShenWork.Paper1
