import Mathlib.Data.Real.Sqrt

noncomputable section

def waveExponent (c : ℝ) : ℝ := (c - Real.sqrt (c ^ 2 - 4)) / 2

private lemma waveDisc_nonneg {c : ℝ} (hc : 2 ≤ c) : 0 ≤ c ^ 2 - 4 := by
  have hmul : 0 ≤ (c - 2) * (c + 2) := by
    exact mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem waveExponent_quadratic {c : ℝ} (hc : 2 ≤ c) :
    waveExponent c ^ 2 - c * waveExponent c + 1 = 0 := by
  unfold waveExponent
  have hs : Real.sqrt (c ^ 2 - 4) ^ 2 = c ^ 2 - 4 :=
    Real.sq_sqrt (waveDisc_nonneg hc)
  rw [div_pow]
  field_simp
  nlinarith [hs]

theorem waveExponent_pos {c : ℝ} (hc : 2 ≤ c) : 0 < waveExponent c := by
  unfold waveExponent
  have hslt : Real.sqrt (c ^ 2 - 4) < c := by
    have hlt : c ^ 2 - 4 < c ^ 2 := by nlinarith
    have hsqrt := Real.sqrt_lt_sqrt (waveDisc_nonneg hc) hlt
    have hc0 : 0 ≤ c := by linarith
    rwa [Real.sqrt_sq hc0] at hsqrt
  linarith

theorem waveExponent_lt_one {c : ℝ} (hc : 2 < c) : waveExponent c < 1 := by
  unfold waveExponent
  have hcsqrt : c - 2 < Real.sqrt (c ^ 2 - 4) := by
    have hx : 0 ≤ c - 2 := by linarith
    rw [Real.lt_sqrt hx]
    nlinarith
  linarith

theorem waveExponent_eq_one_of_two : waveExponent 2 = 1 := by
  unfold waveExponent
  norm_num [Real.sqrt_zero]

theorem waveSpeed_eq {c : ℝ} (hc : 2 ≤ c) :
    c = waveExponent c + (waveExponent c)⁻¹ := by
  let k := waveExponent c
  have hkpos : 0 < k := by simpa [k] using waveExponent_pos hc
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hq : k ^ 2 - c * k + 1 = 0 := by
    simpa [k] using waveExponent_quadratic hc
  have hmul : c * k = k ^ 2 + 1 := by nlinarith
  calc
    c = (k ^ 2 + 1) / k := by
      field_simp [hk0]
      nlinarith
    _ = k + k⁻¹ := by
      field_simp [hk0]

theorem admissible_interval_nonempty {c α m : ℝ} (hc : 2 < c)
    (hα : 0 < α) (hm : 1 ≤ m) :
    ∃ k1 k2 : ℝ,
      waveExponent c < k1 ∧ k1 < k2 ∧
        k2 ≤ min ((1 + α) * waveExponent c) (min (m * waveExponent c + 1 / 2) 1) := by
  let k := waveExponent c
  have hkpos : 0 < k := by simpa [k] using waveExponent_pos (le_of_lt hc)
  have hklt1 : k < 1 := by simpa [k] using waveExponent_lt_one hc
  have hleft : k < (1 + α) * k := by
    have : 0 < α * k := mul_pos hα hkpos
    nlinarith
  have hmid : k < m * k + 1 / 2 := by
    have hmk : k ≤ m * k := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hm hkpos.le
    linarith
  have hupper : k < min ((1 + α) * k) (min (m * k + 1 / 2) 1) := by
    exact lt_min hleft (lt_min hmid hklt1)
  obtain ⟨k1, hkk1, hk1upper⟩ := exists_between hupper
  obtain ⟨k2, hk1k2, hk2upper⟩ := exists_between hk1upper
  refine ⟨k1, k2, ?_, ?_, ?_⟩
  · simpa [k] using hkk1
  · exact hk1k2
  · simpa [k] using hk2upper.le
