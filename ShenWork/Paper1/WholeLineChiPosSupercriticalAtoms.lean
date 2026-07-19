import ShenWork.Paper1.WholeLineCauchyChiPosLongTimeBound

/-!
# Scalar atoms for the supercritical positive-sensitivity ceiling

In the supercritical branch `q := m + γ - 1 < α` the relaxing ceiling is based
at the explicit parameter threshold `wholeLineCauchyParameterCeiling p` rather
than at `MChi p`, and the Bernoulli step of the critical branch is replaced by
a normalized gap inequality at exponent `d := α - q > 0`.

Since `d + 1` may lie strictly between `1` and `2`, the committed
`rpow_bernoulli` (stated for `2 ≤ n`) does not apply.  Its proof, however, only
uses convexity of `x ↦ x ^ n` on `[0, ∞)`, which holds for every `1 ≤ n`; the
first theorem below is that sharpening.

The scalar chain proved here is
`d * (r - 1) ≤ r ^ (q + 1) * (r ^ d - 1)` for `1 ≤ r`, and its scaled form,
which is what the supercritical supersolution consumes.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Tangent-line inequality for real powers at `1`, valid for every exponent
`1 ≤ n`.  Sharpening of `rpow_bernoulli`, whose `2 ≤ n` hypothesis is not
needed by its own proof. -/
theorem rpow_tangent_at_one_of_one_le {r n : ℝ} (hr : 1 ≤ r) (hn : 1 ≤ n) :
    n * r - (n - 1) ≤ r ^ n := by
  by_cases hrr : r = 1
  · subst hrr; simp [Real.one_rpow]
  have hr1 : 1 < r := lt_of_le_of_ne hr (Ne.symm hrr)
  have hconv := convexOn_rpow hn
  have h1mem : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr zero_le_one
  have hrmem : r ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (zero_le_one.trans hr)
  have hderiv : HasDerivAt (fun x : ℝ => x ^ n) (n * 1 ^ (n - 1)) 1 :=
    hasDerivAt_rpow_const (Or.inl one_ne_zero)
  rw [Real.one_rpow, mul_one] at hderiv
  have hslope := hconv.le_slope_of_hasDerivAt h1mem hrmem hr1 hderiv
  simp only [Real.one_rpow, slope_def_field] at hslope
  have hr_pos : 0 < r - 1 := sub_pos.mpr hr1
  rw [le_div_iff₀ hr_pos] at hslope
  linarith

/-- Normalized supercritical gap: the multiplicative increment of `r ^ d`,
weighted by `r ^ (q+1)`, dominates the linear increment scaled by `d`. -/
theorem rpow_supercritical_gap {r q d : ℝ}
    (hr : 1 ≤ r) (hq : 0 ≤ q) (hd : 0 < d) :
    d * (r - 1) ≤ r ^ (q + 1) * (r ^ d - 1) := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr
  have htangent : (d + 1) * r - d ≤ r ^ (d + 1) := by
    have h0 := rpow_tangent_at_one_of_one_le (r := r) (n := d + 1) hr
      (by linarith)
    have hsub : d + 1 - 1 = d := by ring
    rwa [hsub] at h0
  have hsplit : r ^ (d + 1) = r ^ d * r := by
    rw [Real.rpow_add hr0, Real.rpow_one]
  -- base form: `r * (r ^ d - 1) ≥ d * (r - 1)`
  have hbase : d * (r - 1) ≤ r * (r ^ d - 1) := by
    rw [hsplit] at htangent
    have hring : r * (r ^ d - 1) = r ^ d * r - r := by ring
    rw [hring]
    linarith
  have hq1 : (1 : ℝ) ≤ r ^ q := Real.one_le_rpow hr hq
  have hgap : 0 ≤ r ^ d - 1 := by
    have : (1 : ℝ) ≤ r ^ d := Real.one_le_rpow hr hd.le
    linarith
  have hsplitq : r ^ (q + 1) = r ^ q * r := by
    rw [Real.rpow_add hr0, Real.rpow_one]
  calc
    d * (r - 1) ≤ r * (r ^ d - 1) := hbase
    _ ≤ (r ^ q * r) * (r ^ d - 1) := by
          have hrgap : 0 ≤ r * (r ^ d - 1) :=
            mul_nonneg hr0.le hgap
          nlinarith [hq1, hrgap, hgap, hr0.le]
    _ = r ^ (q + 1) * (r ^ d - 1) := by rw [hsplitq]

/-- Scaled supercritical gap, the form consumed by the ceiling supersolution:
for `0 < M ≤ B`, the `d`-power gap weighted by `B ^ (q+1)` dominates the linear
increment scaled by `d * M ^ (q+d)`. -/
theorem rpow_supercritical_scaled_gap {M B q d : ℝ}
    (hM : 0 < M) (hMB : M ≤ B) (hq : 0 ≤ q) (hd : 0 < d) :
    d * M ^ (q + d) * (B - M) ≤ B ^ (q + 1) * (B ^ d - M ^ d) := by
  have hB : 0 < B := hM.trans_le hMB
  have hMd : (0 : ℝ) < M ^ d := Real.rpow_pos_of_pos hM d
  have hMd1 : (0 : ℝ) < M ^ (d + 1) := Real.rpow_pos_of_pos hM (d + 1)
  -- (A) homogeneous tangent inequality at the base point `M`
  have htan : (d + 1) * (B / M) - d ≤ (B / M) ^ (d + 1) := by
    have h0 := rpow_tangent_at_one_of_one_le (r := B / M) (n := d + 1)
      ((one_le_div hM).mpr hMB) (by linarith)
    have hsub : d + 1 - 1 = d := by ring
    rwa [hsub] at h0
  rw [Real.div_rpow hB.le hM.le] at htan
  have hsplitM : M ^ (d + 1) = M ^ d * M := by
    rw [Real.rpow_add hM, Real.rpow_one]
  have hA : (d + 1) * B * M ^ d - d * M ^ (d + 1) ≤ B ^ (d + 1) := by
    have hmul := mul_le_mul_of_nonneg_right htan hMd1.le
    rw [div_mul_cancel₀ _ hMd1.ne'] at hmul
    calc
      (d + 1) * B * M ^ d - d * M ^ (d + 1)
          = ((d + 1) * (B / M) - d) * M ^ (d + 1) := by
            rw [hsplitM]; field_simp
      _ ≤ B ^ (d + 1) := hmul
  -- (B) one-step gap at exponent `d`
  have hsplitB : B ^ (d + 1) = B ^ d * B := by
    rw [Real.rpow_add hB, Real.rpow_one]
  have hBd : d * M ^ d * (B - M) ≤ B * (B ^ d - M ^ d) := by
    rw [hsplitB] at hA
    rw [hsplitM] at hA
    nlinarith [hA]
  -- weight by `B ^ q ≥ M ^ q` and reassemble
  have hMq : (0 : ℝ) < M ^ q := Real.rpow_pos_of_pos hM q
  have hBq : M ^ q ≤ B ^ q := Real.rpow_le_rpow hM.le hMB hq
  have hnonneg : 0 ≤ d * M ^ d * (B - M) :=
    mul_nonneg (mul_nonneg hd.le hMd.le) (by linarith)
  have hsplitBq : B ^ (q + 1) = B ^ q * B := by
    rw [Real.rpow_add hB, Real.rpow_one]
  have hsplitMq : M ^ (q + d) = M ^ q * M ^ d := by
    rw [← Real.rpow_add hM]
  calc
    d * M ^ (q + d) * (B - M)
        = M ^ q * (d * M ^ d * (B - M)) := by rw [hsplitMq]; ring
    _ ≤ B ^ q * (d * M ^ d * (B - M)) := by
          exact mul_le_mul_of_nonneg_right hBq hnonneg
    _ ≤ B ^ q * (B * (B ^ d - M ^ d)) := by
          exact mul_le_mul_of_nonneg_left hBd
            (Real.rpow_nonneg hB.le q)
    _ = B ^ (q + 1) * (B ^ d - M ^ d) := by rw [hsplitBq]; ring

section AxiomAudit

#print axioms rpow_tangent_at_one_of_one_le
#print axioms rpow_supercritical_gap
#print axioms rpow_supercritical_scaled_gap

end AxiomAudit

end ShenWork.Paper1
