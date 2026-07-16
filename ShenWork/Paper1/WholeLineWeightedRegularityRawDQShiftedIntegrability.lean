import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Shifted scalar integrability for the raw-DQ Henry profile

These two small lemmas provide the time-integrability facts needed after a
positive-time restart.  The first transports the norm of a Bochner profile
from an absolute time interval to restart coordinates.  The second records
that multiplication by the locally integrable heat-gradient kernel preserves
integrability when the scalar profile is uniformly bounded.
-/

/-- The norm of an `L²` profile remains interval-integrable after translating
the absolute interval `[a, a + q]` to restart coordinates `[0, q]`. -/
theorem wholeLineRealL2_norm_restart_intervalIntegrable
    {P : ℝ → WholeLineRealL2} {a q : ℝ}
    (hP : IntervalIntegrable P volume a (a + q)) :
    IntervalIntegrable (fun τ : ℝ ↦ ‖P (a + τ)‖) volume 0 q := by
  have hshift := hP.norm.comp_add_right a
  simpa [add_comm] using hshift

/-- A bounded interval-integrable scalar profile can be multiplied by the
inverse-square-root heat-gradient kernel without losing interval
integrability. -/
theorem intervalIntegrable_invSqrt_sub_mul_of_abs_le
    {x : ℝ → ℝ} {r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hx : IntervalIntegrable x volume 0 r)
    (hbound : ∀ s ∈ Icc (0 : ℝ) r, |x s| ≤ K) :
    IntervalIntegrable
      (fun s : ℝ ↦ (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r := by
  have hdom : IntervalIntegrable
      (fun s : ℝ ↦ K * (r - s) ^ (-(1 / 2 : ℝ))) volume 0 r :=
    intervalIntegrable_invSqrt_sub.const_mul K
  refine IntervalIntegrable.mono_fun' hdom
    (intervalIntegrable_invSqrt_sub.aestronglyMeasurable_restrict_uIoc.mul
      hx.aestronglyMeasurable_restrict_uIoc) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hr.le] at hs
  have hsIcc : s ∈ Icc (0 : ℝ) r := ⟨hs.1.le, hs.2⟩
  have hbase : 0 ≤ r - s := sub_nonneg.mpr hs.2
  have hkernel : 0 ≤ (r - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hbase _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel]
  simpa [mul_comm] using
    mul_le_mul (hbound s hsIcc) le_rfl hkernel hK

end ShenWork.Paper1

#print axioms ShenWork.Paper1.wholeLineRealL2_norm_restart_intervalIntegrable
#print axioms ShenWork.Paper1.intervalIntegrable_invSqrt_sub_mul_of_abs_le
