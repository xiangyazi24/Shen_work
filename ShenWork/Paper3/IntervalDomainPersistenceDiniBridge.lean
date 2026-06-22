import ShenWork.Paper3.IntervalDomainPersistenceActualLinearDini

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

private theorem add_right_nhdsGT (t : ℝ) :
    Tendsto (fun h : ℝ => t + h) (𝓝[>] (0 : ℝ)) (𝓝[>] t) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have ht : Tendsto (fun _ : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 t) :=
      tendsto_const_nhds
    have h0 : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ht.add h0
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh

/-- Convert a lower bound on the compact-minimum lower-right Dini derivative
into the right-neighbourhood slope form used by the scalar comparison API. -/
theorem rightLowerDiniGE_of_compactMinLowerRightDini
    {z f : ℝ → ℝ} {I : Set ℝ}
    (hD : ∀ t ∈ I, f (z t) ≤ compactMinLowerRightDini z t)
    (hbdd : ∀ t ∈ I,
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ => (z (t + h) - z t) / h)) :
    RightLowerDiniGE z f I := by
  intro t ht r hr
  have hlt : -r < compactMinLowerRightDini z t := by
    have : -r < f (z t) := by linarith
    exact lt_of_lt_of_le this (hD t ht)
  have hev :
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        -r < (z (t + h) - z t) / h :=
    eventually_lt_of_lt_liminf hlt (hbdd t ht)
  have hfreq :
      ∃ᶠ h in 𝓝[>] (0 : ℝ),
        (t + h - t)⁻¹ * (z t - z (t + h)) < r := by
    have hpos_ev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h :=
      self_mem_nhdsWithin
    exact (hev.and hpos_ev).frequently.mono (fun h hh => by
      have hpos : 0 < h := hh.2
      have hq : -((z (t + h) - z t) / h) < r := by linarith
      have hden : t + h - t = h := by ring
      rw [hden, inv_mul_eq_div]
      convert hq using 1
      · field_simp [ne_of_gt hpos]
        ring)
  exact (add_right_nhdsGT t).frequently hfreq

/-- The actual linear interval min-point Dini estimate in the slope-interface
form expected by the scalar logistic comparison layer. -/
theorem ActualLinearSpatialMinimumDini.to_RightLowerDiniGE
    {p : CM2Params} {u : ℝ → intervalDomain.Point → ℝ}
    (hD : ActualLinearSpatialMinimumDini p u)
    (hbdd : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h)) :
    RightLowerDiniGE (intervalDomainSpatialMin u)
      (actualLinearLogisticRhs p) (Set.Ioi (0 : ℝ)) :=
  rightLowerDiniGE_of_compactMinLowerRightDini hD hbdd

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.rightLowerDiniGE_of_compactMinLowerRightDini
#print axioms ShenWork.Paper3.ActualLinearSpatialMinimumDini.to_RightLowerDiniGE
