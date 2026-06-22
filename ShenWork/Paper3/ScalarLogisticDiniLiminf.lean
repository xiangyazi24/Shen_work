import ShenWork.Paper3.ScalarLogisticDiniComparison

open Filter Topology
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- If an eventually lower comparison function tends to `L`, then `liminf z`
is at least `L`, provided `z` is frequently upper-bounded. -/
theorem le_liminf_of_eventually_tendsto_lower
    {Y z : ℝ → ℝ} {L : ℝ}
    (hY : Tendsto Y atTop (𝓝 L))
    (hle : ∀ᶠ t in atTop, Y t ≤ z t)
    (hcobdd : IsCoboundedUnder GE.ge atTop z) :
    L ≤ Filter.liminf z atTop := by
  have hlow_ev : ∀ᶠ t in atTop, L - 1 ≤ z t := by
    have hYlow : ∀ᶠ t in atTop, L - 1 < Y t :=
      hY (Ioi_mem_nhds (by linarith : L - 1 < L))
    filter_upwards [hYlow, hle] with t hyt htz
    exact le_trans (le_of_lt hyt) htz
  have hbdd : IsBoundedUnder GE.ge atTop z :=
    isBoundedUnder_of_eventually_ge hlow_ev
  rw [Filter.le_liminf_iff' hcobdd hbdd]
  intro y hy
  have hYgt : ∀ᶠ t in atTop, y < Y t :=
    hY (Ioi_mem_nhds hy)
  filter_upwards [hYgt, hle] with t hyt htz
  exact le_trans (le_of_lt hyt) htz

/-- Liminf lower bound at the strict logistic threshold `qη.a/qη.b`. -/
theorem strict_logistic_liminf_ge_of_RightLowerDiniGE
    {q qη : CM2Params} {z : ℝ → ℝ} {η T0 : ℝ}
    (hqηa : 0 < qη.a) (hqηb : 0 < qη.b)
    (hη : 0 < η) (hqηa_eq : qη.a = q.a - η)
    (hqηb_eq : qη.b = q.b) (hqηα_eq : qη.α = q.α)
    (hcont : ∀ T, T0 ≤ T → ContinuousOn z (Set.Icc T0 T))
    (hD : RightLowerDiniGE z
      (fun y => q.a * y - q.b * y ^ (1 + q.α)) (Set.Ioi 0))
    (hT0 : 0 < T0) (hz0 : 0 < z T0)
    (hcobdd : IsCoboundedUnder GE.ge atTop z) :
    (qη.a / qη.b) ^ (1 / qη.α) ≤ Filter.liminf z atTop := by
  let Y : ℝ → ℝ := fun t =>
    bernoulliLogisticSolution qη (z T0) (t - T0)
  have hle : ∀ᶠ t in atTop, Y t ≤ z t := by
    filter_upwards [eventually_ge_atTop T0] with t ht
    exact strict_logistic_subsolution_le_of_RightLowerDiniGE
      hqηa hqηb hη hqηa_eq hqηb_eq hqηα_eq
      (hcont t ht) hD hT0 hz0 (le_refl _) t
      (Set.right_mem_Icc.mpr ht)
  have hshift : Tendsto (fun t : ℝ => t - T0) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-T0) tendsto_id
  have hY :
      Tendsto Y atTop (𝓝 ((qη.a / qη.b) ^ (1 / qη.α))) :=
    (bernoulliLogisticSolution_tendsto_atTop qη hqηa hqηb hz0).comp
      hshift
  exact le_liminf_of_eventually_tendsto_lower hY hle hcobdd

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.le_liminf_of_eventually_tendsto_lower
#print axioms ShenWork.Paper3.strict_logistic_liminf_ge_of_RightLowerDiniGE
