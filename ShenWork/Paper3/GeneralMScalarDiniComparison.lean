import ShenWork.Paper3.IntervalDomainPersistenceGeneralMDini
import ShenWork.Paper3.ScalarLogisticDiniLiminf

open Filter Topology
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-!
# Local scalar comparison below the unit level

The faithful general-`m` reaction dominates a single logistic power only on
`0 < y ≤ 1`.  The comparison orbit is therefore required to stay below one;
this avoids the unsound global replacement of the two nonlinear losses.
-/

theorem strict_logistic_subsolution_le_of_local_RightLowerDiniGE
    {q qη : CM2Params} {z F : ℝ → ℝ} {η y0 T0 T : ℝ}
    (hqηa : 0 < qη.a) (hqηb : 0 < qη.b)
    (hη : 0 < η) (hqηa_eq : qη.a = q.a - η)
    (hqηb_eq : qη.b = q.b) (hqηα_eq : qη.α = q.α)
    (hcarry_le_one : (qη.a / qη.b) ^ (1 / qη.α) ≤ 1)
    (hy0 : 0 < y0)
    (hy0_le_carry : y0 ≤ (qη.a / qη.b) ^ (1 / qη.α))
    (hlocal : ∀ y, 0 < y → y ≤ 1 →
      q.a * y - q.b * y ^ (1 + q.α) ≤ F y)
    (hcont : ContinuousOn z (Set.Icc T0 T))
    (hD : RightLowerDiniGE z F (Set.Ioi 0))
    (hT0 : 0 < T0) (hinit : y0 ≤ z T0) :
    ∀ t ∈ Set.Icc T0 T,
      bernoulliLogisticSolution qη y0 (t - T0) ≤ z t := by
  let Y : ℝ → ℝ := fun t =>
    bernoulliLogisticSolution qη y0 (t - T0)
  have hYpos : ∀ t, 0 < Y t := by
    intro t
    exact bernoulliLogisticSolution_pos qη hqηa hqηb hy0
  have hYle_one : ∀ t, T0 ≤ t → Y t ≤ 1 := by
    intro t ht
    have hle := bernoulliLogisticSolution_le_max_of_nonneg_time
      qη hqηa hqηb hy0 (sub_nonneg.mpr ht)
    have hmax : max y0 ((qη.a / qη.b) ^ (1 / qη.α)) =
        (qη.a / qη.b) ^ (1 / qη.α) :=
      max_eq_right hy0_le_carry
    rw [hmax] at hle
    exact hle.trans hcarry_le_one
  have hYderiv : ∀ x,
      HasDerivAt (fun t => -Y t)
        (-(bernoulliLogisticSolutionDerivative qη y0 (x - T0))) x := by
    intro x
    have hbase := bernoulliLogisticSolution_hasDerivAt
      qη hqηa hqηb hy0 (t := x - T0)
    have hshift : HasDerivAt (fun t : ℝ => t - T0) 1 x :=
      (hasDerivAt_id x).sub_const T0
    simpa [Y] using (hbase.comp x hshift).neg
  have hfa : -z T0 ≤ -Y T0 := by
    have hY0 : Y T0 = y0 := by
      have hzero : T0 - T0 = 0 := by ring
      change bernoulliLogisticSolution qη y0 (T0 - T0) = y0
      rw [hzero, bernoulliLogisticSolution_of_nonneg qη y0 0 le_rfl]
      exact bernoulliLogisticForward_zero qη hy0
    linarith
  have hf' : ∀ x ∈ Set.Ico T0 T, ∀ r, -F (z x) < r →
      ∃ᶠ s in 𝓝[>] x, slope (fun t => -z t) x s < r := by
    intro x hx r hr
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le hT0 hx.1
    have hd := hD x hxpos r hr
    exact hd.mono (fun s hs => by
      simpa [slope_def_field, div_eq_inv_mul, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, mul_comm] using hs)
  have hbound : ∀ x ∈ Set.Ico T0 T, (fun t => -z t) x = -Y x →
      -F (z x) <
        -(bernoulliLogisticSolutionDerivative qη y0 (x - T0)) := by
    intro x hx heq
    have hxnonneg : 0 ≤ x - T0 := by linarith [hx.1]
    have hderiv_eq :
        bernoulliLogisticSolutionDerivative qη y0 (x - T0) =
          Y x * (qη.a - qη.b * (Y x) ^ qη.α) := by
      simp [Y, bernoulliLogisticSolutionDerivative, hxnonneg,
        bernoulliLogisticSolution_of_nonneg]
    have hzy : z x = Y x := by linarith
    have hYone : Y x ≤ 1 := hYle_one x hx.1
    have hdom := hlocal (Y x) (hYpos x) hYone
    have hpow : Y x * (q.b * (Y x) ^ q.α) =
        q.b * (Y x) ^ (1 + q.α) := by
      rw [Real.rpow_add (hYpos x) 1 q.α, Real.rpow_one]
      ring
    have hstrict : 0 < η * Y x := mul_pos hη (hYpos x)
    rw [hzy, hderiv_eq, hqηa_eq, hqηb_eq, hqηα_eq]
    rw [← hpow] at hdom
    nlinarith
  have hcmp := image_le_of_liminf_slope_right_lt_deriv_boundary
    (f := fun t => -z t) (f' := fun t => -F (z t))
    (a := T0) (b := T) hcont.neg hf' hfa hYderiv hbound
  intro t ht
  have := hcmp ht
  linarith

theorem local_logistic_liminf_ge_of_RightLowerDiniGE
    {q qη : CM2Params} {z F : ℝ → ℝ} {η y0 T0 : ℝ}
    (hqηa : 0 < qη.a) (hqηb : 0 < qη.b)
    (hη : 0 < η) (hqηa_eq : qη.a = q.a - η)
    (hqηb_eq : qη.b = q.b) (hqηα_eq : qη.α = q.α)
    (hcarry_le_one : (qη.a / qη.b) ^ (1 / qη.α) ≤ 1)
    (hy0 : 0 < y0)
    (hy0_le_carry : y0 ≤ (qη.a / qη.b) ^ (1 / qη.α))
    (hlocal : ∀ y, 0 < y → y ≤ 1 →
      q.a * y - q.b * y ^ (1 + q.α) ≤ F y)
    (hcont : ∀ T, T0 ≤ T → ContinuousOn z (Set.Icc T0 T))
    (hD : RightLowerDiniGE z F (Set.Ioi 0))
    (hT0 : 0 < T0) (hinit : y0 ≤ z T0)
    (hcobdd : IsCoboundedUnder GE.ge atTop z) :
    (qη.a / qη.b) ^ (1 / qη.α) ≤ Filter.liminf z atTop := by
  let Y : ℝ → ℝ := fun t =>
    bernoulliLogisticSolution qη y0 (t - T0)
  have hle : ∀ᶠ t in atTop, Y t ≤ z t := by
    filter_upwards [eventually_ge_atTop T0] with t ht
    exact strict_logistic_subsolution_le_of_local_RightLowerDiniGE
      hqηa hqηb hη hqηa_eq hqηb_eq hqηα_eq hcarry_le_one
      hy0 hy0_le_carry hlocal (hcont t ht) hD hT0 hinit t
      (Set.right_mem_Icc.mpr ht)
  have hshift : Tendsto (fun t : ℝ => t - T0) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-T0) tendsto_id
  have hY : Tendsto Y atTop
      (𝓝 ((qη.a / qη.b) ^ (1 / qη.α))) :=
    (bernoulliLogisticSolution_tendsto_atTop qη hqηa hqηb hy0).comp
      hshift
  exact le_liminf_of_eventually_tendsto_lower hY hle hcobdd

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.strict_logistic_subsolution_le_of_local_RightLowerDiniGE
#print axioms ShenWork.Paper3.local_logistic_liminf_ge_of_RightLowerDiniGE
