import ShenWork.Paper3.IntervalDomainPersistenceDiniBridge
import ShenWork.PDE.UnitPointLogisticODE

open Filter Topology
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Strict logistic subsolutions stay below a scalar trajectory whose right
lower Dini derivative dominates the larger logistic vector field. -/
theorem strict_logistic_subsolution_le_of_RightLowerDiniGE
    {q qη : CM2Params} {z : ℝ → ℝ} {η y0 T0 T : ℝ}
    (hqηa : 0 < qη.a) (hqηb : 0 < qη.b)
    (hη : 0 < η) (hqηa_eq : qη.a = q.a - η)
    (hqηb_eq : qη.b = q.b) (hqηα_eq : qη.α = q.α)
    (hcont : ContinuousOn z (Set.Icc T0 T))
    (hD : RightLowerDiniGE z
      (fun y => q.a * y - q.b * y ^ (1 + q.α)) (Set.Ioi 0))
    (hT0 : 0 < T0) (hy0 : 0 < y0) (hinit : y0 ≤ z T0) :
    ∀ t ∈ Set.Icc T0 T,
      bernoulliLogisticSolution qη y0 (t - T0) ≤ z t := by
  let Y : ℝ → ℝ := fun t =>
    bernoulliLogisticSolution qη y0 (t - T0)
  let F : ℝ → ℝ := fun y => q.a * y - q.b * y ^ (1 + q.α)
  have hYpos : ∀ t, 0 < Y t := by
    intro t
    exact bernoulliLogisticSolution_pos qη hqηa hqηb hy0
  have hYderiv : ∀ x,
      HasDerivAt (fun t => -Y t)
        (-(bernoulliLogisticSolutionDerivative qη y0 (x - T0))) x := by
    intro x
    have hbase :=
      bernoulliLogisticSolution_hasDerivAt qη hqηa hqηb hy0
        (t := x - T0)
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
  have hf' :
      ∀ x ∈ Set.Ico T0 T, ∀ r, -F (z x) < r →
        ∃ᶠ s in 𝓝[>] x, slope (fun t => -z t) x s < r := by
    intro x hx r hr
    have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
      lt_of_lt_of_le hT0 hx.1
    have hd := hD x hxpos r (by simpa [F] using hr)
    exact hd.mono (fun s hs => by
      simpa [slope_def_field, div_eq_inv_mul, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, mul_comm] using hs)
  have hbound :
      ∀ x ∈ Set.Ico T0 T, (fun t => -z t) x = -Y x →
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
    have hpow : Y x * (q.b * (Y x) ^ q.α) =
        q.b * (Y x) ^ (1 + q.α) := by
      rw [Real.rpow_add (hYpos x) 1 q.α, Real.rpow_one]
      ring
    simp only [F]
    rw [hzy, hderiv_eq, hqηa_eq, hqηb_eq, hqηα_eq, ← hpow]
    have hstrict : 0 < η * Y x := mul_pos hη (hYpos x)
    nlinarith
  have hcmp := image_le_of_liminf_slope_right_lt_deriv_boundary
    (f := fun t => -z t) (f' := fun t => -F (z t))
    (a := T0) (b := T) hcont.neg hf' hfa hYderiv hbound
  intro t ht
  have := hcmp ht
  linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.strict_logistic_subsolution_le_of_RightLowerDiniGE
