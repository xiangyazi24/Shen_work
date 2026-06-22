import Mathlib.Topology.Order.LiminfLimsup
import ShenWork.Paper3.IntervalDomainPersistenceDiniFrontier

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- The committed interval-domain chemotaxis flux uses the first power of `u`.
The parameter `p.m` is not present in this definition. -/
theorem intervalDomainChemotaxisDiv_actual_flux_u_power_one
    (p : CM2Params) (u v : intervalDomain.Point → ℝ)
    (x : intervalDomain.Point) :
    intervalDomainChemotaxisDiv p u v x =
      deriv
        (fun y : ℝ =>
          (intervalDomainLift u y) ^ (1 : ℕ) *
              deriv (intervalDomainLift v) y /
            (1 + intervalDomainLift v y) ^ p.β)
        x.1 := by
  simp [intervalDomainChemotaxisDiv]

/-- Replacing only `p.m` leaves the committed interval chemotaxis divergence
unchanged.  Thus the actual interval model cannot expose a superlinear
`u ^ p.m` flux loss by unfolding this operator. -/
theorem intervalDomainChemotaxisDiv_actual_independent_of_m
    (p : CM2Params) {m' : ℝ} (hm' : 0 < m')
    (u v : intervalDomain.Point → ℝ) (x : intervalDomain.Point) :
    intervalDomainChemotaxisDiv { p with m := m', hm := hm' } u v x =
      intervalDomainChemotaxisDiv p u v x := by
  simp [intervalDomainChemotaxisDiv]

/-- Non-strict liminf control of the spatial minimum gives only an
epsilon-below eventual pointwise lower bound. -/
theorem eventually_pointwise_lower_eps_of_liminf_spatialMin_ge
    {u : ℝ → intervalDomain.Point → ℝ} {θ ε : ℝ}
    (hmin_bdd :
      IsBoundedUnder GE.ge atTop (intervalDomainSpatialMin u))
    (hrange_bdd : ∀ᶠ t in atTop, BddBelow (Set.range (u t)))
    (hlim : θ ≤ Filter.liminf (intervalDomainSpatialMin u) atTop)
    (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, θ - ε ≤ u t x := by
  have hneg : -ε < 0 := by linarith
  have hnear :
      ∀ᶠ t in atTop, θ - ε < intervalDomainSpatialMin u t := by
    simpa [sub_eq_add_neg] using
      (eventually_add_neg_lt_of_le_liminf
        (u := intervalDomainSpatialMin u) hmin_bdd hlim hneg)
  filter_upwards [hnear, hrange_bdd] with t ht hbdd x
  have hInf_le : intervalDomainSpatialMin u t ≤ u t x := by
    unfold intervalDomainSpatialMin
    exact csInf_le hbdd ⟨x, rfl⟩
  exact le_trans (le_of_lt ht) hInf_le

/-- To recover an exact displayed threshold from the liminf interface, the
liminf statement must be strict above that threshold. -/
theorem eventually_pointwise_lower_of_liminf_spatialMin_gt
    {u : ℝ → intervalDomain.Point → ℝ} {θ : ℝ}
    (hmin_bdd :
      IsBoundedUnder GE.ge atTop (intervalDomainSpatialMin u))
    (hrange_bdd : ∀ᶠ t in atTop, BddBelow (Set.range (u t)))
    (hlim : θ < Filter.liminf (intervalDomainSpatialMin u) atTop) :
    ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, θ ≤ u t x := by
  have hnear :
      ∀ᶠ t in atTop, θ < intervalDomainSpatialMin u t :=
    eventually_lt_of_lt_liminf hlim hmin_bdd
  filter_upwards [hnear, hrange_bdd] with t ht hbdd x
  have hInf_le : intervalDomainSpatialMin u t ≤ u t x := by
    unfold intervalDomainSpatialMin
    exact csInf_le hbdd ⟨x, rfl⟩
  exact le_trans (le_of_lt ht) hInf_le

/-- A scalar counterexample to the exact-threshold interface: this trajectory
has liminf equal to `θ`, but it is never eventually above `θ`. -/
theorem liminf_threshold_not_eventually_exact (θ : ℝ) :
    Filter.liminf (fun t : ℝ => θ - Real.exp (-t)) atTop = θ ∧
      ¬ (∀ᶠ t in atTop, θ ≤ θ - Real.exp (-t)) := by
  constructor
  · have hzero : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using (tendsto_const_nhds.sub hzero).liminf_eq
  · intro h
    rcases eventually_atTop.1 h with ⟨T, hT⟩
    linarith [hT T le_rfl, Real.exp_pos (-T)]

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainChemotaxisDiv_actual_flux_u_power_one
#print axioms ShenWork.Paper3.intervalDomainChemotaxisDiv_actual_independent_of_m
#print axioms ShenWork.Paper3.eventually_pointwise_lower_eps_of_liminf_spatialMin_ge
#print axioms ShenWork.Paper3.eventually_pointwise_lower_of_liminf_spatialMin_gt
#print axioms ShenWork.Paper3.liminf_threshold_not_eventually_exact
