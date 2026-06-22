import ShenWork.Paper3.IntervalDomainPersistenceLogistic
import ShenWork.Paper2.IntervalDomainChemDivCritical

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

/-!
This file records the formal blockers found while trying to close the three
`IntervalDomainLogisticPersistenceInputs` u-lower fields from
`P3_PERSISTENCE_FINDINGS`.

The current concrete interval chemotaxis operator is

`deriv (fun y => lift u y * deriv (lift v) y / (1 + lift v y) ^ beta)`.

It is independent of `p.m`.  Thus unfolding the committed PDE cannot produce
the requested spatial-minimum loss term `Cchi * z ^ p.m`; it produces a linear
loss in the value of `u` at a critical point.  The file also records that a
limit statement at a proposed threshold is not enough to prove the exact
eventual lower bound used by the current `part2ULower` and `part3ULower`
interfaces.
-/

theorem intervalDomainChemotaxisDiv_eq_of_beta_eq
    {p q : CM2Params} (hbeta : p.β = q.β)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalDomainChemotaxisDiv p u v x =
      intervalDomainChemotaxisDiv q u v x := by
  unfold intervalDomainChemotaxisDiv
  rw [hbeta]

theorem intervalDomainChemotaxisDiv_eq_with_replaced_m
    (p : CM2Params) {m' : ℝ} (hm' : 0 < m')
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalDomainChemotaxisDiv { p with m := m', hm := hm' } u v x =
      intervalDomainChemotaxisDiv p u v x := by
  exact (intervalDomainChemotaxisDiv_eq_of_beta_eq (p := { p with m := m', hm := hm' })
    (q := p) rfl u v x)

theorem intervalDomainChemotaxisDiv_critical_linear_in_u
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    {vx vxx : ℝ}
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y) :
    intervalDomainChemotaxisDiv p u v x =
      intervalDomainLift u x.1 *
        (-p.β * (1 + intervalDomainLift v x.1) ^ (-p.β - 1) * vx ^ 2
          + (1 + intervalDomainLift v x.1) ^ (-p.β) * vxx) := by
  exact chemDiv_at_critical hux hv hvxx hvnn

theorem tendsto_zero_not_eventually_nonneg :
    Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (𝓝 0) ∧
      ¬ (∀ᶠ t in atTop, 0 ≤ -Real.exp (-t)) := by
  constructor
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  · intro h
    rcases eventually_atTop.1 h with ⟨T, hT⟩
    have hbad : 0 ≤ -Real.exp (-T) := hT T le_rfl
    linarith [Real.exp_pos (-T)]

end

end ShenWork.Paper3
