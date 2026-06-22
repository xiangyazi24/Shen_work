import ShenWork.Paper3.IntervalDomainPersistenceActualMInterface
import ShenWork.Paper3.IntervalDomainPersistenceFieldShapeReport

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Having eventual lower bounds for every strict subthreshold `η < θ` still
does not give the exact eventual lower bound at `θ`.  This is the scalar shape
returned by the ε-strict Dini comparison in `P3_DINI_FINDINGS.txt`. -/
theorem strict_subthreshold_eventual_lower_bounds_not_exact
    (θ : ℝ) :
    (∀ η : ℝ, η < θ →
      ∀ᶠ t in atTop, η ≤ θ - Real.exp (-t)) ∧
      ¬ (∀ᶠ t in atTop, θ ≤ θ - Real.exp (-t)) := by
  constructor
  · intro η hη
    have hδ : 0 < θ - η := by linarith
    have hzero : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have hsmall :
        ∀ᶠ t in atTop, Real.exp (-t) < θ - η :=
      hzero.eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall] with t ht
    linarith
  · intro h
    rcases eventually_atTop.1 h with ⟨T, hT⟩
    linarith [hT T le_rfl, Real.exp_pos (-T)]

/-- The committed interval-domain chemotaxis divergence has first power of
`u`; this is the actual exponent found by unfolding the model. -/
theorem intervalDomainChemotaxisDiv_actual_flux_report
    (p : CM2Params) (u v : intervalDomain.Point → ℝ)
    (x : intervalDomain.Point) :
    intervalDomainChemotaxisDiv p u v x =
      deriv
        (fun y : ℝ =>
          (intervalDomainLift u y) ^ (1 : ℕ) *
              deriv (intervalDomainLift v) y /
            (1 + intervalDomainLift v y) ^ p.β)
        x.1 :=
  intervalDomainChemotaxisDiv_actual_flux_u_power_one p u v x

/-- Replacing only `p.m` leaves the actual interval-domain chemotaxis
divergence unchanged. -/
theorem intervalDomainChemotaxisDiv_actual_m_independent_report
    (p : CM2Params) {m' : ℝ} (hm' : 0 < m')
    (u v : intervalDomain.Point → ℝ) (x : intervalDomain.Point) :
    intervalDomainChemotaxisDiv { p with m := m', hm := hm' } u v x =
      intervalDomainChemotaxisDiv p u v x :=
  intervalDomainChemotaxisDiv_actual_independent_of_m p hm' u v x

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.strict_subthreshold_eventual_lower_bounds_not_exact
#print axioms ShenWork.Paper3.intervalDomainChemotaxisDiv_actual_flux_report
#print axioms ShenWork.Paper3.intervalDomainChemotaxisDiv_actual_m_independent_report
