import ShenWork.Paper2.IntervalDomainL2UEnergyUniform
import ShenWork.Paper3.IntervalDomainPersistenceLiminfTransfer

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- A positive global bounded interval solution has an eventually lower-bounded
spatial infimum trajectory.  This is the concrete interval bridge needed by
liminf APIs that require `IsBoundedUnder GE.ge`. -/
theorem intervalDomain_infValue_isBoundedUnder_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    IsBoundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (u t)) := by
  rcases hsol.bounded with ⟨M, hM⟩
  have hfloor :
      ∀ᶠ t in atTop, -M ≤ intervalDomain.infValue (u t) := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with t hMt ht1
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hTpos : 0 < t + 1 := by linarith
    have hclass := hsol.classical.classical (T := t + 1) hTpos
    have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := by
      exact ⟨htpos, by linarith⟩
    change -M ≤ sInf (Set.range (u t))
    refine le_csInf ?_ ?_
    · exact ⟨u t ⟨0, by exact ⟨le_rfl, by norm_num⟩⟩,
        ⟨⟨0, by exact ⟨le_rfl, by norm_num⟩⟩, rfl⟩⟩
    · rintro y ⟨x, rfl⟩
      have habs : |u t x| ≤ M := by
        have hlift : intervalDomainLift (u t) x.1 = u t x := by
          simp [intervalDomainLift]
        have h := (abs_lift_le_supNorm hclass htmem x.2).trans hMt
        simpa [hlift] using h
      exact (abs_le.mp habs).1
  exact isBoundedUnder_of_eventually_ge hfloor

/-- Exact-threshold `v` liminf transfer with the `u` lower-boundedness
side-condition supplied by the positive bounded interval solution itself. -/
theorem intervalDomain_liminf_v_ge_of_u_liminf_lower'
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {θ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hθpos : 0 < θ)
    (hv_cobdd : IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (v t)))
    (hθ : θ ≤ liminfInfValue intervalDomain u) :
    p.ν / p.μ * θ ^ p.γ ≤ liminfInfValue intervalDomain v :=
  intervalDomain_liminf_v_ge_of_u_liminf_lower
    hsol hθpos
    (intervalDomain_infValue_isBoundedUnder_of_positiveGlobalBoundedSolution
      hsol)
    hv_cobdd hθ

#print axioms intervalDomain_infValue_isBoundedUnder_of_positiveGlobalBoundedSolution
#print axioms intervalDomain_liminf_v_ge_of_u_liminf_lower'

end

end ShenWork.Paper3
