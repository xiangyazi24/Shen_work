import ShenWork.Paper3.IntervalDomainMinimalMaxConvergence

/-!
# Uniform convergence in the repulsive minimal model

The maximum convergence is combined with the exact physical mass and the
concrete positive-time Lipschitz producer.  A static one-dimensional rigidity
lemma then controls the lower tail of each profile.
-/

namespace ShenWork.Paper3

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

local instance intervalDomainMinimalUniformMetricSpace : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- Every bounded positive, physical-mass orbit of the strictly repulsive
minimal interval model converges uniformly to its conserved mean. -/
theorem intervalDomain_minimal_chiNeg_uniform_u_converges
    (p : CM2Params) (hm : p.m = 1)
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    UniformConvergesInSup intervalDomain u uStar := by
  obtain ⟨Tlip, G, hG, hlip⟩ :=
    intervalDomain_globalBounded_eventual_lipschitz p hm huv
  unfold UniformConvergesInSup
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hstatic⟩ :=
    intervalDomain_uniform_close_of_mass_and_upper_of_lipschitz
      huStar hG (by linarith : 0 < ε / 2)
  have hmax := intervalDomain_minimal_chiNeg_eventually_supNorm_le_mass_add
    p ha hb hχ huv huStar hδ hmass
  apply eventually_atTop.1
  filter_upwards [hmax,
    eventually_ge_atTop (max Tlip (1 : ℝ))] with t hmax_t ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one
    ((le_max_right Tlip (1 : ℝ)).trans ht)
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let ft : C(intervalDomainPoint, ℝ) :=
    ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous
      hsolM htMem⟩
  have hft_nonneg : ∀ x, 0 ≤ ft x := fun _x =>
    (hsol.u_pos' htMem.1 htMem.2).le
  have hft_upper : ∀ x, ft x ≤ uStar + δ := by
    intro x
    have habs := abs_lift_le_supNorm hsol htMem x.2
    have hpoint : ft x ≤ intervalDomain.supNorm (u t) :=
      le_trans (le_abs_self (ft x)) (by
        simpa [ft, intervalDomainLift, x.2] using habs)
    exact hpoint.trans hmax_t
  have hft_mass : uStar - δ ≤ intervalDomain.integral ft := by
    have hm_t : intervalDomain.integral (u t) = uStar := by
      simpa [intervalDomain] using hmass t htPos
    simpa [ft, hm_t] using (sub_le_self uStar hδ.le)
  have hft_lip : LipschitzWith ⟨G, hG⟩ ft := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := hlip t ((le_max_left Tlip (1 : ℝ)).trans ht)
      x.1 x.2 y.1 y.2
    simpa [ft, intervalDomainLift, x.2, y.2, Real.dist_eq] using hxy
  have hpointClose : ∀ x, |ft x - uStar| < ε / 2 :=
    hstatic ft hft_nonneg hft_upper hft_mass hft_lip
  have hsup_le : intervalDomain.supNorm (fun x => u t x - uStar) ≤ ε / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => (hpointClose x).le)
  have hsup_nonneg : 0 ≤
      intervalDomain.supNorm (fun x => u t x - uStar) :=
    intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
      (fun x => (hpointClose x).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

#print axioms intervalDomain_minimal_chiNeg_uniform_u_converges

end

end ShenWork.Paper3
