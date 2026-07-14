import ShenWork.Paper3.IntervalDomainEntropyStrong2Dynamics

/-!
# Generic interval entropy-slice to weak-sup basin entry

This concrete bridge is shared by the positive-logistic entropy branches.  It
uses only eventual boundedness, positive-time Lipschitz regularity, and the
static theta-dissipation coercivity theorem.
-/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

local instance intervalDomainEntropyBasinMetricSpace : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- Arbitrarily late small theta-dissipation slices force arbitrarily late
entry into every primitive sup neighborhood of the positive equilibrium. -/
theorem intervalDomain_exists_late_supClose_of_thetaDissipation_slices
    (p : CM2Params) (hm : p.m = 1)
    {uStar theta : ℝ} (huStar : 0 < uStar) (htheta : 0 < theta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hlate : ∀ {T q : ℝ}, 0 < q →
      ∃ t, T ≤ t ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u t) < q)
    {T eps : ℝ} (heps : 0 < eps) :
    ∃ t, T ≤ t ∧ SupCloseToConstant intervalDomain (u t) uStar eps := by
  obtain ⟨Tlip, G, hG, hlip⟩ :=
    intervalDomain_globalBounded_eventual_lipschitz p hm huv
  obtain ⟨M0, hM0⟩ := huv.bounded.eventually_bound
  rcases eventually_atTop.1 hM0 with ⟨Tbdd, hTbdd⟩
  let K : ℝ := max M0 1
  have hK : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  obtain ⟨q, hq, hstatic⟩ :=
    intervalDomain_thetaDissipation_uniform_small_of_integral_small
      huStar htheta hK hG (by linarith : 0 < eps / 2)
  let Tbase : ℝ := max (max Tlip Tbdd) (max T 1)
  obtain ⟨t, htbase, hsmall⟩ := hlate (T := Tbase) hq
  have htTlip : Tlip ≤ t :=
    (le_max_left Tlip Tbdd).trans
      ((le_max_left (max Tlip Tbdd) (max T 1)).trans htbase)
  have htTbdd : Tbdd ≤ t :=
    (le_max_right Tlip Tbdd).trans
      ((le_max_left (max Tlip Tbdd) (max T 1)).trans htbase)
  have htT : T ≤ t :=
    (le_max_left T 1).trans
      ((le_max_right (max Tlip Tbdd) (max T 1)).trans htbase)
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one
    ((le_max_right T 1).trans
      ((le_max_right (max Tlip Tbdd) (max T 1)).trans htbase))
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let ft : C(intervalDomainPoint, ℝ) :=
    ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM htMem⟩
  have hft_nonneg : ∀ x, 0 ≤ ft x := fun _x =>
    (hsol.u_pos' htMem.1 htMem.2).le
  have hft_abs : ∀ x, |ft x| ≤ K := by
    intro x
    have habs := abs_lift_le_supNorm hsol htMem x.2
    have hsup : intervalDomain.supNorm (u t) ≤ K :=
      (hTbdd t htTbdd).trans (le_max_left _ _)
    exact le_trans
      (by simpa [ft, intervalDomainLift, x.2] using habs) hsup
  have hft_lip : LipschitzWith ⟨G, hG⟩ ft := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := hlip t htTlip x.1 x.2 y.1 y.2
    simpa [ft, intervalDomainLift, x.2, y.2, Real.dist_eq] using hxy
  have hft_small : intervalDomain.integral
      (fun x => intervalDomainThetaDissipationIntegrand uStar theta (ft x)) < q := by
    simpa [chemotaxisThetaDissipation,
      intervalDomainThetaDissipationIntegrand, ft] using hsmall
  have hpointClose : ∀ x, |ft x - uStar| < eps / 2 :=
    hstatic ft hft_nonneg hft_abs hft_lip hft_small
  have hsup_le : intervalDomain.supNorm (fun x => u t x - uStar) ≤ eps / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => (hpointClose x).le)
  exact ⟨t, htT, lt_of_le_of_lt hsup_le (by linarith)⟩

#print axioms intervalDomain_exists_late_supClose_of_thetaDissipation_slices

end

end ShenWork.Paper3
