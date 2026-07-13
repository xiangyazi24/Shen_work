import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassConvergence
import ShenWork.Paper3.LyapunovFunction

/-!
# Theta-moment convergence implies uniform convergence on the interval

This file closes the compactness half of the stabilization argument on the
actual unit interval.  A bounded family of nonnegative profiles with a common
spatial Lipschitz constant cannot have vanishing theta dissipation while
remaining a fixed distance from the positive equilibrium.  The dynamic result
then combines this static coercivity with the concrete positive-time Lipschitz
producer for bounded classical solutions.

No stability, persistence, basin-entry, or convergence package is assumed.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

local instance : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- The scalar theta-dissipation integrand. -/
def intervalDomainThetaDissipationIntegrand
    (uStar theta z : ℝ) : ℝ :=
  (z - uStar) * (z ^ theta - uStar ^ theta)

theorem continuous_intervalDomainThetaDissipationIntegrand
    {uStar theta : ℝ} (htheta : 0 ≤ theta) :
    Continuous (intervalDomainThetaDissipationIntegrand uStar theta) := by
  unfold intervalDomainThetaDissipationIntegrand
  exact (continuous_id.sub continuous_const).mul
    ((Real.continuous_rpow_const htheta).sub continuous_const)

theorem intervalDomainThetaDissipationIntegrand_nonneg
    {uStar theta z : ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) (hz : 0 ≤ z) :
    0 ≤ intervalDomainThetaDissipationIntegrand uStar theta z := by
  exact thetaDissipationIntegrand_nonneg huStar htheta hz

/-- For a positive exponent and a positive equilibrium, the theta-dissipation
integrand vanishes only at the equilibrium. -/
theorem intervalDomainThetaDissipationIntegrand_eq_zero_iff
    {uStar theta z : ℝ}
    (huStar : 0 < uStar) (htheta : 0 < theta) (hz : 0 ≤ z) :
    intervalDomainThetaDissipationIntegrand uStar theta z = 0 ↔ z = uStar := by
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hzu | hpow
    · exact sub_eq_zero.mp hzu
    · have hpow_eq : z ^ theta = uStar ^ theta := sub_eq_zero.mp hpow
      exact le_antisymm
        ((Real.rpow_le_rpow_iff hz huStar.le htheta).mp hpow_eq.le)
        ((Real.rpow_le_rpow_iff huStar.le hz htheta).mp hpow_eq.ge)
  · rintro rfl
    simp [intervalDomainThetaDissipationIntegrand]

/-- Static coercivity of theta dissipation on uniformly bounded and uniformly
Lipschitz nonnegative interval profiles.  Small integrated dissipation forces
pointwise closeness to the positive equilibrium, with a threshold uniform over
the whole family. -/
theorem intervalDomain_thetaDissipation_uniform_small_of_integral_small
    {uStar theta K G eps : ℝ}
    (huStar : 0 < uStar) (htheta : 0 < theta)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (heps : 0 < eps) :
    ∃ q > 0, ∀ f : C(intervalDomainPoint, ℝ),
      (∀ x, 0 ≤ f x) →
      (∀ x, |f x| ≤ K) →
      LipschitzWith ⟨G, hG⟩ f →
      intervalDomain.integral
          (fun x => intervalDomainThetaDissipationIntegrand uStar theta (f x)) < q →
      ∀ x, |f x - uStar| < eps := by
  by_contra hcoercive
  push_neg at hcoercive
  let q : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hq_pos : ∀ n, 0 < q n := by
    intro n
    positivity
  let f : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
    Classical.choose (hcoercive (q n) (hq_pos n))
  have hf_spec (n : ℕ) :
      (∀ x, 0 ≤ f n x) ∧
      (∀ x, |f n x| ≤ K) ∧
      LipschitzWith ⟨G, hG⟩ (f n) ∧
      intervalDomain.integral
          (fun x => intervalDomainThetaDissipationIntegrand uStar theta (f n x)) <
        q n ∧
      ∃ x, eps ≤ |f n x - uStar| := by
    simpa [f] using Classical.choose_spec (hcoercive (q n) (hq_pos n))
  obtain ⟨g, phi, hphi, hfg⟩ :=
    intervalDomain_exists_uniform_convergent_subseq_of_lipschitz f
      hK hG (fun n x => (hf_spec n).2.1 x) (fun n => (hf_spec n).2.2.1)
  have hq_zero : Tendsto q atTop (𝓝 0) := by
    simpa [q, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hq_subseq_zero : Tendsto (fun n => q (phi n)) atTop (𝓝 0) :=
    hq_zero.comp hphi.tendsto_atTop
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hfg.tendsto_at x)
      (Filter.Eventually.of_forall fun n => (hf_spec (phi n)).1 x)
  have hg_le_K : ∀ x, g x ≤ K := by
    intro x
    exact le_of_tendsto (hfg.tendsto_at x)
      (Filter.Eventually.of_forall fun n =>
        le_trans (le_abs_self (f (phi n) x)) ((hf_spec (phi n)).2.1 x))
  have htheta_uniform : TendstoUniformly
      (fun n x =>
        intervalDomainThetaDissipationIntegrand uStar theta (f (phi n) x))
      (fun x => intervalDomainThetaDissipationIntegrand uStar theta (g x)) atTop := by
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := Set.Icc (0 : ℝ) K)
    · intro n x
      exact ⟨(hf_spec (phi n)).1 x,
        le_trans (le_abs_self (f (phi n) x)) ((hf_spec (phi n)).2.1 x)⟩
    · exact fun x => ⟨hg_nonneg x, hg_le_K x⟩
    · exact isCompact_Icc.uniformContinuousOn_of_continuous
        (continuous_intervalDomainThetaDissipationIntegrand htheta.le).continuousOn
    · exact hfg
  have htheta_int : Tendsto
      (fun n => intervalDomain.integral
        (fun x =>
          intervalDomainThetaDissipationIntegrand uStar theta (f (phi n) x)))
      atTop
      (𝓝 (intervalDomain.integral
        (fun x => intervalDomainThetaDissipationIntegrand uStar theta (g x)))) := by
    let F : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
      ⟨fun x => intervalDomainThetaDissipationIntegrand uStar theta (f (phi n) x),
        (continuous_intervalDomainThetaDissipationIntegrand htheta.le).comp
          (f (phi n)).continuous⟩
    let Fg : C(intervalDomainPoint, ℝ) :=
      ⟨fun x => intervalDomainThetaDissipationIntegrand uStar theta (g x),
        (continuous_intervalDomainThetaDissipationIntegrand htheta.le).comp g.continuous⟩
    exact intervalDomain_integral_tendsto_of_tendstoUniformly
      (f := F) (g := Fg) (by simpa [F, Fg] using htheta_uniform)
  have htheta_int_nonpos :
      intervalDomain.integral
          (fun x => intervalDomainThetaDissipationIntegrand uStar theta (g x)) ≤ 0 := by
    exact le_of_tendsto_of_tendsto htheta_int hq_subseq_zero
      (Filter.Eventually.of_forall fun n => (hf_spec (phi n)).2.2.2.1.le)
  let Fg : C(intervalDomainPoint, ℝ) :=
    ⟨fun x => intervalDomainThetaDissipationIntegrand uStar theta (g x),
      (continuous_intervalDomainThetaDissipationIntegrand htheta.le).comp g.continuous⟩
  have hFg_nonneg : ∀ x, 0 ≤ Fg x := by
    intro x
    exact intervalDomainThetaDissipationIntegrand_nonneg
      huStar.le htheta.le (hg_nonneg x)
  have hFg_zero : ∀ x, Fg x = 0 := by
    intro x
    apply le_antisymm
    · by_contra hx
      have hxpos : 0 < Fg x := lt_of_not_ge hx
      have hint_pos :=
        intervalDomain_integral_pos_of_continuous_nonneg_of_exists_pos
          Fg hFg_nonneg ⟨x, hxpos⟩
      have : intervalDomain.integral Fg ≤ 0 := by
        simpa [Fg] using htheta_int_nonpos
      exact (not_lt_of_ge this) hint_pos
    · exact hFg_nonneg x
  have hg_eq : ∀ x, g x = uStar := by
    intro x
    exact (intervalDomainThetaDissipationIntegrand_eq_zero_iff
      huStar htheta (hg_nonneg x)).mp (by simpa [Fg] using hFg_zero x)
  have huniform := Metric.tendstoUniformly_iff.mp hfg (eps / 2) (by linarith)
  rcases eventually_atTop.1 huniform with ⟨N, hN⟩
  obtain ⟨x, hx⟩ := (hf_spec (phi N)).2.2.2.2
  have hclose := hN N le_rfl x
  rw [Real.dist_eq, hg_eq x] at hclose
  rw [abs_sub_comm] at hclose
  linarith

/-- On the actual interval and the implemented `m = 1` equation, convergence
of the positive-equilibrium theta moment implies uniform convergence.  The
only compactness input is the proved positive-time spatial Lipschitz bound for
bounded classical solutions. -/
theorem intervalDomain_uniformConvergesInSup_of_thetaMoment
    (p : CM2Params) (hm : p.m = 1)
    {uStar theta : ℝ} (huStar : 0 < uStar) (htheta : 0 < theta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmoment : ThetaMomentConvergesToZero intervalDomain u uStar theta) :
    UniformConvergesInSup intervalDomain u uStar := by
  obtain ⟨Tlip, G, hG, hlip⟩ :=
    intervalDomain_globalBounded_eventual_lipschitz p hm huv
  obtain ⟨M0, hM0⟩ := huv.bounded.eventually_bound
  rcases eventually_atTop.1 hM0 with ⟨Tbdd, hTbdd⟩
  let K : ℝ := max M0 1
  have hK : 0 ≤ K := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  unfold UniformConvergesInSup
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨q, hq, hstatic⟩ :=
    intervalDomain_thetaDissipation_uniform_small_of_integral_small
      huStar htheta hK hG (by linarith : 0 < eps / 2)
  have hmoment_small : ∀ᶠ t in atTop,
      dist (intervalDomain.integral
        (fun x => intervalDomainThetaDissipationIntegrand uStar theta (u t x))) 0 < q := by
    have hball := hmoment.tendsto.eventually (Metric.ball_mem_nhds 0 hq)
    simpa [Metric.mem_ball, ThetaMomentConvergesToZero,
      intervalDomainThetaDissipationIntegrand] using hball
  apply eventually_atTop.1
  filter_upwards [hmoment_small,
    eventually_ge_atTop (max (max Tlip Tbdd) (1 : ℝ))] with t hsmall ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one
    ((le_max_right (max Tlip Tbdd) (1 : ℝ)).trans ht)
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
      (hTbdd t ((le_max_right Tlip Tbdd).trans
        ((le_max_left (max Tlip Tbdd) (1 : ℝ)).trans ht))).trans
          (le_max_left _ _)
    exact le_trans (by simpa [ft, intervalDomainLift, x.2] using habs) hsup
  have hft_lip : LipschitzWith ⟨G, hG⟩ ft := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := hlip t
      ((le_max_left Tlip Tbdd).trans
        ((le_max_left (max Tlip Tbdd) (1 : ℝ)).trans ht))
      x.1 x.2 y.1 y.2
    simpa [ft, intervalDomainLift, x.2, y.2, Real.dist_eq] using hxy
  have hft_small : intervalDomain.integral
      (fun x => intervalDomainThetaDissipationIntegrand uStar theta (ft x)) < q := by
    have hleabs : intervalDomain.integral
        (fun x => intervalDomainThetaDissipationIntegrand uStar theta (ft x)) ≤
        |intervalDomain.integral
          (fun x => intervalDomainThetaDissipationIntegrand uStar theta (ft x))| :=
      le_abs_self _
    have habs : |intervalDomain.integral
        (fun x => intervalDomainThetaDissipationIntegrand uStar theta (ft x))| < q := by
      simpa [ft, Real.dist_eq] using hsmall
    exact hleabs.trans_lt habs
  have hpointClose : ∀ x, |ft x - uStar| < eps / 2 :=
    hstatic ft hft_nonneg hft_abs hft_lip hft_small
  have hsup_le : intervalDomain.supNorm (fun x => u t x - uStar) ≤ eps / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => (hpointClose x).le)
  have hsup_nonneg : 0 ≤
      intervalDomain.supNorm (fun x => u t x - uStar) :=
    intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
      (fun x => (hpointClose x).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

#print axioms continuous_intervalDomainThetaDissipationIntegrand
#print axioms intervalDomainThetaDissipationIntegrand_nonneg
#print axioms intervalDomainThetaDissipationIntegrand_eq_zero_iff
#print axioms intervalDomain_thetaDissipation_uniform_small_of_integral_small
#print axioms intervalDomain_uniformConvergesInSup_of_thetaMoment

end

end ShenWork.Paper3
