import ShenWork.Paper3.IntervalDomainTailReactionCoercivity

/-!
# Mass convergence for repulsive interval chemotaxis

The exact mass ODE and the static tail-reaction coercivity force the mass of
every bounded positive orbit to converge to the positive logistic carrying
capacity.  No stability, compactness, or convergence package is assumed.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

local instance : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- A bounded scalar trajectory with a uniformly positive derivative whenever
it is below a threshold eventually reaches that threshold and cannot cross
back below it. -/
theorem eventually_ge_of_hasDerivAt_pos_below_threshold
    {M : ℝ → ℝ} {a threshold q B : ℝ}
    (ha : 0 < a) (hq : 0 < q)
    (hcont : ContinuousOn M (Set.Ioi (0 : ℝ)))
    (hupper : ∀ t, a ≤ t → M t ≤ B)
    (hderiv : ∀ t, a ≤ t → M t < threshold →
      ∃ d : ℝ, q ≤ d ∧ HasDerivAt M d t) :
    ∃ T ≥ a, ∀ t ≥ T, threshold ≤ M t := by
  have hreach : ∃ T ≥ a, threshold ≤ M T := by
    by_contra hnone
    push_neg at hnone
    have hBa : M a ≤ B := hupper a le_rfl
    let T : ℝ := a + (B - M a + 1) / q
    have hnum : 0 < B - M a + 1 := by linarith
    have haT : a < T := by
      dsimp [T]
      exact lt_add_of_pos_right a (div_pos hnum hq)
    let N : ℝ → ℝ := fun t => M t - q * t
    have hNcont : ContinuousOn N (Set.Icc a T) := by
      exact (hcont.mono (fun _t ht => lt_of_lt_of_le ha ht.1)).sub
        (continuous_const.mul continuous_id).continuousOn
    have hNdiff : DifferentiableOn ℝ N (interior (Set.Icc a T)) := by
      intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, _hdq, hd⟩ := hderiv t ht.1.le (hnone t ht.1.le)
      exact (hd.sub ((hasDerivAt_id t).const_mul q)).differentiableAt.differentiableWithinAt
    have hNderiv : ∀ t ∈ interior (Set.Icc a T), 0 ≤ deriv N t := by
      intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hdq, hd⟩ := hderiv t ht.1.le (hnone t ht.1.le)
      have hNd : HasDerivAt N (d - q) t := by
        simpa [N] using hd.sub ((hasDerivAt_id t).const_mul q)
      rw [hNd.deriv]
      linarith
    have hmono : MonotoneOn N (Set.Icc a T) :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _) hNcont hNdiff hNderiv
    have hcompare := hmono (Set.left_mem_Icc.mpr haT.le)
      (Set.right_mem_Icc.mpr haT.le) haT.le
    have hBT : M T ≤ B := hupper T haT.le
    dsimp [N] at hcompare
    have hqcancel : q * (T - a) = B - M a + 1 := by
      dsimp [T]
      field_simp [ne_of_gt hq]
      ring
    nlinarith
  obtain ⟨T, haT, hthreshold⟩ := hreach
  have hT : 0 < T := lt_of_lt_of_le ha haT
  have hnonnegDeriv : ∀ t, T ≤ t → M t < threshold →
      ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt M d t := by
    intro t ht hMt
    obtain ⟨d, hd, hMd⟩ := hderiv t (haT.trans ht) hMt
    exact ⟨d, le_trans hq.le hd, hMd⟩
  have hlower := lower_bound_of_hasDerivAt_nonneg_below_threshold
    (M := M) (a := T) (threshold := threshold) hT hcont hnonnegDeriv
  exact ⟨T, haT, fun t ht => by
    have := hlower t ht
    simpa [min_eq_right hthreshold] using this⟩

/-- Integration over the concrete unit interval commutes with subtracting a
continuous profile from a constant. -/
theorem intervalDomain_integral_const_sub
    (z : ℝ) (f : C(intervalDomainPoint, ℝ)) :
    intervalDomain.integral (fun x => z - f x) =
      z - intervalDomain.integral f := by
  unfold intervalDomain intervalDomainIntegral
  calc
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (fun y => z - f y) x) =
        ∫ x in (0 : ℝ)..1, z - intervalDomainLift f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp [intervalDomainLift, hx]
    _ = (∫ _x in (0 : ℝ)..1, z) -
        ∫ x in (0 : ℝ)..1, intervalDomainLift f x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (intervalDomainLift_intervalIntegrable_of_continuous f)]
    _ = z - ∫ x in (0 : ℝ)..1, intervalDomainLift f x := by simp

/-- Quantitative static rigidity: a uniformly Lipschitz nonnegative profile
whose maximum and mass are both sufficiently close to `c` is uniformly close
to the constant profile `c`. -/
theorem intervalDomain_uniform_close_of_mass_and_upper_of_lipschitz
    {c G ε : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : C(intervalDomainPoint, ℝ),
      (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ c + δ) →
      c - δ ≤ intervalDomain.integral f →
      LipschitzWith ⟨G, hG⟩ f →
      ∀ x, |f x - c| < ε := by
  let ell : ℝ := min (1 / 2 : ℝ) ((2 * ε) / (8 * (G + 1)))
  let L : ℝ := (2 * ε) * ell / 4
  have hG1 : 0 < G + 1 := by linarith
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) (div_pos (by positivity) (by positivity))
  have hL : 0 < L := by dsimp [L]; positivity
  let δ : ℝ := min (ε / 2) (L / 4)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by positivity)
  have hδε : δ ≤ ε / 2 := by dsimp [δ]; exact min_le_left _ _
  have hδL : δ ≤ L / 4 := by dsimp [δ]; exact min_le_right _ _
  refine ⟨δ, hδ, fun f _hf_nonneg hf_upper hmass hlip x => ?_⟩
  rw [abs_lt]
  constructor
  · by_contra hnot
    have hfx : f x ≤ c - ε := by linarith
    let deficit : C(intervalDomainPoint, ℝ) :=
      ⟨fun y => c + δ - f y, continuous_const.sub f.continuous⟩
    have hdef_nonneg_sub : ∀ y, 0 ≤ deficit y := by
      intro y
      dsimp [deficit]
      linarith [hf_upper y]
    have hdef_cont : ContinuousOn (intervalDomainLift deficit)
        (Set.Icc (0 : ℝ) 1) :=
      ShenWork.Paper2.IntervalDomainM.lift_continuousOn_Icc_of_continuous
        deficit.continuous
    have hdef_nonneg : ∀ y, 0 ≤ intervalDomainLift deficit y := by
      intro y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
      · rw [intervalDomainLift, dif_pos hy]
        exact hdef_nonneg_sub _
      · simp [intervalDomainLift, hy]
    have hdef_lip : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ∀ z ∈ Set.Icc (0 : ℝ) 1,
          |intervalDomainLift deficit y - intervalDomainLift deficit z| ≤
            G * |y - z| := by
      intro y hy z hz
      have hdist := hlip.dist_le_mul ⟨y, hy⟩ ⟨z, hz⟩
      simpa [deficit, intervalDomainLift, hy, hz, Real.dist_eq,
        Subtype.dist_eq, abs_sub_comm] using hdist
    have hdef_at_x : ε ≤ intervalDomainLift deficit x.1 := by
      simp [deficit, intervalDomainLift, x.2]
      linarith
    have hbdd : BddAbove
        (intervalDomainLift deficit '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hdef_cont).bddAbove
    have hsup : (2 * ε) / 2 ≤
        sSup (intervalDomainLift deficit '' Set.Icc (0 : ℝ) 1) := by
      have hxmem : intervalDomainLift deficit x.1 ∈
          intervalDomainLift deficit '' Set.Icc (0 : ℝ) 1 :=
        ⟨x.1, x.2, rfl⟩
      exact (by linarith : (2 * ε) / 2 ≤ intervalDomainLift deficit x.1).trans
        (le_csSup hbdd hxmem)
    have hgeom := interval_lipschitz_mass_lower_of_sSup_ge_half
      (c := 2 * ε) (G := G) (by positivity) hG hdef_cont hdef_nonneg
      hdef_lip hsup
    have hgeom' : L ≤ intervalDomain.integral deficit := by
      simpa [L, ell, intervalDomain, intervalDomainIntegral] using hgeom
    have hdefIntegral : intervalDomain.integral deficit =
        c + δ - intervalDomain.integral f := by
      simpa [deficit] using intervalDomain_integral_const_sub (c + δ) f
    have hdefUpper : intervalDomain.integral deficit ≤ 2 * δ := by
      rw [hdefIntegral]
      linarith
    linarith
  · have := hf_upper x
    linarith

/-- Every bounded positive repulsive orbit eventually has mass at least any
fixed level strictly below the logistic carrying capacity. -/
theorem intervalDomain_chiNonpos_eventually_mass_ge_capacity_sub
    (p : CM2Params) (hm : p.m = 1) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {d : ℝ} (hd : 0 < d)
    (hdc : d < (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∀ᶠ t in atTop,
      (positiveEquilibrium p ⟨ha, hb⟩).1 - d ≤
        intervalDomain.integral (u t) := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  obtain ⟨Tlip, G, hG, hlip⟩ :=
    intervalDomain_globalBounded_eventual_lipschitz p hm huv
  obtain ⟨Tmass, eta, hTmass, heta, hmass⟩ :=
    intervalDomain_globalBounded_eventual_mass_pos p hm ha hb huv
  obtain ⟨eps, heps, q, hq, hcoercive⟩ :=
    intervalDomain_logisticReaction_coercive_of_mass_gap
      p ha hb heta hd (by simpa [c] using hdc) hG
  obtain ⟨Tmax, hmax⟩ := eventually_atTop.1
    (intervalDomain_chiNonpos_eventually_supNorm_le_capacity_add
      p hχ ha hb huv heps)
  let a₀ : ℝ := max 1 (max Tlip (max Tmass Tmax))
  have ha₀ : 0 < a₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hTlip₀ : Tlip ≤ a₀ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hTmass₀ : Tmass ≤ a₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hTmax₀ : Tmax ≤ a₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  let Mass : ℝ → ℝ := fun t => intervalDomain.integral (u t)
  have hMassCont : ContinuousOn Mass (Set.Ioi (0 : ℝ)) := by
    intro t ht
    change 0 < t at ht
    have hH : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hH
    have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
    exact (ShenWork.Paper2.IntervalDomainM.mass_hasDerivAt
      hsolM ht (by linarith)).continuousAt.continuousWithinAt
  have hMassUpper : ∀ t, a₀ ≤ t → Mass t ≤ c + eps := by
    intro t ht
    have htPos : 0 < t := lt_of_lt_of_le ha₀ ht
    have hH : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hH
    have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
    have hmassSup := intervalDomain_classicalSolution_mass_le_supNorm hsol htMem
    exact hmassSup.trans (by
      simpa [c, positiveEquilibrium, one_div] using
        hmax t (hTmax₀.trans ht))
  have hMassDeriv : ∀ t, a₀ ≤ t → Mass t < c - d →
      ∃ r : ℝ, q ≤ r ∧ HasDerivAt Mass r t := by
    intro t ht hMt
    have htPos : 0 < t := lt_of_lt_of_le ha₀ ht
    have hH : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hH
    have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
    have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
    let ft : C(intervalDomainPoint, ℝ) :=
      ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM htMem⟩
    have hft_nonneg : ∀ x, 0 ≤ ft x := fun x =>
      (hsol.u_pos' htMem.1 htMem.2).le
    have hft_upper : ∀ x, ft x ≤ c + eps := by
      intro x
      have habs := abs_lift_le_supNorm hsol htMem x.2
      have hpoint : ft x ≤ intervalDomain.supNorm (u t) := by
        exact le_trans (le_abs_self (ft x)) (by
          simpa [ft, intervalDomainLift, x.2] using habs)
      exact hpoint.trans (by
        simpa [c, positiveEquilibrium, one_div] using
          hmax t (hTmax₀.trans ht))
    have hft_lip : LipschitzWith ⟨G, hG⟩ ft := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have hxy := hlip t (hTlip₀.trans ht) x.1 x.2 y.1 y.2
      simpa [ft, intervalDomainLift, x.2, y.2, Real.dist_eq] using hxy
    have hreact : q ≤ intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (ft x)) :=
      hcoercive ft hft_nonneg hft_upper
        (by simpa [Mass, ft] using hmass t (hTmass₀.trans ht))
        (by simpa [Mass, ft] using hMt.le) hft_lip
    let r : ℝ := intervalDomain.integral
      (fun x => intervalDomainLogisticReaction p (ft x))
    have hrDeriv : HasDerivAt Mass r t := by
      have hbase := ShenWork.Paper2.IntervalDomainM.mass_logistic_hasDerivAt
        hsolM htMem.1 htMem.2
      have hreactionEq := intervalDomain_reaction_integral_eq hsol htMem
      rw [← hreactionEq] at hbase
      simpa [Mass, r, ft, intervalDomainLogisticReaction] using hbase
    exact ⟨r, by simpa [r] using hreact, hrDeriv⟩
  obtain ⟨T, haT, htail⟩ := eventually_ge_of_hasDerivAt_pos_below_threshold
    (M := Mass) (a := a₀) (threshold := c - d) (q := q) (B := c + eps)
    ha₀ hq hMassCont hMassUpper hMassDeriv
  exact eventually_atTop.2 ⟨T, fun t ht => by simpa [Mass, c] using htail t ht⟩

/-- The mass of every bounded positive repulsive orbit converges to the
positive logistic carrying capacity. -/
theorem intervalDomain_chiNonpos_mass_tendsto_capacity
    (p : CM2Params) (hm : p.m = 1) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    Tendsto (fun t => intervalDomain.integral (u t)) atTop
      (𝓝 (positiveEquilibrium p ⟨ha, hb⟩).1) := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  change Tendsto (fun t => intervalDomain.integral (u t)) atTop (𝓝 c)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let d : ℝ := min (ε / 2) (c / 2)
  have hd : 0 < d := by dsimp [d]; exact lt_min (by linarith) (by linarith)
  have hdc : d < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hlower := intervalDomain_chiNonpos_eventually_mass_ge_capacity_sub
    p hm hχ ha hb huv hd (by simpa [c] using hdc)
  have hmax := intervalDomain_chiNonpos_eventually_supNorm_le_capacity_add
    p hχ ha hb huv (by linarith : 0 < ε / 2)
  apply eventually_atTop.1
  filter_upwards [hlower, hmax, eventually_ge_atTop (1 : ℝ)] with t hlow hsup ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have hmassSup := intervalDomain_classicalSolution_mass_le_supNorm hsol
    (⟨htPos, by linarith⟩ : t ∈ Set.Ioo (0 : ℝ) (t + 1))
  have hupper : intervalDomain.integral (u t) ≤ c + ε / 2 :=
    hmassSup.trans (by
      simpa [c, positiveEquilibrium, one_div] using hsup)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [min_le_left (ε / 2) (c / 2)]

/-- Pointwise absolute control bounds the concrete interval supremum norm. -/
theorem intervalDomain_supNorm_le_of_pointwise_abs_le
    {f : intervalDomainPoint → ℝ} {K : ℝ}
    (h : ∀ x, |f x| ≤ K) :
    intervalDomain.supNorm f ≤ K := by
  unfold intervalDomain intervalDomainSupNorm
  let x₀ : intervalDomainPoint := ⟨0, ⟨by norm_num, by norm_num⟩⟩
  have hne : (Set.range fun x : intervalDomainPoint => |f x|).Nonempty :=
    ⟨|f x₀|, Set.mem_range_self x₀⟩
  exact csSup_le hne (by
    rintro _ ⟨x, rfl⟩
    exact h x)

/-- A pointwise bounded interval supremum norm is nonnegative. -/
theorem intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
    {f : intervalDomainPoint → ℝ} {K : ℝ}
    (h : ∀ x, |f x| ≤ K) :
    0 ≤ intervalDomain.supNorm f := by
  unfold intervalDomain intervalDomainSupNorm
  have hbdd : BddAbove (Set.range fun x : intervalDomainPoint => |f x|) :=
    ⟨K, by rintro _ ⟨x, rfl⟩; exact h x⟩
  let x₀ : intervalDomainPoint := ⟨0, ⟨by norm_num, by norm_num⟩⟩
  exact (abs_nonneg (f x₀)).trans (le_csSup hbdd (Set.mem_range_self x₀))

/-- Every bounded positive repulsive interval orbit converges uniformly in
its `u` component to the positive logistic equilibrium. -/
theorem intervalDomain_chiNonpos_uniform_u_converges
    (p : CM2Params) (hm : p.m = 1) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    UniformConvergesInSup intervalDomain u
      (positiveEquilibrium p ⟨ha, hb⟩).1 := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  obtain ⟨Tlip, G, hG, hlip⟩ :=
    intervalDomain_globalBounded_eventual_lipschitz p hm huv
  have hmasslim := intervalDomain_chiNonpos_mass_tendsto_capacity
    p hm hχ ha hb huv
  unfold UniformConvergesInSup
  change Tendsto (fun t => intervalDomain.supNorm (fun x => u t x - c))
    atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hstatic⟩ :=
    intervalDomain_uniform_close_of_mass_and_upper_of_lipschitz
      hc hG (by linarith : 0 < ε / 2)
  let δ₀ : ℝ := min δ (c / 2)
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδ (by linarith)
  have hδ₀δ : δ₀ ≤ δ := by dsimp [δ₀]; exact min_le_left _ _
  have hmax := intervalDomain_chiNonpos_eventually_supNorm_le_capacity_add
    p hχ ha hb huv hδ₀
  have hmassClose : ∀ᶠ t in atTop,
      dist (intervalDomain.integral (u t)) c < δ₀ := by
    have hball := hmasslim.eventually (Metric.ball_mem_nhds c hδ₀)
    simpa [Metric.mem_ball, c] using hball
  apply eventually_atTop.1
  filter_upwards [hmax, hmassClose,
    eventually_ge_atTop (max Tlip (1 : ℝ))] with t hmax_t hmass_t ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one
    ((le_max_right Tlip (1 : ℝ)).trans ht)
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let ft : C(intervalDomainPoint, ℝ) :=
    ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM htMem⟩
  have hft_nonneg : ∀ x, 0 ≤ ft x := fun _x =>
    (hsol.u_pos' htMem.1 htMem.2).le
  have hft_upper : ∀ x, ft x ≤ c + δ := by
    intro x
    have habs := abs_lift_le_supNorm hsol htMem x.2
    have hpoint : ft x ≤ intervalDomain.supNorm (u t) :=
      le_trans (le_abs_self (ft x)) (by
        simpa [ft, intervalDomainLift, x.2] using habs)
    have hsupδ₀ : intervalDomain.supNorm (u t) ≤ c + δ₀ := by
      simpa [c, positiveEquilibrium, one_div] using hmax_t
    linarith
  have hft_mass : c - δ ≤ intervalDomain.integral ft := by
    rw [Real.dist_eq, abs_lt] at hmass_t
    simpa [ft] using (show c - δ ≤ intervalDomain.integral (u t) by linarith)
  have hft_lip : LipschitzWith ⟨G, hG⟩ ft := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := hlip t ((le_max_left Tlip (1 : ℝ)).trans ht)
      x.1 x.2 y.1 y.2
    simpa [ft, intervalDomainLift, x.2, y.2, Real.dist_eq] using hxy
  have hpointClose : ∀ x, |ft x - c| < ε / 2 :=
    hstatic ft hft_nonneg hft_upper hft_mass hft_lip
  have hsup_le : intervalDomain.supNorm (fun x => u t x - c) ≤ ε / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => (hpointClose x).le)
  have hsup_nonneg : 0 ≤ intervalDomain.supNorm (fun x => u t x - c) :=
    intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
      (fun x => (hpointClose x).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

#print axioms eventually_ge_of_hasDerivAt_pos_below_threshold
#print axioms intervalDomain_integral_const_sub
#print axioms intervalDomain_uniform_close_of_mass_and_upper_of_lipschitz
#print axioms intervalDomain_chiNonpos_eventually_mass_ge_capacity_sub
#print axioms intervalDomain_chiNonpos_mass_tendsto_capacity
#print axioms intervalDomain_supNorm_le_of_pointwise_abs_le
#print axioms intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
#print axioms intervalDomain_chiNonpos_uniform_u_converges

end

end ShenWork.Paper3
