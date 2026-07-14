import ShenWork.Paper2.IntervalDomainMCriticalLpSeed
import ShenWork.PDE.P3MoserAgmonDirectRoute
import ShenWork.PDE.P3MoserIntegratedClosure

/-!
# Finite-power bootstrap in the faithful critical interval equation

The critical seed only lies above `gamma / 2`.  This file applies the
seed-relative one-dimensional Agmon/GN estimate already proved in
`P3MoserAgmonDirectRoute` to the concrete `LpBootstrapEnergyInequality`.
The resulting linear damping inequality is closed by the same positive-time
threshold argument used by the faithful slow branch.  No Moser dissipation
drop or relative weighted-gradient bridge is used.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- A positive-time linear damping inequality, together with the initial
trace, bounds the corresponding power uniformly before the horizon. -/
theorem lp_power_bounded_before_of_linear_damping
    {p : CM2Params} {T pExp B D : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hp : 1 < pExp) (hB : 0 < B)
    (hdamp : ∀ t, 0 < t → t < T →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        B * intervalDomainLpEnergy pExp u t ≤ D) :
    LpPowerBoundedBefore intervalDomainM pExp T u := by
  let E : ℝ → ℝ := fun s => intervalDomainLpEnergy pExp u s
  let K : ℝ := max 0 (D / B)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hDK : D ≤ B * K := by
    have hdiv : D / B ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_left hdiv hB.le
    have hcancel : B * (D / B) = D := by
      field_simp [ne_of_gt hB]
    rwa [hcancel] at hmul
  have hEcont : ContinuousOn E (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact (lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2).continuousAt.continuousWithinAt
  have hEderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, K < E s →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt E d s := by
    intro s hs hKs
    have hDamp := hdamp s hs.1 hs.2
    have hp0 : 0 < pExp := lt_trans zero_lt_one hp
    refine ⟨deriv E s, ?_, ?_⟩
    · dsimp [E] at hDamp ⊢
      have hinv : 0 < 1 / pExp := one_div_pos.mpr hp0
      have hBE : B * K < B * intervalDomainLpEnergy pExp u s :=
        mul_lt_mul_of_pos_left hKs hB
      nlinarith
    · simpa [E] using lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2
  obtain ⟨δ, hδ, htraceδ⟩ := htrace 1 (by norm_num)
  have hu0bdd :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  obtain ⟨M₀, hM₀⟩ := hu0bdd
  let R : ℝ := max 0 M₀ + 1
  have hM₀nonneg : 0 ≤ M₀ := by
    let x₀ : intervalDomainPoint :=
      ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    have hx := hM₀ ⟨x₀, rfl⟩
    exact (abs_nonneg (u₀ x₀)).trans hx
  have hR : 0 < R := by
    dsimp [R]
    linarith [le_max_left (0 : ℝ) M₀]
  have hinitial : ∀ s, 0 < s → s < δ → s < T → E s ≤ R ^ pExp := by
    intro s hs0 hsδ hsT
    have hs : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
    have hdiffBdd := bddAbove_range_abs_diff_of_bddAbove
      (solution_slice_abs_bddAbove hsol hs)
      (by simpa [intervalDomainM] using hu₀.admissible.1)
    have hsup : intervalDomain.supNorm (fun x => u s x - u₀ x) < 1 := by
      simpa [intervalDomainM, intervalDomain] using htraceδ s hs0 hsδ
    have hpoint : ∀ x : intervalDomain.Point, u s x ≤ R := by
      intro x
      have hdiff : |u s x - u₀ x| ≤
          intervalDomain.supNorm (fun y => u s y - u₀ y) := by
        change |u s x - u₀ x| ≤
          intervalDomainSupNorm (fun y => u s y - u₀ y)
        unfold intervalDomainSupNorm
        exact le_csSup hdiffBdd ⟨x, rfl⟩
      have hu₀x : |u₀ x| ≤ M₀ := hM₀ ⟨x, rfl⟩
      have htri : u s x ≤ |u s x - u₀ x| + |u₀ x| := by
        calc
          u s x = (u s x - u₀ x) + u₀ x := by ring
          _ ≤ |u s x - u₀ x| + |u₀ x| :=
            add_le_add (le_abs_self _) (le_abs_self _)
      dsimp [R]
      linarith [lt_of_le_of_lt hdiff hsup, le_max_right (0 : ℝ) M₀]
    have hint : IntervalIntegrable
        (fun x => intervalDomainLift (u s) x ^ pExp) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact power_continuousOn_timeSlice (q := pExp) hsol hs
    rw [show E s = ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u s) x ^ pExp by
      dsimp [E]
      exact lpEnergy_eq_lift_power_of_solution hsol hs0 hsT]
    calc
      (∫ x in (0 : ℝ)..1, intervalDomainLift (u s) x ^ pExp) ≤
          ∫ _x in (0 : ℝ)..1, R ^ pExp :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          intervalIntegrable_const (fun x hx => by
            have hpos := solution_lift_pos_Icc hsol hs x hx
            have hle : intervalDomainLift (u s) x ≤ R := by
              simpa [intervalDomainLift, hx] using
                hpoint (⟨x, hx⟩ : intervalDomain.Point)
            exact Real.rpow_le_rpow hpos.le hle
              (le_of_lt (lt_trans zero_lt_one hp)))
      _ = R ^ pExp := by
        rw [intervalIntegral.integral_const]
        norm_num [smul_eq_mul]
  let C : ℝ := max K (R ^ pExp)
  refine ⟨C, ?_⟩
  intro t ht0 htT
  have hEt : E t ≤ C := by
    by_cases hle : E t ≤ K
    · exact hle.trans (le_max_left _ _)
    · push Not at hle
      have habove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < E s :=
        threshold_persists_below_of_hasDerivAt_nonpos
          ht0 htT hEcont hEderiv hle
      let s : ℝ := min (δ / 2) (t / 2)
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hst : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hsT : s < T := lt_trans hst htT
      have hsubIoo : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T := fun z hz =>
        ⟨lt_of_lt_of_le hs0 hz.1, lt_of_le_of_lt hz.2 htT⟩
      have hsubIoc : Set.Ioo s t ⊆ Set.Ioc (0 : ℝ) t := fun z hz =>
        ⟨lt_trans hs0 hz.1, hz.2.le⟩
      have hanti : AntitoneOn E (Set.Icc s t) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          (hEcont.mono hsubIoo)
        · intro z hz
          rw [interior_Icc] at hz
          exact (lpEnergy_hasDerivAt_of_solution hsol
            (lt_trans hs0 hz.1) (lt_trans hz.2 htT)).differentiableAt.differentiableWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hzIoo : z ∈ Set.Ioo (0 : ℝ) T :=
            ⟨lt_trans hs0 hz.1, lt_trans hz.2 htT⟩
          obtain ⟨d, hd, hD⟩ := hEderiv z hzIoo (habove z (hsubIoc hz))
          rw [hD.deriv]
          exact hd
      have hEtEs : E t ≤ E s :=
        hanti (Set.left_mem_Icc.mpr hst.le)
          (Set.right_mem_Icc.mpr hst.le) hst.le
      exact (hEtEs.trans (hinitial s hs0 hsδ hsT)).trans (le_max_right _ _)
  have hdomain : intervalDomainM.integral (fun x => (u t x) ^ pExp) = E t := by
    change intervalDomain.integral (fun x => (u t x) ^ pExp) = E t
    rw [show E t = ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ pExp by
      dsimp [E]
      exact lpEnergy_eq_lift_power_of_solution hsol ht0 htT]
    exact intervalDomain_integral_rpow_eq_lift_integral
  rw [hdomain]
  exact hEt

/-- The concrete bootstrap energy inequality plus the correct seed-relative
Agmon estimate gives a positive linear damping coefficient at every exponent
above the seed. -/
theorem critical_bootstrap_linear_damping
    {p : CM2Params} {T rho p0 pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain p T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T rho p0)
    (hpExp : p0 ≤ pExp) :
    ∃ B > 0, ∃ D, ∀ t, 0 < t → t < T →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        B * intervalDomainLpEnergy pExp u t ≤ D := by
  have henergy :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  have hinterp :=
    produce_AgmonAbsorbedInterpolationBefore_of_classical hsol hboot
  obtain ⟨A, hA, B, hB, K, hK, L, hfull⟩ := henergy pExp hpExp
  let eps : ℝ := A / (2 * K)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨Ceps, hCeps⟩ := hinterp pExp hpExp eps heps
  refine ⟨B, hB, K * Ceps + L, ?_⟩
  intro t ht0 htT
  let G : ℝ := intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm
      (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
  let E : ℝ := intervalDomainLpEnergy pExp u t
  let Z : ℝ := intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  have hfull_t := hfull t ht0 htT
  have hinterp_t : Z ≤ eps * G + Ceps := by
    simpa [Z, G] using hCeps t ht0 htT
  have hG : 0 ≤ G := by
    dsimp [G]
    rw [intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := p) (T := T) (pExp := pExp)
      (u := u) (v := v) hsol ht0 htT]
    exact mul_nonneg (sq_nonneg _) <|
      intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT
  have hscaled : K * Z ≤ K * (eps * G + Ceps) :=
    mul_le_mul_of_nonneg_left hinterp_t hK.le
  have hKe : K * eps = A / 2 := by
    dsimp [eps]
    field_simp [ne_of_gt hK]
  have hscaled' : K * Z ≤ (A / 2) * G + K * Ceps := by
    calc
      K * Z ≤ K * (eps * G + Ceps) := hscaled
      _ = (A / 2) * G + K * Ceps := by
        rw [mul_add, ← mul_assoc, hKe]
  have hEnergyEq :=
    intervalDomainLpEnergy_eq_power_of_regularity
      (pExp := pExp) hsol ht0 htT
  have hDerivEq :
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t =
        deriv (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t :=
    (intervalDomainLpEnergy_eventuallyEq_power_of_regularity
      (pExp := pExp) hsol ht0 htT).deriv_eq
  rw [← hDerivEq, ← hEnergyEq] at hfull_t
  dsimp [G, E, Z] at hfull_t hscaled' ⊢
  nlinarith

/-- A critical positive-sensitivity seed controls every larger finite power.
This is the paper's finite-exponent bootstrap, closed without the repository's
obsolete dissipation-drop interface. -/
theorem critical_lp_power_bounded_before_positive_of_seed
    {p : CM2Params} {T p0 pExp : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hm : p.m = 1) (hbeta : 1 ≤ p.β)
    (hp0 : max 1 (p.γ * (p.N : ℝ) / 2) < p0)
    (hseed : LpPowerBoundedBefore intervalDomainM p0 T u)
    (hpExp : p0 ≤ pExp) :
    LpPowerBoundedBefore intervalDomainM pExp T u := by
  have hsol' : IsPaper2ClassicalSolution intervalDomain p T u v :=
    classicalSolution_intervalDomain_of_m_eq_one hm hsol
  have hcross : CrossDiffusionBootstrapEstimate intervalDomain p T p.γ u v :=
    intervalDomain_crossDiffusionBootstrapEstimate_sharp hsol' hbeta
  have hseed' : LpPowerBoundedBefore intervalDomain p0 T u := by
    simpa [intervalDomainM, intervalDomain] using hseed
  have hboot : AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T p.γ p0 :=
    ⟨p.hγ, hsol.1, hp0, hseed'⟩
  obtain ⟨B, hB, D, hdamp⟩ :=
    critical_bootstrap_linear_damping hsol' hcross hboot hpExp
  have hp0_one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hp : 1 < pExp := lt_of_lt_of_le hp0_one hpExp
  exact lp_power_bounded_before_of_linear_damping
    hu₀ hsol htrace hp hB hdamp

/-- The fixed critical seed gives the one-rung first-crossing interface used by
the abstract Moser closure.  In fact the finite-power bootstrap above is
stronger: it bounds every exponent above `p0` directly, so the supplied bound
at the current rung is not needed. -/
theorem critical_integratedMoserFirstCrossingStep_positive_of_seed
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hm : p.m = 1) (hbeta : 1 ≤ p.β)
    (hp0 : max 1 (p.γ * (p.N : ℝ) / 2) < p0)
    (hseed : LpPowerBoundedBefore intervalDomainM p0 T u) :
    IntegratedMoserFirstCrossingStep intervalDomainM u T p.γ p0 := by
  intro q hq _hqBound
  apply critical_lp_power_bounded_before_positive_of_seed
    hu₀ hsol htrace hm hbeta hp0 hseed
  exact hq.trans (le_add_of_nonneg_right p.hγ.le)

/-- Under the critical small-sensitivity condition there is a uniformly
bounded power strictly above both one and the signal exponent `gamma`. -/
theorem exists_critical_lp_above_gamma
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    ∃ pExp : ℝ, max 1 p.γ < pExp ∧
      LpPowerBoundedBefore intervalDomainM pExp T u := by
  obtain ⟨p0, hp0, hseed⟩ :=
    exists_high_critical_lp_power_bounded_before
      hguard hu₀ hsol htrace hbeta hm hchi hthreshold
  let pExp : ℝ := p0 + p.γ
  have hp0_one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hpExp : p0 ≤ pExp := by
    dsimp [pExp]
    linarith [p.hγ]
  have hpHigh : max 1 p.γ < pExp := by
    apply max_lt
    · dsimp [pExp]
      linarith [p.hγ]
    · dsimp [pExp]
      linarith [hp0_one]
  refine ⟨pExp, hpHigh, ?_⟩
  exact critical_lp_power_bounded_before_positive_of_seed
    hu₀ hsol htrace hm hbeta hp0 hseed hpExp

#print axioms lp_power_bounded_before_of_linear_damping
#print axioms critical_bootstrap_linear_damping
#print axioms critical_lp_power_bounded_before_positive_of_seed
#print axioms critical_integratedMoserFirstCrossingStep_positive_of_seed
#print axioms exists_critical_lp_above_gamma

end ShenWork.Paper2.IntervalDomainM

end
