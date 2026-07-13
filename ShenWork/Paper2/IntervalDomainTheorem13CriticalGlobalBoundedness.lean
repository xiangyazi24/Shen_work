import ShenWork.Paper2.IntervalDomainTheorem13CriticalThreshold
import ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap
import ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness

/-!
# Horizon-independent bounds for the critical branches of Theorem 1.3

The scalar threshold first selects one seed exponent.  Its autonomous energy
remainder gives a uniform seed on the whole positive time axis.  The explicit
seed-relative Agmon constant then gives one autonomous target inequality at a
single exponent above the restarted endpoint thresholds.  No all-exponent
Moser package is used.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CriticalGlobalBoundedness

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMRestartedLpLinfGeneral
open ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer
open ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
open ShenWork.Paper2.IntervalDomainTheorem13CriticalSeed
open ShenWork.Paper2.IntervalDomainTheorem13CriticalThreshold
open ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap

/-- The critical (iii) threshold produces a single all-time seed bound. -/
theorem exists_case_iii_seed_power_global
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p))) :
    ∃ p0, theorem13CriticalQStar p < p0 ∧
      ∃ C0, ∀ t, 0 < t →
        intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0 := by
  obtain ⟨p0, hqp0, hcoef⟩ := exists_case_iii_seed_exponent
    p hN hb hchi hbeta hcrit hthreshold
  have hp0 : 1 < p0 :=
    lt_of_le_of_lt (one_le_theorem13CriticalQStar p) hqp0
  have hdamp : ∀ t, 0 < t →
      (1 / p0) * deriv (fun τ => intervalDomainLpEnergy p0 u τ) t +
        intervalDomainLpEnergy p0 u t ≤
          criticalCaseIIIDampingConstant p p0 := by
    intro t ht0
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (critical_case_iii_lp_energy_damping
      (hglobal.classical hT) hchi hbeta hcrit hp0 hcoef).2 t ht0 htT
  have hearly : LpPowerBoundedBefore intervalDomainM p0 2 u :=
    critical_case_iii_lp_power_bounded_before hu₀
      (hglobal.classical (by norm_num)) htrace hchi hbeta hcrit hp0 hcoef
  exact ⟨p0, hqp0,
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hp0 hdamp hearly⟩

/-- The corrected critical (iv) threshold produces a single all-time seed. -/
theorem exists_case_iv_seed_power_global
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))) :
    ∃ p0, theorem13CriticalQStar p < p0 ∧
      2 - 2 * p.m < p0 ∧
      ∃ C0, ∀ t, 0 < t →
        intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0 := by
  obtain ⟨p0, hqp0, hvalid0, hcoef⟩ := exists_case_iv_seed_exponent
    p hN hb hchi hbeta hcrit hvalid hthreshold
  have hp0 : 1 < p0 :=
    lt_of_le_of_lt (one_le_theorem13CriticalQStar p) hqp0
  have hdamp : ∀ t, 0 < t →
      (1 / p0) * deriv (fun τ => intervalDomainLpEnergy p0 u τ) t +
        intervalDomainLpEnergy p0 u t ≤
          criticalCaseIVDampingConstant p p0 := by
    intro t ht0
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (critical_case_iv_lp_energy_damping
      (hglobal.classical hT) hbeta hcrit hp0 hvalid0 hcoef).2 t ht0 htT
  have hearly : LpPowerBoundedBefore intervalDomainM p0 2 u :=
    critical_case_iv_lp_power_bounded_before hu₀
      (hglobal.classical (by norm_num)) htrace hbeta hcrit hp0 hvalid0 hcoef
  exact ⟨p0, hqp0, hvalid0,
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hp0 hdamp hearly⟩

/-- Critical alternative (iii) has a horizon-independent global supremum
bound at the corrected interval constant. -/
theorem boundedGlobal_critical_case_iii
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p))) :
    IsPaper2Bounded intervalDomainM u := by
  obtain ⟨p0, hqp0, C0, hseed⟩ := exists_case_iii_seed_power_global
    hN hb hu₀ hglobal htrace hchi hbeta hcrit hthreshold
  let P : ℝ := criticalEndpointExponent p p0
  let Q : ℝ := P / p.m
  let epsCross : ℝ := 0
  let Kcross : ℝ := criticalCaseIIICoefficient p P
  have hp0pos : 0 < p0 := (theorem13CriticalQStar_pos p).trans hqp0
  have hp0P : p0 ≤ P := (criticalEndpointExponent_gt_seed p p0).le
  have hP : 1 < P := one_lt_two.trans (criticalEndpointExponent_gt_two p p0)
  have halpha2 : p.α < 2 * p0 := by
    have hqeq := theorem13CriticalQStar_eq_interval p hN
    have halphaHalf : p.α / 2 ≤ theorem13CriticalQStar p := by
      rw [hqeq]
      exact le_max_right _ _
    linarith
  have hepsGap : epsCross < P - 1 := by dsimp [epsCross]; linarith
  have hsP : 1 < (P + p.α) / p.γ := by
    rw [one_lt_div p.hγ, hcrit]
    linarith [p.hm]
  have hKcross : 0 ≤ Kcross := by
    dsimp [Kcross, criticalCaseIIICoefficient]
    have hden : 0 < P - 1 + p.m := by linarith [p.hm]
    exact mul_nonneg
      (div_nonneg (mul_nonneg hchi.le (sub_pos.mpr hP).le) hden.le)
      (add_nonneg p.hν.le
        (mul_nonneg (Psi_beta_nonneg hbeta)
          (theorem13CriticalProfile_pos p hsP).le))
  have hdamp : ∀ t, 0 < t →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤
          criticalTargetDampingConstant p p0 P epsCross Kcross C0 := by
    intro t ht0
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    have hsol := hglobal.classical hT
    have hcross := critical_case_iii_cross_bound
      hsol hchi hbeta hcrit hP
    exact (critical_target_lp_energy_damping_of_bound hsol hP hp0pos hp0P
      halpha2 (fun s hs0 _ => hseed s hs0) hepsGap hKcross (by
        intro s hs0 hsT
        simpa [epsCross, Kcross] using hcross s hs0 hsT)).2 t ht0 htT
  have hsol2 := hglobal.classical (show (0 : ℝ) < 2 by norm_num)
  have hcross2 := critical_case_iii_cross_bound hsol2 hchi hbeta hcrit hP
  have hearly : LpPowerBoundedBefore intervalDomainM P 2 u :=
    critical_target_lp_power_bounded_before_of_cross hu₀ hsol2 htrace hP
      hp0pos hp0P halpha2 ⟨C0, fun s hs0 _ => hseed s hs0⟩ hepsGap
      hKcross (by
        intro s hs0 hs2
        simpa [epsCross, Kcross] using hcross2 s hs0 hs2)
  obtain ⟨C, hpower⟩ :=
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hP hdamp hearly
  have hmP : p.m < P := criticalEndpointExponent_gt_m p p0
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  exact boundedGlobal_of_lp_restarted_affine_general hglobal hP hQ hmQ
    (criticalEndpointExponent_ge_gamma p p0) hpower

/-- Corrected critical alternative (iv) has a horizon-independent global
supremum bound. -/
theorem boundedGlobal_critical_case_iv_corrected
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))) :
    IsPaper2Bounded intervalDomainM u := by
  obtain ⟨p0, hqp0, hvalid0, C0, hseed⟩ :=
    exists_case_iv_seed_power_global hN hb hu₀ hglobal htrace hchi hbeta
      hcrit hvalid hthreshold
  let P : ℝ := criticalEndpointExponent p p0
  let Q : ℝ := P / p.m
  let epsCross : ℝ := (P - 1) / 2
  let Kcross : ℝ :=
    ((|p.χ₀| * (P - 1)) ^ 2 / (4 * epsCross) *
      Theta_beta (2 * p.β - 1) * theorem13CriticalProfile p P)
  have hp0pos : 0 < p0 := (theorem13CriticalQStar_pos p).trans hqp0
  have hp0P : p0 ≤ P := (criticalEndpointExponent_gt_seed p p0).le
  have hP : 1 < P := one_lt_two.trans (criticalEndpointExponent_gt_two p p0)
  have hvalidP : 2 - 2 * p.m < P :=
    hvalid0.trans (criticalEndpointExponent_gt_seed p p0)
  have halpha2 : p.α < 2 * p0 := by
    have hqeq := theorem13CriticalQStar_eq_interval p hN
    have halphaHalf : p.α / 2 ≤ theorem13CriticalQStar p := by
      rw [hqeq]
      exact le_max_right _ _
    linarith
  have heps : 0 < epsCross := by dsimp [epsCross]; linarith
  have hepsGap : epsCross < P - 1 := by dsimp [epsCross]; linarith
  have hsP : 1 < (P + p.α) / p.γ := by
    rw [one_lt_div p.hγ, hcrit]
    linarith
  have hbeta' : 0 ≤ 2 * p.β - 1 := by linarith
  have hKcross : 0 ≤ Kcross := by
    dsimp [Kcross]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (sq_nonneg _)
        (mul_nonneg (by norm_num) heps.le)) (Theta_beta_nonneg hbeta'))
      (theorem13CriticalProfile_pos p hsP).le
  have hdamp : ∀ t, 0 < t →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤
          criticalTargetDampingConstant p p0 P epsCross Kcross C0 := by
    intro t ht0
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    have hsol := hglobal.classical hT
    have hcross := critical_case_iv_cross_bound
      hsol hbeta hcrit hP hvalidP heps
    exact (critical_target_lp_energy_damping_of_bound hsol hP hp0pos hp0P
      halpha2 (fun s hs0 _ => hseed s hs0) hepsGap hKcross (by
        intro s hs0 hsT
        simpa [Kcross, epsCross] using hcross s hs0 hsT)).2 t ht0 htT
  have hsol2 := hglobal.classical (show (0 : ℝ) < 2 by norm_num)
  have hcross2 := critical_case_iv_cross_bound
    hsol2 hbeta hcrit hP hvalidP heps
  have hearly : LpPowerBoundedBefore intervalDomainM P 2 u :=
    critical_target_lp_power_bounded_before_of_cross hu₀ hsol2 htrace hP
      hp0pos hp0P halpha2 ⟨C0, fun s hs0 _ => hseed s hs0⟩ hepsGap
      hKcross (by
        intro s hs0 hs2
        simpa [Kcross, epsCross] using hcross2 s hs0 hs2)
  obtain ⟨C, hpower⟩ :=
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hP hdamp hearly
  have hmP : p.m < P := criticalEndpointExponent_gt_m p p0
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  exact boundedGlobal_of_lp_restarted_affine_general hglobal hP hQ hmQ
    (criticalEndpointExponent_ge_gamma p p0) hpower

#print axioms exists_case_iii_seed_power_global
#print axioms exists_case_iv_seed_power_global
#print axioms boundedGlobal_critical_case_iii
#print axioms boundedGlobal_critical_case_iv_corrected

end ShenWork.Paper2.IntervalDomainTheorem13CriticalGlobalBoundedness

end
