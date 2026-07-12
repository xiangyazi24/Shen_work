import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpSeed
import ShenWork.Paper2.IntervalDomainMCriticalLpBootstrap

/-!
# Horizon-independent finite-power bootstrap in the critical case

This file fixes the quantifier order in the finite-power bootstrap.  A single
critical seed bound is fed into the explicit sharp cross-diffusion coefficient
and the scalar Agmon absorption constant.  The resulting damping coefficient
is chosen before time, hence it supplies one global power strictly above
`gamma`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

private lemma intervalDomainSupNorm_nonneg_global
    (f : intervalDomain.Point → ℝ) :
    0 ≤ intervalDomainSupNorm f := by
  unfold intervalDomainSupNorm
  by_cases hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))
  · exact le_csSup_of_le hbdd ⟨⟨0, le_refl 0, zero_le_one⟩, rfl⟩
      (abs_nonneg _)
  · change 0 ≤ sSup (Set.range fun x : intervalDomain.Point => |f x|)
    rw [Real.sSup_def, dif_neg (by simp [hbdd])]

/-- A fixed global seed coefficient yields a fixed Agmon absorption
coefficient at every larger exponent. -/
theorem global_agmon_absorbed_interpolation_of_seed
    {p : CM2Params} {rho p0 C0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hrho : 0 < rho)
    (hp0 : max 1 (rho * (p.N : ℝ) / 2) < p0)
    (hseed : ∀ t, 0 < t →
      intervalDomain.integral (fun x => (u t x) ^ p0) ≤ C0) :
    ∀ pExp, p0 ≤ pExp → ∀ eps > 0,
      ∃ Ceps : ℝ, ∀ t, 0 < t →
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) + Ceps := by
  intro pExp hpExp eps heps
  let M0 : ℝ := max C0 0
  have hM0_nonneg : 0 ≤ M0 := by
    dsimp [M0]
    exact le_max_right C0 0
  have hseed_bound : ∀ t, 0 < t →
      intervalDomain.integral (fun x => (u t x) ^ p0) ≤ M0 := by
    intro t ht0
    exact (hseed t ht0).trans (le_max_left C0 0)
  have hp0_gt_one : 1 < p0 :=
    lt_of_le_of_lt (le_max_left _ _) hp0
  have hp0_pos : 0 < p0 := lt_trans zero_lt_one hp0_gt_one
  have hpExp_pos : 0 < pExp := lt_of_lt_of_le hp0_pos hpExp
  have hrho_lt_two_p0 : rho < 2 * p0 := by
    have hrhoN_lt : rho * (p.N : ℝ) / 2 < p0 :=
      lt_of_le_of_lt (le_max_right _ _) hp0
    have hN_ge_one_nat : 1 ≤ p.N := Nat.succ_le_of_lt p.hN
    have hN_ge_one : (1 : ℝ) ≤ (p.N : ℝ) := by
      exact_mod_cast hN_ge_one_nat
    have hhalf_le : rho / 2 ≤ rho * (p.N : ℝ) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hN_ge_one hrho.le]
    nlinarith
  refine ⟨scalarSeedAgmonAbsorbConstant M0 pExp p0 rho eps, ?_⟩
  intro t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain p T u v :=
    hglobal.classical hT
  let U : ℝ := intervalDomainSupNorm (u t)
  let S : ℝ := U ^ pExp
  let Y : ℝ := intervalDomain.integral (fun x => (u t x) ^ pExp)
  let G : ℝ := intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm
      (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
  let seed : ℝ := intervalDomain.integral (fun x => (u t x) ^ p0)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ u t x :=
    fun x => (hsol.u_pos' ht0 htT (x := x)).le
  have hf_bdd :
      BddAbove (Set.range fun x : intervalDomain.Point => |u t x|) :=
    ShenWork.IntervalDomainExistence.intervalDomain_solution_slice_abs_bddAbove
      hsol ht
  have hp0_nonneg : 0 ≤ p0 := hp0_pos.le
  have hp_minus_nonneg : 0 ≤ pExp - p0 := sub_nonneg.mpr hpExp
  have hhigh_minus_nonneg : 0 ≤ pExp + rho - p0 := by
    linarith [hp_minus_nonneg, hrho.le]
  have hseed_int : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0))
      volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := p0) hsol ht0 htT
  have hY_int : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
      volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := pExp) hsol ht0 htT
  have hhigh_int : IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ (pExp + rho)))
      volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := pExp + rho) hsol ht0 htT
  have hY_left_int : IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ (p0 + (pExp - p0))))
      volume 0 1 := by
    have hpow : p0 + (pExp - p0) = pExp := by ring
    simpa [hpow] using hY_int
  have hhigh_left_int : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point =>
        (u t x) ^ (p0 + (pExp + rho - p0)))) volume 0 1 := by
    have hpow : p0 + (pExp + rho - p0) = pExp + rho := by ring
    simpa [hpow] using hhigh_int
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact intervalDomainSupNorm_nonneg_global (u t)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Real.rpow_nonneg hU_nonneg pExp
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    exact intervalDomain_integral_u_rpow_nonneg_of_regularity
      (q := pExp) hsol ht0 htT
  have hchain :=
    intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := p) (T := T) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    rw [hchain]
    exact mul_nonneg (sq_nonneg _) <|
      intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT
  have hY_raw :=
    intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
      (f := u t) hf_nonneg hf_bdd
      (pExp := p0) (rho := pExp - p0)
      hp0_nonneg hp_minus_nonneg hY_left_int hseed_int
  have hY_seed : Y ≤ U ^ (pExp - p0) * seed := by
    have hpow : p0 + (pExp - p0) = pExp := by ring
    simpa [Y, U, seed, hpow] using hY_raw
  have hU_theta : U ^ (pExp - p0) =
      S ^ ((pExp - p0) / pExp) := by
    have hmul : pExp * ((pExp - p0) / pExp) = pExp - p0 := by
      field_simp [ne_of_gt hpExp_pos]
    calc
      U ^ (pExp - p0) = U ^ (pExp * ((pExp - p0) / pExp)) := by rw [hmul]
      _ = (U ^ pExp) ^ ((pExp - p0) / pExp) := by
        rw [Real.rpow_mul hU_nonneg]
      _ = S ^ ((pExp - p0) / pExp) := rfl
  have hY_le_seed : Y ≤ M0 * S ^ ((pExp - p0) / pExp) := by
    have hseed_t : seed ≤ M0 := by
      dsimp [seed]
      exact hseed_bound t ht0
    have hcoef_nonneg : 0 ≤ U ^ (pExp - p0) :=
      Real.rpow_nonneg hU_nonneg _
    calc
      Y ≤ U ^ (pExp - p0) * seed := hY_seed
      _ ≤ U ^ (pExp - p0) * M0 :=
        mul_le_mul_of_nonneg_left hseed_t hcoef_nonneg
      _ = M0 * S ^ ((pExp - p0) / pExp) := by rw [hU_theta]; ring
  have hsup_step : S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := by
    have hstep := intervalDomain_supNorm_rpow_le_energy_plus_gradient
      (params := p) (T := T) (t := t) (pExp := pExp)
      (u := u) (v := v) hsol ht0 htT hpExp_pos
    simpa [S, U, Y, G] using hstep
  have hsqrtY_le : Real.sqrt Y ≤
      Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) :=
    Real.sqrt_le_sqrt hY_le_seed
  have hYterm_le : 2 * Y ≤
      2 * (M0 * S ^ ((pExp - p0) / pExp)) :=
    mul_le_mul_of_nonneg_left hY_le_seed (by norm_num)
  have hsqrtterm_le : 2 * Real.sqrt Y * Real.sqrt G ≤
      2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) * Real.sqrt G := by
    have hmul := mul_le_mul_of_nonneg_right hsqrtY_le (Real.sqrt_nonneg G)
    nlinarith
  have hSineq : S ≤
      2 * M0 * S ^ ((pExp - p0) / pExp) +
        2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) * Real.sqrt G := by
    calc
      S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := hsup_step
      _ ≤ 2 * (M0 * S ^ ((pExp - p0) / pExp)) +
          2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) * Real.sqrt G :=
        add_le_add hYterm_le hsqrtterm_le
      _ = _ := by ring
  have hhigh_raw :=
    intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
      (f := u t) hf_nonneg hf_bdd
      (pExp := p0) (rho := pExp + rho - p0)
      hp0_nonneg hhigh_minus_nonneg hhigh_left_int hseed_int
  have hhigh_seed :
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        U ^ (pExp + rho - p0) * seed := by
    have hpow : p0 + (pExp + rho - p0) = pExp + rho := by ring
    simpa [U, seed, hpow] using hhigh_raw
  have hU_alpha : U ^ (pExp + rho - p0) =
      S ^ ((pExp + rho - p0) / pExp) := by
    have hmul : pExp * ((pExp + rho - p0) / pExp) =
        pExp + rho - p0 := by
      field_simp [ne_of_gt hpExp_pos]
    calc
      U ^ (pExp + rho - p0) =
          U ^ (pExp * ((pExp + rho - p0) / pExp)) := by rw [hmul]
      _ = (U ^ pExp) ^ ((pExp + rho - p0) / pExp) := by
        rw [Real.rpow_mul hU_nonneg]
      _ = S ^ ((pExp + rho - p0) / pExp) := rfl
  have hhigh_le_seed :
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        M0 * S ^ ((pExp + rho - p0) / pExp) := by
    have hseed_t : seed ≤ M0 := by
      dsimp [seed]
      exact hseed_bound t ht0
    have hcoef_nonneg : 0 ≤ U ^ (pExp + rho - p0) :=
      Real.rpow_nonneg hU_nonneg _
    calc
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
          U ^ (pExp + rho - p0) * seed := hhigh_seed
      _ ≤ U ^ (pExp + rho - p0) * M0 :=
        mul_le_mul_of_nonneg_left hseed_t hcoef_nonneg
      _ = M0 * S ^ ((pExp + rho - p0) / pExp) := by rw [hU_alpha]; ring
  have hscalar : M0 * S ^ ((pExp + rho - p0) / pExp) ≤
      eps * G + scalarSeedAgmonAbsorbConstant M0 pExp p0 rho eps :=
    scalar_seed_agmon_absorb hM0_nonneg hS_nonneg hG_nonneg
      hp0_pos hpExp hrho hrho_lt_two_p0 heps hSineq
  exact hhigh_le_seed.trans (by simpa [G] using hscalar)

set_option maxHeartbeats 800000

/-- The seed-relative bootstrap at a fixed target exponent has a single
autonomous damping constant on the whole positive time axis. -/
theorem critical_bootstrap_linear_damping_global
    {p : CM2Params} {p0 pExp C0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hm : p.m = 1) (hbeta : 1 ≤ p.β)
    (hp0 : max 1 (p.γ * (p.N : ℝ) / 2) < p0)
    (hseed : ∀ t, 0 < t →
      intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0)
    (hpExp : p0 ≤ pExp) :
    ∃ D, ∀ t, 0 < t →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        intervalDomainLpEnergy pExp u t ≤ D := by
  have hp0_one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hpExp_one : 1 < pExp := hp0_one.trans_le hpExp
  have hpExp_pos : 0 < pExp := zero_lt_one.trans hpExp_one
  have hglobal' : IsPaper2GlobalClassicalSolution intervalDomain p u v := by
    intro T hT
    exact classicalSolution_intervalDomain_of_m_eq_one hm (hglobal.classical hT)
  have hseed' : ∀ t, 0 < t →
      intervalDomain.integral (fun x => (u t x) ^ p0) ≤ C0 := by
    intro t ht0
    simpa [intervalDomainM, intervalDomain] using hseed t ht0
  let A0 : ℝ := pExp - 1
  let chiBound : ℝ := |p.χ₀| * (pExp - 1)
  let epsCross : ℝ := A0 / (2 * (chiBound + 1))
  have hA0 : 0 < A0 := by dsimp [A0]; linarith
  have hchiBound : 0 ≤ chiBound := by
    dsimp [chiBound]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hden : 0 < 2 * (chiBound + 1) := by nlinarith
  have hepsCross : 0 < epsCross := by
    dsimp [epsCross]
    exact div_pos hA0 hden
  have habsorbHalf : chiBound * epsCross ≤ A0 / 2 := by
    simpa [epsCross] using
      intervalDomain_young_absorption_coefficient_half
        (A := A0) (chiBound := chiBound) hA0 hchiBound
  have hAabs : 0 < A0 - chiBound * epsCross := by nlinarith
  let cGrad : ℝ := (pExp / 2) ^ 2
  have hcGrad : 0 < cGrad := by
    dsimp [cGrad]
    exact sq_pos_of_pos (by linarith)
  let Acoef : ℝ := (A0 - chiBound * epsCross) / cGrad
  have hAcoef : 0 < Acoef := by
    dsimp [Acoef]
    exact div_pos hAabs hcGrad
  let Ccross : ℝ := intervalDomainSharpCrossDiffusionConstant p pExp epsCross
  let Klow : ℝ := p.a + 1
  have hKlow : 0 < Klow := by dsimp [Klow]; linarith [p.ha]
  let K : ℝ := max 1 (chiBound * Ccross + Klow)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let epsInterp : ℝ := Acoef / (2 * K)
  have hepsInterp : 0 < epsInterp := by
    dsimp [epsInterp]
    exact div_pos hAcoef (mul_pos (by norm_num) hK)
  obtain ⟨Ceps, hinterp⟩ :=
    global_agmon_absorbed_interpolation_of_seed
      hglobal' p.hγ hp0 hseed' pExp hpExp epsInterp hepsInterp
  let D : ℝ := K * Ceps + Klow
  refine ⟨D, ?_⟩
  intro t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsolM : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    hglobal.classical hT
  have hsol : IsPaper2ClassicalSolution intervalDomain p T u v :=
    classicalSolution_intervalDomain_of_m_eq_one hm hsolM
  let Y : ℝ := (1 / pExp) *
    deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
  let G : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
  let H : ℝ := intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
  let E : ℝ := intervalDomainLpEnergy pExp u t
  let Z : ℝ := intervalDomain.integral (fun x => (u t x) ^ (pExp + p.γ))
  let R : ℝ := intervalDomainLpLogisticIntegral p pExp u t
  have hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s) :=
    intervalDomain_lp_energy_hLpTime_frontier (q := pExp) hsol
  have hPDEIntegral := intervalDomain_lp_energy_hPDEIntegral_of_regularity
    (pExp := pExp) hsol ht0 htT
  have hIBP := intervalDomain_lp_energy_hIBP_of_regularity
    (pExp := pExp) hsol ht0 htT
  have hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1
  have hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1
  have hDiffusionCoercive :
      A0 * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t := by
    simpa [A0] using
      intervalDomain_lp_energy_hDiffusionCoercive_of_regularity
        (params := p) (T := T) (pExp := pExp)
        (u := u) (v := v) hsol t ht0 htT
  have hCrossControl :
      -p.χ₀ * intervalDomainLpChemotaxisIntegral p pExp u v t ≤
        chiBound * intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) := by
    simpa [chiBound] using
      intervalDomain_lp_energy_hCrossControl_of_regularity
        (params := p) (T := T) (pExp := pExp)
        (u := u) (v := v) hpExp_one hsol t ht0 htT
  have hbasic : Y + A0 * G ≤
      chiBound * intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) + R := by
    simpa [Y, G, R, intervalDomainLpEnergy] using
      intervalDomain_lp_energy_gradient_inequality_of_frontiers
        (params := p) (T := T) (pExp := pExp)
        (A := A0) (chiBound := chiBound) (t := t)
        (u := u) (v := v) (ne_of_gt hpExp_pos) ht0 htT hLpTime
        hPDEIntegral hIBP hNeuR hNeuL hDiffusionCoercive hCrossControl
  have hCrossAt :
      intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        epsCross * G + Ccross * Z := by
    simpa [G, Z, Ccross, intervalDomainLpWeightedGradientDissipation] using
      intervalDomain_crossDiffusionBootstrapEstimate_sharp_explicit
        hsol hbeta hepsCross hpExp_one t ht0 htT
  have hpre : Y + (A0 - chiBound * epsCross) * G ≤
      chiBound * Ccross * Z + R := by
    have hscaled := mul_le_mul_of_nonneg_left hCrossAt hchiBound
    nlinarith
  have hLogistic : R ≤ p.a * E := by
    simpa [R, E] using
      intervalDomain_lp_logisticIntegral_le_a_energy_of_regularity
        hsol ht0 htT
  have hp_int : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
      volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := pExp) hsol ht0 htT
  have hq_int : IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ (pExp + p.γ)))
      volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := pExp + p.γ) hsol ht0 htT
  have hpoint : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp) y ≤
        intervalDomainLift
          (fun x : intervalDomain.Point => (u t x) ^ (pExp + p.γ)) y + 1 := by
    intro y hy
    have hu_nonneg : 0 ≤ u t (⟨y, hy⟩ : intervalDomain.Point) :=
      (hsol.u_pos' ht0 htT).le
    simp only [intervalDomainLift, dif_pos hy]
    exact ShenWork.Paper2.IntervalDomainLpMonotonicity.rpow_le_one_add_rpow_of_nonneg_of_le
      hu_nonneg hpExp_pos.le (by linarith [p.hγ])
  have hintegral : intervalDomain.integral
      (fun x : intervalDomain.Point => (u t x) ^ pExp) ≤
        intervalDomain.integral
          (fun x : intervalDomain.Point => (u t x) ^ (pExp + p.γ)) + 1 := by
    change intervalDomainIntegral _ ≤ intervalDomainIntegral _ + 1
    unfold intervalDomainIntegral
    have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hp_int (hq_int.add intervalIntegrable_const) hpoint
    have hadd :
        (∫ y in (0 : ℝ)..1,
          intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (pExp + p.γ)) y + 1) =
        (∫ y in (0 : ℝ)..1,
          intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (pExp + p.γ)) y) + 1 := by
      rw [intervalIntegral.integral_add hq_int intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    simpa [hadd] using hle
  have henergyEq : E = intervalDomain.integral
      (fun x : intervalDomain.Point => (u t x) ^ pExp) := by
    dsimp [E]
    exact intervalDomainLpEnergy_eq_power_of_regularity hsol ht0 htT
  have hLower : Klow * E ≤ Klow * Z + Klow := by
    rw [henergyEq]
    have hscaled := mul_le_mul_of_nonneg_left hintegral hKlow.le
    calc
      Klow * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
          Klow * (intervalDomain.integral
            (fun x => (u t x) ^ (pExp + p.γ)) + 1) := hscaled
      _ = Klow * Z + Klow := by dsimp [Z]; ring
  have hGrad : H = cGrad * G := by
    dsimp [H, cGrad, G]
    exact intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := p) (T := T) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT
  have hAgrad : Acoef * H = (A0 - chiBound * epsCross) * G := by
    rw [hGrad]
    dsimp [Acoef]
    field_simp [ne_of_gt hcGrad]
  have hcore : Y + Acoef * H + E ≤ K * Z + Klow := by
    have hcoeff : chiBound * Ccross + Klow ≤ K := le_max_right _ _
    have hZ : 0 ≤ Z := by
      dsimp [Z]
      exact intervalDomain_integral_u_rpow_nonneg_of_regularity
        (q := pExp + p.γ) hsol ht0 htT
    have hcoeffZ := mul_le_mul_of_nonneg_right hcoeff hZ
    rw [hAgrad]
    nlinarith
  have hInterp : Z ≤ epsInterp * H + Ceps := by
    simpa [Z, H] using hinterp t ht0
  have hH : 0 ≤ H := by
    rw [hGrad]
    exact mul_nonneg hcGrad.le
      (intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT)
  have hscaledInterp : K * Z ≤ K * (epsInterp * H + Ceps) :=
    mul_le_mul_of_nonneg_left hInterp hK.le
  have hKeps : K * epsInterp = Acoef / 2 := by
    dsimp [epsInterp]
    field_simp [ne_of_gt hK]
  dsimp [D]
  dsimp [Y, E] at hcore
  nlinarith

/-- A global linear damping inequality controls the target power after time
one.  No initial trace estimate is needed in this late-time reducer. -/
theorem lp_power_bounded_global_after_one_of_linear_damping
    {p : CM2Params} {pExp D : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hp : 1 < pExp)
    (hdamp : ∀ t, 0 < t →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        intervalDomainLpEnergy pExp u t ≤ D) :
    ∃ C, ∀ t, 1 ≤ t →
      intervalDomainM.integral (fun x => (u t x) ^ pExp) ≤ C := by
  let E : ℝ → ℝ := fun s => intervalDomainLpEnergy pExp u s
  let K : ℝ := max 0 D
  have hDK : D ≤ K := le_max_right _ _
  have hsol2 : IsPaper2ClassicalSolution intervalDomainM p 2 u v :=
    hglobal.classical (by norm_num)
  let E1 : ℝ := E 1
  let C : ℝ := max K E1
  refine ⟨C, ?_⟩
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    hglobal.classical hT
  have hEcont : ContinuousOn E (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact (lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2).continuousAt.continuousWithinAt
  have hEderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, K < E s →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt E d s := by
    intro s hs hKs
    have hD := hdamp s hs.1
    have hinv : 0 < 1 / pExp := one_div_pos.mpr (zero_lt_one.trans hp)
    refine ⟨deriv E s, ?_, ?_⟩
    · dsimp [E] at hD ⊢
      nlinarith
    · simpa [E] using lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2
  have hEt : E t ≤ C := by
    by_cases hle : E t ≤ K
    · exact hle.trans (le_max_left _ _)
    · push Not at hle
      rcases eq_or_lt_of_le ht1 with rfl | ht1lt
      · exact le_max_right _ _
      · have habove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < E s :=
          threshold_persists_below_of_hasDerivAt_nonpos
            ht0 htT hEcont hEderiv hle
        have hsubIoo : Set.Icc (1 : ℝ) t ⊆ Set.Ioo (0 : ℝ) T :=
          fun z hz => ⟨lt_of_lt_of_le zero_lt_one hz.1,
            lt_of_le_of_lt hz.2 htT⟩
        have hanti : AntitoneOn E (Set.Icc (1 : ℝ) t) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
            (hEcont.mono hsubIoo)
          · intro z hz
            rw [interior_Icc] at hz
            exact (lpEnergy_hasDerivAt_of_solution hsol
              (lt_trans zero_lt_one hz.1) (lt_trans hz.2 htT)).differentiableAt.differentiableWithinAt
          · intro z hz
            rw [interior_Icc] at hz
            have hzIoo : z ∈ Set.Ioo (0 : ℝ) T :=
              ⟨lt_trans zero_lt_one hz.1, lt_trans hz.2 htT⟩
            have hzIoc : z ∈ Set.Ioc (0 : ℝ) t :=
              ⟨lt_trans zero_lt_one hz.1, hz.2.le⟩
            obtain ⟨d, hd, hder⟩ := hEderiv z hzIoo (habove z hzIoc)
            rw [hder.deriv]
            exact hd
        exact (hanti (Set.left_mem_Icc.mpr ht1)
          (Set.right_mem_Icc.mpr ht1) ht1).trans (le_max_right _ _)
  have hdomain : intervalDomainM.integral (fun x => (u t x) ^ pExp) = E t := by
    change intervalDomain.integral (fun x => (u t x) ^ pExp) = E t
    rw [show E t = ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ pExp by
      dsimp [E]
      exact lpEnergy_eq_lift_power_of_solution hsol ht0 htT]
    exact intervalDomain_integral_rpow_eq_lift_integral
  rw [hdomain]
  exact hEt

/-- A global critical seed controls every larger finite power with one
horizon-independent constant. -/
theorem critical_lp_power_bounded_global_positive_of_seed
    {p : CM2Params} {p0 pExp C0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hm : p.m = 1) (hbeta : 1 ≤ p.β)
    (hp0 : max 1 (p.γ * (p.N : ℝ) / 2) < p0)
    (hseed : ∀ t, 0 < t →
      intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0)
    (hpExp : p0 ≤ pExp) :
    ∃ C, ∀ t, 0 < t →
      intervalDomainM.integral (fun x => (u t x) ^ pExp) ≤ C := by
  obtain ⟨D, hdamp⟩ := critical_bootstrap_linear_damping_global
    hglobal hm hbeta hp0 hseed hpExp
  have hp0_one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hp : 1 < pExp := hp0_one.trans_le hpExp
  obtain ⟨Clate, hlate⟩ :=
    lp_power_bounded_global_after_one_of_linear_damping hglobal hp hdamp
  have hsol2 : IsPaper2ClassicalSolution intervalDomainM p 2 u v :=
    hglobal.classical (by norm_num)
  have hseed2 : LpPowerBoundedBefore intervalDomainM p0 2 u :=
    ⟨C0, fun t ht0 _ht2 => hseed t ht0⟩
  obtain ⟨Cearly, hearly⟩ :=
    critical_lp_power_bounded_before_positive_of_seed
      hu₀ hsol2 htrace hm hbeta hp0 hseed2 hpExp
  refine ⟨max Cearly Clate, ?_⟩
  intro t ht0
  by_cases ht2 : t < 2
  · exact (hearly t ht0 ht2).trans (le_max_left _ _)
  · have ht1 : 1 ≤ t := by linarith
    exact (hlate t ht1).trans (le_max_right _ _)

/-- Under the critical small-sensitivity condition there is one globally
bounded power strictly above `gamma`. -/
theorem exists_critical_lp_above_gamma_global
    {p : CM2Params}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    ∃ pExp : ℝ, max 1 p.γ < pExp ∧
      ∃ C, ∀ t, 0 < t →
        intervalDomainM.integral (fun x => (u t x) ^ pExp) ≤ C := by
  obtain ⟨p0, hp0, C0, hseed⟩ :=
    exists_high_critical_lp_power_bounded_global
      hguard hu₀ hglobal htrace hbeta hm hchi hthreshold
  let pExp : ℝ := p0 + p.γ
  have hpExp : p0 ≤ pExp := by dsimp [pExp]; linarith [p.hγ]
  have hp0_one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hpHigh : max 1 p.γ < pExp := by
    apply max_lt
    · dsimp [pExp]
      linarith [p.hγ]
    · dsimp [pExp]
      linarith [hp0_one]
  exact ⟨pExp, hpHigh,
    critical_lp_power_bounded_global_positive_of_seed
      hu₀ hglobal htrace hm hbeta hp0 hseed hpExp⟩

#print axioms global_agmon_absorbed_interpolation_of_seed
#print axioms critical_bootstrap_linear_damping_global
#print axioms lp_power_bounded_global_after_one_of_linear_damping
#print axioms critical_lp_power_bounded_global_positive_of_seed
#print axioms exists_critical_lp_above_gamma_global

end ShenWork.Paper2.IntervalDomainM

end
