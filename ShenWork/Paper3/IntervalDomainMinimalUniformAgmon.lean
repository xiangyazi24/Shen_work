import ShenWork.Paper3.IntervalDomainMinimalEventualLp
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpBootstrap

/-!
# Uniform seed-relative Agmon absorption

The Paper 2 theorem exposes an existential coefficient after the orbit.  Its
proof is in fact explicit.  This version states that explicit coefficient so
it can be selected before a minimal-model orbit is quantified.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

namespace ShenWork.Paper3

noncomputable section

private lemma intervalDomainSupNorm_nonneg_uniformAgmon
    (f : intervalDomain.Point → ℝ) :
    0 ≤ intervalDomainSupNorm f := by
  unfold intervalDomainSupNorm
  by_cases hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))
  · exact le_csSup_of_le hbdd ⟨⟨0, le_refl 0, zero_le_one⟩, rfl⟩
      (abs_nonneg _)
  · change 0 ≤ sSup (Set.range fun x : intervalDomain.Point => |f x|)
    rw [Real.sSup_def, dif_neg (by simp [hbdd])]

set_option maxHeartbeats 800000 in
/-- Explicit seed-relative Agmon absorption.  The rightmost coefficient uses
only `C0` and the displayed scalar parameters, not the solution orbit. -/
theorem intervalDomain_uniform_agmon_absorbed_of_seed
    {p : CM2Params} {rho p0 C0 pExp eps : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hrho : 0 < rho)
    (hp0 : max 1 (rho * (p.N : ℝ) / 2) < p0)
    (hseed : ∀ t, 0 < t →
      intervalDomain.integral (fun x => (u t x) ^ p0) ≤ C0)
    (hpExp : p0 ≤ pExp) (heps : 0 < eps) :
    ∀ t, 0 < t →
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        eps * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
        scalarSeedAgmonAbsorbConstant (max C0 0) pExp p0 rho eps := by
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
    exact intervalDomainSupNorm_nonneg_uniformAgmon (u t)
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
  exact hhigh_le_seed.trans (by simpa [G, M0] using hscalar)

#print axioms intervalDomain_uniform_agmon_absorbed_of_seed

end

end ShenWork.Paper3
