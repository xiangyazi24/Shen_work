import ShenWork.Paper3.EventualLinearDamping
import ShenWork.Paper3.EventualGlobalStability
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpSeed

/-!
# Orbit-independent eventual `L^p` absorption in the minimal model

The critical Paper 2 energy estimate originally chooses its mass constant
from the initial datum.  On the physical-mass minimal branch that constant is
exactly the prescribed equilibrium mass.  This file repeats the last energy
closure with that mass fixed before the orbit is quantified, then applies the
scalar eventual-damping lemma.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainM

namespace ShenWork.Paper3

noncomputable section

set_option maxHeartbeats 800000 in

/-- At a fixed critical seed exponent, physical mass produces one damping
constant before any global orbit is chosen. -/
theorem exists_minimal_critical_lp_damping_constant
    (p : CM2Params) {pExp uStar : ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hp : 1 < pExp)
    (hupper : p.χ₀ < (2 * p.β - 1) / pExp)
    (huStar : 0 < uStar) :
    ∃ K, 0 ≤ K ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomain p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
        ∀ t, 0 < t →
          (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
            intervalDomainLpEnergy pExp u t ≤ K := by
  let eta : ℝ := 2 * p.β - 1
  let D : ℝ := (pExp - 1) / 2
  let Acoef : ℝ := (pExp - 1) * p.χ₀ * eta / pExp
  let Bcoef : ℝ := (pExp - 1) * p.χ₀ ^ 2 / 2
  let Hcoef : ℝ := Acoef - Bcoef
  let cY : ℝ := (pExp - 1) * p.χ₀ * p.μ / pExp
  let theta : ℝ := Bcoef / Hcoef
  let delta : ℝ := D * (1 - theta)
  have hp0 : 0 < pExp := lt_trans zero_lt_one hp
  have hp1 : 0 < pExp - 1 := sub_pos.mpr hp
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hD : 0 < D := div_pos hp1 (by norm_num)
  have hBcoef : 0 < Bcoef := by
    dsimp [Bcoef]
    positivity
  have hgap : 0 < Hcoef - Bcoef := by
    have hsmall : 0 < eta / pExp - p.χ₀ := by
      dsimp [eta] at hupper ⊢
      linarith
    have heq : Hcoef - Bcoef =
        (pExp - 1) * p.χ₀ * (eta / pExp - p.χ₀) := by
      dsimp [Hcoef, Acoef, Bcoef]
      ring
    rw [heq]
    positivity
  have hHcoef : 0 < Hcoef := lt_trans hBcoef (sub_pos.mp hgap)
  have htheta : 0 < theta := div_pos hBcoef hHcoef
  have htheta1 : theta < 1 := by
    rw [div_lt_one hHcoef]
    linarith
  have hdelta : 0 < delta :=
    mul_pos hD (sub_pos.mpr htheta1)
  have hcY : 0 ≤ cY := by
    dsimp [cY]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hp1.le hchi.le) p.hμ.le) hp0.le
  let Bmain : ℝ := p.a + cY + 1
  have hBmain : 0 < Bmain := by
    dsimp [Bmain]
    linarith [p.ha, hcY]
  obtain ⟨Cagmon, hCagmon, hagmon⟩ :=
    unitIntervalPositiveAgmonInterpolation pExp hp (delta / Bmain)
      (div_pos hdelta hBmain)
  let K : ℝ := Bmain * Cagmon * uStar ^ pExp
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hBmain.le hCagmon.le)
      (Real.rpow_nonneg huStar.le _)
  refine ⟨K, hK, ?_⟩
  intro u v huv hmass t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
      p hm (huv.1.classical hT)
  let Y : ℝ := intervalDomainLpEnergy pExp u t
  let G : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
  let J : ℝ := descentVGradient pExp (2 * p.β) u v t
  let Z : ℝ := intervalDomain.integral (fun x => (u t x) ^ (pExp + p.α))
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hYeq : Y = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ pExp := by
    dsimp [Y]
    exact lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  have hGeq : G = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (pExp - 2) *
        |deriv (intervalDomainLift (u t)) x| ^ 2 := by
    dsimp [G]
    exact weightedDissipation_eq_lift pExp u t
  have hYdomain : Y =
      intervalDomain.integral (fun x => (u t x) ^ pExp) := by
    rw [hYeq]
    exact (intervalDomain_integral_rpow_eq_lift_integral
      (q := pExp) (f := u t)).symm
  have hYnonneg : 0 ≤ Y := by
    rw [hYeq]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hGnonneg : 0 ≤ G := by
    rw [hGeq]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (sq_nonneg _))
  have hJnonneg : 0 ≤ J := by
    dsimp [J]
    exact descentVGradient_nonneg_of_solution hsol ht0 htT
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    unfold intervalDomain intervalDomainIntegral
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact Real.rpow_nonneg (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
  have hell := critical_elliptic_gradient_control
    (p := p) (T := T) (t := t) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT hbeta hp hchi
  dsimp only at hell
  rw [← hGeq, ← hYeq] at hell
  change Hcoef * J ≤ D * G + cY * Y at hell
  have hthetaH : theta * Hcoef = Bcoef := by
    dsimp [theta]
    field_simp [ne_of_gt hHcoef]
  have hBJ : Bcoef * J ≤ theta * D * G + cY * Y := by
    have hmul := mul_le_mul_of_nonneg_left hell htheta.le
    have htheta_le : theta ≤ 1 := htheta1.le
    have hcYY : 0 ≤ cY * Y := mul_nonneg hcY hYnonneg
    calc
      Bcoef * J = theta * (Hcoef * J) := by rw [← hthetaH]; ring
      _ ≤ theta * (D * G + cY * Y) := hmul
      _ = theta * D * G + theta * (cY * Y) := by ring
      _ ≤ theta * D * G + cY * Y := by
        have hthetaCY : theta * (cY * Y) ≤ cY * Y := by
          simpa using mul_le_mul_of_nonneg_right htheta_le hcYY
        linarith
  have hcross := critical_energy_cross_young
    (p := p) (T := T) (t := t) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT hm hp hchi
  rw [← hGeq] at hcross
  change p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
      D * G + Bcoef * J at hcross
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := pExp)
      (u := u) (v := v) (ne_of_gt hp0) hsol ht0 htT
  rw [← hYdomain] at henergy
  change (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      (pExp - 1) * G + p.b * Z =
        p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t +
          p.a * Y at henergy
  have hbZ : 0 ≤ p.b * Z := mul_nonneg p.hb hZnonneg
  have hpre :
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        delta * G ≤ (p.a + cY) * Y := by
    dsimp [delta]
    dsimp [D] at hcross hBJ ⊢
    nlinarith
  have hmass_t : intervalDomain.integral (u t) = uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomain] using
      hmass t ht0
  have hmass_nonneg : 0 ≤ intervalDomain.integral (u t) :=
    (mass_pos hsol ht).le
  have hmass_pow : (intervalDomain.integral (u t)) ^ pExp ≤
      uStar ^ pExp := by
    rw [hmass_t]
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hag := hagmon (u t) (fun x => u_pos hsol ht0 htT x) hC2
  have hag' : Y ≤ (delta / Bmain) * G +
      Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
    rw [hYdomain]
    simpa [G, intervalDomainLpWeightedGradientDissipation] using hag
  have habsorb : Bmain * Y ≤ delta * G +
      Bmain * Cagmon * uStar ^ pExp := by
    have hmul := mul_le_mul_of_nonneg_left hag' hBmain.le
    have hpowmul := mul_le_mul_of_nonneg_left hmass_pow
      (mul_nonneg hBmain.le hCagmon.le)
    calc
      Bmain * Y ≤ Bmain * ((delta / Bmain) * G +
          Cagmon * (intervalDomain.integral (u t)) ^ pExp) := hmul
      _ = delta * G +
          Bmain * Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
        field_simp [ne_of_gt hBmain]
      _ ≤ delta * G + Bmain * Cagmon * uStar ^ pExp := by
        linarith
  dsimp [Y] at hpre habsorb ⊢
  dsimp [K, Bmain]
  nlinarith

/-- The critical threshold supplies a seed exponent and an orbit-independent
eventual `L^p` bound on every physical-mass bounded global orbit. -/
theorem exists_minimal_eventual_lp_power_bound
    (p : CM2Params) {uStar : ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiBeta p) (huStar : 0 < uStar) :
    ∃ pExp C : ℝ,
      max 1 (p.γ * (p.N : ℝ) / 2) < pExp ∧ 0 ≤ C ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomain p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
        ∀ᶠ t : ℝ in atTop,
          intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ C := by
  obtain ⟨pExp, hpLower, hpUpper⟩ :=
    exists_critical_seed_exponent p hbeta hchi hthreshold
  have hp : 1 < pExp := lt_of_le_of_lt (le_max_left _ _) hpLower
  have hp0 : 0 < pExp := lt_trans zero_lt_one hp
  have hupper : p.χ₀ < (2 * p.β - 1) / pExp := by
    rw [lt_div_iff₀ hp0]
    have hmul := (lt_div_iff₀ hchi).mp hpUpper
    nlinarith
  obtain ⟨K, hK, hdamp⟩ := exists_minimal_critical_lp_damping_constant
    p hm ha0 hb0 hbeta hchi hp hupper huStar
  refine ⟨pExp, K + 1, hpLower, by linarith, ?_⟩
  intro u v huv hmass
  have hglobalM : IsPaper2GlobalClassicalSolution intervalDomainM p u v :=
    isPaper2GlobalClassicalSolution_intervalDomainM_of_m_eq_one p hm huv.1
  have hderiv : ∀ t, 0 < t →
      HasDerivAt (fun τ => intervalDomainLpEnergy pExp u τ)
        (deriv (fun τ => intervalDomainLpEnergy pExp u τ) t) t := by
    intro t ht
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    exact lpEnergy_hasDerivAt_of_solution (hglobalM.classical hT) ht htT
  have hev := eventually_le_add_one_of_linear_damping hp0 hderiv
    (hdamp u v huv hmass)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t ht hTpos
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  have heq : intervalDomainLpEnergy pExp u t =
      ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp :=
    lpEnergy_eq_lift_power_of_solution
      (q := pExp) (hglobalM.classical hH) hTpos htH
  have hdomain : intervalDomain.integral (fun x => (u t x) ^ pExp) =
      intervalDomainLpEnergy pExp u t := by
    rw [heq]
    exact intervalDomain_integral_rpow_eq_lift_integral
  rw [hdomain]
  exact ht

#print axioms exists_minimal_critical_lp_damping_constant
#print axioms exists_minimal_eventual_lp_power_bound

end

end ShenWork.Paper3
