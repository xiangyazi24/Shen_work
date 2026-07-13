import ShenWork.Paper3.IntervalDomainMinimalUniformAgmon

/-!
# Orbit-independent finite-power bootstrap for the minimal model

The damping constant below is assembled entirely from scalar parameters and
the already uniform seed bound.  The solution orbit is quantified only after
that constant has been fixed.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute
open ShenWork.Paper2.IntervalDomainM

namespace ShenWork.Paper3

noncomputable section

set_option maxHeartbeats 800000 in
/-- A uniform seed bound supplies a target-power damping constant before the
global solution is selected. -/
theorem exists_uniform_critical_bootstrap_damping
    (p : CM2Params) {p0 pExp C0 : ℝ}
    (hm : p.m = 1) (hbeta : 1 ≤ p.β)
    (hp0 : max 1 (p.γ * (p.N : ℝ) / 2) < p0)
    (hpExp : p0 ≤ pExp) :
    ∃ D : ℝ,
      ∀ (u v : ℝ → intervalDomain.Point → ℝ),
        IsPaper2GlobalClassicalSolution intervalDomainM p u v →
        (∀ t, 0 < t →
          intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0) →
        ∀ t, 0 < t →
          (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
            intervalDomainLpEnergy pExp u t ≤ D := by
  have hp0_one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hpExp_one : 1 < pExp := hp0_one.trans_le hpExp
  have hpExp_pos : 0 < pExp := zero_lt_one.trans hpExp_one
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
  let Ceps : ℝ := scalarSeedAgmonAbsorbConstant
    (max C0 0) pExp p0 p.γ epsInterp
  let D : ℝ := K * Ceps + Klow
  refine ⟨D, ?_⟩
  intro u v hglobal hseed t ht0
  have hglobal' : IsPaper2GlobalClassicalSolution intervalDomain p u v := by
    intro T hT
    exact classicalSolution_intervalDomain_of_m_eq_one hm (hglobal.classical hT)
  have hseed' : ∀ s, 0 < s →
      intervalDomain.integral (fun x => (u s x) ^ p0) ≤ C0 := by
    intro s hs0
    simpa [intervalDomainM, intervalDomain] using hseed s hs0
  have hinterp : ∀ s, 0 < s →
      intervalDomain.integral (fun x => (u s x) ^ (pExp + p.γ)) ≤
        epsInterp * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u s y) ^ (pExp / 2)) x) ^ 2) + Ceps := by
    intro s hs0
    simpa [Ceps] using intervalDomain_uniform_agmon_absorbed_of_seed
      hglobal' p.hγ hp0 hseed' hpExp hepsInterp s hs0
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

#print axioms exists_uniform_critical_bootstrap_damping

end

end ShenWork.Paper3
