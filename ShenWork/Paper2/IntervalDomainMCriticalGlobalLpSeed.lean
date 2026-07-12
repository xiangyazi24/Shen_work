import ShenWork.Paper2.IntervalDomainMCriticalLpSeed

/-!
# Horizon-independent critical seed for the faithful interval equation

The finite-horizon critical seed already uses autonomous constants, but its
existential witness is quantified after the horizon.  This file exposes the
same argument with the witness quantified before time.  It is the first input
to the moving-window global critical Moser estimate.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- The critical seed damping constant can be chosen once for a global
solution; it does not depend on a finite restriction horizon. -/
theorem critical_lp_energy_damping_global
    {p : CM2Params} {pExp : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hp : 1 < pExp)
    (hupper : p.χ₀ < (2 * p.β - 1) / pExp) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t →
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
  let Cmass : ℝ := uniformMassBoundConstant p u₀
  have hCmass : 0 ≤ Cmass := by
    dsimp [Cmass]
    exact uniformMassBoundConstant_nonneg p u₀
  let Bmain : ℝ := p.a + cY + 1
  have hBmain : 0 < Bmain := by
    dsimp [Bmain]
    linarith [p.ha, hcY]
  obtain ⟨Cagmon, hCagmon, hagmon⟩ :=
    unitIntervalPositiveAgmonInterpolation pExp hp (delta / Bmain)
      (div_pos hdelta hBmain)
  let K : ℝ := Bmain * Cagmon * Cmass ^ pExp
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hBmain.le hCagmon.le)
      (Real.rpow_nonneg hCmass _)
  refine ⟨K, hK, ?_⟩
  intro t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    hglobal.classical hT
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
  have hmass_t : intervalDomain.integral (u t) ≤ Cmass := by
    dsimp [Cmass]
    exact mass_le_uniformMassBoundConstant_of_guard
      hguard hu₀ hsol htrace t ht0 htT
  have hmass_nonneg : 0 ≤ intervalDomain.integral (u t) :=
    (mass_pos hsol ht).le
  have hmass_pow : (intervalDomain.integral (u t)) ^ pExp ≤
      Cmass ^ pExp :=
    Real.rpow_le_rpow hmass_nonneg hmass_t hp0.le
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hag := hagmon (u t) (fun x => u_pos hsol ht0 htT x) hC2
  have hag' : Y ≤ (delta / Bmain) * G +
      Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
    rw [hYdomain]
    simpa [G, intervalDomainLpWeightedGradientDissipation] using hag
  have habsorb : Bmain * Y ≤ delta * G +
      Bmain * Cagmon * Cmass ^ pExp := by
    have hmul := mul_le_mul_of_nonneg_left hag' hBmain.le
    have hpowmul := mul_le_mul_of_nonneg_left hmass_pow
      (mul_nonneg hBmain.le hCagmon.le)
    calc
      Bmain * Y ≤ Bmain * ((delta / Bmain) * G +
          Cagmon * (intervalDomain.integral (u t)) ^ pExp) := hmul
      _ = delta * G +
          Bmain * Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
        field_simp [ne_of_gt hBmain]
      _ ≤ delta * G + Bmain * Cagmon * Cmass ^ pExp := by
        linarith
  dsimp [Y] at hpre habsorb ⊢
  dsimp [K, Bmain]
  nlinarith

/-- A global critical solution has one power bound, with a witness chosen
before time, at every exponent in the seed range. -/
theorem critical_lp_power_bounded_global
    {p : CM2Params} {pExp : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hp : 1 < pExp)
    (hupper : p.χ₀ < (2 * p.β - 1) / pExp) :
    ∃ C, ∀ t, 0 < t →
      intervalDomainM.integral (fun x => (u t x) ^ pExp) ≤ C := by
  obtain ⟨K, _hK, hdamp⟩ := critical_lp_energy_damping_global
    hguard hu₀ hglobal htrace hbeta hm hchi hp hupper
  let E : ℝ → ℝ := fun s => intervalDomainLpEnergy pExp u s
  obtain ⟨δ, hδ, htraceδ⟩ := htrace 1 (by norm_num)
  have hu0bdd :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  obtain ⟨M₀, hM₀⟩ := hu0bdd
  let R : ℝ := max 0 M₀ + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [le_max_left (0 : ℝ) M₀]
  let C : ℝ := max K (R ^ pExp)
  refine ⟨C, ?_⟩
  intro t ht0
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
    have hp0 : 0 < pExp := lt_trans zero_lt_one hp
    refine ⟨deriv E s, ?_, ?_⟩
    · dsimp [E] at hD ⊢
      have hinv : 0 < 1 / pExp := one_div_pos.mpr hp0
      nlinarith
    · simpa [E] using lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2
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

/-- The printed critical threshold supplies a horizon-independent seed power
strictly above the finite-dimensional bootstrap threshold. -/
theorem exists_high_critical_lp_power_bounded_global
    {p : CM2Params}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    ∃ pExp : ℝ,
      max 1 (p.γ * (p.N : ℝ) / 2) < pExp ∧
        ∃ C, ∀ t, 0 < t →
          intervalDomainM.integral (fun x => (u t x) ^ pExp) ≤ C := by
  obtain ⟨pExp, hpLower, hpUpper⟩ :=
    exists_critical_seed_exponent p hbeta hchi hthreshold
  have hp : 1 < pExp := lt_of_le_of_lt (le_max_left _ _) hpLower
  have hp0 : 0 < pExp := lt_trans zero_lt_one hp
  have hupper : p.χ₀ < (2 * p.β - 1) / pExp := by
    rw [lt_div_iff₀ hp0]
    have hmul := (lt_div_iff₀ hchi).mp hpUpper
    nlinarith
  exact ⟨pExp, hpLower,
    critical_lp_power_bounded_global
      hguard hu₀ hglobal htrace hbeta hm hchi hp hupper⟩

#print axioms critical_lp_energy_damping_global
#print axioms critical_lp_power_bounded_global
#print axioms exists_high_critical_lp_power_bounded_global

end ShenWork.Paper2.IntervalDomainM

end
