import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2

set_option linter.style.longLine false

/-!
# p-dependent epsilon refactor for the interval-domain Moser energy gap

This file leaves the existing fixed-epsilon producer untouched and adds the
parallel p-dependent coefficient route requested by Task 22.

The expression displayed in the task note,
`4 * (p - 1) / p * (c + p) / (c + 1)`, is not algebraically equal to the
specified coefficient when `cGrad = (p / 2)^2`.  The verified expression below
is
`4 * (p - 1) * (p * (c + 1) - c) / (p^2 * (c + 1))`, which tends to `4` as
`p → ∞` and gives the uniform explicit threshold `p ≥ 4`.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyGapRefactor

/-- The p-dependent absorption coefficient from Task 22. -/
def AcoefPDep (pExp chi0 : ℝ) : ℝ :=
  let A0 := pExp - 1
  let chiBound := |chi0| * A0
  let eps := A0 / (pExp * (chiBound + 1))
  let cGrad := (pExp / 2) ^ 2
  (A0 - chiBound * eps) / cGrad

/-- Local copy of the old fixed-epsilon coefficient, used only for comparison. -/
def AcoefFixedEps (pExp chi0 : ℝ) : ℝ :=
  let A0 := pExp - 1
  let chiBound := |chi0| * A0
  let eps := A0 / (2 * (chiBound + 1))
  let cGrad := (pExp / 2) ^ 2
  (A0 - chiBound * eps) / cGrad

/-- A conservative explicit threshold for the p-dependent gap. -/
def gapThresholdPDep (_chi0 : ℝ) : ℝ := 4

/-- Correct cleared-denominator algebraic simplification of `p * AcoefPDep`.

Writing `c = |chi0| * (pExp - 1)`, the right-hand side is
`4 * (pExp - 1) * (pExp * (c + 1) - c)`.  Since
`pExp^2 * (c + 1)` is positive in the gap range, this is equivalent to the
quotient formula
`pExp * AcoefPDep = 4 * (pExp - 1) * (pExp * (c + 1) - c) /
  (pExp^2 * (c + 1))`. -/
theorem p_mul_AcoefPDep_eq_cleared
    {pExp chi0 : ℝ}
    (hp : pExp ≠ 0)
    (hc : |chi0| * (pExp - 1) + 1 ≠ 0) :
    (pExp ^ 2 * (|chi0| * (pExp - 1) + 1)) *
      (pExp * AcoefPDep pExp chi0) =
      4 * (pExp - 1) *
        (pExp * (|chi0| * (pExp - 1) + 1) -
          |chi0| * (pExp - 1)) := by
  have hc' : 1 + pExp * |chi0| - |chi0| ≠ 0 := by
    convert hc using 1; ring
  have hhalf : (pExp / 2) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (div_ne_zero hp (by norm_num))
  unfold AcoefPDep
  field_simp [hp, hc, hc', hhalf]
  norm_num

/-- For every chemotactic coefficient, `p ≥ 4` gives the strict Moser gap. -/
theorem AcoefPDep_gap_of_threshold
    {pExp chi0 : ℝ}
    (hp : gapThresholdPDep chi0 ≤ pExp) :
    (2 : ℝ) < pExp * AcoefPDep pExp chi0 := by
  let a : ℝ := |chi0|
  let q : ℝ := pExp - 1
  have ha : 0 ≤ a := by
    dsimp [a]
    exact abs_nonneg chi0
  have hp4 : 4 ≤ pExp := by
    simpa [gapThresholdPDep] using hp
  have hp_pos : 0 < pExp := by linarith
  have hp_ne : pExp ≠ 0 := ne_of_gt hp_pos
  have hq_ge : 3 ≤ q := by
    dsimp [q]
    linarith
  have hq_pos : 0 < q := by linarith
  have hc_pos : 0 < a * q + 1 := by nlinarith
  have hc_ne : a * q + 1 ≠ 0 := ne_of_gt hc_pos
  have hden_pos : 0 < pExp ^ 2 * (a * q + 1) := by
    exact mul_pos (sq_pos_of_ne_zero hp_ne) hc_pos
  have hquad_nonneg : 0 ≤ q ^ 2 - 2 * q - 1 := by nlinarith
  have hq_sq_gt : 0 < q ^ 2 - 1 := by nlinarith
  have hmain_pos :
      0 < a * q ^ 3 - 2 * a * q ^ 2 - a * q + q ^ 2 - 1 := by
    have hterm_nonneg : 0 ≤ a * q * (q ^ 2 - 2 * q - 1) := by
      exact mul_nonneg (mul_nonneg ha hq_pos.le) hquad_nonneg
    nlinarith
  have hnum :
      2 * (pExp ^ 2 * (a * q + 1)) <
        4 * q * (pExp * (a * q + 1) - a * q) := by
    have hp_eq : pExp = q + 1 := by
      dsimp [q]
      ring
    nlinarith
  have hcleared :=
    p_mul_AcoefPDep_eq_cleared (pExp := pExp) (chi0 := chi0) hp_ne
      (by dsimp [a, q] at hc_ne ⊢; exact hc_ne)
  have hmul :
      (pExp ^ 2 * (a * q + 1)) * 2 <
        (pExp ^ 2 * (a * q + 1)) *
          (pExp * AcoefPDep pExp chi0) := by
    calc
      (pExp ^ 2 * (a * q + 1)) * 2 =
          2 * (pExp ^ 2 * (a * q + 1)) := by ring
      _ < 4 * q * (pExp * (a * q + 1) - a * q) := hnum
      _ =
          (pExp ^ 2 * (a * q + 1)) *
            (pExp * AcoefPDep pExp chi0) := by
          dsimp [a, q] at hcleared ⊢
          exact hcleared.symm
  exact lt_of_mul_lt_mul_left hmul hden_pos.le

/-- At `χ₀ = 0`, the p-dependent and old fixed-epsilon coefficients agree. -/
theorem AcoefPDep_eq_fixedEps_chi_zero (pExp : ℝ) :
    AcoefPDep pExp 0 = AcoefFixedEps pExp 0 := by
  unfold AcoefPDep AcoefFixedEps
  simp

/-- Explicit one-exponent p-dependent energy witness.  This keeps the
coefficient visible so the gap wrapper can attach the strict surplus to the
same `A`. -/
theorem lpBootstrapEnergyInequality_pointwise_of_classical_pDep
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (pExp : ℝ) (hp : p0 ≤ pExp)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    ∃ _hA : 0 < AcoefPDep pExp params.χ₀,
      ∃ B > 0, ∃ K > 0, ∃ L,
        ∀ t, 0 < t → t < T →
          (1 / pExp) *
              deriv
                (fun τ => intervalDomain.integral
                  (fun x => (u τ x) ^ pExp)) t +
            AcoefPDep pExp params.χ₀ *
              intervalDomain.integral
                (fun x =>
                  (intervalDomain.gradNorm
                    (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + L := by
  have hlower : IntervalDomainLpLowerOrderControl params u T rho p0 :=
    intervalDomainLpLowerOrderControl_of_regularity hsol hboot
  have hp0_gt_one : 1 < p0 := by
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hone_le :
        (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
      le_max_left _ _
    linarith
  have hpExp : 1 < pExp := by linarith
  let A0 : ℝ := pExp - 1
  let chiBound : ℝ := |params.χ₀| * (pExp - 1)
  let eps : ℝ := A0 / (pExp * (chiBound + 1))
  have hA0_pos : 0 < A0 := by
    dsimp [A0]
    linarith
  have hpExp_pos : 0 < pExp := by linarith
  have hpExp_ne : pExp ≠ 0 := by linarith
  have hchiBound_nonneg : 0 ≤ chiBound := by
    dsimp [chiBound]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hchiBound_one_pos : 0 < chiBound + 1 := by nlinarith
  have hden_pos : 0 < pExp * (chiBound + 1) := by
    exact mul_pos hpExp_pos hchiBound_one_pos
  have hden_ne : pExp * (chiBound + 1) ≠ 0 := ne_of_gt hden_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact div_pos hA0_pos hden_pos
  obtain ⟨Ccross, hCrossAt⟩ := hcross eps heps_pos pExp hpExp
  let cGrad : ℝ := (pExp / 2) ^ 2
  have hcGrad_pos : 0 < cGrad := by
    dsimp [cGrad]
    exact sq_pos_of_pos (by linarith)
  have hGradAt :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤
          cGrad * intervalDomainLpWeightedGradientDissipation pExp u t := by
    intro t ht0 htT
    exact (intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := params) (T := T) (pExp := pExp)
      (u := u) (v := v) hsol ht0 htT).le
  obtain ⟨Klow, hKlow_pos, Llow, hLowerAt⟩ := hlower pExp hp
  have hAabs_pos : 0 < A0 - chiBound * eps := by
    rw [sub_pos]
    have hden_gt_chi : chiBound < pExp * (chiBound + 1) := by
      nlinarith [hchiBound_nonneg, hpExp]
    have hscaled :
        chiBound * A0 < A0 * (pExp * (chiBound + 1)) := by
      have hscaled' := mul_lt_mul_of_pos_left hden_gt_chi hA0_pos
      nlinarith
    dsimp [eps]
    calc
      chiBound * (A0 / (pExp * (chiBound + 1))) =
          (chiBound * A0) / (pExp * (chiBound + 1)) := by ring
      _ < A0 := (div_lt_iff₀ hden_pos).2 hscaled
  let Acoef : ℝ := AcoefPDep pExp params.χ₀
  let K : ℝ := max 1 (chiBound * Ccross + Klow)
  have hAcoef_pos : 0 < Acoef := by
    dsimp [Acoef, AcoefPDep, A0, chiBound, eps, cGrad]
    exact div_pos hAabs_pos hcGrad_pos
  have hK_pos : 0 < K := by
    dsimp [K]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨hAcoef_pos, 1, by norm_num, K, hK_pos, Llow, ?_⟩
  intro t ht0 htT
  set Y : ℝ :=
    (1 / pExp) *
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
  set G : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
  set H : ℝ :=
    intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
  set E : ℝ := intervalDomainLpEnergy pExp u t
  set Z : ℝ :=
    intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  set R : ℝ := intervalDomainLpLogisticIntegral params pExp u t
  have hLpTime :
      ∀ s, 0 < s → s < T →
        deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
          pExp *
            intervalDomain.integral
              (intervalDomainLpEnergyWeightedTimeTerm pExp u s) :=
    intervalDomain_lp_energy_hLpTime_frontier (q := pExp) hsol
  have hPDEIntegral :=
    intervalDomain_lp_energy_hPDEIntegral_of_regularity
      (pExp := pExp) hsol ht0 htT
  have hIBP :=
    intervalDomain_lp_energy_hIBP_of_regularity
      (pExp := pExp) hsol ht0 htT
  have hNeuR :
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1
  have hNeuL :
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1
  have hDiffusionCoercive :
      A0 * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t := by
    simpa [A0] using
      intervalDomain_lp_energy_hDiffusionCoercive_of_regularity
        (params := params) (T := T) (pExp := pExp)
        (u := u) (v := v) hsol t ht0 htT
  have hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) := by
    simpa [chiBound] using
      intervalDomain_lp_energy_hCrossControl_of_regularity
        (params := params) (T := T) (pExp := pExp)
        (u := u) (v := v) hpExp hsol t ht0 htT
  have hbasic :
      Y + A0 * G ≤
        chiBound *
            intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) +
          R := by
    simpa [Y, G, R, intervalDomainLpEnergy] using
      intervalDomain_lp_energy_gradient_inequality_of_frontiers
        (params := params) (T := T) (pExp := pExp)
        (A := A0) (chiBound := chiBound) (t := t)
        (u := u) (v := v) hpExp_ne ht0 htT hLpTime
        hPDEIntegral hIBP hNeuR hNeuL hDiffusionCoercive hCrossControl
  have hCrossAt_t :
      intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        eps * G + Ccross * Z := by
    simpa [G, Z, intervalDomainLpWeightedGradientDissipation] using
      hCrossAt t ht0 htT
  have hscaled :
      chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        chiBound * (eps * G + Ccross * Z) :=
    mul_le_mul_of_nonneg_left hCrossAt_t hchiBound_nonneg
  have hpre :
      Y + A0 * G ≤ chiBound * (eps * G + Ccross * Z) + R := by
    linarith
  have habsorbed :
      Y + (A0 - chiBound * eps) * G ≤ chiBound * Ccross * Z + R := by
    calc
      Y + (A0 - chiBound * eps) * G
          = Y + A0 * G - chiBound * (eps * G) := by ring
      _ ≤ chiBound * (eps * G + Ccross * Z) + R -
            chiBound * (eps * G) := by
          linarith
      _ = chiBound * Ccross * Z + R := by ring
  have hLogistic :
      R ≤ params.a * E := by
    simpa [R, E] using
      intervalDomain_lp_logisticIntegral_le_a_energy_of_regularity
        hsol ht0 htT
  have hLower_t :
      (params.a + 1) * E ≤ Klow * Z + Llow := by
    simpa [E, Z] using hLowerAt t ht0 htT
  have hclosed :
      Y + (A0 - chiBound * eps) * G + E ≤
        (chiBound * Ccross + Klow) * Z + Llow := by
    linarith
  have hGrad_t : H ≤ cGrad * G := by
    simpa [H, G] using hGradAt t ht0 htT
  have hAgrad :
      Acoef * H ≤ (A0 - chiBound * eps) * G := by
    calc
      Acoef * H ≤ Acoef * (cGrad * G) :=
        mul_le_mul_of_nonneg_left hGrad_t hAcoef_pos.le
      _ = (A0 - chiBound * eps) * G := by
        dsimp [Acoef, AcoefPDep, A0, chiBound, eps, cGrad]
        field_simp [ne_of_gt hcGrad_pos]
  have hwith_moser :
      Y + Acoef * H + E ≤
        (chiBound * Ccross + Klow) * Z + Llow := by
    linarith
  have hZ_nonneg : 0 ≤ Z := by
    simpa [Z] using
      intervalDomain_integral_u_rpow_nonneg_of_regularity
        (params := params) (T := T) (t := t) (q := pExp + rho)
        (u := u) (v := v) hsol ht0 htT
  have hcoeff_le_K : chiBound * Ccross + Klow ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  have hKbound :
      (chiBound * Ccross + Klow) * Z + Llow ≤ K * Z + Llow := by
    have hmul := mul_le_mul_of_nonneg_right hcoeff_le_K hZ_nonneg
    linarith
  have hfinal : Y + Acoef * H + E ≤ K * Z + Llow := by
    exact hwith_moser.trans hKbound
  have hEnergyEq :=
    intervalDomainLpEnergy_eq_power_of_regularity
      (pExp := pExp) hsol ht0 htT
  have hDerivEq :
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t =
        deriv
          (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t :=
    (intervalDomainLpEnergy_eventuallyEq_power_of_regularity
      (pExp := pExp) hsol ht0 htT).deriv_eq
  rw [← hDerivEq, ← hEnergyEq]
  simpa [Y, H, E, Z] using hfinal

/-- Same signature as the existing interval-domain energy producer, but with
the p-dependent Young parameter and coefficient `AcoefPDep`. -/
theorem lpBootstrapEnergyInequality_of_classical_pDep
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequality intervalDomain u T rho p0 := by
  intro pExp hp
  rcases lpBootstrapEnergyInequality_pointwise_of_classical_pDep
      (params := params) (T := T) (rho := rho) (p0 := p0)
      (u := u) (v := v) pExp hp hsol hcross hboot with
    ⟨hA, B, hB, K, hK, L, hpoint⟩
  exact ⟨AcoefPDep pExp params.χ₀, hA, B, hB, K, hK, L, hpoint⟩

/-- Classical producer for the combined energy inequality and p-dependent gap.
The extra hypothesis is exactly the explicit threshold needed by the gap. -/
theorem lpBootstrapEnergyInequalityWithGap_of_classical_pDep
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hp0_gap : gapThresholdPDep params.χ₀ ≤ p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0 := by
  intro pExp hp
  rcases lpBootstrapEnergyInequality_pointwise_of_classical_pDep
      (params := params) (T := T) (rho := rho) (p0 := p0)
      (u := u) (v := v) pExp hp hsol hcross hboot with
    ⟨hA, B, hB, K, hK, L, hpoint⟩
  refine ⟨AcoefPDep pExp params.χ₀, hA, B, hB, K, hK, L, hpoint, ?_⟩
  have hp_gap : gapThresholdPDep params.χ₀ ≤ pExp := by linarith
  simpa using AcoefPDep_gap_of_threshold
    (pExp := pExp) (chi0 := params.χ₀) hp_gap

#print axioms p_mul_AcoefPDep_eq_cleared
#print axioms AcoefPDep_gap_of_threshold
#print axioms AcoefPDep_eq_fixedEps_chi_zero
#print axioms lpBootstrapEnergyInequality_pointwise_of_classical_pDep
#print axioms lpBootstrapEnergyInequality_of_classical_pDep
#print axioms lpBootstrapEnergyInequalityWithGap_of_classical_pDep

end ShenWork.IntervalDomainExistence.P3MoserEnergyGapRefactor

end
