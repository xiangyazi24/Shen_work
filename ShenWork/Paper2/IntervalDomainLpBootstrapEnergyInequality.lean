import ShenWork.Paper2.IntervalDomainLpEnergyFrontiers

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

/-- Chain-rule comparison needed to express the absorbed weighted-gradient
dissipation in the Moser-gradient form used by `LpBootstrapEnergyInequality`. -/
def IntervalDomainLpMoserGradientControl
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ cGrad > 0, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤
        cGrad * intervalDomainLpWeightedGradientDissipation pExp u t

/-- Lower-order comparison needed to move the logistic growth contribution and
the target `+ ∫u^p` term to the `∫u^(p+rho) + L` right-hand side. -/
def IntervalDomainLpLowerOrderControl
    (params : CM2Params) (u : ℝ → intervalDomain.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ Klow > 0, ∃ Llow,
      ∀ t, 0 < t → t < T →
        (params.a + 1) * intervalDomainLpEnergy pExp u t ≤
          Klow *
              intervalDomain.integral
                (fun x => (u t x) ^ (pExp + rho)) +
            Llow

/-- Positivity of the classical solution makes every interval-domain power
integral nonnegative. -/
theorem intervalDomain_integral_u_rpow_nonneg_of_regularity
    {params : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 ≤ intervalDomain.integral (fun x => (u t x) ^ q) := by
  change 0 ≤ intervalDomainIntegral _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y hy => ?_)
  have hu_pos : 0 < u t (⟨y, hy⟩ : intervalDomain.Point) :=
    hsol.u_pos' ht0 htT
  simpa [intervalDomainLift, hy] using Real.rpow_nonneg hu_pos.le q

/-- On positive classical solution slices, the repository's absolute Lp energy
is the same as the plain `u^p` energy used in the statement layer. -/
theorem intervalDomainLpEnergy_eq_power_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpEnergy pExp u t =
      intervalDomain.integral (fun x => (u t x) ^ pExp) := by
  unfold intervalDomainLpEnergy
  change intervalDomainIntegral _ = intervalDomainIntegral _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hy
  have hu_pos : 0 < u t (⟨y, hy⟩ : intervalDomain.Point) :=
    hsol.u_pos' ht0 htT
  simp [intervalDomainLift, hy, abs_of_pos hu_pos]

/-- Local-in-time version of `intervalDomainLpEnergy_eq_power_of_regularity`,
used to transport the derivative from `|u|^p` to `u^p`. -/
theorem intervalDomainLpEnergy_eventuallyEq_power_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    (fun τ => intervalDomainLpEnergy pExp u τ) =ᶠ[nhds t]
      fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp) := by
  filter_upwards [Ioo_mem_nhds ht0 htT] with s hs
  exact intervalDomainLpEnergy_eq_power_of_regularity
    (pExp := pExp) hsol hs.1 hs.2

/-- Early assembly skeleton for the interval-domain Lp energy inequality.

The named `have`s below are the committed PDE-side inputs: cross-control,
logistic upper bound, diffusion coercivity, and nonnegative weighted
dissipation. -/
theorem intervalDomain_lp_bootstrap_energy_assembly_skeleton
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    True := by
  have hCrossControl :=
    intervalDomain_lp_energy_hCrossControl_of_regularity hpExp hsol
  have hLogisticUpper :
      ∀ t, 0 < t → t < T →
        intervalDomainLpLogisticIntegral params pExp u t ≤
          params.a * intervalDomainLpEnergy pExp u t := by
    intro t ht0 htT
    exact intervalDomain_lp_logisticIntegral_le_a_energy_of_regularity
      hsol ht0 htT
  have hDiffusionCoercive :=
    intervalDomain_lp_energy_hDiffusionCoercive_of_regularity
      (params := params) (T := T) (pExp := pExp) (u := u) (v := v) hsol
  have hDissNonneg :
      ∀ t, 0 < t → t < T →
        0 ≤ intervalDomainLpWeightedGradientDissipation pExp u t := by
    intro t ht0 htT
    exact intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
      hsol ht0 htT
  trivial

/-- Assemble `LpBootstrapEnergyInequality` from the committed interval-domain
energy identity, cross-control, logistic upper bound, and diffusion coercivity.

The two explicit extra assumptions are the remaining non-circular analytic
frontiers in the current API: the chain-rule comparison to the Moser gradient,
and the lower-order comparison that absorbs `(a+1) * ∫u^p` into
`K * ∫u^(p+rho) + L`. -/
theorem intervalDomain_LpBootstrapEnergyInequality_of_regularity
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hgrad : IntervalDomainLpMoserGradientControl u T p0)
    (hlower : IntervalDomainLpLowerOrderControl params u T rho p0) :
    LpBootstrapEnergyInequality intervalDomain u T rho p0 := by
  intro pExp hp
  have hp0_gt_one : 1 < p0 := by
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hone_le :
        (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
      le_max_left _ _
    linarith
  have hpExp : 1 < pExp := by linarith
  let A0 : ℝ := pExp - 1
  let chiBound : ℝ := |params.χ₀| * (pExp - 1)
  let eps : ℝ := A0 / (2 * (chiBound + 1))
  have hA0_pos : 0 < A0 := by
    dsimp [A0]
    linarith
  have hpExp_ne : pExp ≠ 0 := by linarith
  have hchiBound_nonneg : 0 ≤ chiBound := by
    dsimp [chiBound]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hden_pos : 0 < 2 * (chiBound + 1) := by
    nlinarith
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact div_pos hA0_pos hden_pos
  obtain ⟨Ccross, hCrossAt⟩ := hcross eps heps_pos pExp hpExp
  obtain ⟨cGrad, hcGrad_pos, hGradAt⟩ := hgrad pExp hp
  obtain ⟨Klow, hKlow_pos, Llow, hLowerAt⟩ := hlower pExp hp
  have habsorb_half :
      chiBound * eps ≤ A0 / 2 := by
    simpa [eps] using
      intervalDomain_young_absorption_coefficient_half
        (A := A0) (chiBound := chiBound) hA0_pos hchiBound_nonneg
  have hAabs_pos : 0 < A0 - chiBound * eps := by
    nlinarith
  let Acoef : ℝ := (A0 - chiBound * eps) / cGrad
  let K : ℝ := max 1 (chiBound * Ccross + Klow)
  have hAcoef_pos : 0 < Acoef := by
    dsimp [Acoef]
    exact div_pos hAabs_pos hcGrad_pos
  have hK_pos : 0 < K := by
    dsimp [K]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Acoef, hAcoef_pos, 1, by norm_num, K, hK_pos, Llow, ?_⟩
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
        dsimp [Acoef]
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

/-- Structured-Moser handoff using the assembled interval-domain energy
inequality instead of taking `LpBootstrapEnergyInequality` as an input. -/
def intervalDomain_structuredMoserBootstrapData_of_regularity
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hgrad : IntervalDomainLpMoserGradientControl u T p0)
    (hlower : IntervalDomainLpLowerOrderControl params u T rho p0)
    (hdiss :
      IntervalDomainMoserClosure.MoserDissipationDropBefore
        intervalDomain u T rho p0)
    (hrel :
      IntervalDomainMoserClosure.RelativeMoserInterpolationBefore
        intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainStructuredMoserBootstrapData u T :=
  intervalDomain_structuredMoserBootstrapData_of_energy_interfaces
    hboot
    (intervalDomain_LpBootstrapEnergyInequality_of_regularity
      hsol hcross hboot hgrad hlower)
    hdiss hrel hLpMono hEndpoint

end ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
