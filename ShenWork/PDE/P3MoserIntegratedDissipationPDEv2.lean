import ShenWork.PDE.P3MoserRegularityProducer

set_option linter.style.longLine false

/-!
# Frontier #3: integrated Moser dissipation with a satisfiable coefficient gap

This file replaces the old universal coefficient-gap residual by a combined
energy-plus-gap hypothesis.  The gap is attached to the same coefficient `A`
chosen by the strict-time `LpBootstrapEnergyInequality`, which is the only
coefficient used by the integrated absorption proof.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2

/-- `LpBootstrapEnergyInequality` plus the coefficient gap for the specific
strict-time gradient coefficient `A` supplied by the same witness. -/
def LpBootstrapEnergyInequalityWithGap
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      (∀ t, 0 < t → t < T →
        (1 / pExp) *
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A *
            D.integral
              (fun x =>
                (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L) ∧
      (2 : ℝ) < pExp * A

/-- Forget the attached coefficient gap and recover the original strict-time
bootstrap energy inequality. -/
theorem lpBootstrapEnergyInequality_of_withGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (heg : LpBootstrapEnergyInequalityWithGap D u T rho p0) :
    LpBootstrapEnergyInequality D u T rho p0 := by
  intro pExp hp
  rcases heg pExp hp with ⟨A, hA, B, hB, K, hK, L, hpoint, _hgap⟩
  exact ⟨A, hA, B, hB, K, hK, L, hpoint⟩

/-- Extract the energy inequality and the absorption surplus for the same
specific coefficients chosen by `LpBootstrapEnergyInequalityWithGap`. -/
theorem surplus_of_energyWithGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (heg : LpBootstrapEnergyInequalityWithGap D u T rho p0) :
    ∀ pExp, p0 ≤ pExp →
      ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
        (∀ t, 0 < t → t < T →
          (1 / pExp) *
              deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
            A *
              D.integral
                (fun x =>
                  (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
            B * D.integral (fun x => (u t x) ^ pExp) ≤
          K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L) ∧
        ∃ eps : ℝ, 0 < eps ∧ (pExp * K) * eps ≤ pExp * A - 2 := by
  intro pExp hp
  rcases heg pExp hp with ⟨A, hA, B, hB, K, hK, L, hpoint, hgap⟩
  refine ⟨A, hA, B, hB, K, hK, L, hpoint, ?_⟩
  exact exists_pos_eps_mul_le_sub_of_coeff_gap
    (p := pExp) (A := A) (K := K) (theta := (2 : ℝ)) hgap

/-- Closed-window higher-power energy frontier from the combined strict-time
energy-plus-gap hypothesis.

This is the same proof skeleton as
`integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality`,
except the surplus is derived from the gap attached to the chosen `A`. -/
theorem higherPowerWindowCoeffFrontier_of_energyWithGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (heg : LpBootstrapEnergyInequalityWithGap D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hG_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2)
    (hY_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u p s) volume t1 t2)
    (hZ_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u (p + rho) s)
          volume t1 t2)
    (hMax_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
          volume t1 t2)
    (hY_integral_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 (2 : ℝ) := by
  intro p hp
  rcases heg p hp with ⟨A, hA, B, hB, K, hK, L_const, hpoint_raw, hgap⟩
  rcases exists_pos_eps_mul_le_sub_of_coeff_gap
      (p := p) (A := A) (K := K) (theta := (2 : ℝ)) hgap with
    ⟨eps, heps, habsorb⟩
  have hp_pos_p : 0 < p := hp_pos p hp
  have hpoint :
      ∀ t, 0 < t → t < T →
        (1 / p) *
            deriv (fun τ => integratedMoserEnergy D u p τ) t +
          A * integratedMoserGradientEnergy D u p t +
          B * integratedMoserEnergy D u p t ≤
        K * integratedMoserEnergy D u (p + rho) t + L_const := by
    intro t ht0 htT
    simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
      hpoint_raw t ht0 htT
  refine
    ⟨p * A, p * K, 0, max (0 : ℝ) (p * L_const), eps,
      heps, mul_nonneg hp_pos_p.le hK.le, by norm_num,
      le_max_left _ _, ?_, habsorb⟩
  intro t1 ht1 t2 ht2
  rcases
    integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
      (D := D) (u := u) (T := T) (rho := rho) (p := p)
      (A := A) (B := B) (K := K) (L_const := L_const)
      (t1 := t1) (t2 := t2)
      hp_pos_p hA hB hK ht1 ht2 hpoint
      (hFTC.window_ftc p hp t1 ht1 t2 ht2)
      (hFTC.deriv_intervalIntegrable p hp t1 ht1 t2 ht2)
      (hG_int p hp t1 ht1 t2 ht2)
      (hY_int p hp t1 ht1 t2 ht2)
      (hZ_int p hp t1 ht1 t2 ht2)
      (hMax_int p hp t1 ht1 t2 ht2)
      (hY_integral_nonneg p hp t1 ht1 t2 ht2) with
    ⟨_hAwin, _hKwin, _hC0, _hLwin, hwindow⟩
  simpa using hwindow

/-- Full-window higher-power coefficient frontier from the combined
energy-plus-gap hypothesis, with routine window integrability supplied by the
first-crossing regularity package. -/
theorem higherPowerWindowCoeffFrontier_of_regularEnergyWithGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (heg : LpBootstrapEnergyInequalityWithGap D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hrho_nonneg : 0 ≤ rho) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 (2 : ℝ) := by
  refine
    higherPowerWindowCoeffFrontier_of_energyWithGap
      heg hFTC hp_pos ?_ ?_ ?_ ?_ ?_
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    exact hreg.gradient_intervalIntegrable_of_Icc hp ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    exact hreg.power_intervalIntegrable_of_Icc hp ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    have hp_rho : p0 ≤ p + rho := by
      linarith
    exact hreg.power_intervalIntegrable_of_Icc hp_rho ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    exact hreg.maxOneEnergy_intervalIntegrable_of_Icc hp ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hp_nonneg : 0 ≤ p := (hp_pos p hp).le
    have hY_ae :
        ∀ᵐ s ∂(volume.restrict (Set.Icc t1 t2)),
          0 ≤ integratedMoserEnergy D u p s := by
      filter_upwards
        [ae_restrict_Icc_strictInterior_of_Icc_endpoints ht1 ht2] with s hs
      exact hnonneg p hp hp_nonneg s hs.1 hs.2
    exact intervalIntegral.integral_nonneg_of_ae_restrict ht2.1 hY_ae

/-- Interval-domain coefficient dissipation from the combined strict-time
energy-plus-gap route. -/
theorem intervalDomain_dissipationCoeff_of_regularEnergyWithGap
    {params : CM2Params} {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (heg : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBeforeCoeff
      (2 : ℝ) intervalDomain u T rho p0 := by
  have hp_pos : ∀ p, p0 ≤ p → 0 < p := by
    intro p hp
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hone_le :
        (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
      le_max_left _ _
    have hp0_pos : 0 < p0 := by
      linarith
    linarith
  have hrho_pos : 0 < rho := AbstractLpBootstrapHypothesis.rho_pos hboot
  have hwindow :
      IntegratedHigherPowerEnergyWindowCoeffFrontier
        intervalDomain u T rho p0 (2 : ℝ) :=
    higherPowerWindowCoeffFrontier_of_regularEnergyWithGap
      heg hFTC hreg hnonneg hp_pos hrho_pos.le
  have hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            ∫ s in t1..t2,
                integratedMoserEnergy intervalDomain u (p + rho) s ≤
              eps * (∫ s in t1..t2,
                integratedMoserGradientEnergy intervalDomain u p s) +
              Ceps * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy intervalDomain u p s)) :=
    relativeMoser_hrelInt_closedWindow_of_regular hrel hreg hrho_pos.le
  exact
    intervalDomain_integratedMoserDissipationDropBeforeCoeff_of_windowEnergy_and_relative
      hboot hwindow hrelInt

/-- Fixed-coefficient integrated Moser drop from the combined energy-plus-gap
route. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_energyWithGap
    {params : CM2Params} {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (heg : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
  integratedMoserDissipationDropBefore_of_coeff_two
    (intervalDomain_dissipationCoeff_of_regularEnergyWithGap
      (params := params) (T := T) (rho := rho) (p0 := p0) (u := u)
      hboot heg hFTC hreg hnonneg hrel)

/-- Integrated Moser dissipation from the global PDE route, with the satisfiable
combined energy-plus-gap residual replacing the old universal coefficient gap. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 := by
  have _henergy_from_pde : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  have hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
      hdata hsol
  have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical
      (p0 := p0) hsol
  exact
    intervalDomain_integratedMoserDissipationDropBefore_of_energyWithGap
      (params := params) (T := T) (rho := rho) (p0 := p0) (u := u)
      hboot hgap hftc hreg hnonneg hrel

/-- Fact-instance convenience wrapper for the v2 global PDE route. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2_fact
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    [hdata : Fact (IntervalDomainIntegratedMoserClassicalRegularityData u T p0)]
    [hgap : Fact (LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)]
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
  intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
    hsol hcross hboot hftc hrel hdata.out hgap.out

#print axioms lpBootstrapEnergyInequality_of_withGap
#print axioms surplus_of_energyWithGap
#print axioms higherPowerWindowCoeffFrontier_of_energyWithGap
#print axioms higherPowerWindowCoeffFrontier_of_regularEnergyWithGap
#print axioms intervalDomain_integratedMoserDissipationDropBefore_of_energyWithGap
#print axioms intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
#print axioms intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2_fact

end ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2

end
