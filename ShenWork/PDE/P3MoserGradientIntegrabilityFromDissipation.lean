import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Filter.AtTopBot.Basic
import ShenWork.PDE.P3MoserGradientIntegrability

open Filter
open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserGradientIntegrabilityFromDissipation

/-!
This file packages the short corollary from the integrated Moser dissipation
estimate to raw Moser-gradient time-integrability.  The PDE estimate itself is
kept as the hypothesis `IntegratedMoserDissipationDropBefore`.
-/

/-- Auxiliary endpoint/time-integral bounds used by the integrated-dissipation
corollary.

The first two fields are exactly the endpoint and `max(1,Y_p)` time-integral
bounds consumed by
`integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`.
The last field is only local strict-window integrability; the global closed
time integrability is produced below. -/
structure IntervalDomainIntegratedDissipationGradientBoundData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  p0_nonneg : 0 ≤ p0
  energyUpperBound :
    ∀ p, p0 ≤ p →
      ∃ M, ∀ t ∈ Set.Icc (0 : ℝ) T,
        integratedMoserEnergy intervalDomain u p t ≤ M
  maxOneEnergyTimeIntegralBound :
    ∀ p, p0 ≤ p →
      ∃ H, ∀ a b,
        a ∈ Set.Icc (0 : ℝ) T →
        b ∈ Set.Icc a T →
          ∫ s in a..b,
            max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s) ≤ H
  strictGradientWindowIntegrable :
    IntervalDomainMoserGradientStrictWindowIntegrability u T p0

private theorem tendsto_left_window_scale (T : ℝ) :
    Tendsto (fun n : ℕ => T / ((n : ℝ) + 3)) atTop (nhds 0) := by
  have hbase :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hshift :
      Tendsto (fun n : ℕ =>
          (1 : ℝ) / (((n + 2 : ℕ) : ℝ) + 1))
        atTop (nhds 0) := by
    exact hbase.comp (tendsto_add_atTop_nat 2)
  have hmul :
      Tendsto (fun n : ℕ =>
          T * ((1 : ℝ) / (((n + 2 : ℕ) : ℝ) + 1)))
        atTop (nhds (T * 0)) :=
    hshift.const_mul T
  have hmul' :
      Tendsto (fun n : ℕ => T * ((1 : ℝ) / ((n : ℝ) + 3)))
        atTop (nhds 0) := by
    convert hmul using 1
    · ext n
      norm_num [Nat.cast_add, add_assoc]
    · norm_num
  simpa [div_eq_mul_inv, mul_assoc] using hmul'

private theorem tendsto_right_window_scale (T : ℝ) :
    Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 3)) atTop (nhds T) := by
  have hleft := tendsto_left_window_scale T
  have hsub :
      Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 3))
        atTop (nhds (T - 0)) :=
    tendsto_const_nhds.sub hleft
  simpa using hsub

private theorem left_window_pos {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < T / ((n : ℝ) + 3) := by
  positivity

private theorem left_window_le_right {T : ℝ} (hT : 0 < T) (n : ℕ) :
    T / ((n : ℝ) + 3) ≤ T - T / ((n : ℝ) + 3) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 2 ≤ (n : ℝ) + 3 := by linarith
  have hfrac : T / ((n : ℝ) + 3) ≤ T / 2 := by
    exact div_le_div_of_nonneg_left hT.le (by norm_num) hden
  nlinarith

private theorem right_window_pos {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < T - T / ((n : ℝ) + 3) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 1 < (n : ℝ) + 3 := by linarith
  have hfrac_lt : T / ((n : ℝ) + 3) < T / 1 := by
    exact div_lt_div_of_pos_left hT (by norm_num) hden
  norm_num at hfrac_lt
  linarith

private theorem right_window_lt {T : ℝ} (hT : 0 < T) (n : ℕ) :
    T - T / ((n : ℝ) + 3) < T := by
  have hpos : 0 < T / ((n : ℝ) + 3) := left_window_pos hT n
  linarith

/-- Integrated dissipation plus endpoint/time-integral bounds imply the raw
closed-time Moser-gradient integrability frontier. -/
theorem intervalDomain_gradientTimeIntegrable_of_integratedDissipation_boundData
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hdata : IntervalDomainIntegratedDissipationGradientBoundData u T p0) :
    IntervalDomainRawMoserGradientTimeIntegrability u T p0 := by
  intro p hp
  let G : ℝ → ℝ := fun t =>
    integratedMoserGradientEnergy intervalDomain u p t
  have hT_pos : 0 < T := IsPaper2ClassicalSolution.T_pos hsol
  have hp_nonneg : 0 ≤ p := le_trans hdata.p0_nonneg hp
  have henergyNonneg :
      IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
  rcases hdata.energyUpperBound p hp with ⟨M, hM⟩
  rcases hdata.maxOneEnergyTimeIntegralBound p hp with ⟨H, hH⟩
  rcases hdiss p hp with ⟨C, hC_nonneg, hdrop⟩
  let a : ℕ → ℝ := fun n => T / ((n : ℝ) + 3)
  let b : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 3)
  let I : ℝ := (M + C * p * H) / 2
  have hlocal :
      ∀ n : ℕ, IntegrableOn G (Set.Ioc (a n) (b n)) volume := by
    intro n
    have ha_pos : 0 < a n := by
      simpa [a] using left_window_pos hT_pos n
    have hab : a n ≤ b n := by
      simpa [a, b] using left_window_le_right hT_pos n
    have hb_lt : b n < T := by
      simpa [b] using right_window_lt hT_pos n
    have hwin :
        IntervalIntegrable G volume (a n) (b n) := by
      have hstrict :=
        hdata.strictGradientWindowIntegrable p hp (a n) (b n)
          ha_pos hab hb_lt
      simpa [G, intervalDomainMoserGradientEnergy,
        integratedMoserGradientEnergy] using hstrict
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hwin
  have hbounded :
      ∀ᶠ n : ℕ in atTop,
        (∫ x in Set.Ioc (a n) (b n), ‖G x‖) ≤ I := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have ha_pos : 0 < a n := by
      simpa [a] using left_window_pos hT_pos n
    have hab : a n ≤ b n := by
      simpa [a, b] using left_window_le_right hT_pos n
    have hb_pos : 0 < b n := by
      simpa [b] using right_window_pos hT_pos n
    have hb_lt : b n < T := by
      simpa [b] using right_window_lt hT_pos n
    have haT : a n ∈ Set.Icc (0 : ℝ) T := by
      exact ⟨ha_pos.le, le_trans hab (le_of_lt hb_lt)⟩
    have hbT : b n ∈ Set.Icc (a n) T := by
      exact ⟨hab, le_of_lt hb_lt⟩
    have hYa_le :
        integratedMoserEnergy intervalDomain u p (a n) ≤ M :=
      hM (a n) haT
    have hYb_nonneg :
        0 ≤ integratedMoserEnergy intervalDomain u p (b n) :=
      henergyNonneg p hp hp_nonneg (b n) hb_pos hb_lt
    have hmaxInt :
        (∫ s in a n..b n,
          max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s)) ≤ H :=
      hH (a n) (b n) haT hbT
    have _hbridge :
        ∃ Cbridge, 0 ≤ Cbridge ∧
          2 * (∫ s in a n..b n,
            integratedMoserGradientEnergy intervalDomain u p s) ≤
          M + Cbridge * p * H := by
      simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
        integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
          (D := intervalDomain) (u := u) (T := T) (rho := rho)
          (p0 := p0) (p := p) (a := a n) (b := b n)
          (M := M) (H := H)
          hdiss hp hp_nonneg haT hbT
          (by simpa [integratedMoserEnergy] using hYa_le)
          (by simpa [integratedMoserEnergy] using hYb_nonneg)
          (by simpa [integratedMoserEnergy] using hmaxInt)
    have hCp_nonneg : 0 ≤ C * p :=
      mul_nonneg hC_nonneg hp_nonneg
    have hmax_scaled :
        C * p *
            (∫ s in a n..b n,
              max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s)) ≤
          C * p * H :=
      mul_le_mul_of_nonneg_left hmaxInt hCp_nonneg
    have hdrop_ab := hdrop (a n) haT (b n) hbT
    have hdrop_ab' :
        integratedMoserEnergy intervalDomain u p (b n) -
            integratedMoserEnergy intervalDomain u p (a n) +
          2 * (∫ s in a n..b n,
            integratedMoserGradientEnergy intervalDomain u p s) ≤
        C * p *
          (∫ s in a n..b n,
            max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s)) := by
      simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using hdrop_ab
    have htwo :
        2 * (∫ s in a n..b n, G s) ≤ M + C * p * H := by
      change
        2 * (∫ s in a n..b n,
          integratedMoserGradientEnergy intervalDomain u p s) ≤
            M + C * p * H
      nlinarith
    have hG_interval :
        (∫ s in a n..b n, G s) ≤ I := by
      dsimp [I]
      linarith
    have hset_eq :
        (∫ x in Set.Ioc (a n) (b n), ‖G x‖) =
          ∫ x in a n..b n, G x := by
      rw [intervalIntegral.integral_of_le hab]
      refine integral_congr_ae ?_
      filter_upwards with x
      exact Real.norm_of_nonneg
        (intervalDomain_integratedMoserGradientEnergy_nonneg
          (u := u) (p := p) (t := x))
    rw [hset_eq]
    exact hG_interval
  have hIoc :
      IntegrableOn G (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded
      (ι := ℕ) (l := atTop) (a := a) (b := b)
      (f := G) (I := I) (a₀ := 0) (b₀ := T)
      hlocal
      (by simpa [a] using tendsto_left_window_scale T)
      (by simpa [b] using tendsto_right_window_scale T)
      hbounded
  have hIcc :
      IntegrableOn G (Set.Icc (0 : ℝ) T) volume := by
    exact
      (integrableOn_Icc_iff_integrableOn_Ioc
        (f := G) (a := (0 : ℝ)) (b := T)).2 hIoc
  have huIcc :
      IntegrableOn G (Set.uIcc (0 : ℝ) T) volume := by
    simpa [Set.uIcc_of_le hT_pos.le] using hIcc
  simpa [IntervalDomainRawMoserGradientTimeIntegrability, G,
    integratedMoserGradientEnergy] using huIcc

/-- The same corollary packaged as the `gradientTimeIntegrable` field of the
classical regularity data used by the integrated Moser route. -/
theorem intervalDomain_classicalRegularityData_of_integratedDissipation_boundData
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hdata : IntervalDomainIntegratedDissipationGradientBoundData u T p0) :
    IntervalDomainIntegratedMoserClassicalRegularityData u T p0 where
  endpointEnergy := hend
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_of_integratedDissipation_boundData
      hsol hdiss hdata

#print axioms intervalDomain_gradientTimeIntegrable_of_integratedDissipation_boundData
#print axioms intervalDomain_classicalRegularityData_of_integratedDissipation_boundData

end ShenWork.IntervalDomainExistence.P3MoserGradientIntegrabilityFromDissipation

end
