import ShenWork.PDE.P3MoserHighExcursionProducer

open MeasureTheory Set
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserHighExcursionProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer

/-- The main integration theorem: from all four abstract data packages plus
`p0 ≥ 0`, produce `IntegratedMoserFirstCrossingStep`.

This goes through the threshold-plan crossing route: for each exponent `p`,
the plan is assembled from the supplied dissipation, interpolation, and Lp
data, then `LpPowerBoundedBefore_of_crossingThresholdPlan` does the
contradiction argument.

The `hgrad_nonneg` hypothesis asks that gradient integrals are nonneg — for
`intervalDomain` this follows from pointwise nonnegativity of squared norms. -/
theorem integratedMoserFirstCrossingStep_of_abstract_data
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hgrad_nonneg :
      ∀ q, p0 ≤ q →
        ∀ a b, 0 ≤ a → a ≤ b → b ≤ T →
          0 ≤ ∫ s in a..b, integratedMoserGradientEnergy D u q s) :
    IntegratedMoserFirstCrossingStep D u T rho p0 := by
  intro p hp hLp
  have hp_nonneg : 0 ≤ p := le_trans hp0_nonneg hp
  have hp_rho : p0 ≤ p + rho := le_trans hp (le_add_of_nonneg_right hrho.le)
  obtain ⟨Cq, hCq_nonneg, hCq_ineq⟩ := hdiss (p + rho) hp_rho
  rcases eq_or_lt_of_le hCq_nonneg with hCq_zero | hCq_pos
  · -- Case Cq = 0: the dissipation drop inequality with Cq=0 gives
    -- Y(t2) - Y(t1) + 2∫G ≤ 0, so Y is non-increasing.
    obtain ⟨C0, _hC0_nonneg, hC0_bound⟩ := hreg.initialPowerBound (p + rho) hp_rho
    refine ⟨C0, fun t ht0 htT => ?_⟩
    have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl _, by linarith⟩
    have htT' : t ∈ Icc (0 : ℝ) T := ⟨ht0.le, htT.le⟩
    have hdrop_0t := hCq_ineq 0 h0T t htT'
    have hCq_eq : Cq = 0 := hCq_zero.symm
    rw [hCq_eq, zero_mul, zero_mul] at hdrop_0t
    have hG_nn := hgrad_nonneg (p + rho) hp_rho 0 t (le_refl _) ht0.le htT.le
    unfold integratedMoserGradientEnergy at hG_nn
    nlinarith
  · -- Case Cq > 0: use the threshold plan
    obtain ⟨Cp, hCp_nonneg, hCp_ineq⟩ := hdiss p hp
    obtain ⟨Ceps, hCeps_nonneg, hCeps_ineq⟩ := hrel p hp (1 : ℝ) one_pos
    obtain ⟨C0, _hC0_nonneg, hC0_bound⟩ := hreg.initialPowerBound (p + rho) hp_rho
    obtain ⟨M_raw, hM_raw⟩ := hLp
    set M := max 1 M_raw with hM_def
    have hM_one : 1 ≤ M := le_max_left _ _
    have hM_bound : ∀ s, 0 < s → s < T →
        integratedMoserEnergy D u p s ≤ M :=
      fun s hs0 hsT => le_trans (hM_raw s hs0 hsT) (le_max_right _ _)
    set Tbar := max 1 T with hTbar_def
    set Gbar := (M + Cp * p * (Tbar * M)) / 2 with hGbar_def
    set R := 1 * Gbar + Tbar * (Ceps * M) with hR_def
    set K := max 1 (max (C0 + 1) (Cq * (p + rho) * (R + 1) + 1)) with hK_def
    have hplan : IntegratedMoserCrossingThresholdPlan D u T rho p0 p := by
      refine
        { M := M
          Cp := Cp
          Cq := Cq
          eps := 1
          Ceps := Ceps
          Tbar := Tbar
          Gbar := Gbar
          R := R
          K := K
          M_one_le := hM_one
          M_bound := hM_bound
          Cq_pos := hCq_pos
          eps_pos := one_pos
          Ceps_nonneg := hCeps_nonneg
          T_le_Tbar := le_max_right _ _
          one_le_Tbar := le_max_left _ _
          Gbar_def := rfl
          R_def := rfl
          K_one_le := le_max_left _ _
          init_lt_K := ?_
          K_gap := ?_
          gradient_bound := ?_
          rel_interp := ?_
          drop_q := hCq_ineq }
      · -- init_lt_K
        show integratedMoserEnergy D u (p + rho) 0 < K
        unfold integratedMoserEnergy
        calc D.integral (fun x => (u 0 x) ^ (p + rho))
            ≤ C0 := hC0_bound
          _ < C0 + 1 := lt_add_one _
          _ ≤ max (C0 + 1) (Cq * (p + rho) * (R + 1) + 1) := le_max_left _ _
          _ ≤ K := le_max_right _ _
      · -- K_gap
        have : Cq * (p + rho) * (R + 1) + 1 ≤ K :=
          le_trans (le_max_right _ _) (le_max_right _ _)
        linarith
      · -- gradient_bound
        intro a b ha_pos hab hb_lt
        have ha_mem : a ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
        have hb_mem : b ∈ Icc a T := ⟨hab, by linarith⟩
        have hCp_ineq_ab := hCp_ineq a ha_mem b hb_mem
        have hYa_le := hM_bound a ha_pos (by linarith)
        have hYb_nonneg := hnonneg p hp hp_nonneg b (by linarith) hb_lt
        have hCp_p_nonneg : 0 ≤ Cp * p := mul_nonneg hCp_nonneg hp_nonneg
        have hmax_bound :
            ∫ s in a..b, max 1 (integratedMoserEnergy D u p s) ≤
              (b - a) * M := by
          have := intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
            hab
            (hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab
              (Icc_subset_uIcc_zero_T_of_endpoint_memberships ha_mem hb_mem))
            (fun s hs => hM_bound s (lt_of_lt_of_le ha_pos hs.1)
              (lt_of_le_of_lt hs.2 (by linarith)))
          rwa [max_eq_right hM_one] at this
        have hba_le_Tbar : b - a ≤ Tbar := by
          calc b - a ≤ T := by linarith [ha_mem.1]
            _ ≤ Tbar := le_max_right _ _
        have hmax_le_Tbar : (b - a) * M ≤ Tbar * M :=
          mul_le_mul_of_nonneg_right hba_le_Tbar (le_trans zero_le_one hM_one)
        have hCpMax_le : Cp * p * ∫ s in a..b,
            max 1 (integratedMoserEnergy D u p s) ≤
            Cp * p * (Tbar * M) :=
          le_trans (mul_le_mul_of_nonneg_left hmax_bound hCp_p_nonneg)
            (mul_le_mul_of_nonneg_left hmax_le_Tbar hCp_p_nonneg)
        unfold integratedMoserEnergy at hYa_le hYb_nonneg hmax_bound hCpMax_le
        unfold integratedMoserGradientEnergy
        nlinarith [hCp_ineq_ab, hCpMax_le, hYa_le, hYb_nonneg]
      · -- rel_interp
        intro s hs0 hsT
        show integratedMoserEnergy D u (p + rho) s ≤
          1 * integratedMoserGradientEnergy D u p s +
          Ceps * integratedMoserEnergy D u p s
        unfold integratedMoserEnergy integratedMoserGradientEnergy
        exact hCeps_ineq s hs0 hsT
    exact LpPowerBoundedBefore_of_crossingThresholdPlan hplan
      (hreg.energyContinuous (p + rho) hp_rho)
      (fun a b ha hab hb => hgrad_nonneg (p + rho) hp_rho a b ha.le hab hb.le)
      (by
        intro a b ha hb hab
        exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset hab
          (hreg.powerTimeIntegrable (p + rho) hp_rho)
          (Icc_subset_uIcc_zero_T_of_endpoint_memberships
            ⟨by linarith, by linarith⟩ ⟨hab, by linarith⟩))
      (by
        intro a b ha hb hab
        exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset hab
          (hreg.gradientTimeIntegrable p hp)
          (Icc_subset_uIcc_zero_T_of_endpoint_memberships
            ⟨by linarith, by linarith⟩ ⟨hab, by linarith⟩))
      hp_nonneg hrho

open ShenWork.IntervalDomain in
/-- For `intervalDomain`, gradient energies are pointwise nonneg (squared norms),
so their time integrals over `[a,b]` with `a ≤ b` are nonneg. -/
theorem intervalDomain_gradient_integral_nonneg
    {u : ℝ → intervalDomain.Point → ℝ}
    {q a b : ℝ}
    (hab : a ≤ b) :
    0 ≤ ∫ s in a..b, integratedMoserGradientEnergy intervalDomain u q s :=
  intervalIntegral.integral_nonneg_of_forall hab
    (fun _ => intervalDomain_integral_nonneg _
      (fun _ => sq_nonneg _))

open ShenWork.IntervalDomain in
/-- Produce `IntegratedMoserFirstCrossingStep` for `intervalDomain` from the
four abstract data packages plus `p0 ≥ 0`. -/
theorem intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
    {u : ℝ → intervalDomain.Point → ℝ}
    {T rho p0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  integratedMoserFirstCrossingStep_of_abstract_data hreg hnonneg hdiss hrel hrho hp0_nonneg
    (fun _q _hq _a _b _ha hab _hb =>
      intervalDomain_gradient_integral_nonneg hab)

#print axioms integratedMoserFirstCrossingStep_of_abstract_data
#print axioms intervalDomain_gradient_integral_nonneg
#print axioms intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data

end ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer

end
