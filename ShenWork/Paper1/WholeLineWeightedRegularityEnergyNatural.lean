import ShenWork.Paper1.WholeLineWeightedRegularityNaturalCoreProducer
import ShenWork.Paper1.WholeLineWeightedRegularityRemainderNatural

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural positive-time weighted energy inequality

This file combines the canonical fixed-point regularity capstone with the
natural corrected-remainder producer.  All exact-weight Hilbert trajectories,
the target-time `H1` data, and the physical remainder integrability are built
internally from the initial weighted closeness.
-/

/-- At every strictly positive interior time, the canonical BUC mild fixed
point satisfies the corrected full weighted-energy differential inequality
with any common bound valid at the target slice.  The construction clamp
`M₀` is deliberately separate from the energy bound `M`: global restart
segments may be built with a large invariant clamp even after the actual
solution has entered a smaller asymptotic strip. -/
theorem
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_common_of_target_bound_natural
    (p : CMParams)
    {M₀ M T t Blog eta c D E Kflux FD B : ℝ}
    (hM₀ : 0 ≤ M₀) (hT : 0 ≤ T) (ht0 : 0 < t) (htT : t < T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta)
    (heta_one : eta < 1) (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M₀ T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM₀ hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M₀)
    {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hMChi₀ : MChi p ≤ M₀)
    (hMChi : MChi p ≤ M)
    (htarget : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM₀ hT u₀ hsmall
        ⟨t, ht0.le, htT.le⟩).1 x ∈ Set.Icc (0 : ℝ) M)
    (hlog : ∀ y, |deriv U y / U y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - U y| ^ 2)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM₀ hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    deriv (paper5WeightedEnergy eta c u U) t ≤
      2 * paper531Quadratic c (paper531CommonA p M)
        (paper531CommonB p M) eta * paper5WeightedEnergy eta c u U t := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM₀ hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  obtain ⟨hu2, hhalf, hdiff, hWx2⟩ :=
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_natural
      p hM₀ hT ht0 htT hBlog heta heta_one hetaCap u₀ hsmall hstrip
        hchi hc hTW hbound hreg hMChi₀ hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        hdata_full
  obtain ⟨hsol, huMwin, _hu2win, hv2win⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_slice_data
      (c := c) p hM₀ hT ht0 (le_refl t) htT u₀ hsmall hstrip
  dsimp only at hsol huMwin hv2win
  have huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht0.le, htT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj t = Traj zt :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zt.2
    simpa only [coMovingPath, u, hext, Traj, zt] using htarget (x + c * t)
  have hv2 : ContDiff ℝ 2 (coMovingPath c v t) :=
    hv2win t ⟨le_rfl, le_rfl⟩
  have hU2 : ContDiff ℝ 2 U := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 V := hreg.V_contDiff_two hTW
  have hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t) := by
    have htmem : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0.le, htT.le⟩
    let zt : Set.Icc (0 : ℝ) T := ⟨t, htmem⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj t = Traj zt :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zt.2
    have huC : IsCUnifBdd (u t) := by
      simpa only [u, hext] using WholeLineBUC.isCUnifBdd (Traj zt)
    have hu0 : ∀ x, 0 ≤ u t x := by
      intro x
      simpa only [u, hext, Traj] using (hstrip zt x).1
    change (fun x => frozenElliptic p (u t) (x + c * t)) =
      frozenElliptic p (fun x => u t (x + c * t))
    exact (frozenElliptic_comp_add_const_fun p huC hu0 (c * t)).symm
  let E0 : ℝ := ∫ y : ℝ,
    Real.exp (2 * eta * y) * |u₀.1 y - U y| ^ 2
  let B0 : ℝ := Real.sqrt E0
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact integral_nonneg fun y =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hB0 : 0 ≤ B0 := Real.sqrt_nonneg _
  have hdata_energy :
      (∫ y : ℝ, Real.exp (2 * eta * y) * |u₀.1 y - U y| ^ 2) ≤
        B0 ^ 2 := by
    dsimp only [B0, E0]
    rw [Real.sq_sqrt hE0]
  obtain ⟨_EW, _hEW, hfull⟩ :=
    exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon
      p hT heta heta_one hB0 u₀ hsmall hTW hbound hreg hMChi₀
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has
        hfluxd_cont hreact hreact_cont hgrad_int hdata_full hdata_energy
  have hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2) := by
    have htmem : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0.le, htT.le⟩
    simpa only [u, Traj, coMovingPath] using (hfull t htmem).1
  exact paper5WeightedEnergy_deriv_le_common_of_coreIntegrability_natural
    p hchi hc heta hetaCap hsol ht0 htT hTW hreg hbound hMChi
      hu2 hv2 hU2 hV2 huM hvEq hclose hhalf hdiff hWx2

/-- Same-bound specialization of the target-bound theorem. -/
theorem wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_common_natural
    (p : CMParams)
    {M T t Blog eta c D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht0 : 0 < t) (htT : t < T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta)
    (heta_one : eta < 1) (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hMChi : MChi p ≤ M)
    (hlog : ∀ y, |deriv U y / U y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - U y| ^ 2)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    deriv (paper5WeightedEnergy eta c u U) t ≤
      2 * paper531Quadratic c (paper531CommonA p M)
        (paper531CommonB p M) eta * paper5WeightedEnergy eta c u U t := by
  apply
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_common_of_target_bound_natural
      p hM hT ht0 htT hBlog heta heta_one hetaCap u₀ hsmall hstrip
        hchi hc hTW hbound hreg hMChi hMChi
  · intro x
    exact hstrip ⟨t, ht0.le, htT.le⟩ x
  · exact hlog
  · exact hD
  · exact hFD
  · exact hB
  · exact hUd
  · exact hUdd
  · exact hUddcont
  · exact hflux
  · exact hfluxd
  · exact hflux_has
  · exact hfluxd_cont
  · exact hreact
  · exact hreact_cont
  · exact hgrad_int
  · exact hdata_full

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_common_of_target_bound_natural
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_common_natural
