import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyNatural
import ShenWork.Paper1.Theorem12CommonBoundSelection
import ShenWork.Paper1.WholeLineCauchyLongTimeBound

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Eventual strict weighted-energy dissipation for negative sensitivity

The global maximum estimate only gives a limsup ceiling.  We first select a
common bound strictly above `MChi` at which the corrected quadratic remains
negative, then wait until the canonical global solution lies below that
bound.  The positive-time natural energy theorem applies on every remaining
slice.
-/

/-- For strictly negative sensitivity, every admissible corrected weight has
a strictly dissipative natural weighted-energy inequality on a time tail.
The construction clamp of the global solution is absent from the resulting
coefficient. -/
theorem
    wholeLineCauchyGlobal_eventually_weightedEnergy_deriv_le_negative_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c D E Kflux FD B : ℝ}
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
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
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ M : ℝ, MChi p < M ∧
      paper531Quadratic c (paper531CommonA p M)
          (paper531CommonB p M) eta < 0 ∧
      ∀ᶠ t in atTop, 0 < t ∧
        deriv (paper5WeightedEnergy eta c
          (wholeLineCauchyGlobalU p u₀) U) t ≤
          2 * paper531Quadratic c (paper531CommonA p M)
              (paper531CommonB p M) eta *
            paper5WeightedEnergy eta c
              (wholeLineCauchyGlobalU p u₀) U t := by
  obtain ⟨M, hM, hquadratic⟩ :=
    exists_common_bound_gt_MChi_of_weight_window
      p hregime hc hroot hetaCap
  have hMone : 1 < M := by
    rw [hregime.MChi_eq_one_of_chi_neg hchi] at hM
    exact hM
  have htail :=
    wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
      p hchi.le u₀ hu₀ (M - 1) (by linarith)
  refine ⟨M, hM, hquadratic, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℝ)] with t ht htp
  refine ⟨htp, ?_⟩
  apply
    wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_natural
      p hchi u₀ hu₀ htp hM.le
  · intro x
    have hx := ht x
    linarith
  · exact hBlog
  · exact heta
  · exact heta_one
  · exact hetaCap
  · exact hc
  · exact hTW
  · exact hbound
  · exact hreg
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
  · exact hinitial

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_eventually_weightedEnergy_deriv_le_negative_natural

end AxiomAudit

end ShenWork.Paper1
