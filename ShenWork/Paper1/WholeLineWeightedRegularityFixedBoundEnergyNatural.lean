import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyChiPosNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyDifferentiableNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyDifferentiableChiPosNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroCoreAssemblyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityWaveStaticBoundedNatural
import ShenWork.Paper1.WholeLineCauchyLongTimeBound
import ShenWork.Paper1.WholeLineCauchyChiPosLongTimeBound

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Eventual natural weighted-energy inequality at a fixed common bound

The Section 5 common bound is selected before the analytic energy argument.
This file keeps that caller-supplied bound fixed: the canonical whole-line
Cauchy solution eventually lies below it, so the positive-time natural energy
inequality has exactly the coefficient `paper531CommonA/B p M` requested by
the corrected stability argument.
-/

/-- For every stable sensitivity branch and every caller-supplied strict
common bound `M > MChi p`, the canonical global weighted energy eventually
satisfies the corrected differential inequality evaluated at that same `M`.

At `chi = 0` both corrected common-bound coefficients vanish identically, so
the sharp zero-sensitivity inequality supplies the result without waiting for
an upper-bound tail. -/
theorem
    wholeLineCauchyGlobal_eventually_weightedEnergy_deriv_le_fixed_common_natural
    (p : CMParams) (hstable : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {M eta c : ℝ} {U V : ℝ → ℝ}
    (hM : MChi p < M)
    (heta : 0 < eta) (heta_one : eta < 1)
    (hetaCap : eta < stabilityWeightCap p)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∀ᶠ t in atTop, 0 < t ∧
      deriv (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t ≤
        2 * paper531Quadratic c (paper531CommonA p M)
            (paper531CommonB p M) eta *
          paper5WeightedEnergy eta c
            (wholeLineCauchyGlobalU p u₀) U t := by
  obtain ⟨D, hs⟩ :=
    paper5WaveStaticBoundedData_of_wave p hc hTW hbound hreg
  rcases lt_trichotomy p.χ 0 with hchi_neg | hchi_zero | hchi_pos
  · have hMone : 1 < M := by
      rw [hstable.MChi_eq_one_of_chi_neg hchi_neg] at hM
      exact hM
    have htail :=
      wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
        p hchi_neg.le u₀ hu₀ (M - 1) (by linarith)
    filter_upwards [htail, eventually_gt_atTop (0 : ℝ)] with t ht htp
    refine ⟨htp, ?_⟩
    apply
      wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_natural
        p hchi_neg u₀ hu₀ htp hM.le
    · intro x
      have hx := ht x
      linarith
    · exact hs.hBlog
    · exact heta
    · exact heta_one
    · exact hetaCap
    · exact hc
    · exact hTW
    · exact hbound
    · exact hreg
    · exact hs.hlog
    · exact hs.hD
    · exact hs.hFD
    · exact hs.hB
    · exact hs.hUd
    · exact hs.hUdd
    · exact hs.hUddcont
    · exact hs.hflux
    · exact hs.hfluxd
    · exact hs.hflux_has
    · exact hs.hfluxd_cont
    · exact hs.hreact
    · exact hs.hreact_cont
    · exact hs.hgrad_int
    · exact hinitial
  · have hchi : p.χ = 0 := hchi_zero
    have hA : paper531CommonA p M = 0 := by
      simp [paper531CommonA, paper531CorrectedAFromBounds, hchi]
    have hB : paper531CommonB p M = 0 := by
      simp [paper531CommonB, paper531CorrectedBFromBounds, hchi]
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine ⟨ht, ?_⟩
    have hdata :=
      wholeLineCauchyGlobal_weightedEnergy_data_chi_zero_natural
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hchi u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
    simpa [paper531Quadratic, hA, hB] using hdata.2
  · have hbranch := hstable.positive_branch_of_chi_nonneg hchi_pos.le
    have hchi_lt : p.χ < 1 :=
      lt_of_lt_of_le hbranch.1 (chiStar_le_one p)
    have htail :=
      wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
        p hchi_pos hchi_lt hbranch.2
        hstable.toWholeLineCauchyCeilingRegime u₀ hu₀
        (M - MChi p) (by linarith)
    filter_upwards [htail, eventually_gt_atTop (0 : ℝ)] with t ht htp
    refine ⟨htp, ?_⟩
    apply
      wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_chi_pos_natural
        p hstable hchi_pos u₀ hu₀ htp hM.le
    · intro x
      have hx := ht x
      linarith
    · exact hs.hBlog
    · exact heta
    · exact heta_one
    · exact hetaCap
    · exact hc
    · exact hTW
    · exact hbound
    · exact hreg
    · exact hs.hlog
    · exact hs.hD
    · exact hs.hFD
    · exact hs.hB
    · exact hs.hUd
    · exact hs.hUdd
    · exact hs.hUddcont
    · exact hs.hflux
    · exact hs.hfluxd
    · exact hs.hflux_has
    · exact hs.hfluxd_cont
    · exact hs.hreact
    · exact hs.hreact_cont
    · exact hs.hgrad_int
    · exact hinitial

/-- In the stable parameter regime, the canonical physical weighted energy is
differentiable at every positive time, uniformly across the negative, zero,
and positive sensitivity branches. -/
theorem wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_stable_natural
    (p : CMParams) (hstable : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {eta c t : ℝ} {U V : ℝ → ℝ}
    (ht : 0 < t)
    (heta : 0 < eta) (heta_one : eta < 1)
    (hetaCap : eta < stabilityWeightCap p)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    DifferentiableAt ℝ (paper5WeightedEnergy eta c
      (wholeLineCauchyGlobalU p u₀) U) t := by
  obtain ⟨D, hs⟩ :=
    paper5WaveStaticBoundedData_of_wave p hc hTW hbound hreg
  rcases lt_trichotomy p.χ 0 with hchi_neg | hchi_zero | hchi_pos
  · exact
      wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_natural
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hchi_neg u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
  · exact
      (wholeLineCauchyGlobal_weightedEnergy_data_chi_zero_natural
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hchi_zero u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial).1
  · exact
      wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_chi_pos_natural
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hstable hchi_pos u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW
          hbound hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd
          hs.hUddcont hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont
          hs.hreact hs.hreact_cont hs.hgrad_int hinitial

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_eventually_weightedEnergy_deriv_le_fixed_common_natural
#print axioms
  wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_stable_natural

end AxiomAudit

end ShenWork.Paper1
