import ShenWork.Paper1.WholeLineWeightedRegularityChiNegCompatiblePlateauSeedNatural

open Filter MeasureTheory Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A scaled-compatible plateau seed at a prescribed positive time

The first natural seed theorem chooses some positive time from the initial
trace.  Late-window propagation instead needs the seed at an already selected
canonical restart seam.  Positivity, the one-sided left floor, and exact
weighted `H¹` regularity are all available at every positive global time, so
the same profile argument can be applied at that prescribed slice.
-/

/-- At every prescribed positive time, the canonical negative-sensitivity
orbit lies above a patched plateau whose one coefficient satisfies both the
paper conditions and an arbitrary scaled-trap margin `Bfun`.

No whole-line positive floor is assumed: the physical datum supplies only
`StrictlyPositiveAtLeft`, which is preserved by the canonical segments. -/
theorem
    wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_neg
    (p : CMParams) (hchi : p.χ < 0)
    (Bfun : ℝ → ℝ) {Q c κ₁ eta cap t₀ : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hQ : 1 ≤ Q)
    (hκ₁ : kappa c < κ₁) (heta : kappa c < eta)
    (heta_one : eta < 1) (hcap : kappa c < cap)
    (hcapRange :
      cap ≤ min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1))
    (hα_le : p.α ≤ p.m + p.γ - 1)
    (ht₀ : 0 < t₀)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (htail : HasWaveRightTailAsymptotic c κ₁ U)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hu₀left : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ kappaTilde D : ℝ,
      kappa c < kappaTilde ∧
      kappaTilde < κ₁ ∧
      kappaTilde < eta ∧
      kappaTilde < cap ∧
      kappaTilde < 2 * kappa c ∧
      PaperLemma42ExactConditions p c (kappa c) kappaTilde Q ∧
      1 ≤ D ∧
      paperDMin p.χ Q (kappa c) kappaTilde p.m p.γ c < D ∧
      Bfun kappaTilde < D ∧
      (∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        constantSubsolutionThreshold p.χ (kappa c) kappaTilde D) ∧
      ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀ x := by
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi.le
  have hbaseline : stabilitySpeedBaseline p ≤
      paper5CorrectedCStarStar p p.χ :=
    paper5CorrectedCStarStar_baseline_le p
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  have hκ : 0 < kappa c := kappa_pos_of_two_lt hc_two
  have hκ_one : kappa c < 1 := kappa_lt_one_of_two_lt hc_two
  have hcκ : c = kappa c + (kappa c)⁻¹ :=
    (kappa_add_inv_eq_of_two_lt hc_two).symm
  have heta_pos : 0 < eta := hκ.trans heta
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave
      p (ne_of_lt hchi) hc hTW hbound hreg
  have hu2 : ContDiff ℝ 2
      (coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀) :=
    wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hregime u₀ hu₀ ht₀
  have hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U t₀ x ^ 2) := by
    apply paper5WeightedPopulation_sq_integrable_of_weighted_difference
    exact
      wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness
        (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hchi.le u₀ ht₀ heta_pos heta_one hTW hbound hreg hs.hD hs.hFD
          hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial
  have hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U t₀ x ^ 2) := by
    exact
      paper5WeightedPopulationX_sq_integrable_global_chi_nonpos_of_initialCloseness
        (Blog := 1) (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hchi.le u₀ hu₀ ht₀ hs.hBlog heta_pos heta_one hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
  obtain ⟨C, hC, henv⟩ :=
    exists_weightedDifference_pointwise_envelope_of_H1
      hu2 (hreg.U_contDiff_two hTW) hW2 hWx2
  have hwpos : ∀ x,
      0 < coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀ x := by
    intro x
    exact wholeLineCauchyGlobal_pos_of_posAtBot
      p hregime u₀ hu₀ hu₀left ht₀ (x + c * t₀)
  let n := wholeLineCauchyGlobalIndex p u₀ t₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t₀
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht₀.le,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht₀.le).le⟩
  have hglobalLeft : StrictlyPositiveAtLeft
      (wholeLineCauchyGlobalU p u₀ t₀) := by
    have hsegLeft :=
      (wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
        p hregime u₀ hu₀ hu₀left n).2.2 z
    have heq' : wholeLineCauchyGlobalU p u₀ t₀ =
        (wholeLineCauchyGlobalSegment p u₀ n z).1 := by
      funext x
      have heq := congrArg (fun w : WholeLineBUC => w.1 x)
        (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht₀.le)
      simpa [wholeLineCauchyGlobalU, n, q, z] using heq
    rw [heq']
    exact hsegLeft
  have hwleft : StrictlyPositiveAtLeft
      (coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀) := by
    simpa only [coMovingPath] using hglobalLeft.shift (c * t₀)
  exact exists_chiNonpos_compatible_lowerBarrierPlateau_seed_of_profile_bounds
    p Bfun hκ hκ_one hκ₁ heta hcap hQ hcapRange hcκ hchi.le hα_le
      hu2.continuous hwpos hwleft hC henv htail

#print axioms
  wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_neg

end ShenWork.Paper1
