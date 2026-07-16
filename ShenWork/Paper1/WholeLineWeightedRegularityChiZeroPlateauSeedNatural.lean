import ShenWork.Paper1.WholeLineWeightedRegularityPlateauSeedNatural
import ShenWork.Paper1.WholeLineWeightedRegularityWaveStaticBoundedNatural

open Filter MeasureTheory Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A canonical positive-time plateau seed at zero sensitivity

The nonzero-sensitivity static package chooses derivative budgets by dividing
by a power of `|chi|`, so it cannot be specialized to `chi = 0`.  The bounded
static package instead obtains a finite `U'` bound from the wave tails.  This
file connects that package to the already proved positive-time weighted
`H^1` propagation and lower-plateau seed theorem.

The conclusion is deliberately only an initial ordering.  Propagating and
lifting this plateau to the equilibrium value one is a separate scalar KPP
comparison problem.
-/

/-- For zero sensitivity, the canonical global orbit admits a positive-time
patched two-exponential lower-plateau seed.  The hypotheses are the paper's
one-sided initial positivity and exact weighted initial closeness; no
whole-line uniform positive floor is assumed. -/
theorem
    wholeLineCauchyGlobal_exists_positive_time_lowerBarrierPlateau_seed_chi_zero_natural
    (p : CMParams) (hchi : p.χ = 0)
    {c κ₁ eta cap B : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hκ₁ : kappa c < κ₁) (heta : kappa c < eta)
    (heta_one : eta < 1) (hcap : kappa c < cap)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (htail : HasWaveRightTailAsymptotic c κ₁ U)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hu₀left : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∃ kappaTilde : ℝ,
        kappa c < kappaTilde ∧
        kappaTilde < κ₁ ∧
        kappaTilde < eta ∧
        kappaTilde < cap ∧
        kappaTilde < 2 * kappa c ∧
        ∃ D : ℝ, 1 ≤ D ∧ B < D ∧
          ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
            coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀ x := by
  have hchi_nonpos : p.χ ≤ 0 := hchi.le
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi_nonpos
  have hκ : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt
      (paper5CorrectedCStarStar_baseline_le p) hc
  have heta_pos : 0 < eta := hκ.trans heta
  obtain ⟨Dwave, hs⟩ :=
    paper5WaveStaticBoundedData_of_wave p hc hTW hbound hreg
  apply exists_positive_time_lowerBarrierPlateau_seed_of_H1
    (u := wholeLineCauchyGlobalU p u₀) (u₀ := u₀.1)
    (U := U) hκ hκ₁ heta hcap
  · exact wholeLineCauchyGlobal_hasUniformInitialTrace p u₀
  · exact hu₀left
  · intro t x ht
    exact wholeLineCauchyGlobal_pos_of_posAtBot
      p hregime u₀ hu₀ hu₀left ht x
  · intro t ht
    exact wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hregime u₀ hu₀ ht
  · exact hreg.U_contDiff_two hTW
  · intro t ht
    apply paper5WeightedPopulation_sq_integrable_of_weighted_difference
    exact
      wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness
        (D := Dwave)
        (E := paper5WaveSecondDerivativeBoundOf p c Dwave)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p Dwave)
        (B := paper5WaveShiftedReactionBound p)
        p hchi_nonpos u₀ ht heta_pos heta_one hTW hbound hreg
          hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux
          hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial
  · intro t ht
    exact
      paper5WeightedPopulationX_sq_integrable_global_chi_nonpos_of_initialCloseness
        (Blog := 1) (D := Dwave)
        (E := paper5WaveSecondDerivativeBoundOf p c Dwave)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p Dwave)
        (B := paper5WaveShiftedReactionBound p)
        p hchi_nonpos u₀ hu₀ ht hs.hBlog heta_pos heta_one hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
  · exact htail

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_exists_positive_time_lowerBarrierPlateau_seed_chi_zero_natural

end AxiomAudit

end ShenWork.Paper1
