import ShenWork.Paper1.Theorem12ConcreteBudget

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Selecting the strict Section 5 common bound

The eventual ceiling in Section 5 is a limsup bound by `MChi`; it does not
give the exact eventual pointwise bound `u <= MChi`.  The paper therefore
chooses a slightly larger common bound.  This file justifies that choice:
the corrected energy coefficient depends continuously on the common bound,
so its strict negativity at `MChi` persists at some `M > MChi`.
-/

/-- The corrected scalar energy coefficient is continuous in a positive
common profile bound.  Positivity is needed because some real powers have
negative exponents. -/
theorem paper531CommonQuadratic_continuousAt
    (p : CMParams) {M : ℝ} (hM : 0 < M) (c η : ℝ) :
    ContinuousAt
      (fun R => paper531Quadratic c
        (paper531CommonA p R) (paper531CommonB p R) η) M := by
  unfold paper531Quadratic paper531CommonA paper531CommonB
    paper5CommonB1 paper5CommonB2 paper5CommonB3 paper5CommonB4
    paper5CommonResolverK paper520B1
    paper5B2BoundFromDerivativeData
    paper531CorrectedAFromBounds paper531CorrectedBFromBounds
    paper5CorrectedResolverCapFactor
  have hMne : M ≠ 0 := ne_of_gt hM
  have hpow_mg : ContinuousAt (fun R : ℝ => R ^ (p.m + p.γ - 1)) M :=
    continuousAt_id.rpow_const (Or.inl hMne)
  have hpow_m1 : ContinuousAt (fun R : ℝ => R ^ (p.m - 1)) M :=
    continuousAt_id.rpow_const (Or.inl hMne)
  have hpow_2g1 : ContinuousAt (fun R : ℝ => R ^ (2 * (p.γ - 1))) M :=
    continuousAt_id.rpow_const (Or.inl hMne)
  have hpow_g : ContinuousAt (fun R : ℝ => R ^ p.γ) M :=
    continuousAt_id.rpow_const (Or.inl hMne)
  have hpow_m2 : ContinuousAt (fun R : ℝ => R ^ (p.m - 2)) M :=
    continuousAt_id.rpow_const (Or.inl hMne)
  have hpow_m : ContinuousAt (fun R : ℝ => R ^ p.m) M :=
    continuousAt_id.rpow_const (Or.inl hMne)
  fun_prop

/-- Strict negativity of the corrected scalar coefficient persists at some
strictly larger positive common bound. -/
theorem exists_common_bound_gt_of_quadratic_neg
    (p : CMParams) {M0 c η : ℝ} (hM0 : 0 < M0)
    (hneg : paper531Quadratic c
      (paper531CommonA p M0) (paper531CommonB p M0) η < 0) :
    ∃ M : ℝ, M0 < M ∧
      paper531Quadratic c
        (paper531CommonA p M) (paper531CommonB p M) η < 0 := by
  let f : ℝ → ℝ := fun M => paper531Quadratic c
    (paper531CommonA p M) (paper531CommonB p M) η
  have hcont : ContinuousAt f M0 := by
    exact paper531CommonQuadratic_continuousAt p hM0 c η
  have hbase : f M0 < 0 := by
    simpa [f] using hneg
  have hpre : f ⁻¹' Set.Iio 0 ∈ 𝓝 M0 :=
    hcont (Iio_mem_nhds hbase)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hball⟩
  refine ⟨M0 + δ / 2, by linarith, ?_⟩
  have hmem : M0 + δ / 2 ∈ Metric.ball M0 δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact hball hmem

/-- Specialization of the continuity choice at the paper's asymptotic
ceiling `MChi`. -/
theorem exists_common_bound_gt_MChi_of_quadratic_neg
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    {c η : ℝ}
    (hneg : paper531Quadratic c
      (paper531ConcreteA p) (paper531ConcreteB p) η < 0) :
    ∃ M : ℝ, MChi p < M ∧
      paper531Quadratic c
        (paper531CommonA p M) (paper531CommonB p M) η < 0 := by
  apply exists_common_bound_gt_of_quadratic_neg p hregime.MChi_pos
  simpa using hneg

/-- Every admissible corrected root-window weight admits a strictly larger
common bound while retaining the negative energy coefficient. -/
theorem exists_common_bound_gt_MChi_of_weight_window
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    {c η : ℝ} (hc : paper5CorrectedCStarStar p p.χ < c)
    (hminus : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < η)
    (hcap : η < stabilityWeightCap p) :
    ∃ M : ℝ, MChi p < M ∧
      paper531Quadratic c
        (paper531CommonA p M) (paper531CommonB p M) η < 0 := by
  apply exists_common_bound_gt_MChi_of_quadratic_neg p hregime
  simpa using (paper531ConcreteStabilityBudget p hregime).quadratic_neg
    hc hminus hcap

/-! ## Faithful concrete Section 5 capstone

The analytic core is parameterized by the common eventual bound selected
above.  It is not asked to prove an exact eventual `MChi` ceiling. -/

/-- The corrected theorem consumes the genuine whole-line Cauchy,
common-bound energy, and Step 4 block.  The scalar threshold, perturbed-root
budget, and the strictly larger common bound are all constructed internally. -/
theorem paper1_Theorem_1_2_amended_of_concrete_wholeLineCauchyEnergyStep4
    (hcore :
      ∀ p : CMParams, ∀ hregime : StableWaveParameterRegime p,
      ∀ c : ℝ, paper5CorrectedCStarStar p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        TravelingWaveRegularity p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ,
          paper531RootMinus c
              (paper531ConcreteStabilityBudget p hregime).A
              (paper531ConcreteStabilityBudget p hregime).B < η →
          η < stabilityWeightCap p →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          Section5ProfileInitialSignalBounds p U V u₀ →
          ∀ M : ℝ, MChi p < M →
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in atTop,
              coMovingWeightedL2Energy η c u U t ≤ E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤
              2 * paper531Quadratic c (paper531CommonA p M)
                (paper531CommonB p M) η * E t) ∧
            EventuallyIntegrableMovingFrameEnergy η 0
              (coMovingPath c u) U ∧
            EventuallyUniformMovingFrameSpatialModulus 0
              (coMovingPath c u) U ∧
            UniformMovingFrameLeftTailConvergence 0
              (coMovingPath c u) U) :
    Theorem_1_2_amended := by
  intro p hregime
  let budget := paper531ConcreteStabilityBudget p hregime
  refine ⟨paper5CorrectedCStarStar p, budget,
    paper5CorrectedCStarStar_asymptotic p,
    paper5CorrectedCStarStar_baseline_le p, ?_⟩
  intro c hc U V hTW hreg hstrict htail η hroot heta u₀ hu₀ hleft hclose
  have hsignal : Section5ProfileInitialSignalBounds p U V u₀ :=
    section5ProfileInitialSignalBounds_proved p hTW hreg
      hstrict.hasWaveUpperTailBound hu₀
  obtain ⟨M, hM, hq⟩ :=
    exists_common_bound_gt_MChi_of_weight_window p hregime hc hroot heta
  rcases hcore p hregime c hc U V u₀ hTW hreg hstrict htail η hroot heta
      hu₀ hleft hclose hsignal M hM with
    ⟨u, v, E, hsol, hcontrol, hcont, hderiv, hdiss,
      hint, hmod, hleftStep4⟩
  have hint_direct : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2) := by
    simpa [EventuallyIntegrableMovingFrameEnergy, movingFrameError,
      coMovingPath] using hint
  have hweighted : CoMovingWeightedL2Convergence η c u U :=
    CoMovingWeightedL2Convergence.of_paper531_energy_inequality
      hq hcontrol hint_direct hcont hderiv hdiss
  have hη : 0 < η :=
    (paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc |>.trans hroot
  exact ⟨u, v, hsol, hweighted,
    uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4
      hη hint hweighted hmod hleftStep4⟩

section Theorem12CommonBoundSelectionAxiomAudit

#print axioms paper531CommonQuadratic_continuousAt
#print axioms exists_common_bound_gt_of_quadratic_neg
#print axioms exists_common_bound_gt_MChi_of_quadratic_neg
#print axioms exists_common_bound_gt_MChi_of_weight_window
#print axioms
  paper1_Theorem_1_2_amended_of_concrete_wholeLineCauchyEnergyStep4

end Theorem12CommonBoundSelectionAxiomAudit

end ShenWork.Paper1
