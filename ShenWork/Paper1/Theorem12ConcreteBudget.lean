import ShenWork.Paper1.Theorem12WeightedEnergy
import ShenWork.Paper1.CStarStarSpecSatisfiable
import ShenWork.Paper1.Theorem12Corrected

noncomputable section

namespace ShenWork.Paper1

/-!
# Concrete corrected Section 5 stability budget

This file substitutes the actual coefficient bounds into the corrected
quadratic from (5.31).  Its threshold simultaneously dominates the Remark
5.1 derivative condition, the two-sided logarithmic Riccati barrier, and the
exact cap-evaluation condition for the perturbed roots.
-/

def paper5ConcreteLu (p : CMParams) : ℝ :=
  remark51MPrime p / remark5ChiSigma p paper5Sigma

def paper5ConcreteB1 (p : CMParams) : ℝ :=
  paper520B1 p (MChi p)

def paper5ConcreteB2 (p : CMParams) : ℝ :=
  paper5B2BoundFromDerivativeData p (MChi p) (paper5ConcreteLu p) 1

def paper5ConcreteB3 (p : CMParams) : ℝ :=
  p.m * (MChi p) ^ (p.m - 1) * paper5ConcreteLu p

def paper5ConcreteB4 (p : CMParams) : ℝ :=
  (MChi p) ^ p.m

def paper5ConcreteResolverK (p : CMParams) : ℝ :=
  paper5CorrectedResolverCapFactor p (MChi p)

/-! ## Common-bound variants

Section 5 does not obtain the exact pointwise bound `u <= MChi`.  It first
chooses an arbitrary common bound `M > MChi` from the eventual limsup estimate.
The following constants retain that common bound instead of prematurely
specializing it to `MChi`.
-/

def paper5CommonB1 (p : CMParams) (M : ℝ) : ℝ :=
  paper520B1 p M

def paper5CommonB2 (p : CMParams) (M : ℝ) : ℝ :=
  paper5B2BoundFromDerivativeData p M (paper5ConcreteLu p) 1

def paper5CommonB3 (p : CMParams) (M : ℝ) : ℝ :=
  p.m * M ^ (p.m - 1) * paper5ConcreteLu p

def paper5CommonB4 (p : CMParams) (M : ℝ) : ℝ :=
  M ^ p.m

def paper5CommonResolverK (p : CMParams) (M : ℝ) : ℝ :=
  paper5CorrectedResolverCapFactor p M

def paper531CommonA (p : CMParams) (M : ℝ) : ℝ :=
  paper531CorrectedAFromBounds p
    (paper5CommonB1 p M) (paper5CommonB3 p M)
    (paper5CommonResolverK p M)

def paper531CommonB (p : CMParams) (M : ℝ) : ℝ :=
  paper531CorrectedBFromBounds p M
    (paper5CommonB1 p M) (paper5CommonB2 p M)
    (paper5CommonB3 p M) (paper5CommonB4 p M)
    (paper5CommonResolverK p M)

@[simp] theorem paper5CommonB1_MChi (p : CMParams) :
    paper5CommonB1 p (MChi p) = paper5ConcreteB1 p := rfl

@[simp] theorem paper5CommonB2_MChi (p : CMParams) :
    paper5CommonB2 p (MChi p) = paper5ConcreteB2 p := rfl

@[simp] theorem paper5CommonB3_MChi (p : CMParams) :
    paper5CommonB3 p (MChi p) = paper5ConcreteB3 p := rfl

@[simp] theorem paper5CommonB4_MChi (p : CMParams) :
    paper5CommonB4 p (MChi p) = paper5ConcreteB4 p := rfl

@[simp] theorem paper5CommonResolverK_MChi (p : CMParams) :
    paper5CommonResolverK p (MChi p) = paper5ConcreteResolverK p := rfl

def paper531ConcreteA (p : CMParams) : ℝ :=
  paper531CorrectedAFromBounds p
    (paper5ConcreteB1 p) (paper5ConcreteB3 p)
    (paper5ConcreteResolverK p)

def paper531ConcreteB (p : CMParams) : ℝ :=
  paper531CorrectedBFromBounds p (MChi p)
    (paper5ConcreteB1 p) (paper5ConcreteB2 p)
    (paper5ConcreteB3 p) (paper5ConcreteB4 p)
    (paper5ConcreteResolverK p)

@[simp] theorem paper531CommonA_MChi (p : CMParams) :
    paper531CommonA p (MChi p) = paper531ConcreteA p := rfl

@[simp] theorem paper531CommonB_MChi (p : CMParams) :
    paper531CommonB p (MChi p) = paper531ConcreteB p := rfl

/-- The right-hand side in the paper's strengthened derivative speed
condition, at `sigma = 1/6`. -/
def paper5RemarkSpeedThreshold (p : CMParams) : ℝ :=
  max
    (p.γ + remark5ChiSigma p paper5Sigma +
      1 / (p.γ + remark5ChiSigma p paper5Sigma))
    (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
      remark5ChiSigma p paper5Sigma)

/-- Exact speed needed to put the weight cap between the corrected roots. -/
def paper531ConcreteCapThreshold (p : CMParams) : ℝ :=
  paper531ConcreteA p + stabilityWeightCap p +
    (1 + paper531ConcreteB p) / stabilityWeightCap p

/-- One concrete corrected speed threshold dominating every scalar and
coefficient requirement in the Section 5 energy calculation. -/
def paper5ConcreteRequiredSpeed (p : CMParams) : ℝ :=
  max (cStarStarWitness p p.χ)
    (max (paper5RemarkSpeedThreshold p)
      (max (paper52MonotoneBarrierSpeed p)
        (paper531ConcreteCapThreshold p)))

/-- Preserve the paper's asymptotic family away from the parameter's actual
`chi`, while raising its value at the actual parameter to the honest
corrected threshold. -/
def paper5CorrectedCStarStar (p : CMParams) (χ : ℝ) : ℝ :=
  if χ = p.χ then paper5ConcreteRequiredSpeed p else cStarStarWitness p χ

theorem paper5ConcreteLu_nonneg
    (p : CMParams) (hM : 0 < MChi p) :
    0 ≤ paper5ConcreteLu p := by
  unfold paper5ConcreteLu
  exact div_nonneg (remark51MPrime_nonneg_of_MChi_pos p hM)
    (remark5ChiSigma_nonneg p paper5Sigma)

theorem paper5ConcreteBounds_nonneg
    (p : CMParams) (hM : 0 < MChi p) :
    0 ≤ paper5ConcreteB1 p ∧ 0 ≤ paper5ConcreteB2 p ∧
      0 ≤ paper5ConcreteB3 p ∧ 0 ≤ paper5ConcreteB4 p ∧
      0 ≤ paper5ConcreteResolverK p := by
  have hM0 : 0 ≤ MChi p := hM.le
  have hLu := paper5ConcreteLu_nonneg p hM
  have hB1 : 0 ≤ paper5ConcreteB1 p := by
    exact paper520B1_nonneg p hM0
  have hB2 : 0 ≤ paper5ConcreteB2 p := by
    exact paper5B2BoundFromDerivativeData_nonneg p
      (MChi p) (paper5ConcreteLu p) 1
  have hB3 : 0 ≤ paper5ConcreteB3 p := by
    unfold paper5ConcreteB3
    exact mul_nonneg
      (mul_nonneg (le_trans zero_le_one p.hm)
        (Real.rpow_nonneg hM0 _)) hLu
  have hB4 : 0 ≤ paper5ConcreteB4 p := by
    unfold paper5ConcreteB4
    exact Real.rpow_nonneg hM0 _
  have hK : 0 ≤ paper5ConcreteResolverK p := by
    unfold paper5ConcreteResolverK paper5CorrectedResolverCapFactor
    dsimp only
    positivity
  exact ⟨hB1, hB2, hB3, hB4, hK⟩

theorem paper5CommonBounds_nonneg
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (hMChi : 0 < MChi p) :
    0 ≤ paper5CommonB1 p M ∧ 0 ≤ paper5CommonB2 p M ∧
      0 ≤ paper5CommonB3 p M ∧ 0 ≤ paper5CommonB4 p M ∧
      0 ≤ paper5CommonResolverK p M := by
  have hLu := paper5ConcreteLu_nonneg p hMChi
  have hB1 : 0 ≤ paper5CommonB1 p M :=
    paper520B1_nonneg p hM
  have hB2 : 0 ≤ paper5CommonB2 p M :=
    paper5B2BoundFromDerivativeData_nonneg p M (paper5ConcreteLu p) 1
  have hB3 : 0 ≤ paper5CommonB3 p M := by
    unfold paper5CommonB3
    exact mul_nonneg
      (mul_nonneg (le_trans zero_le_one p.hm)
        (Real.rpow_nonneg hM _)) hLu
  have hB4 : 0 ≤ paper5CommonB4 p M := by
    exact Real.rpow_nonneg hM _
  have hK : 0 ≤ paper5CommonResolverK p M := by
    unfold paper5CommonResolverK paper5CorrectedResolverCapFactor
    positivity
  exact ⟨hB1, hB2, hB3, hB4, hK⟩

theorem paper531CommonAB_nonneg
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (hMChi : 0 < MChi p) :
    0 ≤ paper531CommonA p M ∧ 0 ≤ paper531CommonB p M := by
  obtain ⟨hB1, hB2, hB3, hB4, hK⟩ :=
    paper5CommonBounds_nonneg p hM hMChi
  constructor
  · unfold paper531CommonA paper531CorrectedAFromBounds
    positivity
  · unfold paper531CommonB paper531CorrectedBFromBounds
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hg0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
    have hpow : 0 ≤ M ^ (p.m + p.γ - 1) :=
      Real.rpow_nonneg hM _
    positivity

theorem paper531ConcreteAB_nonneg
    (p : CMParams) (hM : 0 < MChi p) :
    0 ≤ paper531ConcreteA p ∧ 0 ≤ paper531ConcreteB p := by
  obtain ⟨hB1, hB2, hB3, hB4, hK⟩ :=
    paper5ConcreteBounds_nonneg p hM
  constructor
  · unfold paper531ConcreteA paper531CorrectedAFromBounds
    positivity
  · unfold paper531ConcreteB paper531CorrectedBFromBounds
    have hM0 : 0 ≤ MChi p := hM.le
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hg0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
    have hpow : 0 ≤ (MChi p) ^ (p.m + p.γ - 1) :=
      Real.rpow_nonneg hM0 _
    positivity

theorem paper5CorrectedCStarStar_value (p : CMParams) :
    paper5CorrectedCStarStar p p.χ = paper5ConcreteRequiredSpeed p := by
  simp [paper5CorrectedCStarStar]

theorem paper5CorrectedCStarStar_required_le (p : CMParams) :
    paper5ConcreteRequiredSpeed p ≤ paper5CorrectedCStarStar p p.χ := by
  rw [paper5CorrectedCStarStar_value]

theorem paper5CorrectedCStarStar_baseline_le (p : CMParams) :
    stabilitySpeedBaseline p ≤ paper5CorrectedCStarStar p p.χ := by
  rw [paper5CorrectedCStarStar_value]
  exact (stabilitySpeedBaseline_le_cStarStarWitness p).trans
    (le_max_left _ _)

theorem paper5CorrectedCStarStar_remark_le (p : CMParams) :
    paper5RemarkSpeedThreshold p ≤ paper5CorrectedCStarStar p p.χ := by
  rw [paper5CorrectedCStarStar_value]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem paper5CorrectedCStarStar_barrier_le (p : CMParams) :
    paper52MonotoneBarrierSpeed p ≤ paper5CorrectedCStarStar p p.χ := by
  rw [paper5CorrectedCStarStar_value]
  exact (le_max_left _ _).trans <|
    (le_max_right _ _).trans (le_max_right _ _)

theorem paper5CorrectedCStarStar_cap_le (p : CMParams) :
    paper531ConcreteCapThreshold p ≤ paper5CorrectedCStarStar p p.χ := by
  rw [paper5CorrectedCStarStar_value]
  exact (le_max_right _ _).trans <|
    (le_max_right _ _).trans (le_max_right _ _)

theorem paper5CorrectedCStarStar_asymptotic_of_chi_ne_zero
    (p : CMParams) (hχ : p.χ ≠ 0) :
    StabilitySpeedThresholdFamilyAsymptotic p
      (paper5CorrectedCStarStar p) := by
  refine ⟨1, one_pos, |p.χ|, abs_pos.mpr hχ, ?_⟩
  intro χ hχsmall
  have hne : χ ≠ p.χ := by
    intro heq
    subst χ
    exact (lt_irrefl |p.χ|) hχsmall
  rw [paper5CorrectedCStarStar]
  simp only [hne, ↓reduceIte, cStarStarWitness]
  have hpow : 0 ≤ |χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg χ) _
  rw [show p.γ + p.γ⁻¹ + |χ| ^ (1 / 6 : ℝ) -
      (p.γ + p.γ⁻¹) = |χ| ^ (1 / 6 : ℝ) by ring,
    abs_of_nonneg hpow, one_mul]

theorem paper5ConcreteRequiredSpeed_eq_witness_of_chi_eq_zero
    (p : CMParams) (hχ : p.χ = 0) :
    paper5ConcreteRequiredSpeed p = cStarStarWitness p 0 := by
  have hγpos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hγinv : 0 < p.γ⁻¹ := inv_pos.mpr hγpos
  have hγtwo : 2 ≤ p.γ + p.γ⁻¹ := two_le_gamma_add_inv p
  have hM : MChi p = 1 := by simp [MChi, hχ]
  have hA : paper531ConcreteA p = 0 := by
    simp [paper531ConcreteA, paper531CorrectedAFromBounds,
      paper5ConcreteB1, paper5ConcreteB3, hχ]
  have hB : paper531ConcreteB p = 0 := by
    simp [paper531ConcreteB, paper531CorrectedBFromBounds, hχ]
  have hremark : paper5RemarkSpeedThreshold p = p.γ + p.γ⁻¹ := by
    simp [paper5RemarkSpeedThreshold, remark5ChiSigma, paper5Sigma, hχ]
    positivity
  have hbarrier : paper52MonotoneBarrierSpeed p = 2 := by
    norm_num [paper52MonotoneBarrierSpeed, paper52RiccatiB, hM, hχ]
  have hcap : paper531ConcreteCapThreshold p = 2 := by
    norm_num [paper531ConcreteCapThreshold, hA, hB, stabilityWeightCap,
      paper5Sigma, hχ]
  simp [paper5ConcreteRequiredSpeed, cStarStarWitness, hremark,
    hbarrier, hcap, hχ, max_eq_left hγtwo]

theorem paper5CorrectedCStarStar_asymptotic_of_chi_eq_zero
    (p : CMParams) (hχ : p.χ = 0) :
    StabilitySpeedThresholdFamilyAsymptotic p
      (paper5CorrectedCStarStar p) := by
  have hrequired := paper5ConcreteRequiredSpeed_eq_witness_of_chi_eq_zero p hχ
  have heq : paper5CorrectedCStarStar p = cStarStarWitness p := by
    funext χ
    by_cases hχ0 : χ = p.χ
    · subst χ
      simp [paper5CorrectedCStarStar, hrequired, hχ]
    · simp [paper5CorrectedCStarStar, hχ0]
  rw [heq]
  exact cStarStarWitness_asymptotic p

theorem paper5CorrectedCStarStar_asymptotic (p : CMParams) :
    StabilitySpeedThresholdFamilyAsymptotic p
      (paper5CorrectedCStarStar p) := by
  by_cases hχ : p.χ = 0
  · exact paper5CorrectedCStarStar_asymptotic_of_chi_eq_zero p hχ
  · exact paper5CorrectedCStarStar_asymptotic_of_chi_ne_zero p hχ

/-- The concrete corrected `A,B` produce the non-vacuous perturbed-root
budget at the concrete threshold family. -/
def paper531ConcreteStabilityBudget
    (p : CMParams) (hregime : StableWaveParameterRegime p) :
    Paper531StabilityBudget p (paper5CorrectedCStarStar p) := by
  have hM : 0 < MChi p := hregime.MChi_pos
  obtain ⟨hA, hB⟩ := paper531ConcreteAB_nonneg p hM
  apply paper531StabilityBudget_of_cap_threshold hA hB
  exact paper5CorrectedCStarStar_cap_le p

theorem paper5Concrete_speed_data
    (p : CMParams) (hregime : StableWaveParameterRegime p) :
    StabilitySpeedThresholdFamilyAsymptotic p
        (paper5CorrectedCStarStar p) ∧
      stabilitySpeedBaseline p ≤ paper5CorrectedCStarStar p p.χ ∧
      Nonempty (Paper531StabilityBudget p (paper5CorrectedCStarStar p)) :=
  ⟨paper5CorrectedCStarStar_asymptotic p,
    paper5CorrectedCStarStar_baseline_le p,
    ⟨paper531ConcreteStabilityBudget p hregime⟩⟩

/-- The corrected theorem now consumes only the genuine whole-line
Cauchy/energy/Step-4 block.  The scalar threshold family and the complete
perturbed-root budget are produced above rather than carried as hypotheses. -/
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
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in Filter.atTop,
              coMovingWeightedL2Energy η c u U t ≤ E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤
              2 * paper531Quadratic c
                (paper531ConcreteStabilityBudget p hregime).A
                (paper531ConcreteStabilityBudget p hregime).B η * E t) ∧
            EventuallyIntegrableMovingFrameEnergy η 0
              (coMovingPath c u) U ∧
            EventuallyUniformMovingFrameSpatialModulus 0
              (coMovingPath c u) U ∧
            UniformMovingFrameLeftTailConvergence 0
              (coMovingPath c u) U) :
    Theorem_1_2_amended := by
  refine paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4
      (fun p ↦ paper5CorrectedCStarStar p) ?_
      paper531ConcreteStabilityBudget ?_
  · intro p _hregime
    exact ⟨paper5CorrectedCStarStar_asymptotic p,
      paper5CorrectedCStarStar_baseline_le p⟩
  · exact hcore

section Theorem12ConcreteBudgetAxiomAudit

#print axioms paper5CommonBounds_nonneg
#print axioms paper531CommonAB_nonneg
#print axioms paper531ConcreteAB_nonneg
#print axioms paper5CorrectedCStarStar_asymptotic
#print axioms paper531ConcreteStabilityBudget
#print axioms paper5Concrete_speed_data
#print axioms
  paper1_Theorem_1_2_amended_of_concrete_wholeLineCauchyEnergyStep4

end Theorem12ConcreteBudgetAxiomAudit

end ShenWork.Paper1
