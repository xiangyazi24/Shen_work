import ShenWork.Paper2.IntervalBFormFaithfulBridgeProducer
import ShenWork.Paper2.IntervalBFormCron2CoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Regular mild-to-weak data for the negative-part test, stated directly by
the coefficient weak-test route for the faithful truncated Picard fixed point. -/
structure TruncatedNegativePartMildToWeakRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) where
  coeff_weak :
    ∀ t, 0 < t → t ≤ DT.T →
      TruncatedNegativePartCoefficientWeakTestData p DT t

def TruncatedNegativePartMildToWeakRegularData.semigroup_weak
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (H : TruncatedNegativePartMildToWeakRegularData p DT) :
    NegativePartMildSemigroupWeakAfterFluxTestDuality p DT.T u₀
      (truncatedConjugatePicardLimit p u₀ DT.T) :=
  negativePartMildSemigroupWeakAfterFluxTestDuality_of_coefficientWeakTestData
    (p := p) (T := DT.T) (u₀ := u₀)
    (u := truncatedConjugatePicardLimit p u₀ DT.T)
    { coeff_weak := H.coeff_weak }

def TruncatedNegativePartMildToWeakRegularData.weakTest
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (H : TruncatedNegativePartMildToWeakRegularData p DT) :
    ∀ t, 0 < t → t ≤ DT.T →
      NegativePartWeakTestIdentityAt p
        (truncatedConjugatePicardLimit p u₀ DT.T) t := by
  intro t ht htT
  exact truncatedNegativePartWeakTestIdentityAt_of_coefficientData
    (H.coeff_weak t ht htT)

/-- Regular negative-part energy core for the faithful truncated Picard fixed
point itself, with no bridge through the full Picard limit. -/
structure TruncatedNegativePartEnergyCoreRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) where
  weak_regular : TruncatedNegativePartMildToWeakRegularData p DT
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate :
    NegativePartEnergyEstimateRegularData p DT.T
      (truncatedConjugatePicardLimit p u₀ DT.T) ell E'
  energy_cont :
    ContinuousOn
      (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
      (Set.Icc (0 : ℝ) DT.T)
  energy_has_deriv :
    ∀ t ∈ Set.Ico (0 : ℝ) DT.T,
      HasDerivWithinAt
        (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
        (E' t) (Set.Ici t) t
  energy_integrable :
    ∀ t, 0 < t → t ≤ DT.T →
      Integrable
        (fun x =>
          (negativePartLift
            (truncatedConjugatePicardLimit p u₀ DT.T t) x) ^ 2)
        (intervalMeasure 1)
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < DT.T →
      negativePartEnergy
        (truncatedConjugatePicardLimit p u₀ DT.T) s < ε
  zero_energy_to_pointwise_nonneg :
    ∀ t, 0 < t → t ≤ DT.T →
      negativePartEnergy
        (truncatedConjugatePicardLimit p u₀ DT.T) t = 0 →
        ∀ x : intervalDomainPoint,
          0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x

theorem truncatedConjugatePicardLimit_nonneg_of_truncated_regular_energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (H : TruncatedNegativePartEnergyCoreRegularData p DT) :
    ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x := by
  intro t ht htT x
  let u := truncatedConjugatePicardLimit p u₀ DT.T
  let E := negativePartEnergy u
  have hE_nonneg : ∀ τ, 0 < τ → τ ≤ DT.T → 0 ≤ E τ := by
    intro τ hτ0 hτT
    have _hint := H.energy_integrable τ hτ0 hτT
    have hnn :
        0 ≤ᵐ[intervalMeasure 1]
          fun x => (negativePartLift (u τ) x) ^ 2 :=
      Eventually.of_forall fun x => negativePartEnergyDensity_nonneg u τ x
    exact MeasureTheory.integral_nonneg_of_ae hnn
  have hderiv_le :
      ∀ τ, 0 < τ → τ < DT.T → H.E' τ ≤ (2 * H.ell) * E τ := by
    intro τ hτ0 hτT
    have hτTle : τ ≤ DT.T := le_of_lt hτT
    have hweak := H.weak_regular.weakTest τ hτ0 hτTle
    have hhalf := negativePart_half_energy_deriv_le_regular
      H.estimate hweak hτ0 hτTle
    nlinarith
  have hgron :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ s t, 0 < s → s ≤ t → t ≤ DT.T →
          E t ≤ E s * Real.exp (K * (t - s)) := by
    refine ⟨2 * H.ell, mul_nonneg (by norm_num) H.hell_nonneg, ?_⟩
    intro s τ hs hst hτT
    have hcont : ContinuousOn E (Set.Icc s τ) :=
      H.energy_cont.mono (by
        intro r hr
        exact ⟨le_trans (le_of_lt hs) hr.1, le_trans hr.2 hτT⟩)
    have hderiv :
        ∀ r ∈ Set.Ico s τ, HasDerivWithinAt E (H.E' r) (Set.Ici r) r := by
      intro r hr
      exact H.energy_has_deriv r
        ⟨le_of_lt (lt_of_lt_of_le hs hr.1), lt_of_lt_of_le hr.2 hτT⟩
    have hbound :
        ∀ r ∈ Set.Ico s τ, H.E' r ≤ (2 * H.ell) * E r := by
      intro r hr
      exact hderiv_le r (lt_of_lt_of_le hs hr.1) (lt_of_lt_of_le hr.2 hτT)
    exact ShenWork.Paper2.intervalDomainL2_gronwall_exp_of_diffIneq
      (E := E) (E' := H.E') (K := 2 * H.ell)
      hst hcont hderiv hbound
  have hE_zero_closed :
      ∀ τ, 0 < τ → τ ≤ DT.T → E τ = 0 :=
    energy_eq_zero_of_positive_time_gronwall hE_nonneg hgron H.initial_vanishes
  have hE_zero : E t = 0 := hE_zero_closed t ht htT
  exact H.zero_energy_to_pointwise_nonneg t ht htT hE_zero x

/-- Producer-data constructor from the direct truncated negative-part core and
the comparison between the truncated Picard ball and the full Picard ball. -/
def truncatedConjugateLimitBridgeProducerData_of_cores
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (hT : DT.T = DB.T)
    (Henergy : TruncatedNegativePartEnergyCoreRegularData p DT)
    (hM_le : DT.M ≤ DB.M) :
    TruncatedConjugateLimitBridgeProducerData p DB DT where
  hT := hT
  truncated_nonneg := by
    intro t ht htT x
    exact truncatedConjugatePicardLimit_nonneg_of_truncated_regular_energyCore
      Henergy t ht htT x
  truncated_bound_in_full_ball := by
    intro t ht htT x
    have htDT : t ≤ DT.T := by
      simpa [hT] using htT
    exact ((truncatedConjugateMildSolutionData_of_data DT).hbound
      t ht htDT x).trans hM_le

end ShenWork.Paper2.BFormPositiveDatumNegPart
