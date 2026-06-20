import ShenWork.Paper2.IntervalBFormCron2NegativePartEnergy
import ShenWork.Paper2.IntervalBFormCron2RegularFluxDuality

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalMeasure intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Remaining semigroup weak identity after the concrete regular B_N identity
has been supplied for the single negative-part test at time `t`. -/
def NegativePartMildSemigroupWeakAfterFluxTestDuality
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  TruncatedConjugateMildSolution p T u₀ u →
    ∀ t, 0 < t → t ≤ T →
      (∀ s, 0 < s → s < t →
        TruncatedBNDualityForTestAt p u t s (negativePartTest u t)) →
        NegativePartWeakTestIdentityAt p u t

/-- Regular mild-to-weak data for the negative-part test only.  The B_N input is
bounded/measurable data for the concrete flux `Q(u_+)` and test `-u_-`; the
actual identity is produced by `BNDualityForFluxTestAt.duality`. -/
structure NegativePartMildToWeakRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  flux_test_duality :
    ∀ t, 0 < t → t ≤ DB.T →
      ∀ s, 0 < s → s < t →
        BNDualityForFluxTestAt p
          (conjugatePicardLimit p u₀ DB.T) t s
          (negativePartTest (conjugatePicardLimit p u₀ DB.T) t)
  semigroup_weak :
    NegativePartMildSemigroupWeakAfterFluxTestDuality p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T)

def NegativePartMildToWeakRegularData.weakTest
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : NegativePartMildToWeakRegularData p DB)
    (hmild :
      TruncatedConjugateMildSolution p DB.T u₀
        (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t, 0 < t → t ≤ DB.T →
      NegativePartWeakTestIdentityAt p
        (conjugatePicardLimit p u₀ DB.T) t := by
  intro t ht htT
  exact H.semigroup_weak hmild t ht htT
    (fun s hs hst =>
      (H.flux_test_duality t ht htT s hs hst).duality hst)

/-- Standard chain-rule and bound data after inserting the single test
`φ = -u_-`.  The weak identity itself is supplied separately by the regular
mild-to-weak bridge above. -/
structure NegativePartEnergyEstimateRegularData
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (ell : ℝ) (E' : ℝ → ℝ) : Prop where
  neg_deriv_zero_on_pos :
    ∀ t, 0 < t → t ≤ T →
      ∀ᵐ x ∂ intervalMeasure 1,
        0 < intervalDomainLift (u t) x →
          deriv (negativePartLift (u t)) x = 0
  time_chain :
    ∀ t, 0 < t → t ≤ T →
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                intervalDomain.timeDeriv u t z) x * negativePartTest u t x
          ∂ intervalMeasure 1)
        = (1 / 2 : ℝ) * E' t
  diffusion_chain :
    ∀ t, 0 < t → t ≤ T →
      (∫ x,
          deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
          ∂ intervalMeasure 1)
        = negativePartDissipation u t
  diffusion_nonneg :
    ∀ t, 0 < t → t ≤ T → 0 ≤ negativePartDissipation u t
  reaction_bound :
    ∀ t, 0 < t → t ≤ T →
      (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
          ∂ intervalMeasure 1)
        ≤ ell * negativePartEnergy u t

theorem negativePart_half_energy_deriv_le_regular
    {p : CM2Params} {T ell : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {E' : ℝ → ℝ}
    (H : NegativePartEnergyEstimateRegularData p T u ell E')
    {t : ℝ} (hweakTest : NegativePartWeakTestIdentityAt p u t)
    (ht : 0 < t) (htT : t ≤ T) :
    (1 / 2 : ℝ) * E' t ≤ ell * negativePartEnergy u t := by
  have htest := hweakTest
  have hchem_neg :
      (∫ x,
        truncatedChemFluxLifted p (u t) x
          * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1) = 0 := by
    refine truncatedChemFluxLifted_mul_negDeriv_integral_eq_zero
      (p := p) (w := u t)
      (duNeg := fun x => deriv (negativePartTest u t) x) ?_
    filter_upwards [H.neg_deriv_zero_on_pos t ht htT] with x hx hpos
    change deriv (-negativePartLift (u t)) x = 0
    rw [deriv.neg]
    simp [hx hpos]
  have hmain :
      (1 / 2 : ℝ) * E' t + negativePartDissipation u t
        =
      (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
          ∂ intervalMeasure 1) := by
    calc
      (1 / 2 : ℝ) * E' t + negativePartDissipation u t
          =
        (∫ x,
            intervalDomainLift
                (fun z : intervalDomainPoint =>
                  intervalDomain.timeDeriv u t z) x * negativePartTest u t x
            ∂ intervalMeasure 1)
          + (∫ x,
              deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
              ∂ intervalMeasure 1) := by
            rw [H.time_chain t ht htT, H.diffusion_chain t ht htT]
      _ =
          p.χ₀ *
            (∫ x,
              truncatedChemFluxLifted p (u t) x
                * deriv (negativePartTest u t) x
              ∂ intervalMeasure 1)
          + (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
              ∂ intervalMeasure 1) := htest
      _ = (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
              ∂ intervalMeasure 1) := by
            simp [hchem_neg]
  calc
    (1 / 2 : ℝ) * E' t
        ≤ (1 / 2 : ℝ) * E' t + negativePartDissipation u t := by
          linarith [H.diffusion_nonneg t ht htT]
    _ = (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
          ∂ intervalMeasure 1) := hmain
    _ ≤ ell * negativePartEnergy u t := H.reaction_bound t ht htT

/-- Regular negative-part energy core: the old all-test weak PDE is replaced by
the concrete regular mild-to-weak bridge for the test `-u_-`. -/
structure NegativePartEnergyCoreRegularData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  weak_regular : NegativePartMildToWeakRegularData p DB
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate :
    NegativePartEnergyEstimateRegularData p DB.T
      (conjugatePicardLimit p u₀ DB.T) ell E'
  energy_cont :
    ContinuousOn
      (negativePartEnergy (conjugatePicardLimit p u₀ DB.T))
      (Set.Icc (0 : ℝ) DB.T)
  energy_has_deriv :
    ∀ t ∈ Set.Ico (0 : ℝ) DB.T,
      HasDerivWithinAt
        (negativePartEnergy (conjugatePicardLimit p u₀ DB.T))
        (E' t) (Set.Ici t) t
  energy_integrable :
    ∀ t, 0 < t → t ≤ DB.T →
      Integrable
        (fun x =>
          (negativePartLift (conjugatePicardLimit p u₀ DB.T t) x) ^ 2)
        (intervalMeasure 1)
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < DB.T →
      negativePartEnergy (conjugatePicardLimit p u₀ DB.T) s < ε
  zero_energy_to_pointwise_nonneg :
    ∀ t, 0 < t → t ≤ DB.T →
      negativePartEnergy (conjugatePicardLimit p u₀ DB.T) t = 0 →
        ∀ x : intervalDomainPoint,
          0 ≤ conjugatePicardLimit p u₀ DB.T t x

theorem negativePart_nonneg_of_regular_energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (hmild :
      TruncatedConjugateMildSolution p DB.T u₀
        (conjugatePicardLimit p u₀ DB.T))
    (H : NegativePartEnergyCoreRegularData p DB) :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardLimit p u₀ DB.T t x := by
  intro t ht htT x
  let u := conjugatePicardLimit p u₀ DB.T
  let E := negativePartEnergy u
  have hE_nonneg : ∀ τ, 0 < τ → τ ≤ DB.T → 0 ≤ E τ := by
    intro τ hτ0 hτT
    have _hint := H.energy_integrable τ hτ0 hτT
    have hnn :
        0 ≤ᵐ[intervalMeasure 1]
          fun x => (negativePartLift (u τ) x) ^ 2 :=
      Eventually.of_forall fun x => negativePartEnergyDensity_nonneg u τ x
    exact MeasureTheory.integral_nonneg_of_ae hnn
  have hderiv_le :
      ∀ τ, 0 < τ → τ < DB.T → H.E' τ ≤ (2 * H.ell) * E τ := by
    intro τ hτ0 hτT
    have hτTle : τ ≤ DB.T := le_of_lt hτT
    have hweak :=
      H.weak_regular.weakTest hmild τ hτ0 hτTle
    have hhalf := negativePart_half_energy_deriv_le_regular
      H.estimate hweak hτ0 hτTle
    nlinarith
  have hgron :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ s t, 0 < s → s ≤ t → t ≤ DB.T →
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
      ∀ τ, 0 < τ → τ ≤ DB.T → E τ = 0 :=
    energy_eq_zero_of_positive_time_gronwall hE_nonneg hgron H.initial_vanishes
  have hE_zero : E t = 0 := hE_zero_closed t ht htT
  exact H.zero_energy_to_pointwise_nonneg t ht htT hE_zero x

theorem bform_negativePart_zero_of_concrete_truncated_regular_energyCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (Hbridge : TruncatedConjugateLimitBridge p DB DT)
    (Henergy : NegativePartEnergyCoreRegularData p DB) :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0 := by
  have hmild :
      TruncatedConjugateMildSolution p DB.T u₀
        (conjugatePicardLimit p u₀ DB.T) :=
    truncatedConjugateMildSolution_conjugatePicardLimit_of_data
      DB DT Hbridge
  intro t ht htT x
  exact negativePart_eq_zero_of_nonneg
    (negativePart_nonneg_of_regular_energyCore hmild Henergy t ht htT x)

end ShenWork.Paper2.BFormPositiveDatumNegPart
