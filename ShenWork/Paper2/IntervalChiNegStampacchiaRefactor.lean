import ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
import ShenWork.Paper2.IntervalBFormCron2NegativePartEnergy
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy
import ShenWork.Paper2.IntervalBFormLinearDriftComparisonRegularDischarge

open Set Filter Topology MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData UniformConjugateMildExistenceCore
   conjugatePicardLimit)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_of_mem)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Trajectory-typed version of the negative-part energy core.

This is the same Stampacchia package as `NegativePartEnergyCoreData`, but indexed
by the actual horizon and trajectory instead of old `ConjugateMildExistenceData`.
It is therefore usable for the floor-free uniform Picard core. -/
structure NegativePartEnergyCoreDataFor
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate : NegativePartEnergyEstimateData p T u ell E'
  energy_cont : ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T)
  energy_has_deriv :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t
  energy_integrable :
    ∀ t, 0 < t → t ≤ T →
      Integrable (fun x => (negativePartLift (u t) x) ^ 2) (intervalMeasure 1)
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      negativePartEnergy u s < ε
  zero_energy_to_pointwise_nonneg :
    ∀ t, 0 < t → t ≤ T →
      negativePartEnergy u t = 0 → ∀ x : intervalDomainPoint, 0 ≤ u t x

/-- The old DB-indexed Cron2 package is a special case of the trajectory package. -/
def NegativePartEnergyCoreData.toFor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : NegativePartEnergyCoreData p DB) :
    NegativePartEnergyCoreDataFor p DB.T
      (conjugatePicardLimit p u₀ DB.T) where
  ell := H.ell
  hell_nonneg := H.hell_nonneg
  E' := H.E'
  estimate := H.estimate
  energy_cont := H.energy_cont
  energy_has_deriv := H.energy_has_deriv
  energy_integrable := H.energy_integrable
  initial_vanishes := H.initial_vanishes
  zero_energy_to_pointwise_nonneg := H.zero_energy_to_pointwise_nonneg

/-- Stampacchia nonnegativity from the trajectory-typed negative-part core. -/
theorem nonneg_of_negativePartEnergyCoreDataFor
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : NegativePartEnergyCoreDataFor p T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u t x := by
  intro t ht htT x
  let E := negativePartEnergy u
  have hE_nonneg : ∀ τ, 0 < τ → τ ≤ T → 0 ≤ E τ := by
    intro τ hτ0 hτT
    have hnn :
        0 ≤ᵐ[intervalMeasure 1]
          fun x => (negativePartLift (u τ) x) ^ 2 :=
      Eventually.of_forall fun x => negativePartEnergyDensity_nonneg u τ x
    exact MeasureTheory.integral_nonneg_of_ae hnn
  have hderiv_le :
      ∀ τ, 0 < τ → τ < T → H.E' τ ≤ (2 * H.ell) * E τ := by
    intro τ hτ0 hτT
    have hhalf := negativePart_half_energy_deriv_le
      H.estimate hτ0 (le_of_lt hτT)
    nlinarith
  have hgron :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ s t, 0 < s → s ≤ t → t ≤ T →
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
  have hE_zero :
      E t = 0 :=
    energy_eq_zero_of_positive_time_gronwall hE_nonneg hgron
      H.initial_vanishes t ht htT
  exact H.zero_energy_to_pointwise_nonneg t ht htT hE_zero x

/-- Trajectory-typed regular negative-part energy core.

The weak identity is needed only at interior times.  This is the exact
quantifier used by the Gronwall argument: even when the target time is `T`,
all derivative estimates are taken on `Ico s T`.  Keeping the endpoint out of
this field is essential for zero-extended Picard limits, whose two-sided
`timeDeriv` at `T` is not their left derivative. -/
structure NegativePartEnergyCoreRegularDataFor
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  weak_test :
    ∀ t, 0 < t → t < T → NegativePartWeakTestIdentityAt p u t
  ell : ℝ
  hell_nonneg : 0 ≤ ell
  E' : ℝ → ℝ
  estimate : NegativePartEnergyEstimateRegularData p T u ell E'
  energy_cont : ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T)
  energy_has_deriv :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t
  energy_integrable :
    ∀ t, 0 < t → t ≤ T →
      Integrable (fun x => (negativePartLift (u t) x) ^ 2) (intervalMeasure 1)
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      negativePartEnergy u s < ε
  zero_energy_to_pointwise_nonneg :
    ∀ t, 0 < t → t ≤ T →
      negativePartEnergy u t = 0 → ∀ x : intervalDomainPoint, 0 ≤ u t x

/-- Stampacchia nonnegativity from the trajectory-typed regular core. -/
theorem nonneg_of_negativePartEnergyCoreRegularDataFor
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : NegativePartEnergyCoreRegularDataFor p T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u t x := by
  intro t ht htT x
  let E := negativePartEnergy u
  have hE_nonneg : ∀ τ, 0 < τ → τ ≤ T → 0 ≤ E τ := by
    intro τ hτ0 hτT
    have hnn :
        0 ≤ᵐ[intervalMeasure 1]
          fun x => (negativePartLift (u τ) x) ^ 2 :=
      Eventually.of_forall fun x => negativePartEnergyDensity_nonneg u τ x
    exact MeasureTheory.integral_nonneg_of_ae hnn
  have hderiv_le :
      ∀ τ, 0 < τ → τ < T → H.E' τ ≤ (2 * H.ell) * E τ := by
    intro τ hτ0 hτT
    have hweak := H.weak_test τ hτ0 hτT
    have hhalf := negativePart_half_energy_deriv_le_regular
      H.estimate hweak hτ0 hτT.le
    nlinarith
  have hgron :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ s t, 0 < s → s ≤ t → t ≤ T →
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
  have hE_zero : E t = 0 :=
    energy_eq_zero_of_positive_time_gronwall hE_nonneg hgron
      H.initial_vanishes t ht htT
  exact H.zero_energy_to_pointwise_nonneg t ht htT hE_zero x

/-- Real-line lift of an interval trajectory, for the regular comparison track. -/
def trajectoryLift (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => u t (unitClip x)

/-- Barrier data for strict positivity of a trajectory.

The square-heat comparison proves positivity on `0 < t < T`.  The closed endpoint
`t = T` is kept as the explicit remaining hypothesis, because the landed barrier
track is open at the terminal time. -/
structure SquareHeatStrictPosDataFor
    (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) where
  A : ℝ
  D : ℝ
  Mbar : ℝ
  f : ℝ → ℝ
  drift : ℝ → ℝ → ℝ
  react : ℝ → ℝ → ℝ
  hcoeff : NeumannLinearDriftCoefficientsRegular T drift react
  hsuper :
    IsClassicalNeumannLinearDriftSuperSolution T drift react
      (trajectoryLift u)
  hu_initial :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      trajectoryLift u 0 x = intervalDomainLift u₀ x
  hbarrier_reg :
    NeumannLinearDriftSubSolutionRegularity T drift react
      (squareHeatBarrier Mbar f)
  hcalc : SquareHeatSubsolutionCalculus T Mbar f drift react
  hM : A ^ 2 / 2 + D ≤ Mbar
  hB_bound :
    ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |drift t x| ≤ A
  hC_neg_bound :
    ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -react t x ≤ D
  hseed : SquareHeatSeed (intervalDomainLift u₀) f
  endpoint_pos : ∀ x : intervalDomainPoint, 0 < u T x

/-- The regular square-heat certificates still missing from the uniform core,
with the weak-PID square-root seed fixed by existing barrier infrastructure.

The uniform Picard core does not itself contain the classical drift/reaction
regularity or the terminal-time positivity needed by the comparison route, so
those analytic certificates remain explicit here. -/
structure SqrtSeedSquareHeatStrictPosInputs
    (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) where
  A : ℝ
  D : ℝ
  Mbar : ℝ
  drift : ℝ → ℝ → ℝ
  react : ℝ → ℝ → ℝ
  hcoeff : NeumannLinearDriftCoefficientsRegular T drift react
  hsuper :
    IsClassicalNeumannLinearDriftSuperSolution T drift react
      (trajectoryLift u)
  hu_initial :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      trajectoryLift u 0 x = intervalDomainLift u₀ x
  hbarrier_reg :
    NeumannLinearDriftSubSolutionRegularity T drift react
      (squareHeatBarrier Mbar (positiveInitialDatumSqrtSeed u₀))
  hcalc : SquareHeatSubsolutionCalculus T Mbar
    (positiveInitialDatumSqrtSeed u₀) drift react
  hM : A ^ 2 / 2 + D ≤ Mbar
  hB_bound :
    ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |drift t x| ≤ A
  hC_neg_bound :
    ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -react t x ≤ D
  endpoint_pos : ∀ x : intervalDomainPoint, 0 < u T x

def SqrtSeedSquareHeatStrictPosInputs.toSquareHeatStrictPosDataFor
    {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (H : SqrtSeedSquareHeatStrictPosInputs T u₀ u) :
    SquareHeatStrictPosDataFor T u₀ u where
  A := H.A
  D := H.D
  Mbar := H.Mbar
  f := positiveInitialDatumSqrtSeed u₀
  drift := H.drift
  react := H.react
  hcoeff := H.hcoeff
  hsuper := H.hsuper
  hu_initial := H.hu_initial
  hbarrier_reg := H.hbarrier_reg
  hcalc := H.hcalc
  hM := H.hM
  hB_bound := H.hB_bound
  hC_neg_bound := H.hC_neg_bound
  hseed := positiveInitialDatumSqrtSeed_squareHeatSeed hu₀
  endpoint_pos := H.endpoint_pos

/-- Strict positivity from the square-heat barrier data, plus the explicit
terminal-time positivity gap. -/
theorem strictPos_of_squareHeatStrictPosDataFor
    {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hT : 0 < T) (H : SquareHeatStrictPosDataFor T u₀ u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 < u t x := by
  intro t ht htT x
  by_cases hlt : t < T
  · have hreal :=
      strict_pos_of_neumann_linear_drift_square_heat_subsolution_regular_unconditional
        (T := T) (A := H.A) (D := H.D) (M := H.Mbar)
        (u₀ := intervalDomainLift u₀) (f := H.f)
        (B := H.drift) (C := H.react) (u := trajectoryLift u)
        hT H.hcoeff H.hsuper H.hu_initial H.hbarrier_reg H.hcalc H.hM
        H.hB_bound H.hC_neg_bound H.hseed
        t x.1 ht hlt x.2
    simpa [trajectoryLift, unitClip_of_mem x.2] using hreal
  · have ht_eq : t = T := le_antisymm htT (le_of_not_gt hlt)
    simpa [ht_eq] using H.endpoint_pos x

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV3

open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Floor-free energy input; the uniform core lacks the weak/chain/trace fields. -/
abbrev UniformCoreStampacchiaEnergy (p : CM2Params) : Type :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      NegativePartEnergyCoreDataFor p C.T (conjugatePicardLimit p u₀ C.T)

abbrev UniformCoreStampacchiaPackage (p : CM2Params) : Prop :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      (∀ t, 0 < t → t ≤ C.T → ∀ x,
        0 ≤ conjugatePicardLimit p u₀ C.T t x) →
      (∀ t, 0 < t → t ≤ C.T → ∀ x,
        0 < conjugatePicardLimit p u₀ C.T t x) →
      ∃ S : ShenWork.IntervalConjugatePicard.ConjugateMildSolutionData p u₀,
        S.T = C.T ∧ S.M = C.R ∧ S.u = conjugatePicardLimit p u₀ C.T ∧
        InitialTrace intervalDomain u₀ S.u

structure UniformCoreStampacchiaInputs (p : CM2Params) where
  energy : UniformCoreStampacchiaEnergy p
  strictPos :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        SquareHeatStrictPosDataFor C.T u₀ (conjugatePicardLimit p u₀ C.T)
  package : UniformCoreStampacchiaPackage p

structure UniformCoreStampacchiaBarrierInputs (p : CM2Params) where
  energy : UniformCoreStampacchiaEnergy p
  strictPosBarrier :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        SqrtSeedSquareHeatStrictPosInputs C.T u₀ (conjugatePicardLimit p u₀ C.T)
  package : UniformCoreStampacchiaPackage p

def UniformCoreStampacchiaInputs.ofBarrier
    {p : CM2Params} (H : UniformCoreStampacchiaBarrierInputs p) :
    UniformCoreStampacchiaInputs p where
  energy := H.energy
  strictPos := by
    intro M hM u₀ hu₀ hbound C
    exact SqrtSeedSquareHeatStrictPosInputs.toSquareHeatStrictPosDataFor hu₀
      (H.strictPosBarrier hM hu₀ hbound C)
  package := H.package

/-- Close the V3 conditional-input record from the Stampacchia/barrier inputs. -/
theorem uniformCoreMildSolutionConditionalInputs_of_stampacchia
    {p : CM2Params} (H : UniformCoreStampacchiaInputs p) :
    UniformCoreMildSolutionConditionalInputs p where
  hnonneg := by
    intro M hM u₀ hu₀ hbound C
    exact nonneg_of_negativePartEnergyCoreDataFor (H.energy hM hu₀ hbound C)
  hpos := by
    intro M hM u₀ hu₀ hbound C
    exact strictPos_of_squareHeatStrictPosDataFor C.hT
      (H.strictPos hM hu₀ hbound C)
  package := H.package

theorem uniformCoreMildSolutionConditionalInputs_of_stampacchia_barrier
    {p : CM2Params} (H : UniformCoreStampacchiaBarrierInputs p) :
    UniformCoreMildSolutionConditionalInputs p :=
  uniformCoreMildSolutionConditionalInputs_of_stampacchia
    (UniformCoreStampacchiaInputs.ofBarrier H)

end ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
