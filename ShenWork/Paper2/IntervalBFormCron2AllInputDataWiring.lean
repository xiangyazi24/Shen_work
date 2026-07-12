import ShenWork.Paper2.IntervalBFormCron2CoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier
import ShenWork.Paper2.IntervalBFormTimeShiftedBarrierWrapper
import ShenWork.Paper2.IntervalBFormSquareHeatSubsolutionRegularAssemblyStall
import ShenWork.Paper2.IntervalBFormMassGronwallNonvanishing
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPosProducer

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
This file is the atom-wiring boundary for the Cron2 negative-part path.

Constructed here:
* A3 side fields from the truncated Picard producer:
  continuous slices, ball bound, positive initial datum, and initial trace.
* the A1/A2/A3 Stampacchia core for the truncated Picard limit;
* the resulting pointwise nonnegativity theorem from atom data.

Fields not currently produced by existing files:
* A1 still needs the full `TruncatedNegativePartCoefficientWeakTestData`:
  the coefficient ODE, two summability facts, the time/gradient tsum
  interchanges, and the source pairing.
* A2 still needs the chain-rule package
  `TruncatedPicardNegativePartEnergyEstimateA2Data`.
* A3 still needs `energy_cont` and `energy_has_deriv`; the Picard producer
  supplies the side fields but not the negative-part energy derivative.
* A4 cannot be produced as typed for a positive seed: the current full
  semigroup is zero at time `0`, so
  `SquareHeatSubsolutionCalculus.initial_eq` forces the seed barrier `f` to
  vanish on `[0,1]`.
* A5 still needs the mass/coefficient identity and the zero-mode source lower
  bound.  Source continuity can come from `DuhamelSourceTimeC1On`, but those
  two facts are not in the present spectral infrastructure as reusable
  theorems.
-/

/-- A3 data from the Picard construction, modulo the two energy-chain fields. -/
def TruncatedPicardNegativePartEnergyA3Data.ofPicard
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {E' : ℝ → ℝ}
    (henergy_cont :
      ContinuousOn
        (negativePartEnergy
          (truncatedConjugatePicardLimit p u₀ DT.T))
        (Set.Icc (0 : ℝ) DT.T))
    (henergy_has_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) DT.T,
        HasDerivWithinAt
          (negativePartEnergy
            (truncatedConjugatePicardLimit p u₀ DT.T))
          (E' t) (Set.Ici t) t) :
    TruncatedPicardNegativePartEnergyA3Data p (u₀ := u₀) DT.T E' := by
  let S := truncatedConjugateMildSolutionData_of_data DT
  refine
    { R := S.M
      hR := le_of_lt S.hM
      hcont := ?_
      hbound := ?_
      hu₀_adm := hu₀.admissible
      hu₀_nonneg := ?_
      htrace :=
        truncatedConjugatePicardLimit_initialTrace_of_truncated_data
          p hu₀.admissible.2 DT
      energy_cont := henergy_cont
      energy_has_deriv := henergy_has_deriv }
  · simpa [S]
      using S.hcont
  · intro t ht htT x
    simpa [S]
      using S.hbound t ht htT x
  · intro x
    have h :=
      positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
    simpa [intervalDomainLift, x.2] using h

/-- A1/A2/A3 atom data assembled into the bare regular Stampacchia core. -/
def truncatedPicardEnergyCoreRegularData_of_atomData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) {E' : ℝ → ℝ}
    (HA1 : ∀ t, 0 < t → t < DT.T →
      TruncatedNegativePartCoefficientWeakTestData p DT t)
    (HA2 : TruncatedPicardNegativePartEnergyEstimateA2Data
      p (u₀ := u₀) DT.T E')
    (HA3 : TruncatedPicardNegativePartEnergyA3Data
      p (u₀ := u₀) DT.T E') :
    TruncatedPicardNegativePartEnergyCoreRegularData
      p (u₀ := u₀) DT.T where
  weak_test := fun t ht htT =>
    truncatedNegativePartWeakTestIdentityAt_of_coefficientData
      (HA1 t ht htT)
  ell := p.a
  hell_nonneg := p.ha
  E' := E'
  estimate := HA2.toEstimate
  energy_cont := HA3.energy_cont
  energy_has_deriv := HA3.energy_has_deriv
  energy_integrable := HA3.energyIntegrable
  initial_vanishes :=
    negativePartEnergy_initial_vanishes_of_trace_nonneg
      HA3.hu₀_adm HA3.hu₀_nonneg HA3.htrace
      HA3.hcont HA3.hR HA3.hbound
  zero_energy_to_pointwise_nonneg :=
    negativePartEnergy_zero_to_pointwise_nonneg_of_continuous
      HA3.hcont HA3.energyIntegrable

/-- The unconditional conclusion once the atom input records are available. -/
theorem truncatedConjugatePicardLimit_nonneg_of_atomData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) {E' : ℝ → ℝ}
    (HA1 : ∀ t, 0 < t → t < DT.T →
      TruncatedNegativePartCoefficientWeakTestData p DT t)
    (HA2 : TruncatedPicardNegativePartEnergyEstimateA2Data
      p (u₀ := u₀) DT.T E')
    (HA3 : TruncatedPicardNegativePartEnergyA3Data
      p (u₀ := u₀) DT.T E') :
    ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x :=
  truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
    (truncatedPicardEnergyCoreRegularData_of_atomData DT HA1 HA2 HA3)

/-- A4 obstruction: the current shifted square-heat data contradicts any
positive seed, because its calculus field forces `f = 0` at time zero. -/
theorem timeShiftedSquareHeatBarrierData_false_of_positive_seed
    {L s A D Mbar : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (H : TimeShiftedSquareHeatBarrierData L s A D Mbar f B C u)
    (hseed : SquareHeatSeed (fun x : ℝ => u s x) f) :
    False :=
  no_squareHeatSubsolutionCalculus_with_positive_seed H.calculus hseed

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2

/-- A5 input record, matching exactly the fields consumed by
`truncatedBForm_mass_nonvanishing`. -/
structure TruncatedBFormMassA5Data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ) (aInit : ℕ → ℝ)
    (T C : ℝ) : Prop where
  hmassCoeff : ∀ t, 0 ≤ t → t ≤ T →
    intervalDomain.integral (u t) =
      localRestartCoeff aInit (bFormSourceCoeffs p u) t 0
  hAcont : ContinuousOn
    (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
    (Icc (0 : ℝ) T)
  hsrcCont : ContinuousOn
    (fun t => bFormSourceCoeffs p u t 0) (Icc (0 : ℝ) T)
  hderiv0 : HasDerivWithinAt
    (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
    (bFormSourceCoeffs p u 0 0) (Ici 0) 0
  hinitCoeff : aInit 0 = intervalDomain.integral u₀
  hinitMass : 0 < intervalDomain.integral u₀
  hchem0 : ∀ t ∈ Ico (0 : ℝ) T,
    coupledChemDivSourceCoeffs p u t 0 = 0
  hlogLower : ∀ t ∈ Ico (0 : ℝ) T,
    -C * localRestartCoeff aInit (bFormSourceCoeffs p u) t 0 ≤
      coupledLogisticSourceCoeffs p u t 0

/-- A5 discharge from the exact input record. -/
theorem TruncatedBFormMassA5Data.nonvanishing
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {aInit : ℕ → ℝ}
    {T C : ℝ} (H : TruncatedBFormMassA5Data p (u₀ := u₀) u aInit T C) :
    ∀ t, 0 < t → t ≤ T → 0 < intervalDomain.integral (u t) :=
  truncatedBForm_mass_nonvanishing p H.hmassCoeff H.hAcont H.hsrcCont
    H.hderiv0 H.hinitCoeff H.hinitMass H.hchem0 H.hlogLower

end ShenWork.Paper2
