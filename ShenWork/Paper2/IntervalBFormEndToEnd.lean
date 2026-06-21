/-
  ShenWork/Paper2/IntervalBFormEndToEnd.lean

  End-to-end B-form wiring for the general-chi interval theorem.

  This file deliberately uses the restart-cosine local-data interface rather than
  the half-step logistic-source interface: for chi != 0, a B-form solution is not
  represented by a logistic-only half-step source.  The restart-cosine interface
  is the faithful bridge consumed by the existing gamma >= 1 umbrella.

-/
import ShenWork.Paper2.IntervalDomainThm11Assembly
import ShenWork.Paper2.IntervalBFormPIDUnconditional
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalRegularityFrontierWiring
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalResolverStrictPositivity
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBankedConcrete

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugateMildSolutionData_of_data conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations RestartCosineRepresentation restartDuhamelCoeff)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildToLocalExistence
  (GradientMildClassicalFrontierCoreData)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs coupledChemDivSourceLift)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring

noncomputable section

namespace ShenWork.Paper2.BFormEndToEnd

/-- Package the banked B-form analytic inputs used to obtain the canonical
global cosine representation, the B-form restart representation, and the
interior PDE identity for `conjugatePicardLimit`. -/
structure BFormBankedInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  MInit : ℝ
  haInit : ∀ n,
    |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit
  hlogSrc : DuhamelSourceTimeC1
    (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
  hchemSrc : DuhamelSourceTimeC1
    (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
  hlogCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p
          ((conjugatePicardLimit p u₀ DB.T) t)))
  hlogFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (ShenWork.IntervalDomainExistence.intervalLogisticSource p
              ((conjugatePicardLimit p u₀ DB.T) t)))) n)
  hchemCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (fun x : intervalDomainPoint =>
          intervalDomainChemotaxisDiv p
            ((conjugatePicardLimit p u₀ DB.T) t)
            (coupledChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t) x))
  hchemFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p
                ((conjugatePicardLimit p u₀ DB.T) t)
                (coupledChemicalConcentration p
                  (conjugatePicardLimit p u₀ DB.T) t) x))) n)

/-- The canonical B-form source coefficients have the time-`C¹` package required
by restart-cosine regularity. -/
def BFormBankedInputs.hsrcB
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    DuhamelSourceTimeC1
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) :=
  bFormSource_duhamelSourceTimeC1 B.hlogSrc B.hchemSrc

def BFormBankedInputs.toDirectClassical
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB where
  huPaper := B.huPaper
  Hinf := B.Hinf
  hsmall := B.hsmall
  MInit := B.MInit
  haInit := B.haInit
  hlogSrc := B.hlogSrc
  hchemSrc := B.hchemSrc
  hlogCont := B.hlogCont
  hlogFourier := B.hlogFourier
  hchemCont := B.hchemCont
  hchemFourier := B.hchemFourier

/-- B-form per-datum frontier over `conjugatePicardLimit`.

This is the source/B-form frontier.  It deliberately does not coerce the
conjugate Picard fixed point into the old output-gradient mild map: the
faithful fixed-point identity is `IntervalConjugateMildSolution`, supplied by
`conjugateMildSolutionData_of_data`, and the direct classical stack below
consumes the B-form spectral data instead. -/
structure BFormSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
  hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t x

/-- Strictly smaller residual for the source/B-form spectral frontier.

Compared with `BFormSpectralFrontier`, the resolver direct spectral package is
reduced to the existing per-`t₀` clamped coefficient producer, and resolver
strict positivity is produced directly from the conjugate Picard data.  There is
no gradient-map fixed-point bridge here. -/
structure BFormSpectralFrontierResidual
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverCoeffTimeC1 :
    ∀ t₀, 0 < t₀ → t₀ < DB.T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k,
          aC s k =
            (ShenWork.PDE.intervalNeumannResolverSourceCoeff p
              ((conjugatePicardLimit p u₀ DB.T) s) k).re)

/-- Construct the actual `BFormSpectralFrontier` from the smaller named
residual.  This is the anti-fanout step: `hResolverData` is produced by the
clamped per-`t₀` resolver assembler, and `hVpos` is produced by the strict
resolver positivity theorem for the actual conjugate Picard limit. -/
theorem bFormSpectralFrontier_of_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (R : BFormSpectralFrontierResidual p DB) :
    Nonempty (BFormSpectralFrontier p DB) := by
  refine ⟨?_⟩
  refine
    { bank := R.bank
      hTimeNhd := R.hTimeNhd
      hResolverData := ?_
      hVpos := ?_ }
  · exact
      ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
        (p := p) (T := DB.T) (u := conjugatePicardLimit p u₀ DB.T)
        R.hResolverCoeffTimeC1
  · exact
      ShenWork.Paper2.BFormPositiveDatumLocalSq.bform_mildChemicalConcentration_pos_of_conjugate_data
        p DB

def BFormSpectralFrontier.toDirectClassical
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB where
  bank := F.bank.toDirectClassical
  hTimeNhd := F.hTimeNhd
  hResolverData := F.hResolverData
  hVpos := F.hVpos

theorem BFormSpectralFrontier.hB_global
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    ∀ t, 0 < t → t ≤ DB.T →
      Set.EqOn
        (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) :=
  F.toDirectClassical.hB_global

theorem hasRestartCosineRepresentations_of_BFormSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    HasRestartCosineRepresentations DB.T
      (conjugatePicardLimit p u₀ DB.T) :=
  ShenWork.Paper2.BFormDirectClassical.hasRestartCosineRepresentations_of_BFormDirectFrontier
    F.toDirectClassical

theorem BFormSpectralFrontier.hpde_u
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α) :=
  F.toDirectClassical.hpde_u

/-- Construct the restart-frontier local data consumed by the gamma >= 1 umbrella
from per-datum B-form frontiers. -/
theorem hLocal_of_BForm
    (p : CM2Params)
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ DB : ConjugateMildExistenceData p u₀,
          Nonempty (BFormSpectralFrontierResidual p DB)) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨R⟩⟩ := hPerDatum u₀ hu₀
  obtain ⟨F⟩ := bFormSpectralFrontier_of_residual R
  exact
    ShenWork.Paper2.BFormDirectClassical.localClassicalSolution_of_BFormDirectFrontier
      F.toDirectClassical

/-- Paper 2 Theorem 1.1, general chi, via the Neumann-faithful B-form frontier.

This uses the direct classical B-form local-existence route.  It does not
require the conjugate fixed point to satisfy the non-equivalent old
output-gradient Duhamel map. -/
theorem paper2_theorem_1_1_general_chi_via_bform
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ DB : ConjugateMildExistenceData p u₀,
          Nonempty (BFormSpectralFrontierResidual p DB)) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.BFormDirectClassical.paper2_theorem_1_1_general_chi_bform
    p hχ ha hb hγ_ge_one (hLocal_of_BForm p hPerDatum) hUniform

#print axioms bFormSpectralFrontier_of_residual
#print axioms BFormBankedInputs.hsrcB
#print axioms BFormSpectralFrontier.hB_global
#print axioms hasRestartCosineRepresentations_of_BFormSpectralFrontier
#print axioms BFormSpectralFrontier.hpde_u
#print axioms hLocal_of_BForm
#print axioms paper2_theorem_1_1_general_chi_via_bform

end ShenWork.Paper2.BFormEndToEnd
