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

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
  (IntervalMildSolution intervalGradientDuhamelMap)
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

/-- View the B-form Picard fixed point as the existing gradient-mild solution
record, once the genuine map bridge to `IntervalMildSolution` is supplied. -/
def conjugateAsGradientMildSolutionData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (hGradient :
      IntervalMildSolution p DB.T u₀ (conjugatePicardLimit p u₀ DB.T)) :
    GradientMildSolutionData p u₀ where
  T := DB.T
  hT := DB.hT
  M := DB.M
  hM := DB.hM
  u := conjugatePicardLimit p u₀ DB.T
  hmild := hGradient
  hbound := (conjugateMildSolutionData_of_data DB).hbound
  hnonneg := (conjugateMildSolutionData_of_data DB).hnonneg
  hpos := (conjugateMildSolutionData_of_data DB).hpos
  hcont := (conjugateMildSolutionData_of_data DB).hcont
  hmeas := (conjugateMildSolutionData_of_data DB).hmeas

/-- B-form per-datum frontier over `conjugatePicardLimit`.

The `hGradientBridge` field is the honest bridge required by the existing local
existence stack, whose solution record is still `GradientMildSolutionData`.
The Neumann regularity is supplied through `bank.hB_global`, not through the
old output-derivative map. -/
structure BFormSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hGradientBridge :
    IntervalMildSolution p DB.T u₀ (conjugatePicardLimit p u₀ DB.T)
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
  hSupNormDeriv :
    IntervalDomainSupNormDerivativeNonposOn
      (conjugatePicardLimit p u₀ DB.T) (Set.Ioo (0 : ℝ) DB.T)
  hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t x

/-- Strictly smaller residual for the B-form spectral frontier.

Compared with `BFormSpectralFrontier`, the resolver direct spectral package is
reduced to the existing per-`t₀` clamped coefficient producer, and the resolver
positivity field is not carried: it is produced from the gradient mild bridge.
The remaining carried fields are the currently missing per-datum producers for
the B-form bank, the gradient-map fixed-point bridge, the u-side time
neighbourhood package, and the sup-norm derivative maximum-principle field. -/
structure BFormSpectralFrontierResidual
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hGradientBridge :
    IntervalMildSolution p DB.T u₀ (conjugatePicardLimit p u₀ DB.T)
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
  hSupNormDeriv :
    IntervalDomainSupNormDerivativeNonposOn
      (conjugatePicardLimit p u₀ DB.T) (Set.Ioo (0 : ℝ) DB.T)

/-- Construct the actual `BFormSpectralFrontier` from the smaller named
residual.  This is the anti-fanout step: `hResolverData` is produced by the
clamped per-`t₀` resolver assembler, and `hVpos` is produced by the strict
resolver positivity theorem applied to the actual conjugate Picard limit
viewed as a gradient mild datum via `hGradientBridge`. -/
theorem bFormSpectralFrontier_of_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (R : BFormSpectralFrontierResidual p DB) :
    Nonempty (BFormSpectralFrontier p DB) := by
  refine ⟨?_⟩
  refine
    { bank := R.bank
      hGradientBridge := R.hGradientBridge
      hTimeNhd := R.hTimeNhd
      hResolverData := ?_
      hSupNormDeriv := R.hSupNormDeriv
      hVpos := ?_ }
  · exact
      ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
        (p := p) (T := DB.T) (u := conjugatePicardLimit p u₀ DB.T)
        R.hResolverCoeffTimeC1
  · exact
      ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos
        p (conjugateAsGradientMildSolutionData DB R.hGradientBridge)

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

/-- The B-form initial approach transfers to the gradient mild map using the
B-form fixed point and the explicit gradient-map bridge. -/
theorem gradientInitialApproach_of_BForm
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀
              (conjugatePicardLimit p u₀ DB.T) t x - u₀ x| < ε := by
  intro ε hε
  have hBInitial :=
    ShenWork.Paper2.BFormInitialTrace.intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
      p (PaperPositiveInitialDatum.admissible F.bank.huPaper).2 DB
  obtain ⟨δ, hδ, hδclose⟩ := hBInitial ε hε
  refine ⟨min δ DB.T, lt_min hδ DB.hT, ?_⟩
  intro t ht htδT x
  have htδ : t < δ := lt_of_lt_of_le htδT (min_le_left _ _)
  have htT_lt : t < DB.T := lt_of_lt_of_le htδT (min_le_right _ _)
  have htT : t ≤ DB.T := le_of_lt htT_lt
  have hBfix :
      (conjugatePicardLimit p u₀ DB.T) t x =
        intervalConjugateDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x :=
    (conjugateMildSolutionData_of_data DB).hmild t ht htT x
  have hGfix :
      (conjugatePicardLimit p u₀ DB.T) t x =
        intervalGradientDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x :=
    F.hGradientBridge t ht htT x
  have hmap :
      intervalGradientDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x =
        intervalConjugateDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x := by
    rw [← hGfix, hBfix]
  rw [hmap]
  exact hδclose t ht htδ x

/-- Assemble the classical frontier core from the B-form spectral frontier. -/
theorem gradientMildClassicalFrontierCoreData_of_BForm
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontier p DB) :
    GradientMildClassicalFrontierCoreData p
      (conjugateAsGradientMildSolutionData DB F.hGradientBridge) where
  hpde_u := F.hpde_u
  hregularityFrontier :=
    gradientMildClassicalRegularityFrontierData_of_spectral
      p (conjugateAsGradientMildSolutionData DB F.hGradientBridge)
      F.hTimeNhd F.hResolverData
      (hasRestartCosineRepresentations_of_BFormSpectralFrontier F)
      F.hVpos

/-- Construct the restart-frontier local data consumed by the gamma >= 1 umbrella
from per-datum B-form frontiers. -/
theorem hMildLocal_of_BForm
    (p : CM2Params)
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ DB : ConjugateMildExistenceData p u₀,
          Nonempty (BFormSpectralFrontierResidual p DB)) :
    IntervalDomainGradientMildRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨R⟩⟩ := hPerDatum u₀ hu₀
  obtain ⟨F⟩ := bFormSpectralFrontier_of_residual R
  exact
    ⟨conjugateAsGradientMildSolutionData DB F.hGradientBridge,
      hasRestartCosineRepresentations_of_BFormSpectralFrontier F,
      gradientInitialApproach_of_BForm F,
      gradientMildClassicalFrontierCoreData_of_BForm F⟩

/-- Paper 2 Theorem 1.1, general chi, via the Neumann-faithful B-form frontier.

This uses the existing restart-frontier umbrella.  Routing through
`paper2_theorem_1_1_of_frontier` would require the half-step logistic-source local
data and would reintroduce a logistic-only restart representation for chi != 0. -/
theorem paper2_theorem_1_1_general_chi_via_bform
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ DB : ConjugateMildExistenceData p u₀,
          Nonempty (BFormSpectralFrontierResidual p DB)) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartFrontierCoreLocalData
    p hχ ha hb hγ_ge_one (hMildLocal_of_BForm p hPerDatum) hUniform

#print axioms bFormSpectralFrontier_of_residual
#print axioms BFormBankedInputs.hsrcB
#print axioms BFormSpectralFrontier.hB_global
#print axioms hasRestartCosineRepresentations_of_BFormSpectralFrontier
#print axioms BFormSpectralFrontier.hpde_u
#print axioms conjugateAsGradientMildSolutionData
#print axioms gradientInitialApproach_of_BForm
#print axioms gradientMildClassicalFrontierCoreData_of_BForm
#print axioms hMildLocal_of_BForm
#print axioms paper2_theorem_1_1_general_chi_via_bform

end ShenWork.Paper2.BFormEndToEnd
