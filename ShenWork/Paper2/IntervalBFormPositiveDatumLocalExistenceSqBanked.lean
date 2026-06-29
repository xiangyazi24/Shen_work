import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSq

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint
   intervalDomainConstExtend intervalDomainChemotaxisDiv)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- The remaining per-datum plumbing needed to build the squared-barrier
`PositiveDatumBFormLocalComponentsSq` package for the canonical B-form Picard
limit.

The `bank` field is the canonical B-form spectral/cosine bank.  The following
fields are the direct classical resolver plumbing, the Cron2 negative-part
energy core, and the linear drift strip data consumed by the squared-barrier
restart route. -/
structure PositiveDatumBFormSqBankedPlumbing
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank :
    ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) p
  hVpos :
    ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t x
  DT : TruncatedConjugateMildExistenceData p u₀
  Hbridge : TruncatedConjugateLimitBridge p DB DT
  HmildWeak : TruncatedMildToWeakAvailable p DB
  Henergy : NegativePartEnergyCoreData p DB
  A : ℝ
  Dbar : ℝ
  M : ℝ
  hM_nonneg : 0 ≤ M
  hM : A ^ 2 / 2 + Dbar ≤ M
  drift : ℝ → ℝ → ℝ
  react : ℝ → ℝ → ℝ
  hstrip :
    ∀ τ, 0 < τ → τ < DB.T →
      NeumannLinearDriftCoefficientsRegular (DB.T - τ)
        (restartTimeShift τ drift) (restartTimeShift τ react) ∧
      IsClassicalNeumannLinearDriftSuperSolution (DB.T - τ)
        (restartTimeShift τ drift) (restartTimeShift τ react)
        (restartTimeShift τ (bformConjugatePicardLift p DB)) ∧
      (∀ s x, 0 < s → s < DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 → |drift (τ + s) x| ≤ A) ∧
      (∀ s x, 0 < s → s < DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 → -react (τ + s) x ≤ Dbar)

def PositiveDatumBFormSqBankedPlumbing.directFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (P : PositiveDatumBFormSqBankedPlumbing p DB) :
    ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB where
  bank := P.bank
  hTimeNhd := P.hTimeNhd
  hResolverData := P.hResolverData
  hVpos := P.hVpos

/-- Assemble the per-datum squared-barrier component bundle from the banked
B-form pieces. -/
def PositiveDatumBFormLocalComponentsSq.of_banked
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (P : PositiveDatumBFormSqBankedPlumbing p DB) :
    PositiveDatumBFormLocalComponentsSq p u₀ :=
  let F := P.directFrontier
  let hsol :=
    ShenWork.Paper2.BFormDirectClassical.intervalConjugatePicardLimit_isClassicalSolution_direct F
  { DB := DB
    huPaper := P.bank.huPaper
    Hinf := P.bank.Hinf
    hsmall := P.bank.hsmall
    hpde_u := P.bank.hpde_u
    DT := P.DT
    Hbridge := P.Hbridge
    HmildWeak := P.HmildWeak
    Henergy := P.Henergy
    A := P.A
    Dbar := P.Dbar
    M := P.M
    hM_nonneg := P.hM_nonneg
    hM := P.hM
    drift := P.drift
    react := P.react
    hstrip := P.hstrip
    regularity :=
      ShenWork.Paper2.BFormDirectClassical.intervalConjugatePicardLimit_classicalRegularity_direct F
    hpde_v := by
      intro t x ht htT hx
      exact hsol.pde_v ht htT hx
    neumann := by
      intro t x ht htT hx
      exact hsol.neumann ht htT hx
  }

/-- Discharge `PositiveDatumBFormLocalHypSq` from the banked per-datum B-form
plumbing. -/
theorem positiveDatumBFormLocalHypSq_of_banked
    {p : CM2Params}
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB)) :
    PositiveDatumBFormLocalHypSq p := by
  intro u₀ hu₀
  rcases hbanked u₀ hu₀ with ⟨DB, ⟨P⟩⟩
  exact ⟨PositiveDatumBFormLocalComponentsSq.of_banked P⟩

/-- General-χ Theorem 1.1 through the squared-barrier B-form route, with the
per-datum B-form bundle supplied by the banked pieces above. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_banked
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq
    p hχ ha hb hγ_ge_one
    (positiveDatumBFormLocalHypSq_of_banked hbanked)
    hUniform

end ShenWork.Paper2.BFormPositiveDatumLocalSq
