/-
  ShenWork/Paper2/IntervalBFormSpectralFrontierNoHvpos.lean

  B-form spectral frontier with `hVpos` filled from the strict resolver
  positivity producer.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalBFormEndToEnd
import ShenWork.Paper2.IntervalResolverStrictPositivity

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
  (IntervalMildSolution intervalGradientDuhamelMap)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.Paper2
open ShenWork.Paper2.BFormEndToEnd

noncomputable section

namespace ShenWork.Paper2.BFormEndToEnd

/-- B-form spectral frontier with the resolver strict-positivity field removed.

The original `BFormSpectralFrontier.hVpos` field is derivable from
`GradientMildSolutionData` once the B-form solution has been bridged to the
gradient mild map. -/
structure BFormSpectralFrontierNoHvpos
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

/-- Fill the original B-form `hVpos` field using strict resolver positivity. -/
def bFormSpectralFrontier_of_noHvpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontierNoHvpos p DB) :
    BFormSpectralFrontier p DB where
  bank := F.bank
  hGradientBridge := F.hGradientBridge
  hTimeNhd := F.hTimeNhd
  hResolverData := F.hResolverData
  hVpos := by
    intro t ht htT x
    let D := conjugateAsGradientMildSolutionData DB F.hGradientBridge
    simpa [D, conjugateAsGradientMildSolutionData] using
      (ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos
        p D t ht htT x)

/-- B-form initial approach with the redundant `hVpos` field discharged
internally. -/
theorem gradientInitialApproach_of_BForm_noHvpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormSpectralFrontierNoHvpos p DB) :
    ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀
              (conjugatePicardLimit p u₀ DB.T) t x - u₀ x| < ε :=
  gradientInitialApproach_of_BForm (bFormSpectralFrontier_of_noHvpos F)

#print axioms bFormSpectralFrontier_of_noHvpos
#print axioms gradientInitialApproach_of_BForm_noHvpos

end ShenWork.Paper2.BFormEndToEnd
