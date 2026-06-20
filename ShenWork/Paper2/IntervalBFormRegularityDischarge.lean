import ShenWork.Paper2.IntervalBFormDirectClassical

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- C²/C¹ regularity of the B-form Picard limit from the direct cosine-series
and resolver spectral frontier.

The input is not a carried regularity conclusion.  The proof routes through
`intervalConjugatePicardLimit_classicalRegularity_direct`, whose proof consumes
the restart cosine representation, eigenvalue-weighted summability of the
restarted coefficients, the resolver source-decay/C² facts, and the u/v
time-neighborhood spectral data. -/
theorem bForm_classicalRegularity_of_direct_frontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB) :
    intervalDomain.classicalRegularity DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  rcases F with ⟨bank, hTimeNhd, hResolverData, hVpos, hInitialApproach⟩
  let F' : ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB :=
    { bank := bank
      hTimeNhd := hTimeNhd
      hResolverData := hResolverData
      hVpos := hVpos
      hInitialApproach := hInitialApproach }
  simpa [intervalDomain] using
    ShenWork.Paper2.BFormDirectClassical.intervalConjugatePicardLimit_classicalRegularity_direct F'

end ShenWork.Paper2.BFormPositiveDatumLocalSq
