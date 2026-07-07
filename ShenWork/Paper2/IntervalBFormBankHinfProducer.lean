/-
  Producer for the B-form bank `Hinf` field.

  The required bounds/integrability leaves over the conjugate Picard iterates
  already live in `IntervalBankInfAndLogSrcWiring`.  This file packages them
  into the public `ConjugatePicardInfThresholdData` producer used by the
  positive B-form route.
-/
import ShenWork.Paper2.IntervalBankInfAndLogSrcWiring

open MeasureTheory Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.BFormBankHinfProducer

open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData)
open ShenWork.IntervalBankInfAndLogSrcWiring

/-- The `Hinf` field for `BFormBankedInputs`, produced directly from the
canonical conjugate mild-existence data. -/
noncomputable def Hinf_of_conjugateMildExistenceData
    {p : CM2Params} {u₀ : ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ConjugatePicardInfThresholdData p u₀ D.T :=
  ShenWork.IntervalConjugatePicard.conjugatePicardInfThresholdData_of_picard_bounds
    D
    (iterCQ D) (iterCL D)
    (iterCQ_nonneg D) (iterCL_nonneg D)
    (fun n s hs hsT => iterChemFlux_integrable D n s hs hsT)
    (fun n s hs hsT y => iterChemFlux_windowBound D n s hs hsT y)
    (fun n _t ht htT x => iterChemFlux_duhamel_intervalIntegrable D n ht htT x)
    (fun n s hs hsT y => iterLogistic_windowBound D n s hs hsT y)
    (fun n _t ht htT x => iterLogistic_duhamel_intervalIntegrable D n ht htT x)

#print axioms Hinf_of_conjugateMildExistenceData

end ShenWork.Paper2.BFormBankHinfProducer
