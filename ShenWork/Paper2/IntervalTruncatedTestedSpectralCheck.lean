/-
  TEMPORARY elaboration check for the `testedSpectralIdentities` patch in
  `IntervalChiNegV5SelfContained` (whose import chain is currently blocked by
  in-flight work elsewhere).  This file replicates the `TestedSpectralIdentities`
  structure verbatim and checks that the three assembly theorems of
  `IntervalTruncatedTestedSpectral` fill its fields.  Delete after
  `IntervalChiNegV5SelfContained` builds.
-/
import ShenWork.Paper2.IntervalTruncatedTestedSpectral

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedTestedSpectralCheck

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.BFormPositiveDatumNegPart

structure TestedSpectralIdentitiesCheck
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) (t : ℝ) : Prop where
  time_leibniz_tsum :
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                intervalDomain.timeDeriv
                  (truncatedConjugatePicardLimit p u₀ DT.T) t z) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        truncatedPicardCoeffTimeDeriv p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k
  gradient_ibp_tsum :
      (∫ x,
          deriv (intervalDomainLift
            ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x *
            deriv
              (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        unitIntervalCosineEigenvalue k *
          truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k
  source_pairing :
      (∑' k : ℕ,
        truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
        =
      p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p
              ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
            deriv
              (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
          ∂ intervalMeasure 1)
        + (∫ x,
            truncatedLogisticLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
              negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
            ∂ intervalMeasure 1)

theorem testedSpectralIdentitiesCheck
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < DT.T) :
    TestedSpectralIdentitiesCheck p DT t := by
  have D := truncatedPositiveTimeSpectralData_of_existenceData DT ht htT
  exact
    { time_leibniz_tsum := tested_time_leibniz_of_spectralData ht htT.le D
      gradient_ibp_tsum := tested_gradient_ibp_of_spectralData ht htT.le D
      source_pairing := tested_source_pairing_of_spectralData ht htT.le D }

end ShenWork.Paper2.IntervalTruncatedTestedSpectralCheck
