import ShenWork.Paper2.IntervalBFormCron2CoefficientWeakTest
import ShenWork.Paper2.IntervalConjugateCosineSeries

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)

/-- Initial cosine coefficients for the truncated Picard restart. -/
def truncatedPicardInitialCoeff
    (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ :=
  cosineCoeffs (intervalDomainLift u₀)

/-- Normalized cosine coefficient of the truncated chemotaxis-divergence source.
This is the coefficient family represented by the conjugate B-kernel acting on
`truncatedChemFluxLifted`. -/
def truncatedChemDivSourceCoeff (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n =>
    ((n : ℝ) * Real.pi) * intervalSineInner (truncatedChemFluxLifted p (u s)) n

/-- Normalized cosine coefficient of the truncated logistic source. -/
def truncatedLogisticSourceCoeff (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (truncatedLogisticLifted p (u s)) n

/-- Total truncated B-form source coefficient:
logistic minus `χ₀` times the chemotaxis-divergence coefficient. -/
def truncatedBFormSourceCoeff (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n =>
    truncatedLogisticSourceCoeff p u s n
      - p.χ₀ * truncatedChemDivSourceCoeff p u s n

/-- Restart coefficient of the truncated Picard limit, written with the
truncated source. -/
def truncatedPicardCoeff (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℕ → ℝ :=
  localRestartCoeff (truncatedPicardInitialCoeff u₀)
    (truncatedBFormSourceCoeff p u) t

/-- The right side of the coefficient ODE. -/
def truncatedPicardCoeffTimeDeriv (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℕ → ℝ :=
  fun k =>
    -unitIntervalCosineEigenvalue k * truncatedPicardCoeff p u₀ u t k
      + truncatedBFormSourceCoeff p u t k

/-- Coefficient FTC for the truncated Picard restart:
`a'_k = -λ_k a_k + src_k`.  The source is the truncated source, so this does
not use nonnegativity of `u`. -/
theorem truncatedPicardCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T t : ℝ}
    (ht0 : 0 < t) (htT : t < T) (k : ℕ)
    (hsrc_cont :
      ContinuousOn (fun s => truncatedBFormSourceCoeff p u s k)
        (Set.Icc (0 : ℝ) T)) :
    HasDerivAt (fun τ => truncatedPicardCoeff p u₀ u τ k)
      (truncatedPicardCoeffTimeDeriv p u₀ u t k) t := by
  simpa [truncatedPicardCoeff, truncatedPicardCoeffTimeDeriv] using
    localRestartCoeff_hasDerivAt_ode_neg_lam_add
      (a₀ := truncatedPicardInitialCoeff u₀)
      (src := truncatedBFormSourceCoeff p u)
      (T := T) ht0 htT k hsrc_cont

/-- Algebraic ODE field used by `NegativePartCoefficientWeakTestData`, with the
derivative value supplied by the preceding FTC theorem. -/
theorem truncatedPicardCoeff_ode
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    ∀ k, truncatedPicardCoeffTimeDeriv p u₀ u t k =
      -unitIntervalCosineEigenvalue k * truncatedPicardCoeff p u₀ u t k
        + truncatedBFormSourceCoeff p u t k := by
  intro k
  rfl

/-- A1 coefficient weak-test data for the faithful truncated Picard limit.

The ODE component is produced here from the truncated restart/FTC route.  The
three tested-series identifications and the two summability facts remain the
explicit spectral-analysis inputs required by `NegativePartCoefficientWeakTestData`. -/
def truncatedNegativePartCoefficientWeakTestData_of_truncatedPicard
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) {t : ℝ}
    (ht0 : 0 < t) (htT : t < DT.T)
    (hsrc_cont :
      ∀ k, ContinuousOn
        (fun s =>
          truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) s k)
        (Set.Icc (0 : ℝ) DT.T))
    (lap_summable :
      Summable (fun k : ℕ =>
        unitIntervalCosineEigenvalue k *
          truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k))
    (source_summable :
      Summable (fun k : ℕ =>
        truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k))
    (time_leibniz_tsum :
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                ShenWork.IntervalDomain.intervalDomain.timeDeriv
                  (truncatedConjugatePicardLimit p u₀ DT.T) t z) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        truncatedPicardCoeffTimeDeriv p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
    (gradient_ibp_tsum :
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
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
    (source_pairing :
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
            ∂ intervalMeasure 1)) :
    TruncatedNegativePartCoefficientWeakTestData p DT t := by
  let u := truncatedConjugatePicardLimit p u₀ DT.T
  have _hftc :
      ∀ k, HasDerivAt (fun τ => truncatedPicardCoeff p u₀ u τ k)
        (truncatedPicardCoeffTimeDeriv p u₀ u t k) t :=
    fun k => truncatedPicardCoeff_hasDerivAt ht0 htT k (hsrc_cont k)
  exact
    { coeff := truncatedPicardCoeff p u₀ u t
      coeffTimeDeriv := truncatedPicardCoeffTimeDeriv p u₀ u t
      sourceCoeff := truncatedBFormSourceCoeff p u t
      coeff_ode := truncatedPicardCoeff_ode p u₀ u t
      lap_summable := lap_summable
      source_summable := source_summable
      time_leibniz_tsum := time_leibniz_tsum
      gradient_ibp_tsum := gradient_ibp_tsum
      source_pairing := source_pairing }

end ShenWork.Paper2.BFormPositiveDatumNegPart
