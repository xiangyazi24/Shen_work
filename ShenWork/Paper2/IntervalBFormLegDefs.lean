import ShenWork.Paper2.IntervalConjugateCosineSeries

open Filter Topology Set MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalBFormSpectral

open ShenWork.IntervalDomain
  (intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries
  (intervalSineInner)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.CosineSpectrum
  (cosineMode)

/-- The flux slice used by the B-form chemotaxis Duhamel leg. -/
def bFormChemFluxAt (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ → ℝ :=
  chemFluxLifted p (u t)

/-- One positive-time cosine term in the B-kernel representation. -/
def bFormPositiveTimeCosineTerm
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t r x : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-r * unitIntervalCosineEigenvalue n) *
    (((n : ℝ) * Real.pi) * intervalSineInner (bFormChemFluxAt p u t) n))
      * cosineMode n x

/-- The B-form chemotaxis Duhamel leg before multiplication by `-χ₀`. -/
def bFormConjugateDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x

/-- The ordinary logistic Duhamel leg. -/
def bFormLogisticDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x

/-- The non-homogeneous part of the B-form mild profile. -/
def bFormInhomogeneousDuhamelLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t x : ℝ) : ℝ :=
  (-p.χ₀) * bFormConjugateDuhamelLeg p u t x
    + bFormLogisticDuhamelLeg p u t x

end ShenWork.IntervalBFormSpectral
