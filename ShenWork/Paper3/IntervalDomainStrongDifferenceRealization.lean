/- Strong spectral realization of the difference of two physical profiles. -/
import ShenWork.Paper3.IntervalDomainStrongRealizationProducer

namespace ShenWork.Paper3

open ShenWork.IntervalDomain

noncomputable section

def intervalDomainX2SigmaDifferenceProfile
    (u₁ u₂ : intervalDomainPoint → ℝ) : intervalDomainPoint → ℝ :=
  fun x => u₁ x - u₂ x

def IntervalDomainX2SigmaPairPerturbation
    (sigma : ℝ) (u₁ u₂ : intervalDomainPoint → ℝ) : Prop :=
  IntervalDomainX2SigmaPerturbation sigma 0
    (intervalDomainX2SigmaDifferenceProfile u₁ u₂)

def intervalDomainX2SigmaPairDistance
    (sigma : ℝ) (u₁ u₂ : intervalDomainPoint → ℝ) : ℝ :=
  intervalDomainX2SigmaDistance sigma 0
    (intervalDomainX2SigmaDifferenceProfile u₁ u₂)

theorem intervalDomainX2SigmaPairDistance_nonneg
    (sigma : ℝ) (u₁ u₂ : intervalDomainPoint → ℝ) :
    0 ≤ intervalDomainX2SigmaPairDistance sigma u₁ u₂ :=
  Real.sqrt_nonneg _

/-- No smallness is needed for the common `C¹` envelope; smallness is only
used separately to preserve positivity of each physical profile. -/
theorem IntervalDomainX2SigmaRealizationBounds.envelope_bounds
    {sigma uStar : ℝ} {w : intervalDomainPoint → ℝ}
    (H : IntervalDomainX2SigmaRealizationBounds sigma uStar w) :
    let d := intervalDomainX2SigmaDistance sigma uStar w
    let M := intervalDomainX2SigmaC1Envelope sigma * d
    (∀ x, |w x - uStar| ≤ M) ∧
      (∀ x, intervalDomain.gradNorm (fun y => w y - uStar) x ≤ M) := by
  dsimp only
  let d := intervalDomainX2SigmaDistance sigma uStar w
  let C := intervalDomainX2SigmaC1Envelope sigma
  have hd : 0 ≤ d := by dsimp [d]; exact Real.sqrt_nonneg _
  have hvalueTrace : intervalDomainX2SigmaValueTrace sigma ≤ C := by
    dsimp [C, intervalDomainX2SigmaC1Envelope]
    linarith [intervalDomainX2SigmaDerivativeTrace_nonneg sigma]
  have hderivTrace : intervalDomainX2SigmaDerivativeTrace sigma ≤ C := by
    dsimp [C, intervalDomainX2SigmaC1Envelope]
    linarith [intervalDomainX2SigmaValueTrace_nonneg sigma]
  constructor
  · intro x
    calc
      |w x - uStar| ≤ intervalDomainX2SigmaValueTrace sigma * d := H.value_bound x
      _ ≤ C * d := mul_le_mul_of_nonneg_right hvalueTrace hd
  · intro x
    calc
      intervalDomain.gradNorm (fun y => w y - uStar) x ≤
          intervalDomainX2SigmaDerivativeTrace sigma * d := H.gradient_bound x
      _ ≤ C * d := mul_le_mul_of_nonneg_right hderivTrace hd

/-- Fractional membership of the physical difference and continuity of both
profiles produce the same coefficient-to-`C¹` realization used for one
trajectory. -/
theorem intervalDomainX2SigmaPairRealizationBounds_of_continuous
    {sigma : ℝ} {u₁ u₂ : intervalDomainPoint → ℝ}
    (hsigma : 3 / 4 < sigma) (hu₁ : Continuous u₁) (hu₂ : Continuous u₂)
    (hmem : IntervalDomainX2SigmaPairPerturbation sigma u₁ u₂) :
    IntervalDomainX2SigmaRealizationBounds sigma 0
      (intervalDomainX2SigmaDifferenceProfile u₁ u₂) := by
  apply intervalDomainX2SigmaRealizationBounds_of_continuous hsigma
  · exact hu₁.sub hu₂
  · exact hmem

theorem intervalDomainX2SigmaPairRealizationBounds_value
    {sigma : ℝ} {u₁ u₂ : intervalDomainPoint → ℝ}
    (H : IntervalDomainX2SigmaRealizationBounds sigma 0
      (intervalDomainX2SigmaDifferenceProfile u₁ u₂))
    (x : intervalDomainPoint) :
    |u₁ x - u₂ x| ≤ intervalDomainX2SigmaC1Envelope sigma *
      intervalDomainX2SigmaPairDistance sigma u₁ u₂ := by
  have h := H.envelope_bounds.1 x
  simpa [intervalDomainX2SigmaDifferenceProfile,
    intervalDomainX2SigmaPairDistance] using h

#print axioms IntervalDomainX2SigmaRealizationBounds.envelope_bounds
#print axioms intervalDomainX2SigmaPairRealizationBounds_of_continuous
#print axioms intervalDomainX2SigmaPairRealizationBounds_value

end

end ShenWork.Paper3
