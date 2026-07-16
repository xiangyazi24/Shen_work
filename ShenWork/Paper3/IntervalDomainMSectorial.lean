/- Faithful general-`m` sectorial constants and stability gauges. -/
import ShenWork.Paper3.IntervalDomainSectorial

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- The unit-interval Paper 3 constants, packaged over the faithful
`intervalDomainM` model.  The spectral formulas are unchanged: only the
nonlinear bounded-domain equation carried by the domain package differs. -/
def intervalDomainMSectorialPaper3Constants
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    Paper3Constants intervalDomainM p where
  chiCritical := fun uStar =>
    paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
      (p.ν / p.μ * uStar ^ p.γ)
  chiStrong1 := fun uStar =>
    chiStrong1Formula p uStar (p.ν / p.μ * uStar ^ p.γ)
  chiStrong2 := fun uStar => chiStrong2Formula p uStar
  chiStrong3 := fun uStar =>
    chiStrong3Formula p M0 uStar (p.ν / p.μ * uStar ^ p.γ)
  chiStrong4 := fun uStar => chiStrong4Formula p M0 uStar
  chiMinimal1 := fun uStar => chiMinimal1Formula p 1 uStar uBar vLower
  chiMinimal2 := fun _uStar => chiMinimal2Formula p uBar vLower
  eventualMinimalUBound := fun _uStar => uBar
  gaussianLowerConst := 1
  gaussianLowerConst_pos := by norm_num

/-- The faithful constants use exactly the discrete unit-interval Neumann
critical spectrum. -/
theorem intervalDomainMSectorialPaper3Constants_usesCriticalSpectrum
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p
      (intervalDomainMSectorialPaper3Constants p M0 uBar vLower) := by
  intro uStar _huStar
  rfl

/-- The concrete interval `C¹`/sup gauges, repackaged over the faithful
general-`m` domain.  Both interval domains have the same point, norm, and
gradient fields; their only difference is the chemotaxis equation. -/
def intervalDomainMSectorialStabilityNorms :
    StabilityNorms intervalDomainM where
  c1Distance := intervalDomainSectorialC1Distance
  xpSigmaDistance := intervalDomainSectorialXpSigmaDistance

@[simp] theorem intervalDomainMSectorialStabilityNorms_c1Distance
    (f g : intervalDomainM.Point → ℝ) :
    intervalDomainMSectorialStabilityNorms.c1Distance f g =
      intervalDomainSectorialC1Distance f g := rfl

@[simp] theorem intervalDomainMSectorialStabilityNorms_xpSigmaDistance
    (sigma pNorm : ℝ) (f g : intervalDomainM.Point → ℝ) :
    intervalDomainMSectorialStabilityNorms.xpSigmaDistance sigma pNorm f g =
      intervalDomainM.supNorm (fun x => f x - g x) := rfl

theorem intervalDomainMSectorialStabilityNorms_xpSigma_le_supNorm
    (sigma pNorm uStar : ℝ) (u₀ : intervalDomainM.Point → ℝ) :
    intervalDomainMSectorialStabilityNorms.xpSigmaDistance sigma pNorm u₀
        (fun _ => uStar) ≤
      intervalDomainM.supNorm (fun x => u₀ x - uStar) := by
  rfl

theorem intervalDomainMSectorialStabilityNorms_supControlsXpSigmaDistance
    (sigma pNorm uStar : ℝ) :
    SupControlsXpSigmaDistance intervalDomainM
      intervalDomainMSectorialStabilityNorms sigma pNorm uStar :=
  SupControlsXpSigmaDistance.of_xpSigma_le_supNorm
    (intervalDomainMSectorialStabilityNorms_xpSigma_le_supNorm
      sigma pNorm uStar)

#print axioms intervalDomainMSectorialPaper3Constants
#print axioms intervalDomainMSectorialPaper3Constants_usesCriticalSpectrum
#print axioms intervalDomainMSectorialStabilityNorms
#print axioms intervalDomainMSectorialStabilityNorms_supControlsXpSigmaDistance

end

end ShenWork.Paper3
