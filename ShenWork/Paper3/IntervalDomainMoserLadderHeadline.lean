import ShenWork.Paper3.IntervalDomainSectorialNonlinearBridges
import ShenWork.PDE.IntervalDomainMoserLadderAtoms

open ShenWork.IntervalDomainExistence

noncomputable section

namespace ShenWork.Paper3

/-- Sectorial mainline facts with the Paper-3 Moser-ladder atoms wired through
the lower-level interval-domain Moser frontiers.  Compared with
`IntervalDomainSectorialMainlineAprioriFacts`, the old mass/Lp/smoothing
package no longer carries `driftBoundFromMass`, `allLpBoundFromBootstrap`, or
`endpointBoundFromLp` as fields. -/
structure IntervalDomainSectorialMainlineMoserLadderFacts
    (p : CM2Params) (uBar : ℝ) where
  m_ge_one : 1 ≤ p.m
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserLadderResiduals p
  persistence : IntervalDomainSectorialPointwisePersistenceFacts p uBar

def IntervalDomainSectorialMainlineMoserLadderFacts.to_aprioriFacts
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineMoserLadderFacts p uBar) :
    IntervalDomainSectorialMainlineAprioriFacts p uBar where
  m_ge_one := h.m_ge_one
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_routeResiduals
  persistence := h.persistence

/-- Headline target from the reduced Moser-ladder facts. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_moserLadderFacts
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfacts : IntervalDomainSectorialMainlineMoserLadderFacts p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_aprioriFacts
    p M0 uBar vLower hfacts.to_aprioriFacts

end ShenWork.Paper3

end
