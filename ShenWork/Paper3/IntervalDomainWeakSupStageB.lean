/- The fully closed weak-sup, eventual nonlinear stability layer. -/
import ShenWork.Paper3.IntervalDomainWeakSupBasinEntry

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- Stage B on the unit interval: weak sup-small perturbations of a positive
logistic equilibrium converge exponentially in the physical `C¹` gauge after
a uniform positive delay.

The multiplier used by the proof is the full diagonal linearized semigroup.
In particular its zeroth coefficient decays with the logistic rate, and no
mass constraint or zero-mode projection occurs. -/
theorem intervalDomain_weakSupEventualSpectralSemigroupOrbitBound
    (p : CM2Params) (hm : p.m = 1) :
    IntervalDomainWeakSupEventualSpectralSemigroupOrbitBound p :=
  intervalDomain_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry
    p hm (intervalDomainSupToStrongBasinEntry_proved p)

/-- The closed Stage-B orbit theorem, together with the independently
constructed global solution, supplies the faithful mass-free local stability
package for the positive logistic branch. -/
theorem intervalDomain_eventualLocallyExponentiallyStableFromSup
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta) :
    EventualLocallyExponentiallyStableFromSup
      intervalDomain p intervalDomainSectorialStabilityNorms uStar vStar :=
  intervalDomain_eventualLocallyExponentiallyStableFromSup_of_eventualEquilibriumOrbitBound
    p intervalDomainSectorialStabilityNorms
    (intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm)
    ha heq hstable hexist

#print axioms intervalDomain_weakSupEventualSpectralSemigroupOrbitBound
#print axioms intervalDomain_eventualLocallyExponentiallyStableFromSup

end

end ShenWork.Paper3
