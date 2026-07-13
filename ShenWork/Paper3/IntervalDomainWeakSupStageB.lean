/- The fully closed weak-sup, eventual nonlinear stability layer. -/
import ShenWork.Paper3.IntervalDomainWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainSmallDataGlobalExistence

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

/-- Fully discharged faithful Stage B.  The global orbit is produced from
local existence and finite-horizon stability; the final radius is the minimum
of the orbit radius and the genuine global-existence radius. -/
theorem intervalDomain_eventualLocallyExponentiallyStableFromSup_unconditional
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    EventualLocallyExponentiallyStableFromSup
      intervalDomain p intervalDomainSectorialStabilityNorms uStar vStar := by
  rcases intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm with
    ⟨_hm, horbit⟩
  rcases horbit uStar vStar ha heq hstable with
    ⟨deltaOrbit, hdeltaOrbit, C, hC, rate, hrate, t₀, ht₀, hbound⟩
  rcases intervalDomain_smallDataGlobalExistence_of_linearlyStable
      p hm ha heq hstable with
    ⟨deltaGlobal, hdeltaGlobal, hglobalExistence⟩
  let delta := min deltaOrbit deltaGlobal
  have hdelta : 0 < delta := by
    simpa [delta] using lt_min hdeltaOrbit hdeltaGlobal
  refine ⟨delta, hdelta, C, hC, rate, hrate, t₀, ht₀, ?_⟩
  intro u₀ hu₀ hclose
  have hcloseOrbit : SupCloseToConstant intervalDomain u₀ uStar deltaOrbit :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_left _ _)
  have hcloseGlobal : SupCloseToConstant intervalDomain u₀ uStar deltaGlobal :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_right _ _)
  obtain ⟨u, v, hglobal, htrace⟩ :=
    hglobalExistence u₀ hu₀ hcloseGlobal
  exact ⟨u, v, hglobal, htrace,
    hbound u₀ hu₀ hcloseOrbit u v hglobal htrace⟩

#print axioms intervalDomain_weakSupEventualSpectralSemigroupOrbitBound
#print axioms intervalDomain_eventualLocallyExponentiallyStableFromSup
#print axioms
  intervalDomain_eventualLocallyExponentiallyStableFromSup_unconditional

end

end ShenWork.Paper3
