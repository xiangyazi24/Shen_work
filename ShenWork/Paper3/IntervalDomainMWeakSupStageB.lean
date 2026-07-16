/- The fully closed faithful general-`m` weak-sup eventual stability layer.

This is the `intervalDomainM` counterpart of `IntervalDomainWeakSupStageB.lean`:
the Stage-B orbit bound is discharged by the proved faithful basin entry, and
the global orbit is produced by the faithful small-data global existence.  No
`p.m = 1` hypothesis appears. -/
import ShenWork.Paper3.IntervalDomainStrongStageBGeneralM
import ShenWork.Paper3.IntervalDomainMSmallDataGlobalExistence

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- Stage B on the faithful general-`m` unit interval: weak sup-small
perturbations of a positive logistic equilibrium converge exponentially in
the physical `C¹` gauge after a uniform positive delay. -/
theorem intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound
    (p : CM2Params) :
    IntervalDomainMWeakSupEventualSpectralSemigroupOrbitBound p :=
  intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry
    p (intervalDomainMSupToStrongBasinEntry_proved p)

/-- Fully discharged faithful general-`m` Stage B.  The global orbit is
produced from faithful local existence and finite-horizon stability; the final
radius is the minimum of the orbit radius and the genuine global-existence
radius. -/
theorem intervalDomainM_eventualLocallyExponentiallyStableFromSup_unconditional
    (p : CM2Params)
    {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    EventualLocallyExponentiallyStableFromSup
      intervalDomainM p intervalDomainMSectorialStabilityNorms uStar vStar := by
  rcases intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound p
      uStar vStar ha heq hstable with
    ⟨deltaOrbit, hdeltaOrbit, C, hC, rate, hrate, t₀, ht₀, hbound⟩
  rcases intervalDomainM_smallDataGlobalExistence_of_linearlyStable
      p ha heq hstable with
    ⟨deltaGlobal, hdeltaGlobal, hglobalExistence⟩
  let delta := min deltaOrbit deltaGlobal
  have hdelta : 0 < delta := by
    simpa [delta] using lt_min hdeltaOrbit hdeltaGlobal
  refine ⟨delta, hdelta, C, hC, rate, hrate, t₀, ht₀, ?_⟩
  intro u₀ hu₀ hclose
  have hcloseOrbit : SupCloseToConstant intervalDomainM u₀ uStar deltaOrbit :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_left _ _)
  have hcloseGlobal : SupCloseToConstant intervalDomainM u₀ uStar deltaGlobal :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_right _ _)
  obtain ⟨u, v, hglobal, htrace⟩ :=
    hglobalExistence u₀ hu₀ hcloseGlobal
  refine ⟨u, v, hglobal, htrace, ?_⟩
  intro t ht
  simpa using hbound u₀ hu₀ hcloseOrbit u v hglobal htrace t ht

#print axioms intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound
#print axioms
  intervalDomainM_eventualLocallyExponentiallyStableFromSup_unconditional

end

end ShenWork.Paper3
