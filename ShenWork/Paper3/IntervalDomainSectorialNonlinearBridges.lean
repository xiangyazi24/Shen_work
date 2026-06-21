/-
  Bridges for the nonlinear inputs in the interval-domain sectorial mainline.

  This file does not prove the Duhamel bootstrap or lower-barrier arguments.
  It discharges the formal glue around them:
  * a global Cauchy-solution package implies both small-data existence fields;
  * pointwise eventual lower barriers imply the four raw persistence fields.
-/
import ShenWork.Paper3.IntervalDomainSectorial
import ShenWork.Paper3.IntervalDomainTheorem21Part1
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalDomainAPrioriGlobal

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- A global interval-domain Cauchy-solution package immediately supplies the
ordinary small-data existence field used by Paper3.  The smallness radius is not
used here; it is only a restriction on the allowed initial data. -/
theorem intervalDomain_smallDataGlobal_of_globalSolutionExists
    (p : CM2Params)
    (hglobal : IntervalDomainGlobalSolutionExists p)
    (hm : 1 ≤ p.m) :
    ∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta := by
  intro _uStar _delta _hdelta u₀ hu₀ _hclose
  exact hglobal.globalSolutionExists u₀ hu₀ hm

/-- The same global Cauchy-solution package also supplies the mass-constrained
small-data existence field; the mass constraint is an extra admissibility
condition on the initial datum. -/
theorem intervalDomain_massConstrainedSmallDataGlobal_of_globalSolutionExists
    (p : CM2Params)
    (hglobal : IntervalDomainGlobalSolutionExists p)
    (hm : 1 ≤ p.m) :
    ∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta := by
  intro _uStar _delta _hdelta u₀ hu₀ _hclose _hmass
  exact hglobal.globalSolutionExists u₀ hu₀ hm

/-! ### Pointwise lower-barrier forms of the four persistence inputs -/

/-- Pointwise version of the first uniform-persistence frontier. -/
def IntervalDomainUniformPersistencePart1PointwiseRaw
    (p : CM2Params) : Prop :=
  1 ≤ p.m →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
        ∃ δu > 0,
          (∀ᶠ t in atTop, ∀ x : intervalDomain.Point, δu ≤ u t x) ∧
          (∀ᶠ t in atTop, ∀ x : intervalDomain.Point,
            p.ν / p.μ * δu ^ p.γ ≤ v t x)

/-- Pointwise version of the second uniform-persistence frontier. -/
def IntervalDomainUniformPersistencePart2PointwiseRaw
    (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          let lowerU :=
            ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
              (1 / p.α)
          (∀ᶠ t in atTop, ∀ x : intervalDomain.Point, lowerU ≤ u t x) ∧
            (∀ᶠ t in atTop, ∀ x : intervalDomain.Point,
              p.ν / p.μ * lowerU ^ p.γ ≤ v t x)

/-- Pointwise version of the third uniform-persistence frontier. -/
def IntervalDomainUniformPersistencePart3PointwiseRaw
    (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
        let lowerU :=
          min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
            max (1 / (p.m - 1)) (1 / p.α)
        (∀ᶠ t in atTop, ∀ x : intervalDomain.Point, lowerU ≤ u t x) ∧
          (∀ᶠ t in atTop, ∀ x : intervalDomain.Point,
            p.ν / p.μ * lowerU ^ p.γ ≤ v t x)

/-- Pointwise version of the fourth uniform-persistence frontier for the
concrete sectorial constants.  Positivity of the displayed lower constant is
included because the raw statement packages an `EventuallyLowerBound`. -/
def IntervalDomainUniformPersistencePart4PointwiseRaw
    (p : CM2Params) (uBar : ℝ) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
      ∀ uStar > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
        HasInitialMass intervalDomain u uStar →
          0 < minimalVLowerFormula 1 p.γ uStar uBar ∧
          (∀ᶠ t in atTop, ∀ x : intervalDomain.Point,
            minimalVLowerFormula 1 p.γ uStar uBar ≤ v t x)

/-- Pointwise lower barriers imply the first raw persistence field. -/
theorem intervalDomain_uniformPersistencePart1Raw_of_pointwise
    {p : CM2Params}
    (hpoint : IntervalDomainUniformPersistencePart1PointwiseRaw p) :
    UniformPersistencePart1Raw intervalDomain p := by
  intro hm u v huv
  rcases hpoint hm u v huv with ⟨δu, hδu, hu, hv⟩
  refine ⟨δu, hδu, ?_, ?_⟩
  · exact
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        hδu hu
  · have hvpos : 0 < p.ν / p.μ * δu ^ p.γ :=
      mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hδu _)
    exact
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        hvpos hv

/-- Pointwise lower barriers imply the second raw persistence field. -/
theorem intervalDomain_uniformPersistencePart2Raw_of_pointwise
    {p : CM2Params}
    (hpoint : IntervalDomainUniformPersistencePart2PointwiseRaw p) :
    UniformPersistencePart2Raw intervalDomain p := by
  intro ha hb hχ0 hm hβ hχ u v huv
  rcases hpoint ha hb hχ0 hm hβ hχ u v huv with ⟨hu, hv⟩
  refine ⟨?_, ?_⟩
  · exact
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        (theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ) hu
  · exact
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        (theorem_2_1_part2_lowerV_pos p ha hb hχ0 hm hβ hχ) hv

/-- Pointwise lower barriers imply the third raw persistence field. -/
theorem intervalDomain_uniformPersistencePart3Raw_of_pointwise
    {p : CM2Params}
    (hpoint : IntervalDomainUniformPersistencePart3PointwiseRaw p) :
    UniformPersistencePart3Raw intervalDomain p := by
  intro ha hb hχ0 hm hβ u v huv
  rcases hpoint ha hb hχ0 hm hβ u v huv with ⟨hu, hv⟩
  refine ⟨?_, ?_⟩
  · exact
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        (theorem_2_1_part3_lowerU_pos p ha hb hχ0 hm hβ) hu
  · exact
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        (theorem_2_1_part3_lowerV_pos p ha hb hχ0 hm hβ) hv

/-- Pointwise lower barriers imply the fourth raw persistence field for the
concrete sectorial constants. -/
theorem intervalDomain_uniformPersistencePart4Raw_of_pointwise
    {p : CM2Params} {uBar : ℝ}
    (hpoint : IntervalDomainUniformPersistencePart4PointwiseRaw p uBar) :
    UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1 := by
  intro hCO ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass
  rcases hpoint ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass with
    ⟨hlower_pos, hpointwise⟩
  simpa [minimalVLowerFormula] using
    (intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hlower_pos hpointwise)

/-- Bundled pointwise persistence frontiers. -/
structure IntervalDomainSectorialPointwisePersistenceFacts
    (p : CM2Params) (uBar : ℝ) where
  part1 : IntervalDomainUniformPersistencePart1PointwiseRaw p
  part2 : IntervalDomainUniformPersistencePart2PointwiseRaw p
  part3 : IntervalDomainUniformPersistencePart3PointwiseRaw p
  part4 : IntervalDomainUniformPersistencePart4PointwiseRaw p uBar

/-- Convert bundled pointwise persistence frontiers to the raw sectorial
persistence package. -/
def IntervalDomainSectorialPointwisePersistenceFacts.to_persistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialPointwisePersistenceFacts p uBar) :
    IntervalDomainSectorialTheorem21Persistence p uBar where
  part1 := intervalDomain_uniformPersistencePart1Raw_of_pointwise h.part1
  part2 := intervalDomain_uniformPersistencePart2Raw_of_pointwise h.part2
  part3 := intervalDomain_uniformPersistencePart3Raw_of_pointwise h.part3
  part4 := intervalDomain_uniformPersistencePart4Raw_of_pointwise h.part4

/-! ### A-priori global-existence route into the sectorial core -/

/-- Sectorial mainline facts with the global Cauchy part supplied by the
mass/Lp/heat-smoothing a-priori route, rather than by a raw
`IntervalDomainGlobalSolutionExists` assumption. -/
structure IntervalDomainSectorialMainlineAprioriFacts
    (p : CM2Params) (uBar : ℝ) where
  m_ge_one : 1 ≤ p.m
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingRouteResiduals p
  persistence : IntervalDomainSectorialPointwisePersistenceFacts p uBar

/-- The mass/Lp/smoothing a-priori bound is derived from the wired interval
route, not carried as a headline atom. -/
def IntervalDomainSectorialMainlineAprioriFacts.aprioriBound
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineAprioriFacts p uBar) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.massLpSmoothing.aprioriBound

/-- The a-priori route proves the corrected interval-domain global-solution
package used to supply the two small-data Cauchy fields. -/
def IntervalDomainSectorialMainlineAprioriFacts.to_globalSolutionExists
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineAprioriFacts p uBar) :
    IntervalDomainGlobalSolutionExists p :=
  intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing
    p h.continuation h.aprioriBound

/-- The a-priori route constructs the canonical sectorial core package. -/
def IntervalDomainSectorialMainlineAprioriFacts.to_coreExistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineAprioriFacts p uBar) :
    IntervalDomainSectorialMainlineCoreExistence p uBar where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  smallDataGlobal :=
    intervalDomain_smallDataGlobal_of_globalSolutionExists
      p h.to_globalSolutionExists h.m_ge_one
  massConstrainedSmallDataGlobal :=
    intervalDomain_massConstrainedSmallDataGlobal_of_globalSolutionExists
      p h.to_globalSolutionExists h.m_ge_one
  persistencePart1 := h.persistence.to_persistence.part1
  persistencePart2 := h.persistence.to_persistence.part2
  persistencePart3 := h.persistence.to_persistence.part3
  persistencePart4 := h.persistence.to_persistence.part4

/-- Mainline target from the sectorial facts plus the a-priori global-existence
route. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_aprioriFacts
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfacts : IntervalDomainSectorialMainlineAprioriFacts p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
    p M0 uBar vLower hfacts.to_coreExistence

/-- Reduced analytic facts sufficient for the canonical sectorial core.

Compared with `IntervalDomainSectorialMainlineCoreExistence`, the four
persistence fields are replaced by pointwise lower-barrier facts.  The two
small-data Cauchy fields are kept at their actual Paper3 strength instead of
being routed through the stronger `IntervalDomainGlobalSolutionExists` package,
whose `globalSolutionExists` field is an all-positive-data Cauchy theory. -/
structure IntervalDomainSectorialMainlineReducedAnalyticFacts
    (p : CM2Params) (uBar : ℝ) where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  smallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta
  massConstrainedSmallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta
  persistence : IntervalDomainSectorialPointwisePersistenceFacts p uBar

/-- The reduced analytic facts construct the canonical sectorial core package. -/
def IntervalDomainSectorialMainlineReducedAnalyticFacts.to_coreExistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineReducedAnalyticFacts p uBar) :
    IntervalDomainSectorialMainlineCoreExistence p uBar where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  smallDataGlobal := h.smallDataGlobal
  massConstrainedSmallDataGlobal := h.massConstrainedSmallDataGlobal
  persistencePart1 := h.persistence.to_persistence.part1
  persistencePart2 := h.persistence.to_persistence.part2
  persistencePart3 := h.persistence.to_persistence.part3
  persistencePart4 := h.persistence.to_persistence.part4

/-- Mainline target from the reduced nonlinear analytic facts. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_reducedAnalyticFacts
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfacts : IntervalDomainSectorialMainlineReducedAnalyticFacts p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
    p M0 uBar vLower hfacts.to_coreExistence

end

end ShenWork.Paper3
