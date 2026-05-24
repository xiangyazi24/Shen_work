/-
  Paper3 Theorem 2.1(1) on the concrete intervalDomain.

  This file assembles the formal theorem from two explicit analytic frontiers
  matching Section 4.1 of the paper:

  * the time-translate compactness/strong-maximum-principle/ODE-subsolution
    argument that gives a pointwise eventual lower bound for u;
  * the elliptic Neumann comparison step that transfers that lower bound to v.

  Status: conditional on those named hypotheses.  No sectorial semigroup input
  is used by Theorem 2.1(1); the H3.1 sectorial framework remains the existing
  explicit `SectorialLocalExponentialRaw` hypothesis for the later stability
  theorems.
-/
import ShenWork.Paper3.Statements

open Filter Topology

namespace ShenWork.Paper3

noncomputable section

/-- On the concrete unit interval, an eventual pointwise lower bound implies
the abstract `EventuallyLowerBound` statement because `infValue` is the
greatest lower bound of the range. -/
theorem intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hpoint :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x) :
    EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta := by
  refine ⟨hdelta, ?_⟩
  filter_upwards [hpoint] with t ht
  change delta ≤ sInf (Set.range (u t))
  refine le_csInf ?_ ?_
  · let x0 : ShenWork.IntervalDomain.intervalDomain.Point :=
      ⟨0, by
        exact ⟨le_rfl, by norm_num⟩⟩
    exact ⟨u t x0, ⟨x0, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ht x

/-- Conditional intervalDomain version of Paper3 Theorem 2.1(1).

The two assumptions are intentionally not hidden inside a constants package:
`hStrongMaximumPersistence` is exactly the missing Section 4.1 compactness plus
strong-maximum-principle argument for the u-equation, while
`hEllipticLowerComparison` is the missing elliptic Neumann comparison argument
for the v-equation.  Given those pointwise analytic inputs, the repository's
existing `Theorem_2_1_part1` statement follows for `intervalDomain`. -/
theorem Theorem_2_1_part1_intervalDomain_of_pointwise_persistence
    (p : CM2Params)
    (hStrongMaximumPersistence :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0,
              ∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaU ≤ u t x)
    (hEllipticLowerComparison :
      ∀ {u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ}
          {deltaU : ℝ},
        PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
          0 < deltaU →
            (∀ᶠ t in atTop,
              ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                deltaU ≤ u t x) →
              ∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  p.ν / p.μ * deltaU ^ p.γ ≤ v t x) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  intro hm u v hsol
  rcases hStrongMaximumPersistence hm u v hsol with
    ⟨deltaU, hdeltaU, hpointU⟩
  have huLower :
      EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u deltaU :=
    intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hdeltaU hpointU
  have hpointV :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          p.ν / p.μ * deltaU ^ p.γ ≤ v t x :=
    hEllipticLowerComparison hsol hdeltaU hpointU
  have hdeltaV : 0 < p.ν / p.μ * deltaU ^ p.γ := by
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos hdeltaU _)
  have hvLower :
      EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain v
        (p.ν / p.μ * deltaU ^ p.γ) :=
    intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hdeltaV hpointV
  exact ⟨deltaU, hdeltaU, huLower, hvLower⟩

end

end ShenWork.Paper3
