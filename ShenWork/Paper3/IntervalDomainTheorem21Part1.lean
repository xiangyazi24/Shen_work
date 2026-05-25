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

/-- Conversely, on intervalDomain the abstract `EventuallyLowerBound` gives a
pointwise eventual lower bound once the time slices have genuine lower-bounded
ranges.  The `BddBelow` assumption is necessary for using `sInf` in a
conditionally complete order; it is a semantic domain regularity input, not a
persistence conclusion. -/
theorem intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hbdd :
      ∀ᶠ t in atTop,
        BddBelow (Set.range (u t)))
    (hlower :
      EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta) :
    ∀ᶠ t in atTop,
      ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x := by
  filter_upwards [hbdd, hlower.eventually] with t ht_bdd ht_lower x
  exact le_trans ht_lower
    (csInf_le ht_bdd ⟨x, rfl⟩)

/-- Equivalence between the statement-layer lower envelope and the pointwise
lower-bound formulation on intervalDomain, under the explicit lower-bounded
range condition needed for the reverse implication. -/
theorem intervalDomain_eventuallyLowerBound_iff_eventually_pointwise_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hbdd :
      ∀ᶠ t in atTop,
        BddBelow (Set.range (u t))) :
    EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta ↔
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x := by
  constructor
  · exact intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound hbdd
  · exact intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower hdelta

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

/-- Direct pointwise intervalDomain persistence theorem from the two Section
4.1 analytic frontiers.  This records the intended pointwise meaning without
going through the statement-layer lower envelope. -/
theorem Theorem_2_1_part1_intervalDomain_pointwise_of_pointwise_persistence
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
    1 ≤ p.m →
      ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
          ∃ deltaU > 0,
            (∀ᶠ t in atTop,
              ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                deltaU ≤ u t x) ∧
            (∀ᶠ t in atTop,
              ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                p.ν / p.μ * deltaU ^ p.γ ≤ v t x) := by
  intro hm u v hsol
  rcases hStrongMaximumPersistence hm u v hsol with
    ⟨deltaU, hdeltaU, hpointU⟩
  exact
    ⟨deltaU, hdeltaU, hpointU,
      hEllipticLowerComparison hsol hdeltaU hpointU⟩

/-- Statement-layer assembly from the exact intended pointwise persistence
formulation.  This isolates the purely formal lower-envelope conversion from
the analytic Section 4.1 frontiers. -/
theorem Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds
    (p : CM2Params)
    (hpointwise :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0,
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  p.ν / p.μ * deltaU ^ p.γ ≤ v t x)) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  intro hm u v hsol
  rcases hpointwise hm u v hsol with
    ⟨deltaU, hdeltaU, hpointU, hpointV⟩
  have hdeltaV : 0 < p.ν / p.μ * deltaU ^ p.γ := by
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos hdeltaU _)
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        hdeltaU hpointU,
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        hdeltaV hpointV⟩

/-- Semantic read-back of `Theorem_2_1_part1 intervalDomain p`: under the
explicit lower-bounded-range regularity of the interval time slices, the
statement-layer formulation is exactly the expected pointwise eventual
persistence statement for both `u` and `v`. -/
theorem Theorem_2_1_part1_intervalDomain_pointwise_of_lowerEnvelope
    {p : CM2Params}
    (h21 : Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p)
    (hbdd :
      ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
          (∀ᶠ t in atTop, BddBelow (Set.range (u t))) ∧
          (∀ᶠ t in atTop, BddBelow (Set.range (v t)))) :
    1 ≤ p.m →
      ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
          ∃ deltaU > 0,
            (∀ᶠ t in atTop,
              ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                deltaU ≤ u t x) ∧
            (∀ᶠ t in atTop,
              ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                p.ν / p.μ * deltaU ^ p.γ ≤ v t x) := by
  intro hm u v hsol
  rcases h21 hm u v hsol with ⟨deltaU, hdeltaU, huLower, hvLower⟩
  rcases hbdd u v hsol with ⟨hbddU, hbddV⟩
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
        hbddU huLower,
      intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
        hbddV hvLower⟩

/-- Exact semantic equivalence between the intervalDomain statement-layer
Theorem 2.1(1) and its intended pointwise eventual-persistence formulation.

The reverse direction needs the explicit `BddBelow` regularity input because
`BoundedDomainData.infValue` is only an abstract lower-envelope field. -/
theorem Theorem_2_1_part1_intervalDomain_iff_pointwise_lower_bounds
    (p : CM2Params)
    (hbdd :
      ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
          (∀ᶠ t in atTop, BddBelow (Set.range (u t))) ∧
          (∀ᶠ t in atTop, BddBelow (Set.range (v t)))) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p ↔
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0,
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  p.ν / p.μ * deltaU ^ p.γ ≤ v t x) := by
  constructor
  · intro h21
    exact Theorem_2_1_part1_intervalDomain_pointwise_of_lowerEnvelope h21 hbdd
  · intro hpointwise
    exact Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds p hpointwise

end

end ShenWork.Paper3
