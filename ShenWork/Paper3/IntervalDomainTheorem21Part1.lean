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

/-- The concrete unit interval is the disjoint union of its open interior and
its two boundary endpoints, for the purpose of pointwise lower bounds. -/
theorem intervalDomain_pointwise_lower_of_inside_boundary_lower
    {f : ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hinside :
      ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
        x ∈ ShenWork.IntervalDomain.intervalDomain.inside → delta ≤ f x)
    (hboundary :
      ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
        x ∈ ShenWork.IntervalDomain.intervalDomain.boundary → delta ≤ f x) :
    ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ f x := by
  intro x
  by_cases hx0 : x.1 = 0
  · exact hboundary x (by
      change x.1 = 0 ∨ x.1 = 1
      exact Or.inl hx0)
  by_cases hx1 : x.1 = 1
  · exact hboundary x (by
      change x.1 = 0 ∨ x.1 = 1
      exact Or.inr hx1)
  exact hinside x (by
    change x.1 ∈ Set.Ioo (0 : ℝ) 1
    exact
      ⟨lt_of_le_of_ne x.2.1 (Ne.symm hx0),
        lt_of_le_of_ne x.2.2 hx1⟩)

/-- Eventual lower bounds on the open interval and on the two endpoints give
an eventual pointwise lower bound on all concrete interval points. -/
theorem intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hinside :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.inside → delta ≤ u t x)
    (hboundary :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.boundary → delta ≤ u t x) :
    ∀ᶠ t in atTop,
      ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x := by
  filter_upwards [hinside, hboundary] with t ht_inside ht_boundary x
  exact intervalDomain_pointwise_lower_of_inside_boundary_lower
    ht_inside ht_boundary x

/-- Eventual pointwise lower bounds on the concrete interval are equivalent
to eventual lower bounds on the open interior and on the two endpoints. -/
theorem intervalDomain_eventually_pointwise_lower_iff_inside_boundary_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ} :
    (∀ᶠ t in atTop,
      ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x) ↔
      (∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.inside → delta ≤ u t x) ∧
      (∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
            delta ≤ u t x) := by
  constructor
  · intro hpoint
    constructor
    · filter_upwards [hpoint] with t ht x _hx
      exact ht x
    · filter_upwards [hpoint] with t ht x _hx
      exact ht x
  · rintro ⟨hinside, hboundary⟩
    exact intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
      hinside hboundary

/-- Lower bounds on the open interval plus the boundary endpoints imply the
statement-layer lower-envelope bound.  This is only a domain-covering bridge;
the analytic work is still proving the two eventual lower-bound hypotheses. -/
theorem intervalDomain_eventuallyLowerBound_of_inside_boundary_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hinside :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.inside → delta ≤ u t x)
    (hboundary :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.boundary → delta ≤ u t x) :
    EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta :=
  intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower hdelta
    (intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
      hinside hboundary)

/-- Conversely, on intervalDomain the abstract `EventuallyLowerBound` gives a
pointwise eventual lower bound.  No separate `BddBelow` input is needed here:
for real-valued functions, an unbounded-below range has `sInf = 0`, which is
incompatible with the positive lower-envelope bound carried by
`EventuallyLowerBound`. -/
theorem intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hlower :
      EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta) :
    ∀ᶠ t in atTop,
      ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x := by
  filter_upwards [hlower.eventually] with t ht_lower x
  change delta ≤ sInf (Set.range (u t)) at ht_lower
  have ht_bdd : BddBelow (Set.range (u t)) := by
    by_contra hnot
    have hInf : sInf (Set.range (u t)) = 0 :=
      Real.sInf_of_not_bddBelow hnot
    have hdelta_nonpos : delta ≤ 0 := by
      simpa [hInf] using ht_lower
    exact (not_lt_of_ge hdelta_nonpos hlower.delta_pos)
  exact le_trans ht_lower
    (csInf_le ht_bdd ⟨x, rfl⟩)

/-- Equivalence between the statement-layer lower envelope and the pointwise
lower-bound formulation on intervalDomain. -/
theorem intervalDomain_eventuallyLowerBound_iff_eventually_pointwise_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) :
    EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta ↔
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point, delta ≤ u t x := by
  constructor
  · exact intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
  · exact intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower hdelta

/-- Lower-envelope persistence is equivalent to the interior-plus-boundary
formulation. -/
theorem intervalDomain_eventuallyLowerBound_iff_inside_boundary_lower
    {u : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) :
    EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u delta ↔
      (∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.inside → delta ≤ u t x) ∧
      (∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
            delta ≤ u t x) := by
  rw [intervalDomain_eventuallyLowerBound_iff_eventually_pointwise_lower
    hdelta]
  exact intervalDomain_eventually_pointwise_lower_iff_inside_boundary_lower

/-- Lower-envelope bounds are monotone in the lower constant: a stronger
positive lower bound implies any smaller positive lower bound. -/
theorem EventuallyLowerBound_of_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {delta eta : ℝ}
    (hdelta : 0 < delta) (hle : delta ≤ eta)
    (heta : EventuallyLowerBound D u eta) :
    EventuallyLowerBound D u delta := by
  refine ⟨hdelta, ?_⟩
  filter_upwards [heta.eventually] with t ht
  exact le_trans hle ht

/-- The `u` component of a positive global bounded solution on the concrete
interval has lower-bounded time slices eventually.  Interior positivity gives
the lower bound away from the endpoints; the two endpoints are just two real
values.  This discharges the `u` half of the lower-bounded-range regularity
needed to read `sInf` back pointwise. -/
theorem intervalDomain_eventually_bddBelow_u_of_positiveGlobalBoundedSolution
    {p : CM2Params}
    {u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ}
    (hsol :
      PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p
        u v) :
    ∀ᶠ t in atTop, BddBelow (Set.range (u t)) := by
  let x0 : ShenWork.IntervalDomain.intervalDomain.Point :=
    ⟨0, by
      exact ⟨le_rfl, by norm_num⟩⟩
  let x1 : ShenWork.IntervalDomain.intervalDomain.Point :=
    ⟨1, by
      exact ⟨by norm_num, le_rfl⟩⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  refine ⟨min 0 (min (u t x0) (u t x1)), ?_⟩
  intro y hy
  rcases hy with ⟨x, rfl⟩
  by_cases hx0 : x.1 = 0
  · have hx : x = x0 := Subtype.ext hx0
    have hle : min 0 (min (u t x0) (u t x1)) ≤ u t x0 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    simp [hx]
  by_cases hx1 : x.1 = 1
  · have hx : x = x1 := Subtype.ext hx1
    have hle : min 0 (min (u t x0) (u t x1)) ≤ u t x1 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    simp [hx]
  · have hxInside : x ∈ ShenWork.IntervalDomain.intervalDomain.inside := by
      change x.1 ∈ Set.Ioo (0 : ℝ) 1
      exact
        ⟨lt_of_le_of_ne x.2.1 (Ne.symm hx0),
          lt_of_le_of_ne x.2.2 hx1⟩
    exact le_trans (min_le_left _ _)
      (le_of_lt (hsol.pos ht hxInside))

/-- Paper3 Theorem 2.1(1) is vacuous on `intervalDomain` when `p.m < 1`,
because the theorem itself assumes `1 ≤ p.m`. -/
theorem Theorem_2_1_part1_intervalDomain_vacuous_when_m_lt_one
    (p : CM2Params) (hm : p.m < 1) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  intro hm'
  exact absurd hm' (not_le.mpr hm)

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

/-- Statement-layer assembly from pointwise persistence when the analytic
frontier gives a possibly stronger `v` lower bound.  The formal work here is
only to weaken that bound to the paper's required
`ν / μ * deltaU ^ γ` lower envelope. -/
theorem Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds_with_v_margin
    (p : CM2Params)
    (hpointwise :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaV ≤ v t x)) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  intro hm u v hsol
  rcases hpointwise hm u v hsol with
    ⟨deltaU, hdeltaU, deltaV, _hdeltaV, htarget_le, hpointU, hpointV⟩
  have htarget_pos : 0 < p.ν / p.μ * deltaU ^ p.γ := by
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos hdeltaU _)
  have htargetV :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
    filter_upwards [hpointV] with t ht x
    exact le_trans htarget_le (ht x)
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        hdeltaU hpointU,
      intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
        htarget_pos htargetV⟩

/-- Statement-layer assembly from lower-envelope persistence when the `v`
frontier gives a possibly stronger positive lower bound than the theorem's
formula. -/
theorem Theorem_2_1_part1_of_lowerEnvelope_with_v_margin
    {D : BoundedDomainData} (p : CM2Params)
    (hlower :
      1 ≤ p.m →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              EventuallyLowerBound D u deltaU ∧
              EventuallyLowerBound D v deltaV) :
    Theorem_2_1_part1 D p := by
  intro hm u v hsol
  rcases hlower hm u v hsol with
    ⟨deltaU, hdeltaU, deltaV, _hdeltaV, htarget_le, huLower, hvLower⟩
  have htarget_pos : 0 < p.ν / p.μ * deltaU ^ p.γ := by
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos hdeltaU _)
  exact
    ⟨deltaU, hdeltaU, huLower,
      EventuallyLowerBound_of_le htarget_pos htarget_le hvLower⟩

/-- Interval-domain statement-layer assembly from lower-envelope persistence
with a stronger `v` lower-bound margin. -/
theorem Theorem_2_1_part1_intervalDomain_of_lowerEnvelope_with_v_margin
    (p : CM2Params)
    (hlower :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u
                deltaU ∧
              EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain v
                deltaV) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p :=
  Theorem_2_1_part1_of_lowerEnvelope_with_v_margin p hlower

/-- Exact statement-layer equivalence with a stronger `v` lower-envelope
frontier. -/
theorem Theorem_2_1_part1_intervalDomain_iff_lowerEnvelope_with_v_margin
    (p : CM2Params) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p ↔
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain u
                deltaU ∧
              EventuallyLowerBound ShenWork.IntervalDomain.intervalDomain v
                deltaV := by
  constructor
  · intro h21 hm u v hsol
    rcases h21 hm u v hsol with ⟨deltaU, hdeltaU, huLower, hvLower⟩
    have hdeltaV : 0 < p.ν / p.μ * deltaU ^ p.γ := by
      exact mul_pos (div_pos p.hν p.hμ)
        (Real.rpow_pos_of_pos hdeltaU _)
    exact
      ⟨deltaU, hdeltaU, p.ν / p.μ * deltaU ^ p.γ, hdeltaV,
        le_rfl, huLower, hvLower⟩
  · intro hlower
    exact
      Theorem_2_1_part1_intervalDomain_of_lowerEnvelope_with_v_margin
        p hlower

/-- Direct pointwise persistence from a stronger `v` lower-bound frontier. -/
theorem
Theorem_2_1_part1_intervalDomain_pointwise_of_pointwise_lower_bounds_with_v_margin
    (p : CM2Params)
    (hpointwise :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaV ≤ v t x)) :
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
  rcases hpointwise hm u v hsol with
    ⟨deltaU, hdeltaU, deltaV, _hdeltaV, htarget_le, hpointU, hpointV⟩
  have htargetV :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
    filter_upwards [hpointV] with t ht x
    exact le_trans htarget_le (ht x)
  exact ⟨deltaU, hdeltaU, hpointU, htargetV⟩

/-- Statement-layer assembly directly from the Section 4.1 persistence
frontiers when the elliptic comparison gives an independent, possibly
stronger, `v` lower constant. -/
theorem
Theorem_2_1_part1_intervalDomain_of_pointwise_persistence_with_v_margin
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
              ∃ deltaV > 0,
                p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
                ∀ᶠ t in atTop,
                  ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                    deltaV ≤ v t x) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  refine
    Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds_with_v_margin
      p ?_
  intro hm u v hsol
  rcases hStrongMaximumPersistence hm u v hsol with
    ⟨deltaU, hdeltaU, hpointU⟩
  rcases hEllipticLowerComparison hsol hdeltaU hpointU with
    ⟨deltaV, hdeltaV, htarget_le, hpointV⟩
  exact
    ⟨deltaU, hdeltaU, deltaV, hdeltaV, htarget_le, hpointU,
      hpointV⟩

/-- Direct pointwise persistence from the Section 4.1 persistence frontiers
when the elliptic comparison returns a stronger `v` lower constant. -/
theorem
Theorem_2_1_part1_intervalDomain_pointwise_of_pointwise_persistence_with_v_margin
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
              ∃ deltaV > 0,
                p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
                ∀ᶠ t in atTop,
                  ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                    deltaV ≤ v t x) :
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
  refine
    Theorem_2_1_part1_intervalDomain_pointwise_of_pointwise_lower_bounds_with_v_margin
      p ?_
  intro hm u v hsol
  rcases hStrongMaximumPersistence hm u v hsol with
    ⟨deltaU, hdeltaU, hpointU⟩
  rcases hEllipticLowerComparison hsol hdeltaU hpointU with
    ⟨deltaV, hdeltaV, htarget_le, hpointV⟩
  exact
    ⟨deltaU, hdeltaU, deltaV, hdeltaV, htarget_le, hpointU,
      hpointV⟩

/-- Statement-layer assembly when the analytic persistence frontiers are
available separately on the open interval and on the two Neumann endpoints.
This discharges only the concrete interval-domain covering step. -/
theorem Theorem_2_1_part1_intervalDomain_of_inside_boundary_lower_bounds
    (p : CM2Params)
    (hbounds :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0,
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    p.ν / p.μ * deltaU ^ p.γ ≤ v t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    p.ν / p.μ * deltaU ^ p.γ ≤ v t x)) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  intro hm u v hsol
  rcases hbounds hm u v hsol with
    ⟨deltaU, hdeltaU, huInside, huBoundary, hvInside, hvBoundary⟩
  have hdeltaV : 0 < p.ν / p.μ * deltaU ^ p.γ := by
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos hdeltaU _)
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventuallyLowerBound_of_inside_boundary_lower
        hdeltaU huInside huBoundary,
      intervalDomain_eventuallyLowerBound_of_inside_boundary_lower
        hdeltaV hvInside hvBoundary⟩

/-- Direct intended pointwise persistence when the analytic frontiers are
available separately on the open interval and on the two Neumann endpoints. -/
theorem Theorem_2_1_part1_intervalDomain_pointwise_of_inside_boundary_lower_bounds
    (p : CM2Params)
    (hbounds :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0,
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    p.ν / p.μ * deltaU ^ p.γ ≤ v t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    p.ν / p.μ * deltaU ^ p.γ ≤ v t x)) :
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
  rcases hbounds hm u v hsol with
    ⟨deltaU, hdeltaU, huInside, huBoundary, hvInside, hvBoundary⟩
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
        huInside huBoundary,
      intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
        hvInside hvBoundary⟩

/-- Semantic read-back of `Theorem_2_1_part1 intervalDomain p`: the
statement-layer lower-envelope formulation is exactly the expected pointwise
eventual persistence statement for both `u` and `v`. -/
theorem Theorem_2_1_part1_intervalDomain_pointwise_of_lowerEnvelope
    {p : CM2Params}
    (h21 : Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p) :
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
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
        huLower,
      intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
        hvLower⟩

/-- Exact semantic equivalence between the intervalDomain statement-layer
Theorem 2.1(1) and its intended pointwise eventual-persistence formulation.
For the concrete interval domain, the positivity of the lower-envelope
constant rules out the unbounded-below `sInf` fallback, so no extra `BddBelow`
input is needed. -/
theorem Theorem_2_1_part1_intervalDomain_iff_pointwise_lower_bounds
    (p : CM2Params) :
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
    exact Theorem_2_1_part1_intervalDomain_pointwise_of_lowerEnvelope h21
  · intro hpointwise
    exact Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds p hpointwise

/-- Exact semantic equivalence between the intervalDomain statement-layer
Theorem 2.1(1) and the formulation with separate open-interior and boundary
eventual lower bounds. -/
theorem Theorem_2_1_part1_intervalDomain_iff_inside_boundary_lower_bounds
    (p : CM2Params) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p ↔
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0,
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    p.ν / p.μ * deltaU ^ p.γ ≤ v t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    p.ν / p.μ * deltaU ^ p.γ ≤ v t x) := by
  constructor
  · intro h21 hm u v hsol
    rcases h21 hm u v hsol with ⟨deltaU, hdeltaU, huLower, hvLower⟩
    have huPoint :
        ∀ᶠ t in atTop,
          ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
            deltaU ≤ u t x :=
      intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
        huLower
    have hvPoint :
        ∀ᶠ t in atTop,
          ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
            p.ν / p.μ * deltaU ^ p.γ ≤ v t x :=
      intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
        hvLower
    rcases
        (intervalDomain_eventually_pointwise_lower_iff_inside_boundary_lower.mp
          huPoint) with
      ⟨huInside, huBoundary⟩
    rcases
        (intervalDomain_eventually_pointwise_lower_iff_inside_boundary_lower.mp
          hvPoint) with
      ⟨hvInside, hvBoundary⟩
    exact
      ⟨deltaU, hdeltaU, huInside, huBoundary, hvInside, hvBoundary⟩
  · intro hbounds
    exact
      Theorem_2_1_part1_intervalDomain_of_inside_boundary_lower_bounds
        p hbounds

/-- Exact semantic equivalence with the pointwise formulation where the
analytic `v` frontier may provide any stronger positive lower bound `deltaV`.
The Lean side only needs the comparison
`ν / μ * deltaU ^ γ ≤ deltaV` to recover the paper's lower envelope. -/
theorem Theorem_2_1_part1_intervalDomain_iff_pointwise_lower_bounds_with_v_margin
    (p : CM2Params) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p ↔
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  deltaV ≤ v t x) := by
  constructor
  · intro h21 hm u v hsol
    rcases
        Theorem_2_1_part1_intervalDomain_pointwise_of_lowerEnvelope
          h21 hm u v hsol with
      ⟨deltaU, hdeltaU, hpointU, hpointV⟩
    have hdeltaV : 0 < p.ν / p.μ * deltaU ^ p.γ := by
      exact mul_pos (div_pos p.hν p.hμ)
        (Real.rpow_pos_of_pos hdeltaU _)
    exact
      ⟨deltaU, hdeltaU, p.ν / p.μ * deltaU ^ p.γ, hdeltaV,
        le_rfl, hpointU, hpointV⟩
  · intro hpointwise
    exact
      Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds_with_v_margin
        p hpointwise

/-- Statement-layer assembly from interior/boundary lower bounds when the
analytic `v` frontier gives a stronger lower constant. -/
theorem
Theorem_2_1_part1_intervalDomain_of_inside_boundary_lower_bounds_with_v_margin
    (p : CM2Params)
    (hbounds :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaV ≤ v t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaV ≤ v t x)) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p := by
  refine
    Theorem_2_1_part1_intervalDomain_of_inside_boundary_lower_bounds
      p ?_
  intro hm u v hsol
  rcases hbounds hm u v hsol with
    ⟨deltaU, hdeltaU, deltaV, _hdeltaV, htarget_le,
      huInside, huBoundary, hvInside, hvBoundary⟩
  have hvInsideTarget :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
            p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
    filter_upwards [hvInside] with t ht x hx
    exact le_trans htarget_le (ht x hx)
  have hvBoundaryTarget :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
            p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
    filter_upwards [hvBoundary] with t ht x hx
    exact le_trans htarget_le (ht x hx)
  exact
    ⟨deltaU, hdeltaU, huInside, huBoundary, hvInsideTarget,
      hvBoundaryTarget⟩

/-- Direct pointwise persistence from interior/boundary lower bounds with a
stronger `v` lower constant. -/
theorem
Theorem_2_1_part1_intervalDomain_pointwise_of_inside_boundary_lower_bounds_with_v_margin
    (p : CM2Params)
    (hbounds :
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaV ≤ v t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaV ≤ v t x)) :
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
  rcases hbounds hm u v hsol with
    ⟨deltaU, hdeltaU, deltaV, _hdeltaV, htarget_le,
      huInside, huBoundary, hvInside, hvBoundary⟩
  have hvInsideTarget :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
            p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
    filter_upwards [hvInside] with t ht x hx
    exact le_trans htarget_le (ht x hx)
  have hvBoundaryTarget :
      ∀ᶠ t in atTop,
        ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
          x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
            p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
    filter_upwards [hvBoundary] with t ht x hx
    exact le_trans htarget_le (ht x hx)
  exact
    ⟨deltaU, hdeltaU,
      intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
        huInside huBoundary,
      intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower
        hvInsideTarget hvBoundaryTarget⟩

/-- Exact semantic equivalence with the interior/boundary formulation where
the `v` frontier may be stronger than the theorem's required constant. -/
theorem
Theorem_2_1_part1_intervalDomain_iff_inside_boundary_lower_bounds_with_v_margin
    (p : CM2Params) :
    Theorem_2_1_part1 ShenWork.IntervalDomain.intervalDomain p ↔
      1 ≤ p.m →
        ∀ u v : ℝ → ShenWork.IntervalDomain.intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution ShenWork.IntervalDomain.intervalDomain p u v →
            ∃ deltaU > 0, ∃ deltaV > 0,
              p.ν / p.μ * deltaU ^ p.γ ≤ deltaV ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaU ≤ u t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
                    deltaV ≤ v t x) ∧
              (∀ᶠ t in atTop,
                ∀ x : ShenWork.IntervalDomain.intervalDomain.Point,
                  x ∈ ShenWork.IntervalDomain.intervalDomain.boundary →
                    deltaV ≤ v t x) := by
  constructor
  · intro h21 hm u v hsol
    rcases
        (Theorem_2_1_part1_intervalDomain_iff_inside_boundary_lower_bounds
          p).mp h21 hm u v hsol with
      ⟨deltaU, hdeltaU, huInside, huBoundary, hvInside, hvBoundary⟩
    have hdeltaV : 0 < p.ν / p.μ * deltaU ^ p.γ := by
      exact mul_pos (div_pos p.hν p.hμ)
        (Real.rpow_pos_of_pos hdeltaU _)
    exact
      ⟨deltaU, hdeltaU, p.ν / p.μ * deltaU ^ p.γ, hdeltaV,
        le_rfl, huInside, huBoundary, hvInside, hvBoundary⟩
  · intro hbounds
    exact
      Theorem_2_1_part1_intervalDomain_of_inside_boundary_lower_bounds_with_v_margin
        p hbounds

end

end ShenWork.Paper3
