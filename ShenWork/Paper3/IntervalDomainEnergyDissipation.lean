/-
  ShenWork/Paper3/IntervalDomainEnergyDissipation.lean

  Energy/dissipation interfaces for Paper 3 interval-domain stability.

  Point 17 status: mixed.  The constant-reference-profile theta dissipation
  data below is fully proved (state ①).  For arbitrary positive global
  solutions, this file still does not prove the PDE derivative identity for
  the theta dissipation functional, nor the integrated dissipation
  inequality.  Those remain honest analytic frontiers: they require
  differentiating the interval integral in time, integrating by parts, and
  using the PDE structure.  The branch-level structures keep that frontier
  explicit; once supplied, the existing `IntervalDomainStabilityChain`
  theorems consume it without additional ad hoc hypotheses.
-/
import ShenWork.Paper3.IntervalDomainStabilityChain

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Fixed-solution theta-dissipation derivative/decay data.

The fields are the analytic energy side of the Paper 3 Lyapunov argument:
`HasDerivAt` for the theta dissipation and the differential inequality
`D'(t) <= -rate * D(t)`.  Positivity of slices is intentionally not a field:
the interval stability chain discharges it from
`PositiveGlobalBoundedSolution`. -/
structure IntervalDomainThetaDissipationDerivativeDecayData
    (u : ℝ → intervalDomain.Point → ℝ) (uStar theta : ℝ) where
  rate : ℝ
  rate_pos : 0 < rate
  start : ℝ
  start_pos : 0 < start
  slope : ℝ → ℝ
  deriv :
    ∀ t, 0 < t →
      HasDerivAt
        (fun tau =>
          chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
        (slope t) t
  dissipative :
    ∀ t, 0 < t →
      slope t ≤
        -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)

/-- The fixed-solution energy/dissipation data gives theta-dissipation
convergence to zero once the solution package supplies positivity. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.tendsto_zero
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    Tendsto
      (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      atTop (𝓝 0) :=
  intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul_of_solution
    (p := p) (u := u) (v := v)
    (uStar := uStar) (theta := theta) (rate := h.rate)
    (s := h.start) (momentSlope := h.slope)
    huv h.rate_pos h.start_pos huStar htheta h.deriv h.dissipative

/-- The same data in the `ThetaMomentConvergesToZero` form used by
moment-to-uniform frontiers. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.thetaMoment
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  intervalDomain_thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
    (h.tendsto_zero huv huStar htheta)

/-- Expose fixed-solution theta-dissipation data in the raw frontier shape
expected by the interval-domain stability chain. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.raw_frontier
    {u : ℝ → intervalDomain.Point → ℝ} {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta) :
    ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
      (∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t) ∧
      (∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta
            (u t)) :=
  ⟨h.rate, h.rate_pos, h.start, h.start_pos,
    h.slope, h.deriv, h.dissipative⟩

/-- Fixed-solution theta-dissipation data gives the full Lyapunov package:
slope nonpositivity, nonnegativity, unweighted and weighted monotonicity,
two-time exponential decay, and theta-moment convergence.

Point 17 status: complete theorem relative to the explicit derivative/decay
data, state ① for this interface layer.  No PDE identity is invented here; the
only analytic input is exactly the data stored in
`IntervalDomainThetaDissipationDerivativeDecayData`. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.completeLyapunovPackage
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    (∀ t, 0 < t → h.slope t ≤ 0) ∧
      (∀ t, 0 < t →
        0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t)) ∧
      AntitoneOn
        (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
        (Ioi (0 : ℝ)) ∧
      AntitoneOn
        (fun t =>
          Real.exp (h.rate * t) *
            chemotaxisThetaDissipation intervalDomain uStar theta (u t))
        (Ioi (0 : ℝ)) ∧
      (∀ a b, 0 < a → a ≤ b →
        0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u b) ∧
          chemotaxisThetaDissipation intervalDomain uStar theta (u b) ≤
            chemotaxisThetaDissipation intervalDomain uStar theta (u a) *
              Real.exp (-h.rate * (b - a))) ∧
      ThetaMomentConvergesToZero intervalDomain u uStar theta :=
  intervalDomain_thetaDissipation_completeLyapunovPackage_of_positiveGlobalBoundedSolution
    (p := p) (u := u) (v := v)
    (uStar := uStar) (theta := theta) (rate := h.rate)
    (s := h.start) (momentSlope := h.slope)
    h.rate_pos h.start_pos huStar htheta huv h.deriv h.dissipative

/-- Fixed-solution theta-dissipation data gives pointwise nonnegativity of the
theta dissipation along a positive global bounded solution. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.thetaDissipation_nonneg
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    ∀ t, 0 < t →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) :=
  (h.completeLyapunovPackage huv huStar htheta).2.1

/-- Fixed-solution theta-dissipation data gives unweighted monotonicity of the
theta dissipation. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.antitoneOn
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    AntitoneOn
      (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      (Ioi (0 : ℝ)) :=
  (h.completeLyapunovPackage huv huStar htheta).2.2.1

/-- Fixed-solution theta-dissipation data gives the weighted monotonicity form
used in exponential decay arguments. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.weightedAntitoneOn
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    AntitoneOn
      (fun t =>
        Real.exp (h.rate * t) *
          chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      (Ioi (0 : ℝ)) :=
  (h.completeLyapunovPackage huv huStar htheta).2.2.2.1

/-- Fixed-solution theta-dissipation data gives the two-time exponential decay
estimate for the theta dissipation. -/
theorem IntervalDomainThetaDissipationDerivativeDecayData.two_time_bound
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    ∀ a b, 0 < a → a ≤ b →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u b) ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u b) ≤
          chemotaxisThetaDissipation intervalDomain uStar theta (u a) *
            Real.exp (-h.rate * (b - a)) :=
  (h.completeLyapunovPackage huv huStar htheta).2.2.2.2.1

/-- Complete fixed-solution theta-dissipation Lyapunov data.

This is the post-energy interface consumed most directly by global-stability
arguments: it records all monotonicity and convergence consequences rather
than the derivative identity from which they may have been proved. -/
structure IntervalDomainThetaDissipationCompleteLyapunovData
    (u : ℝ → intervalDomain.Point → ℝ) (uStar theta : ℝ) where
  rate : ℝ
  rate_pos : 0 < rate
  start : ℝ
  start_pos : 0 < start
  slope : ℝ → ℝ
  slope_nonpos : ∀ t, 0 < t → slope t ≤ 0
  nonneg :
    ∀ t, 0 < t →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t)
  antitone :
    AntitoneOn
      (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      (Ioi (0 : ℝ))
  weighted_antitone :
    AntitoneOn
      (fun t =>
        Real.exp (rate * t) *
          chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      (Ioi (0 : ℝ))
  two_time_bound :
    ∀ a b, 0 < a → a ≤ b →
      0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u b) ∧
        chemotaxisThetaDissipation intervalDomain uStar theta (u b) ≤
          chemotaxisThetaDissipation intervalDomain uStar theta (u a) *
            Real.exp (-rate * (b - a))
  thetaMoment : ThetaMomentConvergesToZero intervalDomain u uStar theta

/-- Complete Lyapunov data gives the theta-dissipation `Tendsto` frontier
expected by the stability chain. -/
theorem IntervalDomainThetaDissipationCompleteLyapunovData.tendsto_zero
    {u : ℝ → intervalDomain.Point → ℝ} {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationCompleteLyapunovData u uStar theta) :
    Tendsto
      (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      atTop (𝓝 0) := by
  simpa [ThetaMomentConvergesToZero, chemotaxisThetaDissipation] using
    h.thetaMoment

/-- The derivative/decay interface proves the complete Lyapunov-data
interface for positive global bounded solutions.

Point 17 status: complete theorem, state ① for this interface conversion.  The
PDE derivative identity is still exactly the named input contained in
`h.deriv`; no additional analytic fact is assumed silently. -/
def IntervalDomainThetaDissipationDerivativeDecayData.toCompleteLyapunovData
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta : ℝ}
    (h : IntervalDomainThetaDissipationDerivativeDecayData u uStar theta)
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    IntervalDomainThetaDissipationCompleteLyapunovData u uStar theta := by
  have hpack := h.completeLyapunovPackage huv huStar htheta
  exact
    { rate := h.rate
      rate_pos := h.rate_pos
      start := h.start
      start_pos := h.start_pos
      slope := h.slope
      slope_nonpos := hpack.1
      nonneg := hpack.2.1
      antitone := hpack.2.2.1
      weighted_antitone := hpack.2.2.2.1
      two_time_bound := hpack.2.2.2.2.1
      thetaMoment := hpack.2.2.2.2.2 }

/-- Complete fixed-solution theta-dissipation derivative/decay data for the
constant reference profile `u(t,x) ≡ u*`.

Point 17 status: complete theorem, state ①.  This does not use the PDE; the
theta dissipation is identically zero, so the derivative and decay inequality
are both discharged by the already-proved interval-domain constant-profile
frontier. -/
def intervalDomainThetaDissipationDerivativeDecayData_const
    (uStar theta : ℝ) {rate start : ℝ}
    (hrate : 0 < rate) (hstart : 0 < start) :
    IntervalDomainThetaDissipationDerivativeDecayData
      (fun _ : ℝ => fun _ : intervalDomain.Point => uStar) uStar theta := by
  have hfrontiers :=
    intervalDomain_thetaDissipation_const_frontiers uStar theta rate
  exact
    { rate := rate
      rate_pos := hrate
      start := start
      start_pos := hstart
      slope := fun _ => 0
      deriv := by
        intro t ht
        exact hfrontiers.1 t ht
      dissipative := by
        intro t ht
        simpa using hfrontiers.2 t ht }

/-- The constant reference profile has theta dissipation converging to zero.

This is the direct, solution-free form of the constant-profile result. -/
theorem intervalDomain_thetaDissipation_const_tendsto_zero
    (uStar theta : ℝ) :
    Tendsto
      (fun t =>
        chemotaxisThetaDissipation intervalDomain uStar theta
          ((fun _ : ℝ => fun _ : intervalDomain.Point => uStar) t))
      atTop (𝓝 0) := by
  simp [intervalDomain_chemotaxisThetaDissipation_const_eq_zero]

/-- The constant reference profile satisfies the theta-moment convergence
statement consumed by the Paper 3 moment-to-uniform interfaces. -/
theorem intervalDomain_thetaMoment_const
    (uStar theta : ℝ) :
    ThetaMomentConvergesToZero intervalDomain
      (fun _ : ℝ => fun _ : intervalDomain.Point => uStar) uStar theta :=
  intervalDomain_thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
    (intervalDomain_thetaDissipation_const_tendsto_zero uStar theta)

/-- Complete Lyapunov data for the constant reference profile. -/
def intervalDomainThetaDissipationCompleteLyapunovData_const
    {uStar theta rate start : ℝ}
    (hrate : 0 < rate) (hstart : 0 < start)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    IntervalDomainThetaDissipationCompleteLyapunovData
      (fun _ : ℝ => fun _ : intervalDomain.Point => uStar) uStar theta := by
  have hpack :=
    intervalDomain_thetaDissipation_const_completeLyapunovPackage
      (uStar := uStar) (theta := theta) (rate := rate) (s := start)
      hrate hstart huStar htheta
  exact
    { rate := rate
      rate_pos := hrate
      start := start
      start_pos := hstart
      slope := fun _ => 0
      slope_nonpos := hpack.1
      nonneg := hpack.2.1
      antitone := hpack.2.2.1
      weighted_antitone := hpack.2.2.2.1
      two_time_bound := hpack.2.2.2.2.1
      thetaMoment := hpack.2.2.2.2.2 }

/-- Constant-profile theta-dissipation data specialized to the nonminimal
positive equilibrium. -/
def intervalDomain_positiveEquilibriumThetaDissipationDerivativeDecayData_const
    (p : CM2Params) {ha : 0 < p.a} {hb : 0 < p.b}
    {rate start : ℝ} (hrate : 0 < rate) (hstart : 0 < start) :
    IntervalDomainThetaDissipationDerivativeDecayData
      (fun _ : ℝ =>
        fun _ : intervalDomain.Point => (positiveEquilibrium p ⟨ha, hb⟩).1)
      (positiveEquilibrium p ⟨ha, hb⟩).1 p.α :=
  intervalDomainThetaDissipationDerivativeDecayData_const
    (positiveEquilibrium p ⟨ha, hb⟩).1 p.α hrate hstart

/-- Constant-profile theta-dissipation data specialized to the minimal
mass-parameter equilibrium. -/
def intervalDomain_minimalEquilibriumThetaDissipationDerivativeDecayData_const
    (p : CM2Params) (uStar : ℝ)
    {rate start : ℝ} (hrate : 0 < rate) (hstart : 0 < start) :
    IntervalDomainThetaDissipationDerivativeDecayData
      (fun _ : ℝ =>
        fun _ : intervalDomain.Point => (minimalEquilibrium p uStar).1)
      (minimalEquilibrium p uStar).1 p.α :=
  intervalDomainThetaDissipationDerivativeDecayData_const
    (minimalEquilibrium p uStar).1 p.α hrate hstart

/-- Branch-level theta-dissipation interfaces needed by Paper 3 Theorem 2.3.

This separates the energy side from the already-existing moment-to-uniform and
uniform exponential-upgrade frontiers. -/
structure IntervalDomainTheorem23ThetaDerivativeInterfaces
    (p : CM2Params) where
  nonminimal :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            IntervalDomainThetaDissipationDerivativeDecayData u eq.1 p.α
  minimal :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            HasInitialMass intervalDomain u uStar →
              IntervalDomainThetaDissipationDerivativeDecayData u eq.1 p.α

/-- Extract the nonminimal raw derivative frontier expected by
`IntervalDomainStabilityChain`. -/
theorem IntervalDomainTheorem23ThetaDerivativeInterfaces.nonminimal_frontier
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaDerivativeInterfaces p) :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
              (∀ t, 0 < t →
                HasDerivAt
                  (fun tau =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u tau))
                  (momentSlope t) t) ∧
              (∀ t, 0 < t →
                momentSlope t ≤
                  -rate *
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u t)) := by
  intro hχ hm ha hb
  dsimp
  intro u v huv
  let data := h.nonminimal hχ hm ha hb u v huv
  exact
    ⟨data.rate, data.rate_pos, data.start, data.start_pos,
      data.slope, data.deriv, data.dissipative⟩

/-- Extract the minimal raw derivative frontier expected by
`IntervalDomainStabilityChain`. -/
theorem IntervalDomainTheorem23ThetaDerivativeInterfaces.minimal_frontier
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaDerivativeInterfaces p) :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            HasInitialMass intervalDomain u uStar →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, 0 < t →
                  HasDerivAt
                    (fun tau =>
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u tau))
                    (momentSlope t) t) ∧
                (∀ t, 0 < t →
                  momentSlope t ≤
                    -rate *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t)) := by
  intro hχ hm ha hb uStar huStar
  dsimp
  intro u v huv hmass
  let data := h.minimal hχ hm ha hb uStar huStar u v huv hmass
  exact
    ⟨data.rate, data.rate_pos, data.start, data.start_pos,
      data.slope, data.deriv, data.dissipative⟩

/-- Extract the full nonminimal theta-dissipation Lyapunov package supplied by
the structured branch interface. -/
theorem
    IntervalDomainTheorem23ThetaDerivativeInterfaces.nonminimal_completeLyapunov_frontier
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaDerivativeInterfaces p) :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
              (∀ t, 0 < t → momentSlope t ≤ 0) ∧
              (∀ t, 0 < t →
                0 ≤ chemotaxisThetaDissipation intervalDomain eq.1 p.α
                  (u t)) ∧
              AntitoneOn
                (fun t =>
                  chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                (Ioi (0 : ℝ)) ∧
              AntitoneOn
                (fun t =>
                  Real.exp (rate * t) *
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u t))
                (Ioi (0 : ℝ)) ∧
              (∀ a b, 0 < a → a ≤ b →
                0 ≤ chemotaxisThetaDissipation intervalDomain eq.1 p.α
                  (u b) ∧
                  chemotaxisThetaDissipation intervalDomain eq.1 p.α
                    (u b) ≤
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u a) * Real.exp (-rate * (b - a))) ∧
              ThetaMomentConvergesToZero intervalDomain u eq.1 p.α := by
  intro hχ hm ha hb
  dsimp
  intro u v huv
  let data := h.nonminimal hχ hm ha hb u v huv
  refine
    ⟨data.rate, data.rate_pos, data.start, data.start_pos,
      data.slope, ?_⟩
  exact
    data.completeLyapunovPackage huv
      (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le p.hα.le

/-- Extract the full minimal theta-dissipation Lyapunov package supplied by
the structured branch interface. -/
theorem
    IntervalDomainTheorem23ThetaDerivativeInterfaces.minimal_completeLyapunov_frontier
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaDerivativeInterfaces p) :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            HasInitialMass intervalDomain u uStar →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, 0 < t → momentSlope t ≤ 0) ∧
                (∀ t, 0 < t →
                  0 ≤ chemotaxisThetaDissipation intervalDomain eq.1 p.α
                    (u t)) ∧
                AntitoneOn
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u t))
                  (Ioi (0 : ℝ)) ∧
                AntitoneOn
                  (fun t =>
                    Real.exp (rate * t) *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t))
                  (Ioi (0 : ℝ)) ∧
                (∀ a b, 0 < a → a ≤ b →
                  0 ≤ chemotaxisThetaDissipation intervalDomain eq.1 p.α
                    (u b) ∧
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u b) ≤
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u a) * Real.exp (-rate * (b - a))) ∧
                ThetaMomentConvergesToZero intervalDomain u eq.1 p.α := by
  intro hχ hm ha hb uStar huStar
  dsimp
  intro u v huv hmass
  let data := h.minimal hχ hm ha hb uStar huStar u v huv hmass
  refine
    ⟨data.rate, data.rate_pos, data.start, data.start_pos,
      data.slope, ?_⟩
  exact
    data.completeLyapunovPackage huv
      (by simpa [minimalEquilibrium] using huStar.le) p.hα.le

/-- Branch-level complete theta-dissipation Lyapunov interfaces needed by
Paper 3 Theorem 2.3 once the PDE energy step has already been post-processed
to monotonicity and theta-moment convergence. -/
structure IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces
    (p : CM2Params) where
  nonminimal :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            IntervalDomainThetaDissipationCompleteLyapunovData u eq.1 p.α
  minimal :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            HasInitialMass intervalDomain u uStar →
              IntervalDomainThetaDissipationCompleteLyapunovData u eq.1 p.α

/-- The derivative branch interface proves the complete Lyapunov branch
interface. -/
def IntervalDomainTheorem23ThetaDerivativeInterfaces.toCompleteLyapunovInterfaces
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaDerivativeInterfaces p) :
    IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces p where
  nonminimal := by
    intro hχ hm ha hb
    dsimp
    intro u v huv
    exact
      (h.nonminimal hχ hm ha hb u v huv).toCompleteLyapunovData
        huv (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le p.hα.le
  minimal := by
    intro hχ hm ha hb uStar huStar
    dsimp
    intro u v huv hmass
    exact
      (h.minimal hχ hm ha hb uStar huStar u v huv hmass).toCompleteLyapunovData
        huv (by simpa [minimalEquilibrium] using huStar.le) p.hα.le

/-- Extract the nonminimal `Tendsto` frontier from complete Lyapunov branch
interfaces. -/
theorem IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces.nonminimal_tendsto_frontier
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces p) :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            Tendsto
              (fun t =>
                chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
              atTop (𝓝 0) := by
  intro hχ hm ha hb
  dsimp
  intro u v huv
  exact (h.nonminimal hχ hm ha hb u v huv).tendsto_zero

/-- Extract the minimal `Tendsto` frontier from complete Lyapunov branch
interfaces. -/
theorem IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces.minimal_tendsto_frontier
    {p : CM2Params}
    (h : IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces p) :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            HasInitialMass intervalDomain u uStar →
              Tendsto
                (fun t =>
                  chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                atTop (𝓝 0) := by
  intro hχ hm ha hb uStar huStar
  dsimp
  intro u v huv hmass
  exact (h.minimal hχ hm ha hb uStar huStar u v huv hmass).tendsto_zero

/-- Paper 3 Theorem 2.3 from Corollary 5.1 plus complete theta-dissipation
Lyapunov interfaces. -/
theorem intervalDomain_Theorem_2_3_of_corollary51_thetaCompleteLyapunovInterfaces
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hCor51 :
      Corollary_5_1 intervalDomain p N
        (intervalDomainPaper3Constants p M0 uBar vLower))
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hExpMinimal :
      1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  HasInitialMass intervalDomain u uStar →
                    UniformConvergesInSup intervalDomain u eq.1 →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem23ThetaCompleteLyapunovInterfaces p) :
    Theorem_2_3 intervalDomain p N :=
  intervalDomain_Theorem_2_3_of_lyapunov_moment_and_exponential_frontiers
    p N (intervalDomain_momentToUniform_of_corollary51 hCor51)
    hExpNonminimal hExpMinimal
    hEnergy.nonminimal_tendsto_frontier hEnergy.minimal_tendsto_frontier

/-- Paper 3 Theorem 2.3 from Corollary 5.1 plus the structured
energy/dissipation interfaces. -/
theorem intervalDomain_Theorem_2_3_of_corollary51_thetaDerivativeInterfaces
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hCor51 :
      Corollary_5_1 intervalDomain p N
        (intervalDomainPaper3Constants p M0 uBar vLower))
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hExpMinimal :
      1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  HasInitialMass intervalDomain u uStar →
                    UniformConvergesInSup intervalDomain u eq.1 →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem23ThetaDerivativeInterfaces p) :
    Theorem_2_3 intervalDomain p N :=
  intervalDomain_Theorem_2_3_of_corollary51_thetaCompleteLyapunovInterfaces
    p N M0 uBar vLower hCor51 hExpNonminimal hExpMinimal
    hEnergy.toCompleteLyapunovInterfaces

/-- Formula-branch theta-dissipation interface needed by Paper 3 Theorem 2.4.

The `M0` parameter appears only in the paper's explicit strong-logistic
formula condition. -/
structure IntervalDomainTheorem24ThetaDerivativeInterfaces
    (p : CM2Params) (M0 : ℝ) where
  strong :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              IntervalDomainThetaDissipationDerivativeDecayData u eq.1 p.α

/-- Extract the formula-branch raw derivative frontier expected by
`IntervalDomainStabilityChain`. -/
theorem IntervalDomainTheorem24ThetaDerivativeInterfaces.strong_frontier
    {p : CM2Params} {M0 : ℝ}
    (h : IntervalDomainTheorem24ThetaDerivativeInterfaces p M0) :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, 0 < t →
                  HasDerivAt
                    (fun tau =>
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u tau))
                    (momentSlope t) t) ∧
                (∀ t, 0 < t →
                  momentSlope t ≤
                    -rate *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t)) := by
  intro ha_pos hb_pos hβ hα hγ ha hb
  dsimp
  intro hcond u v huv
  let data := h.strong ha_pos hb_pos hβ hα hγ ha hb hcond u v huv
  exact
    ⟨data.rate, data.rate_pos, data.start, data.start_pos,
      data.slope, data.deriv, data.dissipative⟩

/-- Extract the full formula-branch theta-dissipation Lyapunov package supplied
by the structured branch interface. -/
theorem
    IntervalDomainTheorem24ThetaDerivativeInterfaces.strong_completeLyapunov_frontier
    {p : CM2Params} {M0 : ℝ}
    (h : IntervalDomainTheorem24ThetaDerivativeInterfaces p M0) :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, 0 < t → momentSlope t ≤ 0) ∧
                (∀ t, 0 < t →
                  0 ≤ chemotaxisThetaDissipation intervalDomain eq.1 p.α
                    (u t)) ∧
                AntitoneOn
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u t))
                  (Ioi (0 : ℝ)) ∧
                AntitoneOn
                  (fun t =>
                    Real.exp (rate * t) *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t))
                  (Ioi (0 : ℝ)) ∧
                (∀ a b, 0 < a → a ≤ b →
                  0 ≤ chemotaxisThetaDissipation intervalDomain eq.1 p.α
                    (u b) ∧
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u b) ≤
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u a) * Real.exp (-rate * (b - a))) ∧
                ThetaMomentConvergesToZero intervalDomain u eq.1 p.α := by
  intro ha_pos hb_pos hβ hα hγ ha hb
  dsimp
  intro hcond u v huv
  let data := h.strong ha_pos hb_pos hβ hα hγ ha hb hcond u v huv
  refine
    ⟨data.rate, data.rate_pos, data.start, data.start_pos,
      data.slope, ?_⟩
  exact
    data.completeLyapunovPackage huv
      (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le hα.le

/-- Formula-branch complete theta-dissipation Lyapunov interface needed by
Paper 3 Theorem 2.4 once the PDE energy estimate has already been
post-processed to monotonicity and theta-moment convergence. -/
structure IntervalDomainTheorem24ThetaCompleteLyapunovInterfaces
    (p : CM2Params) (M0 : ℝ) where
  strong :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              IntervalDomainThetaDissipationCompleteLyapunovData u eq.1 p.α

/-- The formula-branch derivative interface proves the complete Lyapunov
formula-branch interface. -/
def IntervalDomainTheorem24ThetaDerivativeInterfaces.toCompleteLyapunovInterfaces
    {p : CM2Params} {M0 : ℝ}
    (h : IntervalDomainTheorem24ThetaDerivativeInterfaces p M0) :
    IntervalDomainTheorem24ThetaCompleteLyapunovInterfaces p M0 where
  strong := by
    intro ha_pos hb_pos hβ hα hγ ha hb
    dsimp
    intro hcond u v huv
    exact
      (h.strong ha_pos hb_pos hβ hα hγ ha hb hcond u v huv).toCompleteLyapunovData
        huv (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le hα.le

/-- Extract the formula-branch `Tendsto` frontier from complete Lyapunov
interfaces. -/
theorem IntervalDomainTheorem24ThetaCompleteLyapunovInterfaces.strong_tendsto_frontier
    {p : CM2Params} {M0 : ℝ}
    (h : IntervalDomainTheorem24ThetaCompleteLyapunovInterfaces p M0) :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              Tendsto
                (fun t =>
                  chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                atTop (𝓝 0) := by
  intro ha_pos hb_pos hβ hα hγ ha hb
  dsimp
  intro hcond u v huv
  exact (h.strong ha_pos hb_pos hβ hα hγ ha hb hcond u v huv).tendsto_zero

/-- Paper 3 Theorem 2.4 from Corollary 5.1 plus complete formula-branch
theta-dissipation Lyapunov interfaces. -/
theorem intervalDomain_Theorem_2_4_formula_completeLyapunovInterfaces_of_corollary51
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hCor51 :
      Corollary_5_1 intervalDomain p N
        (intervalDomainPaper3Constants p M0 uBar vLower))
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2))
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem24ThetaCompleteLyapunovInterfaces p M0) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_frontiers
    p N M0 uBar vLower hfirst
    (intervalDomain_momentToUniform_of_corollary51 hCor51)
    hExpNonminimal hEnergy.strong_tendsto_frontier

/-- Paper 3 Theorem 2.4 from Corollary 5.1 plus the structured
formula-branch energy/dissipation interface. -/
theorem intervalDomain_Theorem_2_4_formula_derivativeInterfaces_of_corollary51
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hCor51 :
      Corollary_5_1 intervalDomain p N
        (intervalDomainPaper3Constants p M0 uBar vLower))
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2))
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem24ThetaDerivativeInterfaces p M0) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_formula_completeLyapunovInterfaces_of_corollary51
    p N M0 uBar vLower hCor51 hfirst hExpNonminimal
    hEnergy.toCompleteLyapunovInterfaces

/-- Minimal-model complete theta-dissipation Lyapunov interface needed by
Paper 3 Theorem 2.5.  The constants package appears only through the paper's
minimal global-stability condition. -/
structure IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces
    (p : CM2Params) (C : Paper3Constants intervalDomain p) where
  minimal :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        MinimalGlobalStabilityCondition intervalDomain p C uStar →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                IntervalDomainThetaDissipationCompleteLyapunovData
                  u eq.1 p.α

/-- Extract the minimal-model `Tendsto` frontier from complete Lyapunov
interfaces. -/
theorem IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces.minimal_tendsto_frontier
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h : IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces p C) :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        MinimalGlobalStabilityCondition intervalDomain p C uStar →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                Tendsto
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α
                      (u t))
                  atTop (𝓝 0) := by
  intro ha hb hm hβ uStar huStar
  dsimp
  intro hcond u v huv hmass
  exact (h.minimal ha hb hm hβ uStar huStar hcond u v huv hmass).tendsto_zero

/-- Extract the minimal global-stability frontier from complete Lyapunov
interfaces plus the moment-to-uniform bridge. -/
theorem IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces.minimal_global_frontier
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h : IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces p C)
    (hmomentToUniform : MomentConvergenceToUniformRaw intervalDomain p) :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        MinimalGlobalStabilityCondition intervalDomain p C uStar →
          GloballyAsymptoticallyStableMinimal intervalDomain p
            eq.1 eq.2 := by
  intro ha hb hm hβ uStar huStar
  dsimp
  intro hcond u v huv hmass
  let eq := minimalEquilibrium p uStar
  exact
    hmomentToUniform (by simp [hm])
      eq.1 eq.2 p.α p.hα u v huv
      ((h.minimal ha hb hm hβ uStar huStar hcond u v huv hmass).thetaMoment)

/-- Paper 3 Theorem 2.5 from complete minimal-model theta-dissipation
Lyapunov interfaces. -/
theorem intervalDomain_Theorem_2_5_of_thetaCompleteLyapunovInterfaces
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hmomentToUniform : MomentConvergenceToUniformRaw intervalDomain p)
    (hExpMinimal :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p C uStar →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  HasInitialMass intervalDomain u uStar →
                    UniformConvergesInSup intervalDomain u eq.1 →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces p C) :
    Theorem_2_5 intervalDomain p N C :=
  intervalDomain_Theorem_2_5_of_persistence_exp_frontiers
    p N C (hEnergy.minimal_global_frontier hmomentToUniform) hExpMinimal

/-- Paper 3 Theorem 2.5 from Corollary 5.1 plus complete minimal-model
theta-dissipation Lyapunov interfaces. -/
theorem intervalDomain_Theorem_2_5_of_corollary51_thetaCompleteLyapunovInterfaces
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hCor51 : Corollary_5_1 intervalDomain p N C)
    (hExpMinimal :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p C uStar →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  HasInitialMass intervalDomain u uStar →
                    UniformConvergesInSup intervalDomain u eq.1 →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces p C) :
    Theorem_2_5 intervalDomain p N C :=
  intervalDomain_Theorem_2_5_of_thetaCompleteLyapunovInterfaces
    p N C (intervalDomain_momentToUniform_of_corollary51 hCor51)
    hExpMinimal hEnergy

/-- Minimal-model theta-dissipation derivative interface needed by Paper 3
Theorem 2.5. -/
structure IntervalDomainTheorem25ThetaDerivativeInterfaces
    (p : CM2Params) (C : Paper3Constants intervalDomain p) where
  minimal :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        MinimalGlobalStabilityCondition intervalDomain p C uStar →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                IntervalDomainThetaDissipationDerivativeDecayData u eq.1 p.α

/-- The minimal-model derivative interface proves the complete Lyapunov
interface. -/
def IntervalDomainTheorem25ThetaDerivativeInterfaces.toCompleteLyapunovInterfaces
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h : IntervalDomainTheorem25ThetaDerivativeInterfaces p C) :
    IntervalDomainTheorem25ThetaCompleteLyapunovInterfaces p C where
  minimal := by
    intro ha hb hm hβ uStar huStar
    dsimp
    intro hcond u v huv hmass
    exact
      (h.minimal ha hb hm hβ uStar huStar hcond u v huv hmass).toCompleteLyapunovData
        huv (by simpa [minimalEquilibrium] using huStar.le) p.hα.le

/-- Paper 3 Theorem 2.5 from Corollary 5.1 plus the structured
minimal-model theta-dissipation derivative interface. -/
theorem intervalDomain_Theorem_2_5_of_corollary51_thetaDerivativeInterfaces
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hCor51 : Corollary_5_1 intervalDomain p N C)
    (hExpMinimal :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p C uStar →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  HasInitialMass intervalDomain u uStar →
                    UniformConvergesInSup intervalDomain u eq.1 →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate)
    (hEnergy : IntervalDomainTheorem25ThetaDerivativeInterfaces p C) :
    Theorem_2_5 intervalDomain p N C :=
  intervalDomain_Theorem_2_5_of_corollary51_thetaCompleteLyapunovInterfaces
    p N C hCor51 hExpMinimal hEnergy.toCompleteLyapunovInterfaces

end

end ShenWork.Paper3
