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

open Filter Topology
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
  intervalDomain_Theorem_2_3_of_corollary51_theta_derivative_solution
    p N M0 uBar vLower hCor51 hExpNonminimal hExpMinimal
    hEnergy.nonminimal_frontier hEnergy.minimal_frontier

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
  intervalDomain_Theorem_2_4_formula_derivative_solution_of_corollary51
    p N M0 uBar vLower hCor51 hfirst hExpNonminimal
    hEnergy.strong_frontier

end

end ShenWork.Paper3
