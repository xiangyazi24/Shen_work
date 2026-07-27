import ShenWork.Paper3.MinimalSteadyWAPopulationEquation

/-!
# A subcritical nonconstant steady state for the fixed `m = 3` tuple

This file packages the local Wiener branch as an exact classical
counterexample for

`m = 3`, `β = γ = μ = ν = uStar = 1`.

It selects a positive amplitude on the backward side of the branch, obtaining
`0 < χ < 2(1 + π²)`, positive nonconstant population and signal profiles,
Neumann boundary conditions, population mass one, and both stationary
equations.  The same steady state, viewed as a constant-in-time bounded
classical orbit, disproves global attraction to `(1, 1)`.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open Filter Set Topology
open ShenWork.Wiener

/-! ## The fixed classical steady system -/

/-- A positive classical Neumann steady state of the fixed minimal system

`0 = uₓₓ - χ ∂ₓ(u³ vₓ / (1 + v))`,
`0 = vₓₓ - v + u`.

Thus the parameters are exactly
`m = 3`, `β = γ = μ = ν = uStar = 1`, with the mass constraint stated
separately. -/
structure PositiveNeumannMinimalSteadyM3
    (χ : ℝ) (u v : ℝ → ℝ) : Prop where
  population_contDiff_two : ContDiff ℝ 2 u
  signal_contDiff_two : ContDiff ℝ 2 v
  population_pos : ∀ x : ℝ, 0 < u x
  signal_pos : ∀ x : ℝ, 0 < v x
  population_neumann_zero : deriv u 0 = 0
  population_neumann_one : deriv u 1 = 0
  signal_neumann_zero : deriv v 0 = 0
  signal_neumann_one : deriv v 1 = 0
  population_equation : ∀ x : ℝ,
    deriv (deriv u) x -
      χ *
        deriv
          (fun y =>
            u y ^ 3 * deriv v y / (1 + v y)) x = 0
  signal_equation : ∀ x : ℝ,
    deriv (deriv v) x - v x + u x = 0

theorem minimalSteadyBranch_is_classical
    {a : ℝ} (hzero : minimalSteadyPhysicalFluxResidual a = 0)
    (hpos :
      (∀ x : ℝ, 0 < minimalSteadyPopulation a x) ∧
        ∀ x : ℝ, 0 < minimalSteadySignal a x) :
    PositiveNeumannMinimalSteadyM3
      (minimalSteadySensitivity a)
      (minimalSteadyPopulation a)
      (minimalSteadySignal a) where
  population_contDiff_two :=
    minimalSteadyPopulation_contDiff_two a
  signal_contDiff_two :=
    minimalSteadySignal_contDiff_two a
  population_pos := hpos.1
  signal_pos := hpos.2
  population_neumann_zero :=
    minimalSteadyPopulation_neumann_zero a
  population_neumann_one :=
    minimalSteadyPopulation_neumann_one a
  signal_neumann_zero :=
    minimalSteadySignal_neumann_zero a
  signal_neumann_one :=
    minimalSteadySignal_neumann_one a
  population_equation :=
    minimalSteadyPopulation_equation hzero hpos.2
  signal_equation :=
    minimalSteadySignal_equation a

/-! ## Selecting a subcritical positive branch point -/

theorem exists_minimalSteady_positive_subcritical_amplitude :
    ∃ a : ℝ,
      0 < a ∧
      0 < minimalSteadySensitivity a ∧
      minimalSteadySensitivity a < minimalChiLin ∧
      ((∀ x : ℝ, 0 < minimalSteadyPopulation a x) ∧
        ∀ x : ℝ, 0 < minimalSteadySignal a x) ∧
      minimalSteadyPhysicalFluxResidual a = 0 := by
  have hpos :
      ∀ᶠ a in 𝓝[>] (0 : ℝ),
        (∀ x : ℝ, 0 < minimalSteadyPopulation a x) ∧
          ∀ x : ℝ, 0 < minimalSteadySignal a x :=
    eventually_minimalSteady_profiles_positive.filter_mono inf_le_left
  have hflux :
      ∀ᶠ a in 𝓝[>] (0 : ℝ),
        minimalSteadyPhysicalFluxResidual a = 0 :=
    eventually_minimalSteadyPhysicalFluxResidual_zero.filter_mono
      inf_le_left
  have hall :
      ∀ᶠ a in 𝓝[>] (0 : ℝ),
        (0 < minimalSteadySensitivity a ∧
          minimalSteadySensitivity a < minimalChiLin) ∧
        ((∀ x : ℝ, 0 < minimalSteadyPopulation a x) ∧
          ∀ x : ℝ, 0 < minimalSteadySignal a x) ∧
        minimalSteadyPhysicalFluxResidual a = 0 := by
    filter_upwards
      [eventually_minimalSteadySensitivity_bounds_right,
        hpos, hflux] with a hχ hp hf
    exact ⟨hχ, hp, hf⟩
  rcases (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hall with
    ⟨δ, hδ, hallδ⟩
  let a : ℝ := δ / 2
  have ha0 : 0 < a := by
    dsimp [a]
    linarith
  have haδ : a < δ := by
    dsimp [a]
    linarith
  rcases hallδ ⟨ha0, haδ⟩ with ⟨hχ, hp, hf⟩
  exact ⟨a, ha0, hχ.1, hχ.2, hp, hf⟩

/-- Exact nonconstant positive mass-preserving classical Neumann steady state
strictly below the first linear threshold for the fixed
`(m, β, γ, μ, ν, uStar) = (3, 1, 1, 1, 1, 1)` tuple. -/
theorem exists_nonconstant_minimal_steady_below_threshold_m3 :
    ∃ χ : ℝ, ∃ u v : ℝ → ℝ,
      0 < χ ∧
      χ < minimalChiLin ∧
      PositiveNeumannMinimalSteadyM3 χ u v ∧
      (∫ x in (0 : ℝ)..1, u x) = 1 ∧
      ¬ ∀ x y : ℝ, u x = u y := by
  rcases exists_minimalSteady_positive_subcritical_amplitude with
    ⟨a, ha, hχpos, hχlt, hprofiles, hflux⟩
  refine
    ⟨minimalSteadySensitivity a,
      minimalSteadyPopulation a,
      minimalSteadySignal a,
      hχpos, hχlt, ?_, minimalSteadyPopulation_mass a, ?_⟩
  · exact minimalSteadyBranch_is_classical hflux hprofiles
  · exact minimalSteadyPopulation_nonconstant ha.ne'

/-! ## The stationary orbit and failure of global attraction -/

def stationaryPopulationOrbit (u : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun _ => u

def stationarySignalOrbit (v : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun _ => v

/-- A bounded positive mass-one classical orbit of the fixed parabolic-
elliptic system.  Time is represented on `ℝ`; global attraction is tested at
`atTop`. -/
structure BoundedMassOneMinimalOrbitM3
    (χ : ℝ) (U V : ℝ → ℝ → ℝ) : Prop where
  population_time_contDiff_one :
    ∀ x : ℝ, ContDiff ℝ 1 (fun t => U t x)
  signal_time_contDiff_one :
    ∀ x : ℝ, ContDiff ℝ 1 (fun t => V t x)
  population_space_contDiff_two :
    ∀ t : ℝ, ContDiff ℝ 2 (U t)
  signal_space_contDiff_two :
    ∀ t : ℝ, ContDiff ℝ 2 (V t)
  population_pos : ∀ t x : ℝ, 0 < U t x
  signal_pos : ∀ t x : ℝ, 0 < V t x
  population_neumann_zero : ∀ t : ℝ, deriv (U t) 0 = 0
  population_neumann_one : ∀ t : ℝ, deriv (U t) 1 = 0
  signal_neumann_zero : ∀ t : ℝ, deriv (V t) 0 = 0
  signal_neumann_one : ∀ t : ℝ, deriv (V t) 1 = 0
  population_equation : ∀ t x : ℝ,
    deriv (fun s => U s x) t =
      deriv (deriv (U t)) x -
        χ *
          deriv
            (fun y =>
              U t y ^ 3 * deriv (V t) y /
                (1 + V t y)) x
  signal_equation : ∀ t x : ℝ,
    deriv (fun s => V s x) t =
      deriv (deriv (V t)) x - V t x + U t x
  population_mass : ∀ t : ℝ,
    (∫ x in (0 : ℝ)..1, U t x) = 1
  population_bounded : ∃ C : ℝ, ∀ t x : ℝ, |U t x| ≤ C
  signal_bounded : ∃ C : ℝ, ∀ t x : ℝ, |V t x| ≤ C

theorem stationaryOrbit_of_minimalSteady
    {χ : ℝ} {u v : ℝ → ℝ}
    (hsteady : PositiveNeumannMinimalSteadyM3 χ u v)
    (hmass : (∫ x in (0 : ℝ)..1, u x) = 1)
    {Cu Cv : ℝ}
    (huBound : ∀ x : ℝ, |u x| ≤ Cu)
    (hvBound : ∀ x : ℝ, |v x| ≤ Cv) :
    BoundedMassOneMinimalOrbitM3 χ
      (stationaryPopulationOrbit u)
      (stationarySignalOrbit v) where
  population_time_contDiff_one := fun _ => contDiff_const
  signal_time_contDiff_one := fun _ => contDiff_const
  population_space_contDiff_two := fun _ =>
    hsteady.population_contDiff_two
  signal_space_contDiff_two := fun _ =>
    hsteady.signal_contDiff_two
  population_pos := fun _ => hsteady.population_pos
  signal_pos := fun _ => hsteady.signal_pos
  population_neumann_zero := fun _ =>
    hsteady.population_neumann_zero
  population_neumann_one := fun _ =>
    hsteady.population_neumann_one
  signal_neumann_zero := fun _ =>
    hsteady.signal_neumann_zero
  signal_neumann_one := fun _ =>
    hsteady.signal_neumann_one
  population_equation := by
    intro t x
    simpa only [stationaryPopulationOrbit,
      stationarySignalOrbit, deriv_const] using
        (hsteady.population_equation x).symm
  signal_equation := by
    intro t x
    simpa only [stationaryPopulationOrbit,
      stationarySignalOrbit, deriv_const] using
        (hsteady.signal_equation x).symm
  population_mass := fun _ => hmass
  population_bounded := ⟨Cu, fun _ => huBound⟩
  signal_bounded := ⟨Cv, fun _ => hvBound⟩

/-- Pointwise global attraction of every bounded positive mass-one classical
orbit to the minimal constant equilibrium `(1, 1)`. -/
def MinimalEquilibriumGloballyAttractsBoundedMassOneOrbitsM3
    (χ : ℝ) : Prop :=
  ∀ U V : ℝ → ℝ → ℝ,
    BoundedMassOneMinimalOrbitM3 χ U V →
      ∀ x : ℝ,
        Tendsto (fun t => U t x) atTop (𝓝 1) ∧
          Tendsto (fun t => V t x) atTop (𝓝 1)

theorem nonconstant_stationaryOrbit_refutes_globalAttraction
    {χ : ℝ} {u v : ℝ → ℝ}
    (hsteady : PositiveNeumannMinimalSteadyM3 χ u v)
    (hmass : (∫ x in (0 : ℝ)..1, u x) = 1)
    {Cu Cv : ℝ}
    (huBound : ∀ x : ℝ, |u x| ≤ Cu)
    (hvBound : ∀ x : ℝ, |v x| ≤ Cv)
    (hnonconstant : ¬ ∀ x y : ℝ, u x = u y) :
    ¬ MinimalEquilibriumGloballyAttractsBoundedMassOneOrbitsM3 χ := by
  intro hglobal
  have horbit :=
    stationaryOrbit_of_minimalSteady hsteady hmass huBound hvBound
  have hex : ∃ x : ℝ, u x ≠ 1 := by
    by_contra hnone
    apply hnonconstant
    intro x y
    have hx : u x = 1 := by
      by_contra hx
      exact hnone ⟨x, hx⟩
    have hy : u y = 1 := by
      by_contra hy
      exact hnone ⟨y, hy⟩
    exact hx.trans hy.symm
  rcases hex with ⟨x, hx⟩
  have hlimit :
      Tendsto (fun _ : ℝ => u x) atTop (𝓝 1) := by
    simpa only [stationaryPopulationOrbit] using
      (hglobal
        (stationaryPopulationOrbit u)
        (stationarySignalOrbit v) horbit x).1
  have hconstant :
      Tendsto (fun _ : ℝ => u x) atTop (𝓝 (u x)) :=
    tendsto_const_nhds
  exact hx (tendsto_nhds_unique hconstant hlimit)

/-- Global stability of the minimal equilibrium is false below the linear
threshold for the fixed `m = 3` tuple: the counterexample orbit is the bounded
mass-one nonconstant steady state itself. -/
theorem minimal_equilibrium_global_stability_false_m3 :
    ∃ χ : ℝ,
      0 < χ ∧
      χ < minimalChiLin ∧
      ¬ MinimalEquilibriumGloballyAttractsBoundedMassOneOrbitsM3 χ := by
  rcases exists_minimalSteady_positive_subcritical_amplitude with
    ⟨a, ha, hχpos, hχlt, hprofiles, hflux⟩
  let u := minimalSteadyPopulation a
  let v := minimalSteadySignal a
  have hsteady :
      PositiveNeumannMinimalSteadyM3
        (minimalSteadySensitivity a) u v := by
    exact minimalSteadyBranch_is_classical hflux hprofiles
  have huBound :
      ∀ x : ℝ,
        |u x| ≤ ‖minimalSteadyPopulationCoeff a‖ := by
    intro x
    exact abs_staticEval_le_norm
      (minimalSteadyPopulationCoeff a) x
  have hvBound :
      ∀ x : ℝ,
        |v x| ≤ ‖minimalSteadySignalCoeff a‖ := by
    intro x
    exact abs_staticEval_le_norm
      (minimalSteadySignalCoeff a) x
  refine ⟨minimalSteadySensitivity a, hχpos, hχlt, ?_⟩
  exact
    nonconstant_stationaryOrbit_refutes_globalAttraction
      hsteady (minimalSteadyPopulation_mass a)
      huBound hvBound
      (minimalSteadyPopulation_nonconstant ha.ne')

end ShenWork.M3Counterexample
