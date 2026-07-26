import ShenWork.Paper1.WholeLineChiPosFloorQuantifierObstruction
import ShenWork.Paper1.Theorem12WeightedEnergy
import ShenWork.Paper1.WavePositiveConstruction

/-!
# A genuine PDE counterexample from convective escape

Let `(U,V)` be a traveling wave of laboratory speed `s`.  The laboratory
fields

`u(t,x) = U(x-s*t)`, `v(t,x) = V(x-s*t)`

are a global classical solution.  In a frame `z = x-c*t` with `s < c`, they
become

`q(t,z) = U(z+(c-s)*t)`, `W(t,z) = V(z+(c-s)*t)`.

This module verifies the moving-frame PDE directly.  For
`m = α = γ = 1`, it also expands the chemotactic divergence using the
elliptic equation and obtains exactly

`q_t = q_zz + (c-χ W_z)q_z + q(1-χ W+(χ-1)q)`,
`-W_zz + W = q`.

Finally, the positive traveling-wave construction supplies a concrete
counterexample already at `χ = 0`, laboratory speed `3`, and frame speed `4`.
Thus per-slice `StrictlyPositiveAtLeft` data cannot imply an unconditional
far-left floor in an arbitrary frame.  A basin/closeness hypothesis that pins
the frame to the wave speed is necessary.
-/

open Filter Function Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- The laboratory profiles associated with a `C²` traveling wave form a
genuine global classical solution of the original system. -/
theorem IsTravelingWave.laboratoryProfile_isGlobalClassicalSolution
    {p : CMParams} {s : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p s U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    IsGlobalClassicalSolution p
      (travelingWaveLaboratoryProfile s U)
      (travelingWaveLaboratoryProfile s V) := by
  simpa only [travelingWaveLaboratoryProfile] using
    IsTravelingWave.to_movingFrame_global_classical_solution
      p hTW hU2 hV2

/-- Direct chain-rule verification of the population equation in a frame of
speed `c`.  This is the general-exponent divergence-form equation. -/
theorem IsTravelingWave.convectiveEscape_population_equation
    {p : CMParams} {s c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p s U V)
    (hUdiff : Differentiable ℝ U) (t z : ℝ) :
    deriv (fun tau => convectiveEscapeProfile U s c tau z) t =
      iteratedDeriv 2 (convectiveEscapeProfile U s c t) z +
        c * deriv (convectiveEscapeProfile U s c t) z -
        p.χ * deriv
          (fun y => (convectiveEscapeProfile U s c t y) ^ p.m *
            deriv (convectiveEscapeProfile V s c t) y) z +
        convectiveEscapeProfile U s c t z *
          (1 - (convectiveEscapeProfile U s c t z) ^ p.α) := by
  unfold convectiveEscapeProfile
  have hinner :
      HasDerivAt (fun tau : ℝ => z + (c - s) * tau) (c - s) t := by
    simpa [add_comm] using
      ((hasDerivAt_id t).const_mul (c - s)).const_add z
  have htime :
      deriv (fun tau : ℝ => U (z + (c - s) * tau)) t =
        deriv U (z + (c - s) * t) * (c - s) :=
    ((hUdiff _).hasDerivAt.comp t hinner).deriv
  have hU2 :=
    congr_fun
      (iteratedDeriv_comp_add_const 2 U ((c - s) * t)) z
  have hU1 :
      deriv (fun y => U (y + (c - s) * t)) z =
        deriv U (z + (c - s) * t) :=
    deriv_comp_add_const U ((c - s) * t) z
  have hV1 : ∀ y,
      deriv (fun w => V (w + (c - s) * t)) y =
        deriv V (y + (c - s) * t) := by
    intro y
    exact deriv_comp_add_const V ((c - s) * t) y
  have hChem :
      deriv
          (fun y => (U (y + (c - s) * t)) ^ p.m *
            deriv (fun w => V (w + (c - s) * t)) y) z =
        deriv (fun xi => (U xi) ^ p.m * deriv V xi)
          (z + (c - s) * t) := by
    have hfun :
        (fun y => (U (y + (c - s) * t)) ^ p.m *
          deriv (fun w => V (w + (c - s) * t)) y) =
        (fun y => (U (y + (c - s) * t)) ^ p.m *
          deriv V (y + (c - s) * t)) := by
      funext y
      rw [hV1 y]
    rw [hfun]
    have htranslated :=
      congr_fun
        (iteratedDeriv_comp_add_const 1
          (fun xi => (U xi) ^ p.m * deriv V xi)
          ((c - s) * t)) z
    simpa only [iteratedDeriv_one] using htranslated
  rw [htime, hU2, hU1, hChem]
  linarith [hTW.ode_U (z + (c - s) * t)]

/-- Direct verification of the elliptic equation in the mismatched frame. -/
theorem IsTravelingWave.convectiveEscape_elliptic_equation
    {p : CMParams} {s c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p s U V) (t z : ℝ) :
    iteratedDeriv 2 (convectiveEscapeProfile V s c t) z -
        convectiveEscapeProfile V s c t z +
        (convectiveEscapeProfile U s c t z) ^ p.γ = 0 := by
  unfold convectiveEscapeProfile
  have hV2 :=
    congr_fun
      (iteratedDeriv_comp_add_const 2 V ((c - s) * t)) z
  rw [hV2]
  exact hTW.ode_V (z + (c - s) * t)

/-- Parameters of the chemotaxis--logistic system in the exact
`m = α = γ = 1` form used by the far-left argument. -/
def linearChemotaxisLogisticParams (chi : ℝ) : CMParams :=
  { m := 1
    α := 1
    γ := 1
    χ := chi
    hm := by norm_num
    hα := by norm_num
    hγ := by norm_num }

/-- The exact expanded moving-frame system for `m = α = γ = 1`. -/
def SolvesLinearChemotaxisLogisticMovingFrame
    (chi c : ℝ) (q W : ℝ → ℝ → ℝ) : Prop :=
  (∀ t z,
    deriv (fun tau => q tau z) t =
      iteratedDeriv 2 (q t) z +
        (c - chi * deriv (W t) z) * deriv (q t) z +
        q t z * (1 - chi * W t z + (chi - 1) * q t z)) ∧
  (∀ t z, -iteratedDeriv 2 (W t) z + W t z = q t z)

/-- A traveling wave for `m = α = γ = 1`, viewed in any frame, solves the
exact expanded moving-frame system. -/
theorem IsTravelingWave.convectiveEscape_solves_linearMovingFrame
    {chi s c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave
      (linearChemotaxisLogisticParams chi) s U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    SolvesLinearChemotaxisLogisticMovingFrame chi c
      (convectiveEscapeProfile U s c)
      (convectiveEscapeProfile V s c) := by
  constructor
  · intro t z
    have hdiv :=
      IsTravelingWave.convectiveEscape_population_equation
        (c := c) hTW (hU2.differentiable two_ne_zero) t z
    have hell :=
      IsTravelingWave.convectiveEscape_elliptic_equation
        (c := c) hTW t z
    have hq1 :
        ContDiff ℝ 1 (convectiveEscapeProfile U s c t) := by
      have hq2 :=
        ContDiff.two_shift hU2 ((c - s) * t)
      simpa only [convectiveEscapeProfile] using
        hq2.of_le (by norm_num)
    have hW2 :
        ContDiff ℝ 2 (convectiveEscapeProfile V s c t) := by
      simpa only [convectiveEscapeProfile] using
        ContDiff.two_shift hV2 ((c - s) * t)
    have hflux :=
      ShenWork.Paper1.paper5FluxDerivative_realization
        (linearChemotaxisLogisticParams chi) hq1 hW2 hell
    have hdiv' :
        deriv
            (fun tau => convectiveEscapeProfile U s c tau z) t =
          iteratedDeriv 2 (convectiveEscapeProfile U s c t) z +
            c * deriv (convectiveEscapeProfile U s c t) z -
            chi * deriv
              (fun y => convectiveEscapeProfile U s c t y *
                deriv (convectiveEscapeProfile V s c t) y) z +
            convectiveEscapeProfile U s c t z *
              (1 - convectiveEscapeProfile U s c t z) := by
      simpa only [linearChemotaxisLogisticParams, Real.rpow_one] using hdiv
    have hflux' :
        deriv
            (fun y => convectiveEscapeProfile U s c t y *
              deriv (convectiveEscapeProfile V s c t) y) z =
          deriv (convectiveEscapeProfile U s c t) z *
              deriv (convectiveEscapeProfile V s c t) z +
            convectiveEscapeProfile U s c t z *
              (convectiveEscapeProfile V s c t z -
                convectiveEscapeProfile U s c t z) := by
      simpa only [linearChemotaxisLogisticParams, sub_self,
        Real.rpow_zero, Real.rpow_one, one_mul] using hflux
    rw [hflux'] at hdiv'
    nlinarith [hdiv']
  · intro t z
    have hell :=
      IsTravelingWave.convectiveEscape_elliptic_equation
        (c := c) hTW t z
    have hell' :
        iteratedDeriv 2 (convectiveEscapeProfile V s c t) z -
            convectiveEscapeProfile V s c t z +
            convectiveEscapeProfile U s c t z = 0 := by
      simpa only [linearChemotaxisLogisticParams, Real.rpow_one] using hell
    linarith

/-- Concrete linear/logistic parameters at `χ = 0`. -/
def convectiveEscapeChiZeroParams : CMParams :=
  linearChemotaxisLogisticParams 0

/-- A constructed, genuine PDE counterexample at `χ = 0`: laboratory speed
`3`, faster frame speed `4`, exact moving-frame PDE, positive left endpoint on
every slice, but no uniform late-time far-left floor. -/
theorem exists_genuine_convectiveEscape_counterexample_chi_zero :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave convectiveEscapeChiZeroParams 3 U V ∧
      ContDiff ℝ 2 U ∧
      ContDiff ℝ 2 V ∧
      IsGlobalClassicalSolution convectiveEscapeChiZeroParams
        (travelingWaveLaboratoryProfile 3 U)
        (travelingWaveLaboratoryProfile 3 V) ∧
      SolvesLinearChemotaxisLogisticMovingFrame 0 4
        (convectiveEscapeProfile U 3 4)
        (convectiveEscapeProfile V 3 4) ∧
      (∀ t, StrictlyPositiveAtLeft
        (convectiveEscapeProfile U 3 4 t)) ∧
      (∀ ell, 0 < ell → ∀ T R,
        ∃ t z : ℝ, T ≤ t ∧ z ≤ -R ∧
          convectiveEscapeProfile U 3 4 t z < ell) ∧
      (∀ ell M, 0 < ell →
        ¬ EventualCoMovingLeftBand 4 ell M
          (travelingWaveLaboratoryProfile 3 U)) := by
  have halpha :
      convectiveEscapeChiZeroParams.α =
        convectiveEscapeChiZeroParams.m +
          convectiveEscapeChiZeroParams.γ - 1 := by
    norm_num [convectiveEscapeChiZeroParams,
      linearChemotaxisLogisticParams]
  have hchi0 : 0 ≤ convectiveEscapeChiZeroParams.χ := by
    norm_num [convectiveEscapeChiZeroParams,
      linearChemotaxisLogisticParams]
  have hchismall :
      convectiveEscapeChiZeroParams.χ <
        min (1 / 2 : ℝ) (chiStar convectiveEscapeChiZeroParams) := by
    norm_num [convectiveEscapeChiZeroParams,
      linearChemotaxisLogisticParams, chiStar]
  obtain ⟨U, hprofile, hU2, hV2, _hreg, _hupper, _htail⟩ :=
    ShenWork.Paper1.paper1_positiveConstruction_selfStep
      convectiveEscapeChiZeroParams halpha hchi0 hchismall
      3 (by norm_num)
  let V : ℝ → ℝ := frozenElliptic convectiveEscapeChiZeroParams U
  have hTW :
      IsTravelingWave convectiveEscapeChiZeroParams 3 U V := by
    simpa only [V] using
      FrozenStationaryWaveProfile.to_travelingWave hprofile
  have hglobal :
      IsGlobalClassicalSolution convectiveEscapeChiZeroParams
        (travelingWaveLaboratoryProfile 3 U)
        (travelingWaveLaboratoryProfile 3 V) :=
    IsTravelingWave.laboratoryProfile_isGlobalClassicalSolution
      hTW hU2 hV2
  have hframe :
      SolvesLinearChemotaxisLogisticMovingFrame 0 4
        (convectiveEscapeProfile U 3 4)
        (convectiveEscapeProfile V 3 4) :=
    IsTravelingWave.convectiveEscape_solves_linearMovingFrame
      hTW hU2 hV2
  have hquant :=
    IsTravelingWave.convectiveEscape_quantifier_obstruction
      hTW (by norm_num : (3 : ℝ) < 4)
  exact ⟨U, V, hTW, hU2, hV2, hglobal, hframe,
    hquant.2.1, hquant.2.2.1, hquant.2.2.2⟩

/-- Formal negation of the unconditional arbitrary-frame floor assertion.
This fails already at `χ = 0 < 4`; hence a valid sharp-range theorem must
exclude frame-speed mismatch, for example through the basin/closeness
hypothesis used by the basin-conditional result. -/
theorem unconditional_farLeft_floor_arbitraryFrame_false_chi_zero :
    ¬ (∀ (s : ℝ) (U V : ℝ → ℝ),
      IsTravelingWave convectiveEscapeChiZeroParams s U V →
      s < 4 →
      ∃ ell M : ℝ, 0 < ell ∧
        EventualCoMovingLeftBand 4 ell M
          (travelingWaveLaboratoryProfile s U)) := by
  intro hunconditional
  obtain ⟨U, V, hTW, _hU2, _hV2, _hglobal, _hframe,
    _hslices, _hquant, hnoBand⟩ :=
    exists_genuine_convectiveEscape_counterexample_chi_zero
  obtain ⟨ell, M, hell, hband⟩ :=
    hunconditional 3 U V hTW (by norm_num)
  exact (hnoBand ell M hell) hband

section AxiomAudit

#print axioms IsTravelingWave.laboratoryProfile_isGlobalClassicalSolution
#print axioms IsTravelingWave.convectiveEscape_population_equation
#print axioms IsTravelingWave.convectiveEscape_elliptic_equation
#print axioms IsTravelingWave.convectiveEscape_solves_linearMovingFrame
#print axioms exists_genuine_convectiveEscape_counterexample_chi_zero
#print axioms unconditional_farLeft_floor_arbitraryFrame_false_chi_zero

end AxiomAudit

end ShenWork.Paper1
