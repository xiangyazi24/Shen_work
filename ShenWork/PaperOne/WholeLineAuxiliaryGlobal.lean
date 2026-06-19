import ShenWork.PaperOne.WholeLineAuxiliaryContraction
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Global auxiliary-flow existence from the local Banach construction.

The formalized part below is the continuation skeleton that uses one fixed
local time step `T0`: once a trapped solution on `[0,T]` can be restarted and
glued to a trapped local solution on another interval of length `T0`, every
finite horizon is reachable by iterating the same step.  The PDE-level
restart/splice construction is carried by `AuxiliaryUniformRestartGluingData`;
its role is exactly the standard endpoint restart plus overlap gluing for the
mild formulation.
-/

/--
Uniform restart and gluing data for the auxiliary flow at one fixed Banach
time step `T0`.

The `extend_from_solution` field is the PDE continuation content: because each
finite branch remains in the wave-barrier trap, hence in the uniform
`0 ≤ w ≤ 1` box, the Banach local time does not shrink when restarting from an
endpoint slice.  The resulting fresh local branch is glued to the old one to
reach `T + T0`.
-/
structure AuxiliaryUniformRestartGluingData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D T0 : ℝ) : Prop where
  extend_from_solution :
    ∀ {T : ℝ} {w wx : ℝ → ℝ → ℝ}, 0 < T →
      AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx →
        AuxiliaryReachableHorizon p c Uplus V Vx κ κt D (T + T0)
  glue :
    AuxiliaryGlobalSolutionGluingFromReachability p c Uplus V Vx κ κt D

/-- The one-step horizon extension extracted from uniform restart data. -/
theorem auxiliaryReachableHorizon_step_of_uniformRestart
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D T0 T : ℝ}
    (H : AuxiliaryUniformRestartGluingData p c Uplus V Vx κ κt D T0)
    (hT : 0 < T)
    (hreach : AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T) :
    AuxiliaryReachableHorizon p c Uplus V Vx κ κt D (T + T0) := by
  rcases hreach with ⟨w, wx, hsol⟩
  exact H.extend_from_solution hT hsol

/--
Fixed-step continuation reaches every finite horizon.

This is the formal `kT0` iteration: start from the Banach solution on `[0,T0]`,
extend by the same `T0` repeatedly, and then restrict the resulting longer
horizon down to the requested `T`.
-/
theorem auxiliaryReachableArbitrarilyLong_of_uniformRestart
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D T0 : ℝ}
    (hT0 : 0 < T0)
    (hlocal : AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T0)
    (H : AuxiliaryUniformRestartGluingData p c Uplus V Vx κ κt D T0) :
    AuxiliaryReachableArbitrarilyLong p c Uplus V Vx κ κt D := by
  have hgrid :
      ∀ n : ℕ,
        AuxiliaryReachableHorizon p c Uplus V Vx κ κt D
          (((n + 1 : ℕ) : ℝ) * T0) := by
    intro n
    induction n with
    | zero =>
        simpa using hlocal
    | succ n ih =>
        have hpos :
            0 < (((n + 1 : ℕ) : ℝ) * T0) := by
          have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_pos n
          exact mul_pos hnpos hT0
        have hnext :
            AuxiliaryReachableHorizon p c Uplus V Vx κ κt D
              ((((n + 1 : ℕ) : ℝ) * T0) + T0) :=
          auxiliaryReachableHorizon_step_of_uniformRestart H hpos ih
        simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_mul]
          using hnext
  intro T hT
  obtain ⟨n, hn⟩ := exists_nat_gt (T / T0)
  have hlt_grid : T / T0 < ((n + 1 : ℕ) : ℝ) := by
    have hn_succ : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self n
    exact lt_trans hn hn_succ
  have hT_lt_grid : T < ((n + 1 : ℕ) : ℝ) * T0 := by
    have hmul := mul_lt_mul_of_pos_right hlt_grid hT0
    have hcancel : T / T0 * T0 = T := by
      field_simp [ne_of_gt hT0]
    simpa [hcancel] using hmul
  exact auxiliaryReachableHorizon_mono hT (le_of_lt hT_lt_grid) (hgrid n)

/-- Global solution from one local Banach horizon and uniform restart/gluing. -/
theorem auxiliaryFlow_globalExists_of_uniformRestart
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D T0 : ℝ}
    (hT0 : 0 < T0)
    (hlocal : AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T0)
    (H : AuxiliaryUniformRestartGluingData p c Uplus V Vx κ κt D T0) :
    AuxiliaryGlobalMildSolutionFor p c Uplus V Vx κ κt D := by
  exact H.glue
    (auxiliaryReachableArbitrarilyLong_of_uniformRestart hT0 hlocal H)

/--
Uniform restart/gluing supplied for whatever short horizon the local Banach
argument produces.
-/
def AuxiliaryUniformRestartGluingFromLocalBanach
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∀ T0, 0 < T0 →
    AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T0 →
      AuxiliaryUniformRestartGluingData p c Uplus V Vx κ κt D T0

/--
Global auxiliary-flow existence.

The local branch is obtained by `auxiliaryFlow_localExists`; the supplied
uniform restart/gluing data records the standard continuation argument using
the unchanged trap bound `0 ≤ w ≤ 1`.
-/
theorem auxiliaryFlow_globalExists
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (Hrate : AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D,
        AuxiliaryMildMapBanachRealizationData p c Uplus V Vx κ κt D C)
    (hrestart :
      AuxiliaryUniformRestartGluingFromLocalBanach p c Uplus V Vx κ κt D) :
    AuxiliaryGlobalMildSolutionFor p c Uplus V Vx κ κt D := by
  obtain ⟨T0, hT0, hlocal⟩ := auxiliaryFlow_localExists Hrate hrealize
  exact auxiliaryFlow_globalExists_of_uniformRestart hT0 hlocal
    (hrestart T0 hT0 hlocal)

/-- Trapped global auxiliary flow, exposing the uniform `0 ≤ w ≤ 1` bound. -/
theorem auxiliaryFlow_globalExists_trapped
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (Hrate : AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D,
        AuxiliaryMildMapBanachRealizationData p c Uplus V Vx κ κt D C)
    (hrestart :
      AuxiliaryUniformRestartGluingFromLocalBanach p c Uplus V Vx κ κt D) :
    ∃ w wx : ℝ → ℝ → ℝ,
      (∀ T > 0, AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx) ∧
        ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x ∧ w t x ≤ 1 := by
  exact auxiliaryGlobalMildSolution_nonneg
    (auxiliaryFlow_globalExists Hrate hrealize hrestart)

#print axioms auxiliaryReachableHorizon_step_of_uniformRestart
#print axioms auxiliaryReachableArbitrarilyLong_of_uniformRestart
#print axioms auxiliaryFlow_globalExists_of_uniformRestart
#print axioms auxiliaryFlow_globalExists
#print axioms auxiliaryFlow_globalExists_trapped

end ShenWork.PaperOne
