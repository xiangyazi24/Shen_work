import ShenWork.PaperOne.WholeLineParabolicEquicontinuity
import ShenWork.PaperOne.WholeLineOrbitProperties
import ShenWork.PDE.IntervalChemFluxLipschitz
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Auxiliary-flow existence interfaces for the whole-line moving-frame problem.

This file keeps the analytic continuation frontier explicit.  The short-time
contraction skeleton is closed from a rate package of the usual form
`A * sqrt T + B * T < 1`; the missing PDE content is the production of those
rate estimates from the nonlinear frozen source and the textbook
maximal-continuation/restart theorem at a finite endpoint.
-/

/-- The spatial-gradient component paired with `auxiliaryMildMap`. -/
def auxiliaryMildGradMap (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameHeatGradOp c t Uplus x + auxiliaryGradDuhamel p c W Wx V Vx t x

/-- The wave-barrier trap on a finite auxiliary-flow horizon. -/
def AuxiliaryBarrierTrap (κ κt D T : ℝ) (W : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    lowerBarrier κ κt D x ≤ W t x ∧ W t x ≤ upperBarrier κ x

theorem auxiliaryBarrierTrap_nonneg {κ κt D T : ℝ} {W : ℝ → ℝ → ℝ}
    (hW : AuxiliaryBarrierTrap κ κt D T W) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ W t x := by
  intro t ht x
  exact le_trans (lowerBarrier_nonneg κ κt D x) (hW t ht x).1

theorem auxiliaryBarrierTrap_le_one {κ κt D T : ℝ} {W : ℝ → ℝ → ℝ}
    (hW : AuxiliaryBarrierTrap κ κt D T W) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, W t x ≤ 1 := by
  intro t ht x
  exact le_trans (hW t ht x).2 (upperBarrier_le_one κ x)

theorem auxiliaryBarrierTrap_abs_le_one {κ κt D T : ℝ} {W : ℝ → ℝ → ℝ}
    (hW : AuxiliaryBarrierTrap κ κt D T W) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, |W t x| ≤ 1 := by
  intro t ht x
  rw [abs_of_nonneg (auxiliaryBarrierTrap_nonneg hW t ht x)]
  exact auxiliaryBarrierTrap_le_one hW t ht x

/-- Rate estimates that the nonlinear source and moving-frame semigroup must
provide on every sufficiently small auxiliary-flow horizon. -/
structure AuxiliaryMildMapRateEstimates
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop where
  hA_nonneg : 0 ≤ A
  hB_nonneg : 0 ≤ B
  mapsTo_of_small :
    ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
      ∀ W Wx, AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T
          (auxiliaryMildMap p c Uplus W Wx V Vx)
  value_diff_of_small :
    ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
      ∀ W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            |auxiliaryMildMap p c Uplus W Wx V Vx t x -
              auxiliaryMildMap p c Uplus Z Zx V Vx t x| ≤
                B * T * dist
  gradient_diff_of_small :
    ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
      ∀ W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            |auxiliaryMildGradMap p c Uplus W Wx V Vx t x -
              auxiliaryMildGradMap p c Uplus Z Zx V Vx t x| ≤
                A * Real.sqrt T * dist

/-- Closed short-time contraction package for the auxiliary pair map
`(W, Wx) ↦ (Φ(W,Wx), ∂x Φ(W,Wx))` on the wave-barrier trap. -/
structure AuxiliaryMildMapContractionData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) where
  T : ℝ
  hT_pos : 0 < T
  K : ℝ
  hK_nonneg : 0 ≤ K
  hK_lt_one : K < 1
  mapsTo :
    ∀ W Wx, AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T
        (auxiliaryMildMap p c Uplus W Wx V Vx)
  contraction :
    ∀ W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        AuxiliaryC1DistanceBound T (K * dist)
          (auxiliaryMildMap p c Uplus W Wx V Vx)
          (auxiliaryMildGradMap p c Uplus W Wx V Vx)
          (auxiliaryMildMap p c Uplus Z Zx V Vx)
          (auxiliaryMildGradMap p c Uplus Z Zx V Vx)

private theorem mul_le_add_mul_of_nonneg_left
    {a b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) :
    a * d ≤ (a + b) * d := by
  nlinarith [mul_nonneg hb hd]

private theorem mul_le_add_mul_of_nonneg_right
    {a b d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    b * d ≤ (a + b) * d := by
  nlinarith [mul_nonneg ha hd]

/--
Short-time contraction for the auxiliary mild map, from the standard
`A√T + BT < 1` rate estimates.

The value part is the `BT` Duhamel estimate; the gradient part is the
moving-frame `t^{-1/2}` estimate integrated to `A√T`.
-/
theorem auxiliaryMildMap_contraction
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B) :
    ∃ T K : ℝ,
      0 < T ∧ 0 ≤ K ∧ K < 1 ∧
        (∀ W Wx, AuxiliaryBarrierTrap κ κt D T W →
          AuxiliaryBarrierTrap κ κt D T
            (auxiliaryMildMap p c Uplus W Wx V Vx)) ∧
        (∀ W Wx Z Zx dist, 0 ≤ dist →
          AuxiliaryBarrierTrap κ κt D T W →
          AuxiliaryBarrierTrap κ κt D T Z →
          AuxiliaryC1DistanceBound T dist W Wx Z Zx →
            AuxiliaryC1DistanceBound T (K * dist)
              (auxiliaryMildMap p c Uplus W Wx V Vx)
              (auxiliaryMildGradMap p c Uplus W Wx V Vx)
              (auxiliaryMildMap p c Uplus Z Zx V Vx)
              (auxiliaryMildGradMap p c Uplus Z Zx V Vx)) := by
  obtain ⟨T, hT, hsmall⟩ :=
    exists_small_contraction_time_target H.hA_nonneg H.hB_nonneg one_pos
  let K : ℝ := A * Real.sqrt T + B * T
  have hK_nonneg : 0 ≤ K := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    dsimp [K]
    exact add_nonneg (mul_nonneg H.hA_nonneg hsqrt_nonneg)
      (mul_nonneg H.hB_nonneg hT.le)
  refine ⟨T, K, hT, hK_nonneg, hsmall, ?_, ?_⟩
  · intro W Wx hW
    exact H.mapsTo_of_small T hT hsmall W Wx hW
  · intro W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
    constructor
    · have hval :=
        H.value_diff_of_small T hT hsmall W Wx Z Zx dist hdist
          hW hZ hdistWZ t ht x
      have hBT_nonneg : 0 ≤ B * T := mul_nonneg H.hB_nonneg hT.le
      have hAroot_nonneg : 0 ≤ A * Real.sqrt T :=
        mul_nonneg H.hA_nonneg (Real.sqrt_nonneg T)
      exact hval.trans
        (mul_le_add_mul_of_nonneg_right
          (a := A * Real.sqrt T) (b := B * T) (d := dist)
          hAroot_nonneg hdist)
    · have hgrad :=
        H.gradient_diff_of_small T hT hsmall W Wx Z Zx dist hdist
          hW hZ hdistWZ t ht x
      have hBT_nonneg : 0 ≤ B * T := mul_nonneg H.hB_nonneg hT.le
      have hAroot_nonneg : 0 ≤ A * Real.sqrt T :=
        mul_nonneg H.hA_nonneg (Real.sqrt_nonneg T)
      exact hgrad.trans
        (mul_le_add_mul_of_nonneg_left
          (a := A * Real.sqrt T) (b := B * T) (d := dist)
          hBT_nonneg hdist)

/-- One finite horizon of the auxiliary mild problem, with the barrier trap. -/
def AuxiliaryMildSolutionOn
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D T : ℝ) (w wx : ℝ → ℝ → ℝ) : Prop :=
  0 < T ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      w t x = auxiliaryMildMap p c Uplus w wx V Vx t x) ∧
    AuxiliaryBarrierTrap κ κt D T w

/-- Reachability of one finite auxiliary-flow horizon. -/
def AuxiliaryReachableHorizon
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D T : ℝ) : Prop :=
  ∃ w wx : ℝ → ℝ → ℝ,
    AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx

def auxiliaryReachableHorizonSet
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Set ℝ :=
  {T | AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T}

def AuxiliaryReachableArbitrarilyLong
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∀ T > 0, AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T

noncomputable def auxiliaryFiniteMaximalReachableHorizon
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : ℝ :=
  sSup (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D)

def AuxiliaryReachablePast
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D T : ℝ) : Prop :=
  ∃ T' > T, AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T'

theorem auxiliaryReachable_le_finiteMaximalReachableHorizon
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D T : ℝ}
    (hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D))
    (hT : AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T) :
    T ≤ auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D := by
  exact le_csSup hbdd hT

theorem auxiliaryFiniteMaximalReachableHorizon_pos_of_local
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (hlocal : ∃ T > 0,
      AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T)
    (hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D)) :
    0 < auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D := by
  rcases hlocal with ⟨T, hTpos, hT⟩
  exact lt_of_lt_of_le hTpos
    (auxiliaryReachable_le_finiteMaximalReachableHorizon hbdd hT)

theorem not_auxiliaryReachablePast_finiteMaximalReachableHorizon
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D)) :
    ¬ AuxiliaryReachablePast p c Uplus V Vx κ κt D
        (auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D) := by
  intro h
  rcases h with ⟨T', hgt, hT'⟩
  exact not_lt_of_ge
    (auxiliaryReachable_le_finiteMaximalReachableHorizon hbdd hT') hgt

theorem auxiliaryMildSolutionOn_mono
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D Tshort Tlong : ℝ} {w wx : ℝ → ℝ → ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D Tlong w wx) :
    AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D Tshort w wx := by
  refine ⟨hTshort, ?_, ?_⟩
  · intro t ht x
    exact hsol.2.1 t ⟨ht.1, le_trans ht.2 hTL⟩ x
  · intro t ht x
    exact hsol.2.2 t ⟨ht.1, le_trans ht.2 hTL⟩ x

theorem auxiliaryReachableHorizon_mono
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D Tshort Tlong : ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hreach : AuxiliaryReachableHorizon p c Uplus V Vx κ κt D Tlong) :
    AuxiliaryReachableHorizon p c Uplus V Vx κ κt D Tshort := by
  rcases hreach with ⟨w, wx, hsol⟩
  exact ⟨w, wx, auxiliaryMildSolutionOn_mono hTshort hTL hsol⟩

theorem auxiliaryReachableArbitrarilyLong_of_not_bddAbove
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (hnbdd :
      ¬ BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D)) :
    AuxiliaryReachableArbitrarilyLong p c Uplus V Vx κ κt D := by
  intro T hT
  obtain ⟨Tlong, hTlong, hlt⟩ := (not_bddAbove_iff.mp hnbdd) T
  exact auxiliaryReachableHorizon_mono hT (le_of_lt hlt) hTlong

/-- Order-theoretic continuation skeleton: a finite reachable supremum plus a
restart theorem from the trap forces arbitrarily long reachable horizons. -/
theorem auxiliaryReachableArbitrarilyLong_of_finiteSup_extension
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (hlocal : ∃ T > 0,
      AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T)
    (hrealize :
      ∀ _hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D),
        AuxiliaryReachableHorizon p c Uplus V Vx κ κt D
          (auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D))
    (hextend_from_trap :
      ∀ _hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D),
        AuxiliaryReachablePast p c Uplus V Vx κ κt D
          (auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D)) :
    AuxiliaryReachableArbitrarilyLong p c Uplus V Vx κ κt D := by
  by_cases hbdd :
      BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D)
  · have _hTmax_pos :
        0 < auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D :=
      auxiliaryFiniteMaximalReachableHorizon_pos_of_local hlocal hbdd
    have _hrealized := hrealize hbdd
    exact False.elim
      (not_auxiliaryReachablePast_finiteMaximalReachableHorizon hbdd
        (hextend_from_trap hbdd))
  · exact auxiliaryReachableArbitrarilyLong_of_not_bddAbove hbdd

/-- A single global auxiliary mild solution obtained after gluing compatible
finite-horizon branches. -/
def AuxiliaryGlobalMildSolutionFor
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∃ w wx : ℝ → ℝ → ℝ,
    ∀ T > 0, AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx

def AuxiliaryGlobalSolutionGluingFromReachability
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  AuxiliaryReachableArbitrarilyLong p c Uplus V Vx κ κt D →
    AuxiliaryGlobalMildSolutionFor p c Uplus V Vx κ κt D

/-- Global auxiliary-flow existence from the local contraction output and the
standard trap-based continuation/gluing inputs. -/
theorem auxiliaryFlow_global
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (hlocal : ∃ T > 0,
      AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T)
    (hrealize :
      ∀ _hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D),
        AuxiliaryReachableHorizon p c Uplus V Vx κ κt D
          (auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D))
    (hextend_from_trap :
      ∀ _hbdd : BddAbove (auxiliaryReachableHorizonSet p c Uplus V Vx κ κt D),
        AuxiliaryReachablePast p c Uplus V Vx κ κt D
          (auxiliaryFiniteMaximalReachableHorizon p c Uplus V Vx κ κt D))
    (hglue :
      AuxiliaryGlobalSolutionGluingFromReachability p c Uplus V Vx κ κt D) :
    AuxiliaryGlobalMildSolutionFor p c Uplus V Vx κ κt D := by
  exact hglue
    (auxiliaryReachableArbitrarilyLong_of_finiteSup_extension
      hlocal hrealize hextend_from_trap)

theorem auxiliaryGlobalMildSolution_nonneg
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (H : AuxiliaryGlobalMildSolutionFor p c Uplus V Vx κ κt D) :
    ∃ w wx : ℝ → ℝ → ℝ,
      (∀ T > 0, AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx) ∧
      ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x ∧ w t x ≤ 1 := by
  rcases H with ⟨w, wx, hglobal⟩
  refine ⟨w, wx, hglobal, ?_⟩
  intro t ht x
  have hT : 0 < t + 1 := by linarith
  have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hsol := hglobal (t + 1) hT
  exact
    ⟨auxiliaryBarrierTrap_nonneg hsol.2.2 t ht_mem x,
      auxiliaryBarrierTrap_le_one hsol.2.2 t ht_mem x⟩

#print axioms auxiliaryMildGradMap
#print axioms auxiliaryBarrierTrap_abs_le_one
#print axioms auxiliaryMildMap_contraction
#print axioms auxiliaryReachableArbitrarilyLong_of_finiteSup_extension
#print axioms auxiliaryFlow_global
#print axioms auxiliaryGlobalMildSolution_nonneg

end ShenWork.PaperOne
