import ShenWork.PaperOne.WholeLineAuxiliaryExistence
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Short-time contraction and Banach extraction for the whole-line auxiliary
moving-frame mild map.

The analytic smallness part is closed from `AuxiliaryMildMapRateEstimates` by
the same `A * sqrt T + B * T < 1` choice used by `WholeLineMildMap`: the value
Duhamel leg contributes `B T`, and the moving-frame gradient Duhamel leg
contributes `A sqrt T`.  The final Banach step is stated against an explicit
closed-trap metric realization, because the project does not yet define the
actual complete trajectory-pair space for the auxiliary flow.
-/

/-- Short-time contraction for the auxiliary moving-frame mild map on the
closed wave-barrier trap. -/
theorem auxiliaryMildMap_contraction_on_smallTime
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B) :
    ∃ T0 K : ℝ,
      0 < T0 ∧ 0 ≤ K ∧ K < 1 ∧
        (∀ W Wx, AuxiliaryBarrierTrap κ κt D T0 W →
          AuxiliaryBarrierTrap κ κt D T0
            (auxiliaryMildMap p c Uplus W Wx V Vx)) ∧
        (∀ W Wx Z Zx dist, 0 ≤ dist →
          AuxiliaryBarrierTrap κ κt D T0 W →
          AuxiliaryBarrierTrap κ κt D T0 Z →
          AuxiliaryC1DistanceBound T0 dist W Wx Z Zx →
            AuxiliaryC1DistanceBound T0 (K * dist)
              (auxiliaryMildMap p c Uplus W Wx V Vx)
              (auxiliaryMildGradMap p c Uplus W Wx V Vx)
              (auxiliaryMildMap p c Uplus Z Zx V Vx)
              (auxiliaryMildGradMap p c Uplus Z Zx V Vx)) := by
  exact auxiliaryMildMap_contraction H

/-- A complete closed-trap metric model for the auxiliary pair map at a fixed
short time.  The fields say that elements of `X` evaluate to `(W, Wx)` pairs in
the trap, `F` evaluates to the mild map and its moving-frame gradient, and the
metric is compatible with the pointwise `AuxiliaryC1DistanceBound`. -/
structure AuxiliaryMildMapBanachRealization
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D T K : ℝ) (X : Type*) [MetricSpace X] where
  F : X → X
  seed : X
  eval : X → ℝ → ℝ → ℝ
  evalGrad : X → ℝ → ℝ → ℝ
  trap :
    ∀ z, AuxiliaryBarrierTrap κ κt D T (eval z)
  value_comm :
    ∀ z, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      eval (F z) t x =
        auxiliaryMildMap p c Uplus (eval z) (evalGrad z) V Vx t x
  grad_comm :
    ∀ z, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      evalGrad (F z) t x =
        auxiliaryMildGradMap p c Uplus (eval z) (evalGrad z) V Vx t x
  dist_controls :
    ∀ z y,
      AuxiliaryC1DistanceBound T (dist z y)
        (eval z) (evalGrad z) (eval y) (evalGrad y)
  dist_le_of_c1 :
    ∀ z y E, 0 ≤ E →
      AuxiliaryC1DistanceBound T E
        (eval z) (evalGrad z) (eval y) (evalGrad y) →
      dist z y ≤ E

/-- The same realization with its complete metric-space instances packaged, so
the complete closed-trap space may depend on the small horizon. -/
structure AuxiliaryMildMapBanachRealizationData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ)
    (C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D) where
  X : Type*
  [instMetric : MetricSpace X]
  [instComplete : CompleteSpace X]
  [instNonempty : Nonempty X]
  realization :
    AuxiliaryMildMapBanachRealization p c Uplus V Vx κ κt D C.T C.K X

/-- The closed-trap realization inherits a genuine `ContractingWith` structure
from the pointwise mild-map contraction data. -/
theorem auxiliaryMildMapBanachRealization_contracting
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D)
    {X : Type*} [MetricSpace X]
    (R : AuxiliaryMildMapBanachRealization p c Uplus V Vx κ κt D C.T C.K X) :
    ContractingWith ⟨C.K, C.hK_nonneg⟩ R.F := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using C.hK_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro z y
    have hdist_nonneg : 0 ≤ dist z y := dist_nonneg
    have hraw :
        AuxiliaryC1DistanceBound C.T (C.K * dist z y)
          (auxiliaryMildMap p c Uplus (R.eval z) (R.evalGrad z) V Vx)
          (auxiliaryMildGradMap p c Uplus (R.eval z) (R.evalGrad z) V Vx)
          (auxiliaryMildMap p c Uplus (R.eval y) (R.evalGrad y) V Vx)
          (auxiliaryMildGradMap p c Uplus (R.eval y) (R.evalGrad y) V Vx) :=
      C.contraction (R.eval z) (R.evalGrad z) (R.eval y) (R.evalGrad y)
        (dist z y) hdist_nonneg (R.trap z) (R.trap y)
        (R.dist_controls z y)
    have himage :
        AuxiliaryC1DistanceBound C.T (C.K * dist z y)
          (R.eval (R.F z)) (R.evalGrad (R.F z))
          (R.eval (R.F y)) (R.evalGrad (R.F y)) := by
      intro t ht x
      have hx := hraw t ht x
      constructor
      · simpa [R.value_comm z t ht x, R.value_comm y t ht x] using hx.1
      · simpa [R.grad_comm z t ht x, R.grad_comm y t ht x] using hx.2
    have hE_nonneg : 0 ≤ C.K * dist z y :=
      mul_nonneg C.hK_nonneg hdist_nonneg
    have hdist :=
      R.dist_le_of_c1 (R.F z) (R.F y) (C.K * dist z y)
        hE_nonneg himage
    simpa using hdist

/-- Banach fixed-point extraction for one already constructed auxiliary
small-time contraction datum. -/
theorem auxiliaryFlow_localExists_of_contractionData
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D : ℝ}
    (C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D)
    (Rdata :
      AuxiliaryMildMapBanachRealizationData p c Uplus V Vx κ κt D C) :
    AuxiliaryReachableHorizon p c Uplus V Vx κ κt D C.T := by
  letI := Rdata.instMetric
  letI := Rdata.instComplete
  letI := Rdata.instNonempty
  let R := Rdata.realization
  have hcontract :
      ContractingWith ⟨C.K, C.hK_nonneg⟩ R.F :=
    auxiliaryMildMapBanachRealization_contracting C R
  have hseed : edist R.seed (R.F R.seed) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hz_fix, _hz_tendsto, _hz_rate⟩ :=
    hcontract.exists_fixedPoint R.seed hseed
  refine ⟨R.eval z, R.evalGrad z, ?_⟩
  refine ⟨C.hT_pos, ?_, R.trap z⟩
  intro t ht x
  calc
    R.eval z t x = R.eval (R.F z) t x := by
      rw [hz_fix.eq]
    _ = auxiliaryMildMap p c Uplus (R.eval z) (R.evalGrad z) V Vx t x :=
      R.value_comm z t ht x

/-- Local auxiliary-flow existence from the closed small-time contraction and a
closed-trap Banach realization for that contraction datum. -/
theorem auxiliaryFlow_localExists
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D,
        AuxiliaryMildMapBanachRealizationData p c Uplus V Vx κ κt D C) :
    ∃ T0 > 0, AuxiliaryReachableHorizon p c Uplus V Vx κ κt D T0 := by
  obtain ⟨T0, K, hT0, hK_nonneg, hK_lt_one, hmapsTo, hcontr⟩ :=
    auxiliaryMildMap_contraction_on_smallTime H
  let C : AuxiliaryMildMapContractionData p c Uplus V Vx κ κt D :=
    { T := T0
      hT_pos := hT0
      K := K
      hK_nonneg := hK_nonneg
      hK_lt_one := hK_lt_one
      mapsTo := hmapsTo
      contraction := hcontr }
  exact ⟨C.T, C.hT_pos, auxiliaryFlow_localExists_of_contractionData C (hrealize C)⟩

#print axioms auxiliaryMildMap_contraction_on_smallTime
#print axioms auxiliaryMildMapBanachRealization_contracting
#print axioms auxiliaryFlow_localExists_of_contractionData
#print axioms auxiliaryFlow_localExists

end ShenWork.PaperOne
