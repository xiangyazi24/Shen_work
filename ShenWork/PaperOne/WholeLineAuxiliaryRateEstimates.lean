import ShenWork.PaperOne.WholeLineAuxiliaryExistence
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
# Moving-frame auxiliary mild-map rate-estimate producer

This file packages the exact analytic frontiers needed to produce

`AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B`.

Why the requested closed theorem cannot be hypothesis-free:

* `AuxiliaryBarrierTrap κ κt D T W` is imposed for all
  `t ∈ Set.Icc 0 T`, so the `mapsTo` field for
  `auxiliaryMildMap p c Uplus ...` includes the time slice `t = 0`.
* At `t = 0`, the mild map is the initial profile leg. Therefore a
  no-hypothesis maps-to theorem would force `Uplus` to lie between
  `lowerBarrier κ κt D` and `upperBarrier κ` pointwise.
* The existing structure also contains no assumptions giving:
  - frozen-source barrier corrections;
  - frozen-source value Lipschitz estimates;
  - frozen-source gradient Lipschitz estimates;
  - measurability/integrability of the source differences.

Those are genuine analytic inputs, not Lean/Mathlib elaboration problems. This file
therefore isolates them as named frontier propositions and proves the packaging
theorem without `sorry`, `admit`, or custom axioms.
-/

/-- Exact maps-to frontier for the moving-frame auxiliary mild map.

This is the concrete goal left for the parabolic comparison / barrier layer:
for every sufficiently small horizon, the mild map preserves the exponential
barrier trap. -/
def AuxiliaryMildMapMapsToFrontier
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∀ W Wx, AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T
        (auxiliaryMildMap p c Uplus W Wx V Vx)

/-- Exact value-Lipschitz frontier for the moving-frame auxiliary mild map.

This is the `BT` leg: the homogeneous heat terms cancel, and the value Duhamel
leg is controlled by a frozen-source Lipschitz estimate integrated over a time
interval of length `T`. -/
def AuxiliaryMildMapValueDiffFrontier
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∀ W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |auxiliaryMildMap p c Uplus W Wx V Vx t x -
            auxiliaryMildMap p c Uplus Z Zx V Vx t x| ≤
              B * T * dist

/-- Exact gradient-Lipschitz frontier for the moving-frame auxiliary mild map.

This is the `A√T` leg: the homogeneous gradient terms cancel, and the gradient
Duhamel leg is controlled by the moving-frame `t^{-1/2}` kernel estimate. -/
def AuxiliaryMildMapGradientDiffFrontier
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∀ W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |auxiliaryMildGradMap p c Uplus W Wx V Vx t x -
            auxiliaryMildGradMap p c Uplus Z Zx V Vx t x| ≤
              A * Real.sqrt T * dist

/-- All analytic frontiers needed to produce the rate-estimate package. -/
structure AuxiliaryMildMapRateEstimateFrontiers
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop where
  hA_nonneg : 0 ≤ A
  hB_nonneg : 0 ≤ B
  mapsTo :
    AuxiliaryMildMapMapsToFrontier p c Uplus V Vx κ κt D A B
  value_diff :
    AuxiliaryMildMapValueDiffFrontier p c Uplus V Vx κ κt D A B
  gradient_diff :
    AuxiliaryMildMapGradientDiffFrontier p c Uplus V Vx κ κt D A B

theorem AuxiliaryMildMapRateEstimateFrontiers.hA
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B) :
    0 ≤ A :=
  H.hA_nonneg

theorem AuxiliaryMildMapRateEstimateFrontiers.hB
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B) :
    0 ≤ B :=
  H.hB_nonneg

theorem AuxiliaryMildMapRateEstimateFrontiers.mapsTo_of_small
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapMapsToFrontier p c Uplus V Vx κ κt D A B :=
  H.mapsTo

theorem AuxiliaryMildMapRateEstimateFrontiers.value_diff_of_small
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapValueDiffFrontier p c Uplus V Vx κ κt D A B :=
  H.value_diff

theorem AuxiliaryMildMapRateEstimateFrontiers.gradient_diff_of_small
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapGradientDiffFrontier p c Uplus V Vx κ κt D A B :=
  H.gradient_diff

/-- Producer from the exact analytic frontiers to the downstream rate-estimate package.

This is the theorem consumed by `auxiliaryMildMap_contraction`; once the three
frontier estimates are proved from the moving-frame heat kernel and the frozen
nonlinearity, this closes the small-time contraction interface. -/
theorem auxiliaryMildMap_rateEstimates
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B where
  hA_nonneg := H.hA_nonneg
  hB_nonneg := H.hB_nonneg
  mapsTo_of_small := H.mapsTo
  value_diff_of_small := H.value_diff
  gradient_diff_of_small := H.gradient_diff

/-!
## Lower-level concrete goals still to prove

The following `Prop` definitions are the exact concrete analytic statements that
a future file should discharge from the moving-frame semigroup bounds and the
frozen nonlinearity.

They are intentionally definitions, not axioms.
-/

/-- Concrete initial-barrier hypothesis that is necessary because the trap includes
the time slice `t = 0`. -/
def AuxiliaryInitialProfileInBarrierTrap
    (Uplus : ℝ → ℝ) (κ κt D : ℝ) : Prop :=
  ∀ x, lowerBarrier κ κt D x ≤ Uplus x ∧ Uplus x ≤ upperBarrier κ x

/-- Concrete source value-Lipschitz goal.  This is the estimate that should produce
the `B*T` part of the rate package after applying the value Duhamel bound. -/
def AuxiliaryFrozenSourceValueLipschitzGoal
    (p : CMParams) (V Vx : ℝ → ℝ) (κ κt D B : ℝ) : Prop :=
  ∀ T W Wx Z Zx dist, 0 ≤ dist →
    AuxiliaryBarrierTrap κ κt D T W →
    AuxiliaryBarrierTrap κ κt D T Z →
    AuxiliaryC1DistanceBound T dist W Wx Z Zx →
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
        |auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y -
          auxiliaryFrozenNonlinearity p (Z s) (Zx s) V Vx y| ≤
            B * dist

/-- Concrete source gradient-Lipschitz goal.  This is the estimate that should
produce the `A*sqrt T` part after applying the moving-frame gradient Duhamel
kernel bound. -/
def AuxiliaryFrozenSourceGradientLipschitzGoal
    (p : CMParams) (V Vx : ℝ → ℝ) (κ κt D A : ℝ) : Prop :=
  ∀ T W Wx Z Zx dist, 0 ≤ dist →
    AuxiliaryBarrierTrap κ κt D T W →
    AuxiliaryBarrierTrap κ κt D T Z →
    AuxiliaryC1DistanceBound T dist W Wx Z Zx →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
        |auxiliaryGradDuhamel p 0 W Wx V Vx t x -
          auxiliaryGradDuhamel p 0 Z Zx V Vx t x| ≤
            A * Real.sqrt T * dist

/-- Concrete maps-to goal.  This is the parabolic comparison/barrier-correction
statement required to show that the mild image remains trapped. -/
def AuxiliaryMildMapMapsToConcreteGoal
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  AuxiliaryInitialProfileInBarrierTrap Uplus κ κt D →
    AuxiliaryMildMapMapsToFrontier p c Uplus V Vx κ κt D A B

/-- Concrete full rate-estimate goal, split into the necessary analytic ingredients.

This is the honest replacement for a false no-hypothesis theorem. -/
def AuxiliaryMildMapConcreteRateGoal
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    AuxiliaryInitialProfileInBarrierTrap Uplus κ κt D ∧
    AuxiliaryMildMapMapsToFrontier p c Uplus V Vx κ κt D A B ∧
    AuxiliaryMildMapValueDiffFrontier p c Uplus V Vx κ κt D A B ∧
    AuxiliaryMildMapGradientDiffFrontier p c Uplus V Vx κ κt D A B

/-- Package the concrete full goal into the frontier structure. -/
theorem AuxiliaryMildMapConcreteRateGoal.to_frontiers
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapConcreteRateGoal p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B := by
  rcases H with ⟨hA, hB, _hinit, hmaps, hval, hgrad⟩
  exact
    { hA_nonneg := hA
      hB_nonneg := hB
      mapsTo := hmaps
      value_diff := hval
      gradient_diff := hgrad }

/-- Package the concrete full goal directly into `AuxiliaryMildMapRateEstimates`. -/
theorem auxiliaryMildMap_rateEstimates_of_concreteGoal
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapConcreteRateGoal p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B :=
  auxiliaryMildMap_rateEstimates H.to_frontiers

#check auxiliaryMildMap_rateEstimates
#check auxiliaryMildMap_rateEstimates_of_concreteGoal

#print axioms auxiliaryMildMap_rateEstimates
#print axioms auxiliaryMildMap_rateEstimates_of_concreteGoal

end ShenWork.PaperOne
