import ShenWork.PaperOne.WholeLineAuxiliaryRateEstimates
import ShenWork.PaperOne.WholeLineDuhamelDifferentiation
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology
open intervalIntegral

noncomputable section

namespace ShenWork.PaperOne

/-!
# Concrete moving-frame auxiliary rate-estimate frontiers

This file produces `AuxiliaryMildMapRateEstimateFrontiers` for the concrete
moving-frame auxiliary mild map.

The value and gradient Lipschitz frontiers are discharged from the banked
moving-frame value/gradient Duhamel estimates.  The remaining analytic inputs
are named explicitly:

* `mapsTo` is the exponential-barrier comparison/frontier.
* `duhamel_sub` and `grad_duhamel_sub` are the integral-linearity bridges
  identifying a difference of Duhamel terms with the Duhamel term of the
  source difference.
* measurability/integrability hypotheses are stated exactly where the banked
  Duhamel estimates require them.

No new logical primitive is introduced.
-/

/-- Difference of two frozen auxiliary sources. -/
def auxiliaryFrozenSourceDiff
    (p : CMParams)
    (W Wx Z Zx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ)
    (s y : ℝ) : ℝ :=
  auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y -
    auxiliaryFrozenNonlinearity p (Z s) (Zx s) V Vx y

/-- Value-Duhamel term for the difference of two frozen auxiliary sources. -/
def auxiliaryFrozenSourceDiffDuhamel
    (p : CMParams) (c : ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  movingFrameDuhamel c
    (fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) t x

/-- Gradient-Duhamel term for the difference of two frozen auxiliary sources. -/
def auxiliaryFrozenSourceDiffGradDuhamel
    (p : CMParams) (c : ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  movingFrameGradDuhamel c
    (fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) t x

/--
Concrete data needed to turn a pointwise source Lipschitz estimate into the
`B*T` value frontier.

The `duhamel_sub` field is the standard integral-linearity bridge
`Duhamel(F_W) - Duhamel(F_Z) = Duhamel(F_W - F_Z)`.
-/
structure AuxiliaryValueDiffDuhamelData
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ)
    (κ κt D B : ℝ) : Prop where
  source_bound :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
          |auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y| ≤ B * dist
  source_measurable :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∀ s ∈ Set.Icc (0 : ℝ) t,
            AEStronglyMeasurable
              (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) volume
  duhamel_sub :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          auxiliaryDuhamel p c W Wx V Vx t x -
              auxiliaryDuhamel p c Z Zx V Vx t x =
            auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x

/--
Concrete data needed to turn the moving-frame singular gradient-kernel estimate
into the `A*sqrt T` gradient frontier.

The slice bound is stated with coefficient `(A * dist) / 2`, because the banked
Duhamel lemma integrates `τ^(-1/2)` to `2 * sqrt t`.
-/
structure AuxiliaryGradientDiffDuhamelData
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A : ℝ) : Prop where
  grad_integrable :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          IntervalIntegrable
            (fun s : ℝ =>
              movingFrameHeatGradOp c (t - s)
                (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x)
            volume 0 t
  grad_slice_bound :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          ∀ s, 0 ≤ s → s < t →
            |movingFrameHeatGradOp c (t - s)
              (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x|
              ≤ ((A * dist) / 2) * (t - s) ^ (-(1 / 2 : ℝ))
  grad_duhamel_sub :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          auxiliaryGradDuhamel p c W Wx V Vx t x -
              auxiliaryGradDuhamel p c Z Zx V Vx t x =
            auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x
  grad_zero_bound :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ x,
          |auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx 0 x|
            ≤ A * Real.sqrt T * dist

/-- The exact exponential-barrier maps-to input. -/
structure AuxiliaryMapsToBarrierData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop where
  mapsTo :
    AuxiliaryMildMapMapsToFrontier p c Uplus V Vx κ κt D A B

/-- Value difference for the source-difference Duhamel term. -/
theorem auxiliaryFrozenSourceDiffDuhamel_abs_le_of_valueData
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (H : AuxiliaryValueDiffDuhamelData p c V Vx κ κt D B) :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x|
            ≤ B * T * dist := by
  intro T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  have hC : 0 ≤ B * dist := mul_nonneg hB hdist
  have hduh :
      |movingFrameDuhamel c
          (fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y)
          t x| ≤ (B * dist) * t := by
    refine movingFrameDuhamel_abs_le_of_bound
      (c := c) (C := B * dist) (t := t)
      (F := fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y)
      ht.1 hC ?_ ?_ x
    · intro s hs y
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2 ht.2⟩
      exact H.source_bound T W Wx Z Zx dist hdist hW hZ hdistWZ s hsT y
    · intro s hs
      exact H.source_measurable T W Wx Z Zx dist hdist hW hZ hdistWZ t ht s hs
  have hBT : B * t ≤ B * T := mul_le_mul_of_nonneg_left ht.2 hB
  have hBTdist : B * t * dist ≤ B * T * dist :=
    mul_le_mul_of_nonneg_right hBT hdist
  calc
    |auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x|
        = |movingFrameDuhamel c
            (fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y)
            t x| := rfl
    _ ≤ (B * dist) * t := hduh
    _ = B * t * dist := by ring
    _ ≤ B * T * dist := hBTdist

/-- The value frontier from concrete source-difference data. -/
theorem auxiliaryMildMap_valueDiffFrontier_of_valueData
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (hB : 0 ≤ B)
    (H : AuxiliaryValueDiffDuhamelData p c V Vx κ κt D B) :
    AuxiliaryMildMapValueDiffFrontier p c Uplus V Vx κ κt D A B := by
  intro T hT _hsmall W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  have hcancel :
      auxiliaryMildMap p c Uplus W Wx V Vx t x -
          auxiliaryMildMap p c Uplus Z Zx V Vx t x =
        auxiliaryDuhamel p c W Wx V Vx t x -
          auxiliaryDuhamel p c Z Zx V Vx t x := by
    unfold auxiliaryMildMap
    ring
  have hsub :=
    H.duhamel_sub T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  have hbound :=
    auxiliaryFrozenSourceDiffDuhamel_abs_le_of_valueData
      (p := p) (c := c) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (B := B)
      hB H T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  calc
    |auxiliaryMildMap p c Uplus W Wx V Vx t x -
        auxiliaryMildMap p c Uplus Z Zx V Vx t x|
        = |auxiliaryDuhamel p c W Wx V Vx t x -
            auxiliaryDuhamel p c Z Zx V Vx t x| := by rw [hcancel]
    _ = |auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x| := by rw [hsub]
    _ ≤ B * T * dist := hbound

/-- Gradient difference for the source-difference gradient-Duhamel term. -/
theorem auxiliaryFrozenSourceDiffGradDuhamel_abs_le_of_gradientData
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A : ℝ}
    (hA : 0 ≤ A)
    (H : AuxiliaryGradientDiffDuhamelData p c V Vx κ κt D A) :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x|
            ≤ A * Real.sqrt T * dist := by
  intro T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  by_cases ht0 : t = 0
  · subst t
    exact H.grad_zero_bound T W Wx Z Zx dist hdist hW hZ hdistWZ x
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hgrad :=
      movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound
        (c := c) (A := (A * dist) / 2) (t := t)
        (F := fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y)
        htpos x
        (H.grad_integrable T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x)
        (H.grad_slice_bound T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x)
    have hsqr : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
    have hAd : 0 ≤ A * dist := mul_nonneg hA hdist
    have hmul :
        (A * dist) * Real.sqrt t ≤ (A * dist) * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hsqr hAd
    calc
      |auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x|
          = |movingFrameGradDuhamel c
              (fun s y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y)
              t x| := rfl
      _ ≤ ((A * dist) / 2) * (2 * Real.sqrt t) := hgrad
      _ = (A * dist) * Real.sqrt t := by ring
      _ ≤ (A * dist) * Real.sqrt T := hmul
      _ = A * Real.sqrt T * dist := by ring

/-- The gradient frontier from concrete singular-kernel Duhamel data. -/
theorem auxiliaryMildMap_gradientDiffFrontier_of_gradientData
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (hA : 0 ≤ A)
    (H : AuxiliaryGradientDiffDuhamelData p c V Vx κ κt D A) :
    AuxiliaryMildMapGradientDiffFrontier p c Uplus V Vx κ κt D A B := by
  intro T hT _hsmall W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  have hcancel :
      auxiliaryMildGradMap p c Uplus W Wx V Vx t x -
          auxiliaryMildGradMap p c Uplus Z Zx V Vx t x =
        auxiliaryGradDuhamel p c W Wx V Vx t x -
          auxiliaryGradDuhamel p c Z Zx V Vx t x := by
    unfold auxiliaryMildGradMap
    ring
  have hsub :=
    H.grad_duhamel_sub T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  have hbound :=
    auxiliaryFrozenSourceDiffGradDuhamel_abs_le_of_gradientData
      (p := p) (c := c) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (A := A)
      hA H T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x
  calc
    |auxiliaryMildGradMap p c Uplus W Wx V Vx t x -
        auxiliaryMildGradMap p c Uplus Z Zx V Vx t x|
        = |auxiliaryGradDuhamel p c W Wx V Vx t x -
            auxiliaryGradDuhamel p c Z Zx V Vx t x| := by rw [hcancel]
    _ = |auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x| := by rw [hsub]
    _ ≤ A * Real.sqrt T * dist := hbound

/--
Concrete data sufficient to build the exact frontier package for the
moving-frame auxiliary mild map.
-/
structure AuxiliaryConcreteMovingFrameRateFrontierData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop where
  hA_nonneg : 0 ≤ A
  hB_nonneg : 0 ≤ B
  mapsTo :
    AuxiliaryMapsToBarrierData p c Uplus V Vx κ κt D A B
  value :
    AuxiliaryValueDiffDuhamelData p c V Vx κ κt D B
  gradient :
    AuxiliaryGradientDiffDuhamelData p c V Vx κ κt D A

/--
Produce `AuxiliaryMildMapRateEstimateFrontiers` for the concrete moving-frame
auxiliary mild map from the named barrier/source/Duhamel data.
-/
theorem AuxiliaryConcreteMovingFrameRateFrontierData.to_frontiers
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryConcreteMovingFrameRateFrontierData
      p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapRateEstimateFrontiers p c Uplus V Vx κ κt D A B where
  hA_nonneg := H.hA_nonneg
  hB_nonneg := H.hB_nonneg
  mapsTo := H.mapsTo.mapsTo
  value_diff :=
    auxiliaryMildMap_valueDiffFrontier_of_valueData
      (p := p) (c := c) (Uplus := Uplus) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (A := A) (B := B)
      H.hB_nonneg H.value
  gradient_diff :=
    auxiliaryMildMap_gradientDiffFrontier_of_gradientData
      (p := p) (c := c) (Uplus := Uplus) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (A := A) (B := B)
      H.hA_nonneg H.gradient

/--
Direct producer of the downstream `AuxiliaryMildMapRateEstimates` package.
-/
theorem auxiliaryMildMap_rateEstimates_of_concreteMovingFrameData
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryConcreteMovingFrameRateFrontierData
      p c Uplus V Vx κ κt D A B) :
    AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D A B :=
  auxiliaryMildMap_rateEstimates H.to_frontiers

end ShenWork.PaperOne
