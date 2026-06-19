import ShenWork.PaperOne.WholeLineAuxiliaryRateFrontiers
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology
open intervalIntegral

noncomputable section

namespace ShenWork.PaperOne

/-!
# Concrete moving-frame auxiliary rate data from banked Duhamel bounds

This file discharges `AuxiliaryConcreteMovingFrameRateFrontierData` from:

* the banked value-Duhamel estimate `movingFrameDuhamel_abs_le_of_bound`;
* the banked gradient-Duhamel estimate
  `movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound`;
* the banked moving-frame heat-gradient pointwise estimate
  `movingFrameHeatGradOp_norm_le_rpow`.

The only explicit hypotheses left are the genuinely external ones:

* `mapsTo`: the exponential-barrier comparison/mapping theorem;
* `source_bound`: the pointwise frozen-source Lipschitz estimate;
* `source_measurable`: measurability for the value Duhamel estimate;
* `grad_integrable`: integrability for the singular gradient Duhamel estimate;
* `duhamel_sub` / `grad_duhamel_sub`: the integral-linearity bridges identifying
  differences of Duhamel terms with Duhamel terms of source differences.

No `sorry`, `admit`, or custom axiom is introduced.
-/

/-- The explicit gradient rate coming from
`∫₀ᵗ (t-s)^(-1/2) ds = 2√t` and the banked whole-line gradient heat
constant `2 / sqrt (4π)`. -/
def auxiliaryMovingFrameGradientRate (B : ℝ) : ℝ :=
  4 * B / Real.sqrt (4 * Real.pi)

theorem auxiliaryMovingFrameGradientRate_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ auxiliaryMovingFrameGradientRate B := by
  unfold auxiliaryMovingFrameGradientRate
  exact div_nonneg (mul_nonneg (by norm_num) hB) (Real.sqrt_nonneg _)

/-- Construct the value-Duhamel data from the pointwise source-difference bound,
measurability, and the Duhamel-linearity bridge. -/
theorem auxiliaryValueDiffDuhamelData_of_sourceBound
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (source_bound :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y| ≤ B * dist)
    (source_measurable :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∀ s ∈ Set.Icc (0 : ℝ) t,
              AEStronglyMeasurable
                (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) volume)
    (duhamel_sub :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            auxiliaryDuhamel p c W Wx V Vx t x -
                auxiliaryDuhamel p c Z Zx V Vx t x =
              auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x) :
    AuxiliaryValueDiffDuhamelData p c V Vx κ κt D B where
  source_bound := source_bound
  source_measurable := source_measurable
  duhamel_sub := duhamel_sub

/-- The banked moving-frame gradient estimate converts a value source bound
`B * dist` into the gradient slice bound with explicit coefficient
`auxiliaryMovingFrameGradientRate B`. -/
theorem auxiliary_grad_slice_bound_of_sourceBound
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (source_bound :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y| ≤ B * dist) :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          ∀ s, 0 ≤ s → s < t →
            |movingFrameHeatGradOp c (t - s)
              (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x|
              ≤ (((auxiliaryMovingFrameGradientRate B) * dist) / 2) *
                  (t - s) ^ (-(1 / 2 : ℝ)) := by
  intro T W Wx Z Zx dist hdist hW hZ hdistWZ t ht x s hs0 hst
  have hsT : s ∈ Set.Icc (0 : ℝ) T :=
    ⟨hs0, le_trans (le_of_lt hst) ht.2⟩
  have hM : 0 ≤ B * dist := mul_nonneg hB hdist
  have hbase :=
    movingFrameHeatGradOp_norm_le_rpow
      (c := c)
      (τ := t - s)
      (M := B * dist)
      (f := fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y)
      (sub_pos.mpr hst)
      hM
      (source_bound T W Wx Z Zx dist hdist hW hZ hdistWZ s hsT)
      x
  calc
    |movingFrameHeatGradOp c (t - s)
        (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x|
        = ‖movingFrameHeatGradOp c (t - s)
            (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ ((2 / Real.sqrt (4 * Real.pi)) * (B * dist)) *
          (t - s) ^ (-(1 / 2 : ℝ)) := hbase
    _ = (((auxiliaryMovingFrameGradientRate B) * dist) / 2) *
          (t - s) ^ (-(1 / 2 : ℝ)) := by
          unfold auxiliaryMovingFrameGradientRate
          ring_nf

/-- At `t = 0`, the source-difference gradient Duhamel term is zero, hence it
satisfies the required `A√T` bound. -/
theorem auxiliary_sourceDiffGradDuhamel_zero_bound
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B) :
    ∀ T W Wx Z Zx dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryC1DistanceBound T dist W Wx Z Zx →
        ∀ x,
          |auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx 0 x|
            ≤ auxiliaryMovingFrameGradientRate B * Real.sqrt T * dist := by
  intro T W Wx Z Zx dist hdist _hW _hZ _hdistWZ x
  have hA : 0 ≤ auxiliaryMovingFrameGradientRate B :=
    auxiliaryMovingFrameGradientRate_nonneg hB
  have hnonneg :
      0 ≤ auxiliaryMovingFrameGradientRate B * Real.sqrt T * dist :=
    mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg T)) hdist
  have hzero :
      auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx 0 x = 0 := by
    simp [auxiliaryFrozenSourceDiffGradDuhamel, movingFrameGradDuhamel]
  rw [hzero, abs_zero]
  exact hnonneg

/-- Construct the singular-gradient Duhamel data from the banked heat-gradient
bound, the pointwise source-difference bound, integrability, and the gradient
Duhamel-linearity bridge. -/
theorem auxiliaryGradientDiffDuhamelData_of_sourceBound
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (source_bound :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y| ≤ B * dist)
    (grad_integrable :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            IntervalIntegrable
              (fun s : ℝ =>
                movingFrameHeatGradOp c (t - s)
                  (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x)
              volume 0 t)
    (grad_duhamel_sub :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            auxiliaryGradDuhamel p c W Wx V Vx t x -
                auxiliaryGradDuhamel p c Z Zx V Vx t x =
              auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x) :
    AuxiliaryGradientDiffDuhamelData p c V Vx κ κt D
      (auxiliaryMovingFrameGradientRate B) where
  grad_integrable := grad_integrable
  grad_slice_bound :=
    auxiliary_grad_slice_bound_of_sourceBound
      (p := p) (c := c) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (B := B)
      hB source_bound
  grad_duhamel_sub := grad_duhamel_sub
  grad_zero_bound :=
    auxiliary_sourceDiffGradDuhamel_zero_bound
      (p := p) (c := c) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (B := B)
      hB

/--
Concrete moving-frame frontier data from banked Duhamel estimates.

The explicit constants are:

* value rate: `B`;
* gradient rate: `auxiliaryMovingFrameGradientRate B = 4*B/sqrt(4π)`.

The only non-Duhamel input is `mapsTo`, the exponential-barrier comparison
statement for the concrete map.
-/
theorem auxiliaryConcreteMovingFrameRateFrontierData_of_bankedDuhamel
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (mapsTo :
      AuxiliaryMapsToBarrierData p c Uplus V Vx κ κt D
        (auxiliaryMovingFrameGradientRate B) B)
    (source_bound :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y| ≤ B * dist)
    (source_measurable :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∀ s ∈ Set.Icc (0 : ℝ) t,
              AEStronglyMeasurable
                (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) volume)
    (duhamel_sub :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            auxiliaryDuhamel p c W Wx V Vx t x -
                auxiliaryDuhamel p c Z Zx V Vx t x =
              auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x)
    (grad_integrable :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            IntervalIntegrable
              (fun s : ℝ =>
                movingFrameHeatGradOp c (t - s)
                  (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x)
              volume 0 t)
    (grad_duhamel_sub :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            auxiliaryGradDuhamel p c W Wx V Vx t x -
                auxiliaryGradDuhamel p c Z Zx V Vx t x =
              auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x) :
    AuxiliaryConcreteMovingFrameRateFrontierData p c Uplus V Vx κ κt D
      (auxiliaryMovingFrameGradientRate B) B where
  hA_nonneg := auxiliaryMovingFrameGradientRate_nonneg hB
  hB_nonneg := hB
  mapsTo := mapsTo
  value :=
    auxiliaryValueDiffDuhamelData_of_sourceBound
      (p := p) (c := c) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (B := B)
      source_bound source_measurable duhamel_sub
  gradient :=
    auxiliaryGradientDiffDuhamelData_of_sourceBound
      (p := p) (c := c) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (B := B)
      hB source_bound grad_integrable grad_duhamel_sub

/-- Direct downstream rate-estimate package from the banked concrete Duhamel
estimates. -/
theorem auxiliaryMildMap_rateEstimates_of_bankedDuhamel
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (mapsTo :
      AuxiliaryMapsToBarrierData p c Uplus V Vx κ κt D
        (auxiliaryMovingFrameGradientRate B) B)
    (source_bound :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y| ≤ B * dist)
    (source_measurable :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∀ s ∈ Set.Icc (0 : ℝ) t,
              AEStronglyMeasurable
                (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) volume)
    (duhamel_sub :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            auxiliaryDuhamel p c W Wx V Vx t x -
                auxiliaryDuhamel p c Z Zx V Vx t x =
              auxiliaryFrozenSourceDiffDuhamel p c W Wx Z Zx V Vx t x)
    (grad_integrable :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            IntervalIntegrable
              (fun s : ℝ =>
                movingFrameHeatGradOp c (t - s)
                  (fun y => auxiliaryFrozenSourceDiff p W Wx Z Zx V Vx s y) x)
              volume 0 t)
    (grad_duhamel_sub :
      ∀ T W Wx Z Zx dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryC1DistanceBound T dist W Wx Z Zx →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            auxiliaryGradDuhamel p c W Wx V Vx t x -
                auxiliaryGradDuhamel p c Z Zx V Vx t x =
              auxiliaryFrozenSourceDiffGradDuhamel p c W Wx Z Zx V Vx t x) :
    AuxiliaryMildMapRateEstimates p c Uplus V Vx κ κt D
      (auxiliaryMovingFrameGradientRate B) B :=
  auxiliaryMildMap_rateEstimates_of_concreteMovingFrameData
    (auxiliaryConcreteMovingFrameRateFrontierData_of_bankedDuhamel
      (p := p) (c := c) (Uplus := Uplus) (V := V) (Vx := Vx)
      (κ := κ) (κt := κt) (D := D) (B := B)
      hB mapsTo source_bound source_measurable duhamel_sub
      grad_integrable grad_duhamel_sub)

#check auxiliaryConcreteMovingFrameRateFrontierData_of_bankedDuhamel
#check auxiliaryMildMap_rateEstimates_of_bankedDuhamel

#print axioms auxiliaryConcreteMovingFrameRateFrontierData_of_bankedDuhamel
#print axioms auxiliaryMildMap_rateEstimates_of_bankedDuhamel

end ShenWork.PaperOne
