import ShenWork.PaperOne.WholeLineAuxiliaryDivergenceLocal
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
# Divergence-form auxiliary global flow

This file keeps the divergence-form continuation and family interfaces separate
from the older value/gradient auxiliary flow.  The bottom analytic inputs are
split so that no measurability is inferred from the bare barrier trap: source
measurability is only discharged for continuous spatial slices.
-/

/-- Spatial-slice continuity on a finite time window. -/
def AuxiliaryOrbitSliceContinuousOn (T : ℝ) (W : ℝ → ℝ → ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) T, Continuous (W s)

/-- Slices of two continuous trapped orbits give an a.e. strongly measurable
value-source difference. -/
theorem auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuousOrbits
    {p : CMParams} {u : ℝ → ℝ} {T t s : ℝ} {W Z : ℝ → ℝ → ℝ}
    (hW_cont : AuxiliaryOrbitSliceContinuousOn T W)
    (hZ_cont : AuxiliaryOrbitSliceContinuousOn T Z)
    (hu_cont : Continuous u)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hs : s ∈ Set.Icc (0 : ℝ) t) :
    AEStronglyMeasurable
      (fun y => auxiliaryValueSourceDiff p W Z u s y) volume := by
  exact
    auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuous
      (p := p) (W := W) (Z := Z) (u := u) (s := s)
      (hW_cont s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (hZ_cont s ⟨hs.1, le_trans hs.2 ht.2⟩)
      hu_cont

/-- Restricted value-source measurability frontier for continuous orbits. -/
def AuxiliaryMildMapDivValueSourceMeasurableContinuous
    (p : CMParams) (u : ℝ → ℝ) (κ κt D : ℝ) : Prop :=
  ∀ T W Z dist, 0 ≤ dist →
    AuxiliaryBarrierTrap κ κt D T W →
    AuxiliaryBarrierTrap κ κt D T Z →
    AuxiliaryValueDistanceBound T dist W Z →
    AuxiliaryOrbitSliceContinuousOn T W →
    AuxiliaryOrbitSliceContinuousOn T Z →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ s ∈ Set.Icc (0 : ℝ) t,
          AEStronglyMeasurable
            (fun y => auxiliaryValueSourceDiff p W Z u s y) volume

/-- Continuous spatial slices discharge the value-source measurability field. -/
theorem auxiliaryMildMapDiv_valueSourceMeasurable_of_continuousOrbits
    {p : CMParams} {u : ℝ → ℝ} {κ κt D : ℝ}
    (hu_cont : Continuous u) :
    AuxiliaryMildMapDivValueSourceMeasurableContinuous p u κ κt D := by
  intro T W Z dist _hdist _hW _hZ _hdistWZ hW_cont hZ_cont t ht s hs
  exact
    auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuousOrbits
      (p := p) (u := u) (T := T) (t := t) (s := s)
      hW_cont hZ_cont hu_cont ht hs

/-- Integrability data sufficient for the value-Duhamel difference identity. -/
def AuxiliaryValueDuhamelSubIntegrability
    (p : CMParams) (c : ℝ) (W Z : ℝ → ℝ → ℝ) (u : ℝ → ℝ)
    (t x : ℝ) : Prop :=
  IntegrableOn
      (fun s : ℝ =>
        movingFrameHeatOp c (t - s)
          (fun y => auxiliaryValueSource p (W s) u y) x)
      (Set.Icc (0 : ℝ) t) volume ∧
    IntegrableOn
      (fun s : ℝ =>
        movingFrameHeatOp c (t - s)
          (fun y => auxiliaryValueSource p (Z s) u y) x)
      (Set.Icc (0 : ℝ) t) volume

/-- Linearity of the moving-frame heat operator in the source profile. -/
theorem movingFrameHeatOp_sub
    {c τ : ℝ} {f g : ℝ → ℝ} {x : ℝ}
    (hf : Integrable fun y : ℝ => heatKernel τ (x + c * τ - y) * f y)
    (hg : Integrable fun y : ℝ => heatKernel τ (x + c * τ - y) * g y) :
    movingFrameHeatOp c τ f x - movingFrameHeatOp c τ g x =
      movingFrameHeatOp c τ (fun y => f y - g y) x := by
  unfold movingFrameHeatOp wholeLineHeatOp modifiedSemigroup heatSemigroup
  rw [← mul_sub, ← MeasureTheory.integral_sub hf hg]
  refine congrArg (fun z => Real.exp (-τ) * z) ?_
  refine integral_congr_ae (Eventually.of_forall ?_)
  intro y
  ring

/-- Spatial integrability data sufficient to use heat-operator linearity inside
the value-Duhamel identity. -/
def AuxiliaryValueDuhamelSubHeatIntegrability
    (p : CMParams) (c : ℝ) (W Z : ℝ → ℝ → ℝ) (u : ℝ → ℝ)
    (t x : ℝ) : Prop :=
  ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) t),
    Integrable
        (fun y : ℝ =>
          heatKernel (t - s) (x + c * (t - s) - y) *
            auxiliaryValueSource p (W s) u y) ∧
      Integrable
        (fun y : ℝ =>
          heatKernel (t - s) (x + c * (t - s) - y) *
            auxiliaryValueSource p (Z s) u y)

/-- The value-Duhamel difference is the Duhamel term of the value-source
difference, once the two ordinary linearity integrability side conditions are
available. -/
theorem auxiliaryValueDuhamelDiv_sub
    {p : CMParams} {c : ℝ} {W Z : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {t x : ℝ}
    (hInt : AuxiliaryValueDuhamelSubIntegrability p c W Z u t x)
    (hHeatInt : AuxiliaryValueDuhamelSubHeatIntegrability p c W Z u t x) :
    auxiliaryValueDuhamelDiv p c W u t x -
        auxiliaryValueDuhamelDiv p c Z u t x =
      movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x := by
  rcases hInt with ⟨hW_int, hZ_int⟩
  unfold auxiliaryValueDuhamelDiv movingFrameDuhamel
  rw [← MeasureTheory.integral_sub hW_int hZ_int]
  refine integral_congr_ae ?_
  filter_upwards [hHeatInt] with s hs
  rcases hs with ⟨hW_heat, hZ_heat⟩
  simpa [auxiliaryValueSourceDiff] using
    movingFrameHeatOp_sub
      (c := c) (τ := t - s)
      (f := fun y => auxiliaryValueSource p (W s) u y)
      (g := fun y => auxiliaryValueSource p (Z s) u y)
      (x := x) hW_heat hZ_heat

/-- Restricted value-Duhamel subtraction frontier.  The integrability fields are
the standard Bochner-integral side conditions for linearity. -/
def AuxiliaryMildMapDivValueDuhamelSubContinuous
    (p : CMParams) (c : ℝ) (u : ℝ → ℝ) (κ κt D : ℝ) : Prop :=
  ∀ T W Z dist, 0 ≤ dist →
    AuxiliaryBarrierTrap κ κt D T W →
    AuxiliaryBarrierTrap κ κt D T Z →
    AuxiliaryValueDistanceBound T dist W Z →
    AuxiliaryOrbitSliceContinuousOn T W →
    AuxiliaryOrbitSliceContinuousOn T Z →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
        AuxiliaryValueDuhamelSubIntegrability p c W Z u t x →
        AuxiliaryValueDuhamelSubHeatIntegrability p c W Z u t x →
          auxiliaryValueDuhamelDiv p c W u t x -
              auxiliaryValueDuhamelDiv p c Z u t x =
            movingFrameDuhamel c
              (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x

/-- The restricted value-Duhamel subtraction field follows from linearity. -/
theorem auxiliaryMildMapDiv_valueDuhamelSub_of_integrability
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ} {κ κt D : ℝ} :
    AuxiliaryMildMapDivValueDuhamelSubContinuous p c u κ κt D := by
  intro T W Z dist _hdist _hW _hZ _hdistWZ _hWcont _hZcont t _ht x hInt hHeatInt
  exact auxiliaryValueDuhamelDiv_sub
    (p := p) (c := c) (W := W) (Z := Z) (u := u) (t := t) (x := x)
    hInt hHeatInt

/-- A Duhamel correction term for the divergence-form value map. -/
def auxiliaryMildMapDivCorrection (p : CMParams) (c : ℝ)
    (W : ℝ → ℝ → ℝ) (V Vx u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  -p.χ * auxiliaryDivergenceChemDuhamel p c W V Vx t x +
    auxiliaryValueDuhamelDiv p c W u t x

/-- L∞ budget for the divergence-form Duhamel correction on a horizon. -/
def AuxiliaryMildMapDivCorrectionLinftyBudget
    (p : CMParams) (c : ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D T : ℝ) (E : ℝ → ℝ → ℝ) : Prop :=
  ∀ W, AuxiliaryBarrierTrap κ κt D T W →
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      |auxiliaryMildMapDivCorrection p c W V Vx u t x| ≤ E t x

/-- Heat-step margin which, together with a Duhamel L∞ budget, keeps the image
inside the exponential barrier trap. -/
def AuxiliaryMildMapDivHeatTrapMargin
    (c : ℝ) (Uplus : ℝ → ℝ) (κ κt D T : ℝ)
    (E : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    lowerBarrier κ κt D x + E t x ≤ movingFrameHeatOp c t Uplus x ∧
      movingFrameHeatOp c t Uplus x + E t x ≤ upperBarrier κ x

/-- The L∞ correction budget plus the heat-step trap margin imply maps-to. -/
theorem auxiliaryMildMapDiv_mapsTo_of_linfTrap
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D T : ℝ} {E : ℝ → ℝ → ℝ}
    (hbudget :
      AuxiliaryMildMapDivCorrectionLinftyBudget p c V Vx u κ κt D T E)
    (hmargin : AuxiliaryMildMapDivHeatTrapMargin c Uplus κ κt D T E) :
    ∀ W, AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T
        (auxiliaryMildMapDiv p c Uplus W V Vx u) := by
  intro W hW t ht x
  have hcorr := hbudget W hW t ht x
  have hmargin_tx := hmargin t ht x
  let R := auxiliaryMildMapDivCorrection p c W V Vx u t x
  have hR_lower : -E t x ≤ R := by
    have hR_neg_abs : -R ≤ |R| := neg_le_abs R
    linarith
  have hR_upper : R ≤ E t x := by
    have hR_le_abs : R ≤ |R| := le_abs_self R
    linarith
  have hmap :
      auxiliaryMildMapDiv p c Uplus W V Vx u t x =
        movingFrameHeatOp c t Uplus x + R := by
    dsimp [R, auxiliaryMildMapDiv, auxiliaryMildMapDivCorrection]
    ring
  constructor
  · rw [hmap]
    linarith
  · rw [hmap]
    linarith

/-- Maps-to frontier produced by a named L∞ correction budget and heat trap
margin. -/
def AuxiliaryMildMapDivMapsToLinfTrapData
    (p : CMParams) (c : ℝ) (Uplus V Vx u : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∃ E : ℝ → ℝ → ℝ,
      AuxiliaryMildMapDivCorrectionLinftyBudget p c V Vx u κ κt D T E ∧
        AuxiliaryMildMapDivHeatTrapMargin c Uplus κ κt D T E

/-- The L∞+trap data discharge the maps-to frontier. -/
theorem auxiliaryMildMapDiv_mapsToFrontier_of_linfTrapData
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapDivMapsToLinfTrapData
      p c Uplus V Vx u κ κt D A B) :
    AuxiliaryMildMapDivMapsToFrontier p c Uplus V Vx u κ κt D A B := by
  intro T hT hsmall W hW
  rcases H T hT hsmall with ⟨E, hbudget, hmargin⟩
  exact auxiliaryMildMapDiv_mapsTo_of_linfTrap hbudget hmargin W hW

/-- Divergence gradient-Duhamel integrability restricted to continuous orbits. -/
def AuxiliaryMildMapDivGradIntegrableContinuous
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∀ T W Z dist, 0 ≤ dist →
    AuxiliaryBarrierTrap κ κt D T W →
    AuxiliaryBarrierTrap κ κt D T Z →
    AuxiliaryValueDistanceBound T dist W Z →
    AuxiliaryOrbitSliceContinuousOn T W →
    AuxiliaryOrbitSliceContinuousOn T Z →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
        IntervalIntegrable
          (fun s : ℝ =>
            movingFrameHeatGradOp c (t - s)
              (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x)
          volume 0 t

/-- Divergence gradient-Duhamel subtraction restricted to continuous orbits. -/
def AuxiliaryMildMapDivGradDuhamelSubContinuous
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∀ T W Z dist, 0 ≤ dist →
    AuxiliaryBarrierTrap κ κt D T W →
    AuxiliaryBarrierTrap κ κt D T Z →
    AuxiliaryValueDistanceBound T dist W Z →
    AuxiliaryOrbitSliceContinuousOn T W →
    AuxiliaryOrbitSliceContinuousOn T Z →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
        auxiliaryDivergenceChemDuhamel p c W V Vx t x -
            auxiliaryDivergenceChemDuhamel p c Z V Vx t x =
          movingFrameGradDuhamel c
            (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x

/-- Value-Duhamel bound on one continuous-orbit pair. -/
theorem auxiliaryValueSourceDiffDuhamel_abs_le_of_continuousOrbits
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ}
    {κ κt D T : ℝ} {W Z : ℝ → ℝ → ℝ} {dist : ℝ}
    (hu_unit : UnitIntervalProfile u) (hu_cont : Continuous u)
    (hdist : 0 ≤ dist)
    (hW : AuxiliaryBarrierTrap κ κt D T W)
    (hZ : AuxiliaryBarrierTrap κ κt D T Z)
    (hdistWZ : AuxiliaryValueDistanceBound T dist W Z)
    (hW_cont : AuxiliaryOrbitSliceContinuousOn T W)
    (hZ_cont : AuxiliaryOrbitSliceContinuousOn T Z) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      |movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ auxiliaryValueSourceLipConst p * T * dist := by
  intro t ht x
  have hB_nonneg : 0 ≤ auxiliaryValueSourceLipConst p :=
    auxiliaryValueSourceLipConst_nonneg p
  have hC : 0 ≤ auxiliaryValueSourceLipConst p * dist :=
    mul_nonneg hB_nonneg hdist
  have hduh :
      |movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ (auxiliaryValueSourceLipConst p * dist) * t := by
    refine movingFrameDuhamel_abs_le_of_bound
      (c := c) (C := auxiliaryValueSourceLipConst p * dist) (t := t)
      (F := fun s y => auxiliaryValueSourceDiff p W Z u s y)
      ht.1 hC ?_ ?_ x
    · intro s hs y
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2 ht.2⟩
      exact
        auxiliaryValueSourceDiff_bound_of_trap
          (p := p) (u := u) (κ := κ) (κt := κt) (D := D)
          hu_unit T W Z dist hdist hW hZ hdistWZ s hsT y
    · intro s hs
      exact
        auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuousOrbits
          (p := p) (u := u) (T := T) (t := t) (s := s)
          hW_cont hZ_cont hu_cont ht hs
  have hBT : auxiliaryValueSourceLipConst p * t ≤
      auxiliaryValueSourceLipConst p * T :=
    mul_le_mul_of_nonneg_left ht.2 hB_nonneg
  have hBTdist :
      auxiliaryValueSourceLipConst p * t * dist ≤
        auxiliaryValueSourceLipConst p * T * dist :=
    mul_le_mul_of_nonneg_right hBT hdist
  calc
    |movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ (auxiliaryValueSourceLipConst p * dist) * t := hduh
    _ = auxiliaryValueSourceLipConst p * t * dist := by ring
    _ ≤ auxiliaryValueSourceLipConst p * T * dist := hBTdist

/-- Gradient-Duhamel bound on one continuous-orbit pair. -/
theorem auxiliaryDivergenceChemSourceDiffGradDuhamel_abs_le_of_continuousOrbits
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D CVx T : ℝ} {W Z : ℝ → ℝ → ℝ} {dist : ℝ}
    (hCVx : 0 ≤ CVx) (hVx : ∀ y, |Vx y| ≤ CVx)
    (hdist : 0 ≤ dist)
    (hW : AuxiliaryBarrierTrap κ κt D T W)
    (hZ : AuxiliaryBarrierTrap κ κt D T Z)
    (hdistWZ : AuxiliaryValueDistanceBound T dist W Z)
    (hgrad_integrable :
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
        IntervalIntegrable
          (fun s : ℝ =>
            movingFrameHeatGradOp c (t - s)
              (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x)
          volume 0 t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      |movingFrameGradDuhamel c
        (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x|
        ≤ auxiliaryDivMovingFrameGradientRate
            (auxiliaryDivergenceChemSourceLipConst p CVx) *
          Real.sqrt T * dist := by
  intro t ht x
  let B := auxiliaryDivergenceChemSourceLipConst p CVx
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact auxiliaryDivergenceChemSourceLipConst_nonneg p hCVx
  by_cases ht0 : t = 0
  · subst t
    have hrate_nonneg : 0 ≤ auxiliaryDivMovingFrameGradientRate B :=
      auxiliaryDivMovingFrameGradientRate_nonneg hB_nonneg
    have hnonneg :
        0 ≤ auxiliaryDivMovingFrameGradientRate B * Real.sqrt T * dist :=
      mul_nonneg (mul_nonneg hrate_nonneg (Real.sqrt_nonneg T)) hdist
    simp [movingFrameGradDuhamel, B, hnonneg]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hrate_nonneg : 0 ≤ auxiliaryDivMovingFrameGradientRate B :=
      auxiliaryDivMovingFrameGradientRate_nonneg hB_nonneg
    have hgrad :=
      movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound
        (c := c)
        (A := (auxiliaryDivMovingFrameGradientRate B * dist) / 2)
        (t := t)
        (F := fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y)
        htpos x
        (hgrad_integrable t ht x)
        ?_
    · have hsqr : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
      have hrate_dist_nonneg :
          0 ≤ auxiliaryDivMovingFrameGradientRate B * dist :=
        mul_nonneg hrate_nonneg hdist
      have hmul :
          (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt t
            ≤ (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt T :=
        mul_le_mul_of_nonneg_left hsqr hrate_dist_nonneg
      calc
        |movingFrameGradDuhamel c
          (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x|
            ≤ ((auxiliaryDivMovingFrameGradientRate B * dist) / 2) *
                (2 * Real.sqrt t) := hgrad
        _ = (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt t := by ring
        _ ≤ (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt T := hmul
        _ = auxiliaryDivMovingFrameGradientRate B * Real.sqrt T * dist := by ring
    · intro s hs0 hst
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs0, le_trans (le_of_lt hst) ht.2⟩
      have hM : 0 ≤ B * dist := mul_nonneg hB_nonneg hdist
      have hbase :=
        movingFrameHeatGradOp_norm_le_rpow
          (c := c)
          (τ := t - s)
          (M := B * dist)
          (f := fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y)
          (sub_pos.mpr hst)
          hM
          (by
            dsimp [B]
            exact
              auxiliaryDivergenceChemSourceDiff_bound_of_trap
                (p := p) (V := V) (Vx := Vx)
                (κ := κ) (κt := κt) (D := D)
                hCVx hVx T W Z dist hdist hW hZ hdistWZ s hsT)
          x
      calc
        |movingFrameHeatGradOp c (t - s)
          (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x|
            = ‖movingFrameHeatGradOp c (t - s)
                (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x‖ := by
                rw [Real.norm_eq_abs]
        _ ≤ ((2 / Real.sqrt (4 * Real.pi)) * (B * dist)) *
            (t - s) ^ (-(1 / 2 : ℝ)) := hbase
        _ = (((auxiliaryDivMovingFrameGradientRate B) * dist) / 2) *
            (t - s) ^ (-(1 / 2 : ℝ)) := by
            dsimp [B, auxiliaryDivMovingFrameGradientRate]
            ring_nf

/-- Value-difference frontier used by the continuous Banach realization. -/
def AuxiliaryMildMapDivContinuousValueDiffFrontier
    (p : CMParams) (c : ℝ) (Uplus V Vx u : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∀ W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
      AuxiliaryOrbitSliceContinuousOn T W →
      AuxiliaryOrbitSliceContinuousOn T Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |auxiliaryMildMapDiv p c Uplus W V Vx u t x -
            auxiliaryMildMapDiv p c Uplus Z V Vx u t x| ≤
              (A * Real.sqrt T + B * T) * dist

/-- Concrete continuous-orbit rate data for the divergence mild map. -/
structure AuxiliaryMildMapDivContinuousRateData
    (p : CMParams) (c : ℝ) (Uplus V Vx u : ℝ → ℝ)
    (κ κt D CVx : ℝ) : Prop where
  CVx_nonneg : 0 ≤ CVx
  Vx_bound : ∀ y, |Vx y| ≤ CVx
  u_unit : UnitIntervalProfile u
  u_cont : Continuous u
  mapsTo_linfTrap :
    AuxiliaryMildMapDivMapsToLinfTrapData p c Uplus V Vx u κ κt D
      (auxiliaryMildMapDivGradientRate p CVx)
      (auxiliaryValueSourceLipConst p)
  value_duhamel_integrable :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
      AuxiliaryOrbitSliceContinuousOn T W →
      AuxiliaryOrbitSliceContinuousOn T Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          AuxiliaryValueDuhamelSubIntegrability p c W Z u t x
  value_duhamel_heat_integrable :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
      AuxiliaryOrbitSliceContinuousOn T W →
      AuxiliaryOrbitSliceContinuousOn T Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          AuxiliaryValueDuhamelSubHeatIntegrability p c W Z u t x
  div_grad_integrable :
    AuxiliaryMildMapDivGradIntegrableContinuous p c V Vx κ κt D
  div_grad_duhamel_sub :
    AuxiliaryMildMapDivGradDuhamelSubContinuous p c V Vx κ κt D

/-- Continuous-orbit value-difference frontier from the concrete rate data. -/
theorem auxiliaryMildMapDiv_continuousValueDiffFrontier_of_rateData
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D CVx : ℝ}
    (H : AuxiliaryMildMapDivContinuousRateData
      p c Uplus V Vx u κ κt D CVx) :
    AuxiliaryMildMapDivContinuousValueDiffFrontier p c Uplus V Vx u κ κt D
      (auxiliaryMildMapDivGradientRate p CVx)
      (auxiliaryValueSourceLipConst p) := by
  intro T hT _hsmall W Z dist hdist hW hZ hdistWZ hWcont hZcont t ht x
  let Ldiv := auxiliaryDivergenceChemSourceLipConst p CVx
  let A0 := auxiliaryDivMovingFrameGradientRate Ldiv
  let A := auxiliaryMildMapDivGradientRate p CVx
  let B := auxiliaryValueSourceLipConst p
  have hdiv_bound :
      |movingFrameGradDuhamel c
        (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x|
        ≤ A0 * Real.sqrt T * dist := by
    dsimp [A0, Ldiv]
    exact
      auxiliaryDivergenceChemSourceDiffGradDuhamel_abs_le_of_continuousOrbits
        (p := p) (c := c) (V := V) (Vx := Vx)
        (κ := κ) (κt := κt) (D := D) (CVx := CVx)
        H.CVx_nonneg H.Vx_bound hdist hW hZ hdistWZ
        (H.div_grad_integrable T W Z dist hdist hW hZ hdistWZ
          hWcont hZcont)
        t ht x
  have hdiv_sub :=
    H.div_grad_duhamel_sub T W Z dist hdist hW hZ hdistWZ
      hWcont hZcont t ht x
  have hval_bound :
      |movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ B * T * dist := by
    dsimp [B]
    exact
      auxiliaryValueSourceDiffDuhamel_abs_le_of_continuousOrbits
        (p := p) (c := c) (u := u)
        (κ := κ) (κt := κt) (D := D)
        H.u_unit H.u_cont hdist hW hZ hdistWZ hWcont hZcont t ht x
  have hval_sub :
      auxiliaryValueDuhamelDiv p c W u t x -
          auxiliaryValueDuhamelDiv p c Z u t x =
        movingFrameDuhamel c
          (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x :=
    auxiliaryValueDuhamelDiv_sub
      (p := p) (c := c) (W := W) (Z := Z) (u := u) (t := t) (x := x)
      (H.value_duhamel_integrable T W Z dist hdist hW hZ hdistWZ
        hWcont hZcont t ht x)
      (H.value_duhamel_heat_integrable T W Z dist hdist hW hZ hdistWZ
        hWcont hZcont t ht x)
  have hcancel :
      auxiliaryMildMapDiv p c Uplus W V Vx u t x -
          auxiliaryMildMapDiv p c Uplus Z V Vx u t x =
        -p.χ *
            (auxiliaryDivergenceChemDuhamel p c W V Vx t x -
              auxiliaryDivergenceChemDuhamel p c Z V Vx t x)
          +
            (auxiliaryValueDuhamelDiv p c W u t x -
              auxiliaryValueDuhamelDiv p c Z u t x) := by
    unfold auxiliaryMildMapDiv
    ring
  calc
    |auxiliaryMildMapDiv p c Uplus W V Vx u t x -
        auxiliaryMildMapDiv p c Uplus Z V Vx u t x|
        =
      |-p.χ *
          (auxiliaryDivergenceChemDuhamel p c W V Vx t x -
            auxiliaryDivergenceChemDuhamel p c Z V Vx t x)
        +
          (auxiliaryValueDuhamelDiv p c W u t x -
            auxiliaryValueDuhamelDiv p c Z u t x)| := by rw [hcancel]
    _ =
      |-p.χ *
          movingFrameGradDuhamel c
            (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x
        +
          movingFrameDuhamel c
            (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| := by
          rw [hdiv_sub, hval_sub]
    _ ≤
        |p.χ| *
          |movingFrameGradDuhamel c
            (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x| +
        |movingFrameDuhamel c
            (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| := by
          calc
            |-p.χ *
                movingFrameGradDuhamel c
                  (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x
              +
                movingFrameDuhamel c
                  (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
                ≤
                  |-p.χ *
                    movingFrameGradDuhamel c
                      (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x| +
                  |movingFrameDuhamel c
                    (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| :=
                    abs_add_le _ _
            _ =
                  |p.χ| *
                    |movingFrameGradDuhamel c
                      (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x| +
                  |movingFrameDuhamel c
                    (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| := by
                  rw [abs_mul, abs_neg]
    _ ≤ |p.χ| * (A0 * Real.sqrt T * dist) + B * T * dist :=
          add_le_add
            (mul_le_mul_of_nonneg_left hdiv_bound (abs_nonneg p.χ))
            hval_bound
    _ = (A * Real.sqrt T + B * T) * dist := by
          dsimp [A, A0, Ldiv, B, auxiliaryMildMapDivGradientRate]
          ring

/-- Continuous-orbit rate estimates for the divergence-form mild map. -/
structure AuxiliaryMildMapDivContinuousRateEstimates
    (p : CMParams) (c : ℝ) (Uplus V Vx u : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop where
  hA_nonneg : 0 ≤ A
  hB_nonneg : 0 ≤ B
  mapsTo_of_small :
    AuxiliaryMildMapDivMapsToFrontier p c Uplus V Vx u κ κt D A B
  value_diff_of_small :
    AuxiliaryMildMapDivContinuousValueDiffFrontier p c Uplus V Vx u κ κt D A B

/-- Producer for continuous-orbit divergence rate estimates. -/
theorem auxiliaryMildMapDiv_continuousRateEstimates
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D CVx : ℝ}
    (H : AuxiliaryMildMapDivContinuousRateData
      p c Uplus V Vx u κ κt D CVx) :
    AuxiliaryMildMapDivContinuousRateEstimates p c Uplus V Vx u κ κt D
      (auxiliaryMildMapDivGradientRate p CVx)
      (auxiliaryValueSourceLipConst p) where
  hA_nonneg := auxiliaryMildMapDivGradientRate_nonneg p H.CVx_nonneg
  hB_nonneg := auxiliaryValueSourceLipConst_nonneg p
  mapsTo_of_small :=
    auxiliaryMildMapDiv_mapsToFrontier_of_linfTrapData H.mapsTo_linfTrap
  value_diff_of_small :=
    auxiliaryMildMapDiv_continuousValueDiffFrontier_of_rateData H

/-- Closed short-time contraction package for continuous divergence orbits. -/
structure AuxiliaryMildMapDivContinuousContractionData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D : ℝ) where
  T : ℝ
  hT_pos : 0 < T
  K : ℝ
  hK_nonneg : 0 ≤ K
  hK_lt_one : K < 1
  mapsTo :
    ∀ W, AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T
        (auxiliaryMildMapDiv p c Uplus W V Vx u)
  contraction :
    ∀ W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
      AuxiliaryOrbitSliceContinuousOn T W →
      AuxiliaryOrbitSliceContinuousOn T Z →
        AuxiliaryValueDistanceBound T (K * dist)
          (auxiliaryMildMapDiv p c Uplus W V Vx u)
          (auxiliaryMildMapDiv p c Uplus Z V Vx u)

/-- Small-time continuous contraction from continuous rate estimates. -/
theorem auxiliaryMildMapDiv_continuousContraction_on_smallTime
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapDivContinuousRateEstimates
      p c Uplus V Vx u κ κt D A B) :
    Nonempty
      (AuxiliaryMildMapDivContinuousContractionData
        p c Uplus V Vx u κ κt D) := by
  obtain ⟨T0, hT0, hsmall⟩ :=
    exists_small_contraction_time_target H.hA_nonneg H.hB_nonneg one_pos
  let K : ℝ := A * Real.sqrt T0 + B * T0
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg
      (mul_nonneg H.hA_nonneg (Real.sqrt_nonneg T0))
      (mul_nonneg H.hB_nonneg hT0.le)
  refine ⟨?_⟩
  exact
    { T := T0
      hT_pos := hT0
      K := K
      hK_nonneg := hK_nonneg
      hK_lt_one := hsmall
      mapsTo := by
        intro W hW
        exact H.mapsTo_of_small T0 hT0 hsmall W hW
      contraction := by
        intro W Z dist hdist hW hZ hdistWZ hWcont hZcont t ht x
        exact H.value_diff_of_small T0 hT0 hsmall W Z dist hdist
          hW hZ hdistWZ hWcont hZcont t ht x }

/-- A complete closed-trap metric model whose elements evaluate to continuous
spatial slices. -/
structure AuxiliaryMildMapDivContinuousBanachRealization
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D T K : ℝ) (X : Type*) [MetricSpace X] where
  F : X → X
  seed : X
  eval : X → ℝ → ℝ → ℝ
  trap :
    ∀ z, AuxiliaryBarrierTrap κ κt D T (eval z)
  eval_cont :
    ∀ z, AuxiliaryOrbitSliceContinuousOn T (eval z)
  value_comm :
    ∀ z, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      eval (F z) t x =
        auxiliaryMildMapDiv p c Uplus (eval z) V Vx u t x
  dist_controls :
    ∀ z y,
      AuxiliaryValueDistanceBound T (dist z y) (eval z) (eval y)
  dist_le_of_value :
    ∀ z y E, 0 ≤ E →
      AuxiliaryValueDistanceBound T E (eval z) (eval y) →
      dist z y ≤ E

/-- Complete metric-space packaging for the continuous realization. -/
structure AuxiliaryMildMapDivContinuousBanachRealizationData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D : ℝ)
    (C : AuxiliaryMildMapDivContinuousContractionData
      p c Uplus V Vx u κ κt D) where
  X : Type*
  [instMetric : MetricSpace X]
  [instComplete : CompleteSpace X]
  [instNonempty : Nonempty X]
  realization :
    AuxiliaryMildMapDivContinuousBanachRealization
      p c Uplus V Vx u κ κt D C.T C.K X

/-- The continuous closed-trap realization inherits a contraction. -/
theorem auxiliaryMildMapDivContinuousBanachRealization_contracting
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D : ℝ}
    (C : AuxiliaryMildMapDivContinuousContractionData
      p c Uplus V Vx u κ κt D)
    {X : Type*} [MetricSpace X]
    (R : AuxiliaryMildMapDivContinuousBanachRealization
      p c Uplus V Vx u κ κt D C.T C.K X) :
    ContractingWith ⟨C.K, C.hK_nonneg⟩ R.F := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using C.hK_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro z y
    have hdist_nonneg : 0 ≤ dist z y := dist_nonneg
    have hraw :
        AuxiliaryValueDistanceBound C.T (C.K * dist z y)
          (auxiliaryMildMapDiv p c Uplus (R.eval z) V Vx u)
          (auxiliaryMildMapDiv p c Uplus (R.eval y) V Vx u) :=
      C.contraction (R.eval z) (R.eval y) (dist z y)
        hdist_nonneg (R.trap z) (R.trap y) (R.dist_controls z y)
        (R.eval_cont z) (R.eval_cont y)
    have himage :
        AuxiliaryValueDistanceBound C.T (C.K * dist z y)
          (R.eval (R.F z)) (R.eval (R.F y)) := by
      intro t ht x
      simpa [R.value_comm z t ht x, R.value_comm y t ht x] using
        hraw t ht x
    have hE_nonneg : 0 ≤ C.K * dist z y :=
      mul_nonneg C.hK_nonneg hdist_nonneg
    have hdist :=
      R.dist_le_of_value (R.F z) (R.F y) (C.K * dist z y)
        hE_nonneg himage
    simpa using hdist

/-- Banach fixed-point extraction for continuous divergence contraction data. -/
theorem auxiliaryFlowDiv_localExists_of_continuousContractionData
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D : ℝ}
    (C : AuxiliaryMildMapDivContinuousContractionData
      p c Uplus V Vx u κ κt D)
    (Rdata :
      AuxiliaryMildMapDivContinuousBanachRealizationData
        p c Uplus V Vx u κ κt D C) :
    AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D C.T := by
  letI := Rdata.instMetric
  letI := Rdata.instComplete
  letI := Rdata.instNonempty
  let R := Rdata.realization
  have hcontract :
      ContractingWith ⟨C.K, C.hK_nonneg⟩ R.F :=
    auxiliaryMildMapDivContinuousBanachRealization_contracting C R
  have hseed : edist R.seed (R.F R.seed) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hz_fix, _hz_tendsto, _hz_rate⟩ :=
    hcontract.exists_fixedPoint R.seed hseed
  refine ⟨R.eval z, ?_⟩
  refine ⟨C.hT_pos, ?_, R.trap z⟩
  intro t ht x
  calc
    R.eval z t x = R.eval (R.F z) t x := by
      rw [hz_fix.eq]
    _ = auxiliaryMildMapDiv p c Uplus (R.eval z) V Vx u t x :=
      R.value_comm z t ht x

/-- Local divergence-form existence from continuous rate and realization data. -/
theorem auxiliaryFlowDiv_localExists_continuous
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapDivContinuousRateEstimates
      p c Uplus V Vx u κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapDivContinuousContractionData
          p c Uplus V Vx u κ κt D,
        AuxiliaryMildMapDivContinuousBanachRealizationData
          p c Uplus V Vx u κ κt D C) :
    ∃ T0 > 0,
      AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T0 := by
  rcases auxiliaryMildMapDiv_continuousContraction_on_smallTime H with ⟨C⟩
  exact
    ⟨C.T, C.hT_pos,
      auxiliaryFlowDiv_localExists_of_continuousContractionData C
        (hrealize C)⟩

/-- Divergence reachability on every finite horizon. -/
def AuxiliaryMildMapDivReachableArbitrarilyLong
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∀ T > 0, AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T

/-- A single global divergence-form auxiliary mild solution obtained by gluing
compatible finite-horizon branches. -/
def AuxiliaryMildMapDivGlobalSolutionFor
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∃ w : ℝ → ℝ → ℝ,
    ∀ T > 0, AuxiliaryMildMapDivSolutionOn p c Uplus V Vx u κ κt D T w

/-- Uniform restart and gluing data for one divergence-form Banach time step. -/
structure AuxiliaryMildMapDivUniformRestartGluingData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D T0 : ℝ) : Prop where
  extend_from_solution :
    ∀ {T : ℝ} {w : ℝ → ℝ → ℝ}, 0 < T →
      AuxiliaryMildMapDivSolutionOn p c Uplus V Vx u κ κt D T w →
        AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D (T + T0)
  glue :
    AuxiliaryMildMapDivReachableArbitrarilyLong p c Uplus V Vx u κ κt D →
      AuxiliaryMildMapDivGlobalSolutionFor p c Uplus V Vx u κ κt D

/-- Restrict a divergence finite-horizon solution to a shorter horizon. -/
theorem auxiliaryMildMapDivSolutionOn_mono
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D Tshort Tlong : ℝ} {w : ℝ → ℝ → ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hsol : AuxiliaryMildMapDivSolutionOn p c Uplus V Vx u κ κt D Tlong w) :
    AuxiliaryMildMapDivSolutionOn p c Uplus V Vx u κ κt D Tshort w := by
  refine ⟨hTshort, ?_, ?_⟩
  · intro t ht x
    exact hsol.2.1 t ⟨ht.1, le_trans ht.2 hTL⟩ x
  · intro t ht x
    exact hsol.2.2 t ⟨ht.1, le_trans ht.2 hTL⟩ x

/-- Restrict divergence reachability to a shorter positive horizon. -/
theorem auxiliaryMildMapDivReachableHorizon_mono
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D Tshort Tlong : ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hreach :
      AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D Tlong) :
    AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D Tshort := by
  rcases hreach with ⟨w, hsol⟩
  exact ⟨w, auxiliaryMildMapDivSolutionOn_mono hTshort hTL hsol⟩

/-- One fixed divergence restart step. -/
theorem auxiliaryMildMapDivReachableHorizon_step_of_uniformRestart
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D T0 T : ℝ}
    (H : AuxiliaryMildMapDivUniformRestartGluingData
      p c Uplus V Vx u κ κt D T0)
    (hT : 0 < T)
    (hreach :
      AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T) :
    AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D (T + T0) := by
  rcases hreach with ⟨w, hsol⟩
  exact H.extend_from_solution hT hsol

/-- Fixed-step divergence continuation reaches every positive finite horizon. -/
theorem auxiliaryMildMapDivReachableArbitrarilyLong_of_uniformRestart
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D T0 : ℝ}
    (hT0 : 0 < T0)
    (hlocal :
      AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T0)
    (H : AuxiliaryMildMapDivUniformRestartGluingData
      p c Uplus V Vx u κ κt D T0) :
    AuxiliaryMildMapDivReachableArbitrarilyLong p c Uplus V Vx u κ κt D := by
  have hgrid :
      ∀ n : ℕ,
        AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D
          (((n + 1 : ℕ) : ℝ) * T0) := by
    intro n
    induction n with
    | zero =>
        simpa using hlocal
    | succ n ih =>
        have hpos : 0 < (((n + 1 : ℕ) : ℝ) * T0) := by
          have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_pos n
          exact mul_pos hnpos hT0
        have hnext :
            AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D
              ((((n + 1 : ℕ) : ℝ) * T0) + T0) :=
          auxiliaryMildMapDivReachableHorizon_step_of_uniformRestart H hpos ih
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
  exact auxiliaryMildMapDivReachableHorizon_mono
    hT (le_of_lt hT_lt_grid) (hgrid n)

/-- Global divergence-form auxiliary flow from one local Banach horizon and
uniform restart/gluing. -/
theorem auxiliaryFlowDiv_globalExists_of_uniformRestart
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D T0 : ℝ}
    (hT0 : 0 < T0)
    (hlocal :
      AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T0)
    (H : AuxiliaryMildMapDivUniformRestartGluingData
      p c Uplus V Vx u κ κt D T0) :
    AuxiliaryMildMapDivGlobalSolutionFor p c Uplus V Vx u κ κt D := by
  exact H.glue
    (auxiliaryMildMapDivReachableArbitrarilyLong_of_uniformRestart
      hT0 hlocal H)

/-- Uniform restart/gluing supplied for whatever short horizon the local Banach
argument produces. -/
def AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D : ℝ) : Prop :=
  ∀ T0, 0 < T0 →
    AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T0 →
      AuxiliaryMildMapDivUniformRestartGluingData
        p c Uplus V Vx u κ κt D T0

/-- Global divergence-form auxiliary-flow existence from local existence and
uniform restart/gluing. -/
theorem auxiliaryFlowDiv_globalExists
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (Hrate : AuxiliaryMildMapDivRateEstimates p c Uplus V Vx u κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D,
        AuxiliaryMildMapDivBanachRealizationData p c Uplus V Vx u κ κt D C)
    (hrestart :
      AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach
        p c Uplus V Vx u κ κt D) :
    AuxiliaryMildMapDivGlobalSolutionFor p c Uplus V Vx u κ κt D := by
  obtain ⟨T0, hT0, hlocal⟩ := auxiliaryFlowDiv_localExists Hrate hrealize
  exact auxiliaryFlowDiv_globalExists_of_uniformRestart hT0 hlocal
    (hrestart T0 hT0 hlocal)

/-- Global divergence-form auxiliary-flow existence from the continuous-orbit
local Banach construction and uniform restart/gluing. -/
theorem auxiliaryFlowDiv_globalExists_continuous
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (Hrate :
      AuxiliaryMildMapDivContinuousRateEstimates
        p c Uplus V Vx u κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapDivContinuousContractionData
          p c Uplus V Vx u κ κt D,
        AuxiliaryMildMapDivContinuousBanachRealizationData
          p c Uplus V Vx u κ κt D C)
    (hrestart :
      AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach
        p c Uplus V Vx u κ κt D) :
    AuxiliaryMildMapDivGlobalSolutionFor p c Uplus V Vx u κ κt D := by
  obtain ⟨T0, hT0, hlocal⟩ :=
    auxiliaryFlowDiv_localExists_continuous Hrate hrealize
  exact auxiliaryFlowDiv_globalExists_of_uniformRestart hT0 hlocal
    (hrestart T0 hT0 hlocal)

/-- Trapped global divergence-form auxiliary flow. -/
theorem auxiliaryFlowDiv_globalExists_trapped
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (Hrate : AuxiliaryMildMapDivRateEstimates p c Uplus V Vx u κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D,
        AuxiliaryMildMapDivBanachRealizationData p c Uplus V Vx u κ κt D C)
    (hrestart :
      AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach
        p c Uplus V Vx u κ κt D) :
    ∃ w : ℝ → ℝ → ℝ,
      (∀ T > 0,
        AuxiliaryMildMapDivSolutionOn p c Uplus V Vx u κ κt D T w) ∧
        ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x ∧ w t x ≤ 1 := by
  rcases auxiliaryFlowDiv_globalExists Hrate hrealize hrestart with
    ⟨w, hglobal⟩
  refine ⟨w, hglobal, ?_⟩
  intro t ht x
  have hT : 0 < t + 1 := by linarith
  have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hsol := hglobal (t + 1) hT
  exact
    ⟨auxiliaryBarrierTrap_nonneg hsol.2.2 t ht_mem x,
      auxiliaryBarrierTrap_le_one hsol.2.2 t ht_mem x⟩

/-- Family-level divergence auxiliary-flow inputs. -/
structure WholeLineAuxiliaryDivGlobalFamilyData
    (p : CMParams) (c κt D : ℝ) where
  A : (ℝ → ℝ) → ℝ
  B : (ℝ → ℝ) → ℝ
  rate :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivContinuousRateEstimates p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        U
        (waveExponent c) κt D (A U) (B U)
  realize :
    ∀ U, (hU : U ∈ WaveTrap (waveExponent c) κt D) →
      Continuous U →
      ∀ C : AuxiliaryMildMapDivContinuousContractionData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D,
        AuxiliaryMildMapDivContinuousBanachRealizationData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D C
  restart :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        U
        (waveExponent c) κt D

namespace WholeLineAuxiliaryDivGlobalFamilyData

def globalSolution
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryDivGlobalFamilyData p c κt D)
    (U : ℝ → ℝ) (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hU_cont : Continuous U) :
    AuxiliaryMildMapDivGlobalSolutionFor p c
      (upperBarrier (waveExponent c))
      (frozenSignal p.γ U)
      (fun x => deriv (frozenSignal p.γ U) x)
      U
      (waveExponent c) κt D :=
  auxiliaryFlowDiv_globalExists_continuous
    (H.rate U hU hU_cont) (H.realize U hU hU_cont)
    (H.restart U hU hU_cont)

/-- The selected global divergence auxiliary orbit; off the trap it is an inert
extension. -/
noncomputable def raw_w
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryDivGlobalFamilyData p c κt D) :
    (ℝ → ℝ) → ℝ → ℝ → ℝ :=
  by
    classical
    exact fun U =>
      if hU : U ∈ WaveTrap (waveExponent c) κt D ∧ Continuous U then
        Classical.choose (H.globalSolution U hU.1 hU.2)
      else
        fun _t x => upperBarrier (waveExponent c) x

theorem raw_solution
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryDivGlobalFamilyData p c κt D)
    (U : ℝ → ℝ) (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hU_cont : Continuous U) :
    ∀ T > 0,
      AuxiliaryMildMapDivSolutionOn p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        U
        (waveExponent c) κt D T
        (H.raw_w U) := by
  have hglobal := Classical.choose_spec (H.globalSolution U hU hU_cont)
  simpa [raw_w, hU, hU_cont] using hglobal

end WholeLineAuxiliaryDivGlobalFamilyData

/-- Satisfiable frozen-signal family inputs for the divergence global family.
The source measurability is restricted to continuous Banach orbits, and maps-to
is supplied through the L∞ correction budget plus heat trap margin. -/
structure WholeLineAuxiliaryDivFrozenSignalFamilyData
    (p : CMParams) (c κt D : ℝ) where
  realize :
    ∀ U, (hU : U ∈ WaveTrap (waveExponent c) κt D) →
      Continuous U →
      ∀ C : AuxiliaryMildMapDivContinuousContractionData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D,
        AuxiliaryMildMapDivContinuousBanachRealizationData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D C
  restart :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        U
        (waveExponent c) κt D
  mapsTo_linfTrap :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivMapsToLinfTrapData p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        U
        (waveExponent c) κt D
        (auxiliaryMildMapDivGradientRate p 1)
        (auxiliaryValueSourceLipConst p)
  value_duhamel_integrable :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap (waveExponent c) κt D T W →
        AuxiliaryBarrierTrap (waveExponent c) κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
        AuxiliaryOrbitSliceContinuousOn T W →
        AuxiliaryOrbitSliceContinuousOn T Z →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            AuxiliaryValueDuhamelSubIntegrability p c W Z U t x
  value_duhamel_heat_integrable :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap (waveExponent c) κt D T W →
        AuxiliaryBarrierTrap (waveExponent c) κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
        AuxiliaryOrbitSliceContinuousOn T W →
        AuxiliaryOrbitSliceContinuousOn T Z →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            AuxiliaryValueDuhamelSubHeatIntegrability p c W Z U t x
  div_grad_integrable :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivGradIntegrableContinuous p c
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D
  div_grad_duhamel_sub :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivGradDuhamelSubContinuous p c
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D

/-- Constructor for the divergence-form global family from frozen-signal data
with satisfiable inputs. -/
def auxiliaryDivGlobalFamily_of_frozenSignal
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryDivFrozenSignalFamilyData p c κt D) :
    WholeLineAuxiliaryDivGlobalFamilyData p c κt D where
  A := fun _U => auxiliaryMildMapDivGradientRate p 1
  B := fun _U => auxiliaryValueSourceLipConst p
  rate := by
    intro U hU hU_cont
    exact
      auxiliaryMildMapDiv_continuousRateEstimates
        { CVx_nonneg := by norm_num
          Vx_bound :=
            frozenSignal_Vx_bound_one_of_waveTrap p.hγ hU hU_cont
          u_unit := waveTrap_unitIntervalProfile hU
          u_cont := hU_cont
          mapsTo_linfTrap := H.mapsTo_linfTrap U hU hU_cont
          value_duhamel_integrable :=
            H.value_duhamel_integrable U hU hU_cont
          value_duhamel_heat_integrable :=
            H.value_duhamel_heat_integrable U hU hU_cont
          div_grad_integrable := H.div_grad_integrable U hU hU_cont
          div_grad_duhamel_sub := H.div_grad_duhamel_sub U hU hU_cont }
  realize := H.realize
  restart := H.restart

#print axioms auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuousOrbits
#print axioms auxiliaryMildMapDiv_valueSourceMeasurable_of_continuousOrbits
#print axioms movingFrameHeatOp_sub
#print axioms auxiliaryValueDuhamelDiv_sub
#print axioms auxiliaryMildMapDiv_valueDuhamelSub_of_integrability
#print axioms auxiliaryMildMapDiv_mapsTo_of_linfTrap
#print axioms auxiliaryMildMapDiv_mapsToFrontier_of_linfTrapData
#print axioms auxiliaryValueSourceDiffDuhamel_abs_le_of_continuousOrbits
#print axioms auxiliaryDivergenceChemSourceDiffGradDuhamel_abs_le_of_continuousOrbits
#print axioms auxiliaryMildMapDiv_continuousValueDiffFrontier_of_rateData
#print axioms auxiliaryMildMapDiv_continuousRateEstimates
#print axioms auxiliaryMildMapDivContinuousBanachRealization_contracting
#print axioms auxiliaryFlowDiv_localExists_continuous
#print axioms auxiliaryMildMapDivReachableArbitrarilyLong_of_uniformRestart
#print axioms auxiliaryFlowDiv_globalExists_of_uniformRestart
#print axioms auxiliaryFlowDiv_globalExists
#print axioms auxiliaryFlowDiv_globalExists_continuous
#print axioms auxiliaryFlowDiv_globalExists_trapped
#print axioms WholeLineAuxiliaryDivGlobalFamilyData.globalSolution
#print axioms WholeLineAuxiliaryDivGlobalFamilyData.raw_solution
#print axioms auxiliaryDivGlobalFamily_of_frozenSignal

end ShenWork.PaperOne
