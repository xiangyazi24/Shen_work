import ShenWork.PaperOne.WholeLineAuxiliaryMildMapDivergence
import ShenWork.PaperOne.WholeLineFrozenSignal
import ShenWork.PaperOne.WholeLineWaveTrap
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
# Local divergence-form auxiliary flow

This file is the value-only analogue of `WholeLineAuxiliaryContraction` for the
divergence-form auxiliary mild map.  The contraction constant is the banked
`A * sqrt T + B * T` rate from `AuxiliaryMildMapDivRateEstimates`.

The final section records the frozen-signal discharges that are available from
the current library: the `Vx` bound from `frozenSignal_grad_bound`, and the
unit-interval bound on the frozen profile from `WaveTrap`.
-/

/-- Closed short-time contraction package for the value-only divergence mild
map on the wave-barrier trap. -/
structure AuxiliaryMildMapDivContractionData
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
        AuxiliaryValueDistanceBound T (K * dist)
          (auxiliaryMildMapDiv p c Uplus W V Vx u)
          (auxiliaryMildMapDiv p c Uplus Z V Vx u)

/-- Short-time contraction for the divergence-form auxiliary mild map on the
closed wave-barrier trap. -/
theorem auxiliaryMildMapDiv_contraction_on_smallTime
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapDivRateEstimates p c Uplus V Vx u κ κt D A B) :
    ∃ T0 K : ℝ,
      0 < T0 ∧ 0 ≤ K ∧ K < 1 ∧
        (∀ W, AuxiliaryBarrierTrap κ κt D T0 W →
          AuxiliaryBarrierTrap κ κt D T0
            (auxiliaryMildMapDiv p c Uplus W V Vx u)) ∧
        (∀ W Z dist, 0 ≤ dist →
          AuxiliaryBarrierTrap κ κt D T0 W →
          AuxiliaryBarrierTrap κ κt D T0 Z →
          AuxiliaryValueDistanceBound T0 dist W Z →
            AuxiliaryValueDistanceBound T0 (K * dist)
              (auxiliaryMildMapDiv p c Uplus W V Vx u)
              (auxiliaryMildMapDiv p c Uplus Z V Vx u)) := by
  obtain ⟨T0, hT0, hsmall⟩ :=
    exists_small_contraction_time_target H.hA_nonneg H.hB_nonneg one_pos
  let K : ℝ := A * Real.sqrt T0 + B * T0
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg
      (mul_nonneg H.hA_nonneg (Real.sqrt_nonneg T0))
      (mul_nonneg H.hB_nonneg hT0.le)
  refine ⟨T0, K, hT0, hK_nonneg, hsmall, ?_, ?_⟩
  · intro W hW
    exact H.mapsTo_of_small T0 hT0 hsmall W hW
  · intro W Z dist hdist hW hZ hdistWZ t ht x
    exact H.value_diff_of_small T0 hT0 hsmall W Z dist hdist
      hW hZ hdistWZ t ht x

/-- Package the small-time divergence contraction into a reusable data record. -/
theorem auxiliaryMildMapDiv_contractionData
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapDivRateEstimates p c Uplus V Vx u κ κt D A B) :
    Nonempty (AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D) := by
  obtain ⟨T0, K, hT0, hK_nonneg, hK_lt_one, hmapsTo, hcontr⟩ :=
    auxiliaryMildMapDiv_contraction_on_smallTime H
  refine ⟨?_⟩
  exact
    { T := T0
      hT_pos := hT0
      K := K
      hK_nonneg := hK_nonneg
      hK_lt_one := hK_lt_one
      mapsTo := hmapsTo
      contraction := hcontr }

/-- A complete closed-trap metric model for the divergence value map at a fixed
short time. -/
structure AuxiliaryMildMapDivBanachRealization
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D T K : ℝ) (X : Type*) [MetricSpace X] where
  F : X → X
  seed : X
  eval : X → ℝ → ℝ → ℝ
  trap :
    ∀ z, AuxiliaryBarrierTrap κ κt D T (eval z)
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

/-- The same realization with its complete metric-space instances packaged. -/
structure AuxiliaryMildMapDivBanachRealizationData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D : ℝ)
    (C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D) where
  X : Type*
  [instMetric : MetricSpace X]
  [instComplete : CompleteSpace X]
  [instNonempty : Nonempty X]
  realization :
    AuxiliaryMildMapDivBanachRealization p c Uplus V Vx u κ κt D C.T C.K X

/-- The closed-trap realization inherits a genuine `ContractingWith` structure
from the pointwise divergence mild-map contraction data. -/
theorem auxiliaryMildMapDivBanachRealization_contracting
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D : ℝ}
    (C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D)
    {X : Type*} [MetricSpace X]
    (R : AuxiliaryMildMapDivBanachRealization
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

/-- One finite horizon of the divergence-form auxiliary mild problem, with the
barrier trap. -/
def AuxiliaryMildMapDivSolutionOn
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D T : ℝ) (w : ℝ → ℝ → ℝ) : Prop :=
  0 < T ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      w t x = auxiliaryMildMapDiv p c Uplus w V Vx u t x) ∧
    AuxiliaryBarrierTrap κ κt D T w

/-- Reachability of one finite divergence-form auxiliary-flow horizon. -/
def AuxiliaryMildMapDivReachableHorizon
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D T : ℝ) : Prop :=
  ∃ w : ℝ → ℝ → ℝ,
    AuxiliaryMildMapDivSolutionOn p c Uplus V Vx u κ κt D T w

/-- Banach fixed-point extraction for one already constructed divergence
small-time contraction datum. -/
theorem auxiliaryFlowDiv_localExists_of_contractionData
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D : ℝ}
    (C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D)
    (Rdata :
      AuxiliaryMildMapDivBanachRealizationData p c Uplus V Vx u κ κt D C) :
    AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D C.T := by
  letI := Rdata.instMetric
  letI := Rdata.instComplete
  letI := Rdata.instNonempty
  let R := Rdata.realization
  have hcontract :
      ContractingWith ⟨C.K, C.hK_nonneg⟩ R.F :=
    auxiliaryMildMapDivBanachRealization_contracting C R
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

/-- Local divergence-form auxiliary-flow existence from the closed small-time
contraction and a closed-trap Banach realization for that contraction datum. -/
theorem auxiliaryFlowDiv_localExists
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D A B : ℝ}
    (H : AuxiliaryMildMapDivRateEstimates p c Uplus V Vx u κ κt D A B)
    (hrealize :
      ∀ C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D,
        AuxiliaryMildMapDivBanachRealizationData p c Uplus V Vx u κ κt D C) :
    ∃ T0 > 0,
      AuxiliaryMildMapDivReachableHorizon p c Uplus V Vx u κ κt D T0 := by
  obtain ⟨T0, K, hT0, hK_nonneg, hK_lt_one, hmapsTo, hcontr⟩ :=
    auxiliaryMildMapDiv_contraction_on_smallTime H
  let C : AuxiliaryMildMapDivContractionData p c Uplus V Vx u κ κt D :=
    { T := T0
      hT_pos := hT0
      K := K
      hK_nonneg := hK_nonneg
      hK_lt_one := hK_lt_one
      mapsTo := hmapsTo
      contraction := hcontr }
  exact ⟨C.T, C.hT_pos, auxiliaryFlowDiv_localExists_of_contractionData C (hrealize C)⟩

/-! ## Frozen-signal bottom discharges -/

/-- Wave-trap membership gives the unit-interval profile condition required by
the divergence rate data. -/
theorem waveTrap_unitIntervalProfile
    {κ κt D : ℝ} {u : ℝ → ℝ}
    (hu : u ∈ WaveTrap κ κt D) :
    UnitIntervalProfile u := by
  intro x
  exact ⟨waveTrap_mem_nonneg hu x, waveTrap_mem_le_one hu x⟩

/-- Brick-4 frozen-signal gradient bound, specialized to a wave-trap profile.

The continuity assumption is necessary because `WaveTrap` itself currently
records barrier and monotonicity data, but not continuity. -/
theorem frozenSignal_Vx_bound_one_of_waveTrap
    {γ κ κt D : ℝ} {u : ℝ → ℝ}
    (hγ : 1 ≤ γ) (hu : u ∈ WaveTrap κ κt D)
    (hu_cont : Continuous u) :
    ∀ x, |deriv (frozenSignal γ u) x| ≤ 1 := by
  intro x
  exact frozenSignal_grad_bound hγ hu_cont
    (fun y => waveTrap_mem_nonneg hu y)
    (fun y => waveTrap_mem_le_one hu y) x

/-- Continuity of the explicit lower-order divergence value source. -/
theorem auxiliaryValueSource_continuous_of_continuous
    {p : CMParams} {W u : ℝ → ℝ}
    (hW : Continuous W) (hu : Continuous u) :
    Continuous (auxiliaryValueSource p W u) := by
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hWm : Continuous fun y => (W y) ^ p.m :=
    (Real.continuous_rpow_const hm_nonneg).comp hW
  have hWγ : Continuous fun y => (W y) ^ p.γ :=
    (Real.continuous_rpow_const hγ_nonneg).comp hW
  have huγ : Continuous fun y => (u y) ^ p.γ :=
    (Real.continuous_rpow_const hγ_nonneg).comp hu
  have hWα : Continuous fun y => (W y) ^ p.α :=
    (Real.continuous_rpow_const hα_nonneg).comp hW
  simpa [auxiliaryValueSource] using
    ((continuous_const.mul hWm).mul (hWγ.sub huγ)).add
      (hW.mul (continuous_const.sub hWα))

/-- Continuity, hence a.e. strong measurability, of the explicit value-source
difference for continuous slices. -/
theorem auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuous
    {p : CMParams} {W Z : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {s : ℝ}
    (hW : Continuous (W s)) (hZ : Continuous (Z s))
    (hu : Continuous u) :
    AEStronglyMeasurable
      (fun y => auxiliaryValueSourceDiff p W Z u s y) volume := by
  have hcont :
      Continuous (fun y => auxiliaryValueSourceDiff p W Z u s y) := by
    simpa [auxiliaryValueSourceDiff] using
      (auxiliaryValueSource_continuous_of_continuous
        (p := p) (W := W s) (u := u) hW hu).sub
        (auxiliaryValueSource_continuous_of_continuous
          (p := p) (W := Z s) (u := u) hZ hu)
  exact hcont.aestronglyMeasurable

/-- The frozen-signal rate-data fields that the current global
`AuxiliaryMildMapDivRateData` structure still requires in addition to the
discharged `Vx` and `u` bounds.

This is a frontier record rather than an axiom: each field is an explicit
analytic statement.  In particular, the current `AuxiliaryMildMapDivRateData`
quantifies its measurability and Duhamel-linearity fields over every
`AuxiliaryBarrierTrap` trajectory, while `AuxiliaryBarrierTrap` does not record
continuity or measurability of those trajectories. -/
structure AuxiliaryMildMapDivFrozenSignalFrontierData
    (p : CMParams) (c : ℝ) (Uplus u : ℝ → ℝ)
    (κ κt D : ℝ) : Prop where
  mapsTo :
    AuxiliaryMildMapDivMapsToFrontier p c Uplus
      (frozenSignal p.γ u)
      (fun x => deriv (frozenSignal p.γ u) x)
      u κ κt D
      (auxiliaryMildMapDivGradientRate p 1)
      (auxiliaryValueSourceLipConst p)
  value_source_measurable :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∀ s ∈ Set.Icc (0 : ℝ) t,
            AEStronglyMeasurable
              (fun y => auxiliaryValueSourceDiff p W Z u s y) volume
  value_duhamel_sub :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          auxiliaryValueDuhamelDiv p c W u t x -
              auxiliaryValueDuhamelDiv p c Z u t x =
            movingFrameDuhamel c
              (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x
  div_grad_integrable :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          IntervalIntegrable
            (fun s : ℝ =>
              movingFrameHeatGradOp c (t - s)
                (fun y =>
                  auxiliaryDivergenceChemSourceDiff p W Z
                    (frozenSignal p.γ u)
                    (fun x => deriv (frozenSignal p.γ u) x) s y) x)
            volume 0 t
  div_grad_duhamel_sub :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          auxiliaryDivergenceChemDuhamel p c W
              (frozenSignal p.γ u)
              (fun y => deriv (frozenSignal p.γ u) y) t x -
            auxiliaryDivergenceChemDuhamel p c Z
              (frozenSignal p.γ u)
              (fun y => deriv (frozenSignal p.γ u) y) t x =
            movingFrameGradDuhamel c
              (fun s y =>
                auxiliaryDivergenceChemSourceDiff p W Z
                  (frozenSignal p.γ u)
                  (fun z => deriv (frozenSignal p.γ u) z) s y) t x

/-- Constructor for the existing divergence rate-data package after discharging
the frozen-signal `Vx` bound and the wave-trap `u_unit` field.

The remaining argument is the exact analytic frontier still required by the
current global `AuxiliaryMildMapDivRateData` interface. -/
theorem auxiliaryMildMapDivRateData_of_frozenSignal
    {p : CMParams} {c : ℝ} {Uplus u : ℝ → ℝ} {κ κt D : ℝ}
    (hu : u ∈ WaveTrap κ κt D) (hu_cont : Continuous u)
    (H : AuxiliaryMildMapDivFrozenSignalFrontierData p c Uplus u κ κt D) :
    AuxiliaryMildMapDivRateData p c Uplus
      (frozenSignal p.γ u)
      (fun x => deriv (frozenSignal p.γ u) x)
      u κ κt D 1 where
  CVx_nonneg := by norm_num
  Vx_bound := frozenSignal_Vx_bound_one_of_waveTrap p.hγ hu hu_cont
  u_unit := waveTrap_unitIntervalProfile hu
  mapsTo := H.mapsTo
  value_source_measurable := H.value_source_measurable
  value_duhamel_sub := H.value_duhamel_sub
  div_grad_integrable := H.div_grad_integrable
  div_grad_duhamel_sub := H.div_grad_duhamel_sub

/-- Frozen-signal divergence-form rate estimates from the explicit frontier
data above. -/
theorem auxiliaryMildMapDiv_rateEstimates_of_frozenSignal
    {p : CMParams} {c : ℝ} {Uplus u : ℝ → ℝ} {κ κt D : ℝ}
    (hu : u ∈ WaveTrap κ κt D) (hu_cont : Continuous u)
    (H : AuxiliaryMildMapDivFrozenSignalFrontierData p c Uplus u κ κt D) :
    AuxiliaryMildMapDivRateEstimates p c Uplus
      (frozenSignal p.γ u)
      (fun x => deriv (frozenSignal p.γ u) x)
      u κ κt D
      (auxiliaryMildMapDivGradientRate p 1)
      (auxiliaryValueSourceLipConst p) :=
  auxiliaryMildMapDiv_rateEstimates
    (auxiliaryMildMapDivRateData_of_frozenSignal hu hu_cont H)

#print axioms auxiliaryMildMapDiv_contraction_on_smallTime
#print axioms auxiliaryMildMapDivBanachRealization_contracting
#print axioms auxiliaryFlowDiv_localExists_of_contractionData
#print axioms auxiliaryFlowDiv_localExists
#print axioms waveTrap_unitIntervalProfile
#print axioms frozenSignal_Vx_bound_one_of_waveTrap
#print axioms auxiliaryValueSource_continuous_of_continuous
#print axioms auxiliaryValueSourceDiff_aestronglyMeasurable_of_continuous
#print axioms auxiliaryMildMapDivRateData_of_frozenSignal
#print axioms auxiliaryMildMapDiv_rateEstimates_of_frozenSignal

end ShenWork.PaperOne
