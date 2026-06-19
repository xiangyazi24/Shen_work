import ShenWork.PaperOne.WholeLineTravelingWaveResidualReduced
import ShenWork.PaperOne.WholeLineDuhamelDifferentiation
import ShenWork.PaperOne.WholeLineAuxiliaryGlobal
import ShenWork.PaperOne.WholeLineProfileRegularity
import Mathlib.Tactic

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

private theorem differentiableAt_deriv_of_contDiff_two_reduced_local
    {V : ℝ → ℝ} (hV : ContDiff ℝ 2 V) :
    ∀ x, DifferentiableAt ℝ (deriv V) x := by
  have hD : Differentiable ℝ (iteratedDeriv 1 V) :=
    hV.differentiable_iteratedDeriv 1 (by norm_num)
  intro x
  simpa [iteratedDeriv_one] using hD x

/--
Family-level auxiliary-flow inputs from which the banked global-existence
theorem selects one trapped global mild solution for each frozen profile.
-/
structure WholeLineAuxiliaryGlobalFamilyData
    (p : CMParams) (c κt D : ℝ) where
  A : (ℝ → ℝ) → ℝ
  B : (ℝ → ℝ) → ℝ
  rate :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      AuxiliaryMildMapRateEstimates p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D (A U) (B U)
  realize :
    ∀ U, (hU : U ∈ WaveTrap (waveExponent c) κt D) →
      ∀ C : AuxiliaryMildMapContractionData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          (waveExponent c) κt D,
        AuxiliaryMildMapBanachRealizationData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          (waveExponent c) κt D C
  restart :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      AuxiliaryUniformRestartGluingFromLocalBanach p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D

namespace WholeLineAuxiliaryGlobalFamilyData

def globalSolution
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryGlobalFamilyData p c κt D)
    (U : ℝ → ℝ) (hU : U ∈ WaveTrap (waveExponent c) κt D) :
    AuxiliaryGlobalMildSolutionFor p c
      (upperBarrier (waveExponent c))
      (frozenSignal p.γ U)
      (fun x => deriv (frozenSignal p.γ U) x)
      (waveExponent c) κt D :=
  auxiliaryFlow_globalExists
    (H.rate U hU) (H.realize U hU) (H.restart U hU)

/-- The selected global auxiliary orbit; off the trap it is an inert extension. -/
noncomputable def raw_w
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryGlobalFamilyData p c κt D) :
    (ℝ → ℝ) → ℝ → ℝ → ℝ :=
  by
    classical
    exact fun U =>
      if hU : U ∈ WaveTrap (waveExponent c) κt D then
        Classical.choose (H.globalSolution U hU)
      else
        fun _t x => upperBarrier (waveExponent c) x

/-- The selected spatial-gradient component of the global auxiliary orbit. -/
noncomputable def raw_wx
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryGlobalFamilyData p c κt D) :
    (ℝ → ℝ) → ℝ → ℝ → ℝ :=
  by
    classical
    exact fun U =>
      if hU : U ∈ WaveTrap (waveExponent c) κt D then
        Classical.choose (Classical.choose_spec (H.globalSolution U hU))
      else
        fun _t _x => 0

theorem raw_solution
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryGlobalFamilyData p c κt D)
    (U : ℝ → ℝ) (hU : U ∈ WaveTrap (waveExponent c) κt D) :
    ∀ T > 0,
      AuxiliaryMildSolutionOn p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D T
        (H.raw_w U) (H.raw_wx U) := by
  have hglobal :=
    Classical.choose_spec
      (Classical.choose_spec (H.globalSolution U hU))
  simpa [raw_w, raw_wx, hU] using hglobal

end WholeLineAuxiliaryGlobalFamilyData

/--
A certificate that one long-time image is represented by a differentiated
auxiliary mild slice with pointwise gradient bounds.

The `image_eq` field is exactly the missing bridge when the banked Duhamel
Leibniz theorem is compared with the final long-time compactness field.
-/
structure WholeLineLongTimeImageDerivativeCertificate
    (p : CMParams) (c κ Λ : ℝ)
    (U : ℝ → ℝ) (W Wx : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Type where
  t : ℝ
  B0 : ℝ
  BD : ℝ
  total_le : B0 + BD ≤ Λ
  image_eq :
    F =
      fun x =>
        auxiliaryMildMap p c (upperBarrier κ) W Wx
          (frozenSignal p.γ U)
          (fun y => deriv (frozenSignal p.γ U) y) t x
  init_hasDeriv :
    ∀ x,
      HasDerivAt
        (fun y : ℝ => movingFrameHeatOp c t (upperBarrier κ) y)
        (movingFrameHeatGradOp c t (upperBarrier κ) x) x
  duhamel_hasDeriv :
    ∀ x,
      HasDerivAt
        (fun y : ℝ =>
          auxiliaryDuhamel p c W Wx
            (frozenSignal p.γ U)
            (fun z => deriv (frozenSignal p.γ U) z) t y)
        (auxiliaryGradDuhamel p c W Wx
          (frozenSignal p.γ U)
          (fun z => deriv (frozenSignal p.γ U) z) t x) x
  init_bound :
    ∀ x, |movingFrameHeatGradOp c t (upperBarrier κ) x| ≤ B0
  duhamel_bound :
    ∀ x,
      |auxiliaryGradDuhamel p c W Wx
        (frozenSignal p.γ U)
        (fun z => deriv (frozenSignal p.γ U) z) t x| ≤ BD

namespace WholeLineLongTimeImageDerivativeCertificate

theorem differentiable
    {p : CMParams} {c κ Λ : ℝ}
    {U : ℝ → ℝ} {W Wx : ℝ → ℝ → ℝ} {F : ℝ → ℝ}
    (H : WholeLineLongTimeImageDerivativeCertificate p c κ Λ U W Wx F) :
    Differentiable ℝ F := by
  rw [H.image_eq]
  intro x
  exact
    (auxiliaryMildMap_hasDerivAt_of_duhamel_bridge
      (p := p) (c := c) (t := H.t) (x := x)
      (Uplus := upperBarrier κ) (W := W) (Wx := Wx)
      (V := frozenSignal p.γ U)
      (Vx := fun y => deriv (frozenSignal p.γ U) y)
      (H.init_hasDeriv x) (H.duhamel_hasDeriv x)).differentiableAt

theorem deriv_bound
    {p : CMParams} {c κ Λ : ℝ}
    {U : ℝ → ℝ} {W Wx : ℝ → ℝ → ℝ} {F : ℝ → ℝ}
    (H : WholeLineLongTimeImageDerivativeCertificate p c κ Λ U W Wx F) :
    ∀ x, |deriv F x| ≤ Λ := by
  intro x
  rw [H.image_eq]
  exact
    (auxiliaryMildMap_deriv_abs_le_from_duhamel_bridge
      (p := p) (c := c) (B0 := H.B0) (BD := H.BD) (t := H.t)
      (Uplus := upperBarrier κ) (W := W) (Wx := Wx)
      (V := frozenSignal p.γ U)
      (Vx := fun y => deriv (frozenSignal p.γ U) y)
      H.init_hasDeriv H.duhamel_hasDeriv H.init_bound
      H.duhamel_bound x).trans H.total_le

end WholeLineLongTimeImageDerivativeCertificate

/-- Family form of the long-time-image derivative bridge. -/
structure WholeLineLongTimeImageDerivativeBridgeData
    (p : CMParams) (c κ κt D Λ : ℝ)
    (raw_w raw_wx : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Type where
  lambda_nonneg : 0 ≤ Λ
  certificate :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap κ κt D) →
        ∀ n,
          WholeLineLongTimeImageDerivativeCertificate p c κ Λ
            (seq n) (raw_w (seq n)) (raw_wx (seq n))
            (longTimeMap (wholeLineForwardOrbitExtension κ raw_w) (seq n))

namespace WholeLineLongTimeImageDerivativeBridgeData

theorem image_differentiable
    {p : CMParams} {c κ κt D Λ : ℝ}
    {raw_w raw_wx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineLongTimeImageDerivativeBridgeData p c κ κt D Λ raw_w raw_wx) :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap κ κt D) →
        ∀ n, Differentiable ℝ
          (longTimeMap (wholeLineForwardOrbitExtension κ raw_w) (seq n)) := by
  intro seq hseq n
  exact (H.certificate seq hseq n).differentiable

theorem image_deriv_bound
    {p : CMParams} {c κ κt D Λ : ℝ}
    {raw_w raw_wx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineLongTimeImageDerivativeBridgeData p c κ κt D Λ raw_w raw_wx) :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap κ κt D) →
        ∀ n x,
          |deriv
            (longTimeMap (wholeLineForwardOrbitExtension κ raw_w) (seq n)) x|
              ≤ Λ := by
  intro seq hseq n x
  exact (H.certificate seq hseq n).deriv_bound x

theorem parabolicEquicontinuity
    {p : CMParams} {c κ κt D Λ : ℝ}
    {raw_w raw_wx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineLongTimeImageDerivativeBridgeData p c κ κt D Λ raw_w raw_wx) :
    LongTimeMapParabolicEquicontinuity κ κt D
      (wholeLineForwardOrbitExtension κ raw_w) :=
  longTimeMap_parabolic_equicontinuity_of_uniform_deriv_bound
    H.lambda_nonneg H.image_differentiable H.image_deriv_bound

end WholeLineLongTimeImageDerivativeBridgeData

/--
The residual fields still needed after the currently banked whole-line
discharges are wired into the final traveling-wave existence theorem.
-/
structure WholeLineWaveExistenceReducedResidualData
    (p : CMParams) (c κt D Λ : ℝ)
    (Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D)
    (wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (p3 : CM2Params) where
  kappa_lt_kappat : waveExponent c < κt
  D_ge_one : 1 ≤ D
  paper3_chi_nonpos : p3.χ₀ ≤ 0
  orbit_properties :
    WholeLineOrbitPropertiesData p c κt D Haux.raw_w
  auxiliaryDuhamel_continuity :
    ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
        (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t)
  finite_time_slice_continuity :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t, Continuous
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t)
  longTime_uniform_tail :
    LongTimeMapUniformTail (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
  longTime_image_derivative_bridge :
    WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
      Haux.raw_w Haux.raw_wx
  longTime_stationarity :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineLongTimeStationarityData p c
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)
        (wt U) (Haux.raw_wx U) (wxx U)
        (wholeLineLongTimeLimit
          (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
  fixedPoint_profile_contDiff2 :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ContDiff ℝ 2 U
  fixedPoint_flat_left :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ShenWork.Paper1.FrozenStationaryFlatAtLeft p U
  translate_limit_identification :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ∀ L : ℝ,
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L →
          ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
            p3 L

namespace WholeLineWaveExistenceReducedResidualData

theorem mild_decomp
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (_H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3) :
    ∀ t U x,
      wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t x =
        residualAuxSemigroupTerm c (waveExponent c) t x +
          (-p.χ) * residualAuxChemDuhamel t U x +
            residualAuxReactionDuhamel p c (waveExponent c) κt D
              Haux.raw_w Haux.raw_wx t U x := by
  intro t U x
  by_cases hU : U ∈ WaveTrap (waveExponent c) κt D
  · by_cases ht : 0 ≤ t
    · have hT : 0 < t + 1 := by linarith
      have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
      have hsol := Haux.raw_solution U hU (t + 1) hT
      have hmild := hsol.2.1 t ht_mem x
      rw [wholeLineForwardOrbitExtension, if_pos ht, hmild]
      simp [residualAuxSemigroupTerm, residualAuxChemDuhamel,
        residualAuxReactionDuhamel, residualAuxDuhamelOnTrap, hU, ht,
        auxiliaryMildMap]
    · simp [wholeLineForwardOrbitExtension, residualAuxSemigroupTerm,
        residualAuxChemDuhamel, residualAuxReactionDuhamel,
        residualAuxDuhamelOnTrap, hU, ht]
  · simp [residualAuxSemigroupTerm, residualAuxChemDuhamel,
      residualAuxReactionDuhamel, hU]

def longTimeContinuityFields
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3) :
    WholeLineLongTimeContinuityFields (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) :=
  wholeLine_longTime_continuity_fields_of_mildmap
    (κ := waveExponent c) (κt := κt) (D := D) (χ := p.χ)
    (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
    (semigroupTerm := residualAuxSemigroupTerm c (waveExponent c))
    (chemDuhamel := residualAuxChemDuhamel)
    (reactionDuhamel :=
      residualAuxReactionDuhamel p c (waveExponent c) κt D
        Haux.raw_w Haux.raw_wx)
    H.mild_decomp
    (fun _ =>
      localUniformContinuousOn_zero
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D))
    (fun t =>
      residualAuxReactionDuhamel_continuity
        (H.auxiliaryDuhamel_continuity t))
    H.finite_time_slice_continuity
    H.longTime_uniform_tail

theorem fixedPoint_signal_contDiff2
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ContDiff ℝ 2 (frozenSignal p.γ U) := by
  intro U hU hfixed
  exact
    frozenSignal_contDiff_two p
      ⟨(H.fixedPoint_profile_contDiff2 U hU hfixed).continuous,
        waveTrap_bounded hU⟩
      (fun x => waveTrap_mem_nonneg hU x)

theorem fixedPoint_differentiable
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3)
    {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hfixed :
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U) :
    Differentiable ℝ U := by
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap (waveExponent c) κt D := fun _ => hU
  have hdiff :=
    H.longTime_image_derivative_bridge.image_differentiable seq hseq 0
  simpa [seq, hfixed] using hdiff

theorem fixedPoint_deriv_bound
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3)
    {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hfixed :
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U) :
    ∀ x, |deriv U x| ≤ Λ := by
  intro x
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap (waveExponent c) κt D := fun _ => hU
  have hbound :=
    H.longTime_image_derivative_bridge.image_deriv_bound seq hseq 0 x
  simpa [seq, hfixed] using hbound

theorem fixedPoint_frozenWaveOperator_zero
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3)
    {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hfixed :
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U) :
    ∀ x, ShenWork.Paper1.frozenWaveOperator p c U U x = 0 := by
  let wU : ℝ → ℝ → ℝ :=
    wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U
  have hlim_eq : wholeLineLongTimeLimit wU = U := by
    simpa [wU, longTimeMap] using hfixed
  have hstat :=
    wholeLine_longTime_stationary
      (p := p) (c := c) (u := U)
      (w := wU) (wt := wt U) (wx := Haux.raw_wx U) (wxx := wxx U)
      (H.longTime_stationarity U hU)
  have haux : wholeLineAuxStationaryEquation p c U := by
    intro x
    rw [wholeLine_aux_operator_eq_residual p c U x]
    simpa [hlim_eq] using hstat x
  have hU_contDiff : ContDiff ℝ 2 U :=
    H.fixedPoint_profile_contDiff2 U hU hfixed
  have hV_contDiff : ContDiff ℝ 2 (frozenSignal p.γ U) :=
    H.fixedPoint_signal_contDiff2 U hU hfixed
  have hU_bdd : IsCUnifBdd U :=
    ⟨hU_contDiff.continuous, waveTrap_bounded hU⟩
  have hU_nonneg : ∀ x, 0 ≤ U x :=
    fun x => waveTrap_mem_nonneg hU x
  have hU_diff : ∀ x, DifferentiableAt ℝ U x := by
    intro x
    exact hU_contDiff.differentiable two_ne_zero x
  have hV_deriv_diff :
      ∀ x, DifferentiableAt ℝ (deriv (frozenSignal p.γ U)) x :=
    differentiableAt_deriv_of_contDiff_two_reduced_local hV_contDiff
  have hdiv : wholeLineDivergenceStationaryEquation p c U :=
    (wholeLine_diagonal_stationary p hU_bdd hU_nonneg hU_diff hV_deriv_diff).mp haux
  intro x
  rw [← wholeLineDivergenceStationaryOperator_eq_frozenWaveOperator p c U x]
  exact hdiv x

def translate_compactness
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ∀ L : ℝ, Tendsto U atBot (𝓝 L) → L < 1 →
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L := by
  intro U hU hfixed L hlim _hL_lt_one
  have hκ : 0 < waveExponent c :=
    waveExponent_pos ((H.orbit_properties.trapping U hU).speed_ge)
  have hcont : Continuous U :=
    (H.fixedPoint_profile_contDiff2 U hU hfixed).continuous
  have hdiff : Differentiable ℝ U :=
    H.fixedPoint_differentiable hU hfixed
  have hderiv : ∀ x, |deriv U x| ≤ Λ :=
    H.fixedPoint_deriv_bound hU hfixed
  have hequi :
      ∀ K : Set ℝ, IsCompact K →
        EquicontinuousOn
          (fun (n : ℕ) (x : ℝ) => U (x + (-(n : ℝ)))) K :=
    translate_equicontinuousOn_of_uniform_deriv_bound
      H.longTime_image_derivative_bridge.lambda_nonneg hdiff hderiv
  exact
    translate_compactness_of_equicontinuity
      (p := p) (c := c) (κ := waveExponent c) (κt := κt) (D := D)
      (U := U) (L := L)
      hκ H.kappa_lt_kappat H.D_ge_one hU hcont hequi hlim
      (H.fixedPoint_frozenWaveOperator_zero hU hfixed)
      (H.fixedPoint_flat_left U hU hfixed)

def travelingWaveData
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3) :
    WholeLineTravelingWaveData p c (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
      wt Haux.raw_wx wxx p3 where
  kappa_lt_kappat := H.kappa_lt_kappat
  D_ge_one := H.D_ge_one
  orbit_lower_bound := (wholeLine_orbit_fields H.orbit_properties).1
  orbit_upper_bound := (wholeLine_orbit_fields H.orbit_properties).2.1
  orbit_spatial_antitone := (wholeLine_orbit_fields H.orbit_properties).2.2
  longTime_image_continuity :=
    H.longTimeContinuityFields.longTime_image_continuity
  longTime_parabolic_equicontinuity :=
    H.longTime_image_derivative_bridge.parabolicEquicontinuity
  longTime_finite_time_continuity :=
    H.longTimeContinuityFields.longTime_finite_time_continuity
  longTime_uniform_tail :=
    H.longTimeContinuityFields.longTime_uniform_tail
  longTime_stationarity := H.longTime_stationarity
  fixedPoint_profile_contDiff2 := H.fixedPoint_profile_contDiff2
  fixedPoint_signal_contDiff2 := H.fixedPoint_signal_contDiff2
  translate_compactness := H.translate_compactness
  translate_limit_identification := H.translate_limit_identification
  paper3_chi_nonpos := H.paper3_chi_nonpos

end WholeLineWaveExistenceReducedResidualData

/--
Reduced whole-line traveling-wave existence assembler.

All currently available banked whole-line discharges are consumed into the
final `WholeLineTravelingWaveProfile`; the fields of
`WholeLineWaveExistenceReducedResidualData` are the remaining formal frontier.
-/
theorem wholeLine_travelingWave_exists_reduced
    (p : CMParams)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    {c κt D Λ : ℝ}
    (hc : 2 < c)
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceReducedResidualData p c κt D Λ Haux wt wxx p3) :
    ∃ Ustar Vstar : ℝ → ℝ,
      WholeLineTravelingWaveProfile p c (waveExponent c) Ustar Vstar := by
  exact
    wholeLine_travelingWave_exists
      (p := p) hχ hα (c := c) (κt := κt) (D := D) hc
      (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
      (wt := wt) (wx := Haux.raw_wx) (wxx := wxx) (p3 := p3)
      H.travelingWaveData

#print axioms WholeLineAuxiliaryGlobalFamilyData.globalSolution
#print axioms WholeLineAuxiliaryGlobalFamilyData.raw_solution
#print axioms WholeLineLongTimeImageDerivativeCertificate.differentiable
#print axioms WholeLineLongTimeImageDerivativeCertificate.deriv_bound
#print axioms WholeLineLongTimeImageDerivativeBridgeData.parabolicEquicontinuity
#print axioms WholeLineWaveExistenceReducedResidualData.mild_decomp
#print axioms WholeLineWaveExistenceReducedResidualData.longTimeContinuityFields
#print axioms WholeLineWaveExistenceReducedResidualData.fixedPoint_signal_contDiff2
#print axioms WholeLineWaveExistenceReducedResidualData.fixedPoint_frozenWaveOperator_zero
#print axioms WholeLineWaveExistenceReducedResidualData.translate_compactness
#print axioms WholeLineWaveExistenceReducedResidualData.travelingWaveData
#print axioms wholeLine_travelingWave_exists_reduced

end ShenWork.PaperOne
