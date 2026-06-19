import ShenWork.PaperOne.WholeLineWaveExistenceConsolidated
import ShenWork.PaperOne.WholeLineLeftTailDischarge
import ShenWork.PaperOne.WholeLineTimeMonotonicity
import ShenWork.PaperOne.WholeLineMovingFrameGenerator
import Mathlib.Tactic

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

def WholeLineAuxiliaryMildSliceContinuityData
    (p : CMParams) (c κt D : ℝ)
    (Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D) : Prop :=
  ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
    ∀ T, 0 < T →
      ∀ t, t ∈ Set.Icc (0 : ℝ) T →
        Continuous
          (auxiliaryMildSpatialSlice p c (upperBarrier (waveExponent c))
            (Haux.raw_w U) (Haux.raw_wx U)
            (frozenSignal p.γ U)
            (fun x => deriv (frozenSignal p.γ U) x) t)

def WholeLineTimeMonotonicityFamilyData
    (κ κt D : ℝ)
    (raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Type :=
  ∀ U, U ∈ WaveTrap κ κt D →
    ∀ s T, 0 < s → 0 < T →
      Σ a : ℝ → ℝ → ℝ, Σ b : ℝ → ℝ → ℝ, Σ A : ℝ, Σ Bb : ℝ,
        WholeLineTimeMonotonicityData
          (raw_w U) (wt U) (wx U) (wxx U) (upperBarrier κ)
          a b s T A Bb

theorem waveResidualWired9_upperBarrier_continuous (κ : ℝ) :
    Continuous (upperBarrier κ) := by
  unfold upperBarrier
  fun_prop

theorem waveResidualWired9_kappa_lt_kappat
    {p : CMParams} {c κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) :
    waveExponent c < κt :=
  H.kappa_lt_kappat

theorem waveResidualWired9_D_ge_one
    {p : CMParams} {c κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) :
    1 ≤ D :=
  H.D_ge_one

theorem waveResidualWired9_paper3_chi_nonpos
    {p : CMParams} {p3 : CM2Params}
    (hχ : p.χ ≤ 0) (hχ0 : p3.χ₀ = p.χ) :
    p3.χ₀ ≤ 0 := by
  simpa [hχ0] using hχ

def waveResidualWired9_spatial_antitone
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (H : WholeLineOrbitPropertiesData p c κt D Haux.raw_w) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineSpatialAntitoneWitness (waveExponent c) (Haux.raw_w U) :=
  H.spatial

theorem waveResidualWired9_auxiliaryDuhamel_continuity
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (Hcont :
      ∀ t,
        ShenWork.Paper1.LocalUniformContinuousOn
          (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
          (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t)) :
    ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
        (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t) :=
  Hcont

theorem waveResidualWired9_auxiliaryReactionDuhamel_continuity
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (Hcont :
      ∀ t,
        ShenWork.Paper1.LocalUniformContinuousOn
          (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
          (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t)) :
    ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
        (residualAuxReactionDuhamel p c (waveExponent c) κt D
          Haux.raw_w Haux.raw_wx t) := by
  intro t
  exact residualAuxReactionDuhamel_continuity (Hcont t)

theorem waveResidualWired9_finite_time_slice_continuity
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (Hslice : WholeLineAuxiliaryMildSliceContinuityData p c κt D Haux) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t, Continuous
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t) := by
  intro U hU t
  by_cases ht : 0 ≤ t
  · have hT : 0 < t + 1 := by linarith
    have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hsol := Haux.raw_solution U hU (t + 1) hT
    have hslice := Hslice U hU (t + 1) hT t ht_mem
    have hfun :
        wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t =
          auxiliaryMildSpatialSlice p c (upperBarrier (waveExponent c))
            (Haux.raw_w U) (Haux.raw_wx U)
            (frozenSignal p.γ U)
            (fun x => deriv (frozenSignal p.γ U) x) t := by
      funext x
      simpa [wholeLineForwardOrbitExtension, ht, auxiliaryMildSpatialSlice]
        using hsol.2.1 t ht_mem x
    simpa [hfun] using hslice
  · have hfun :
        wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t =
          upperBarrier (waveExponent c) := by
      funext x
      simp [wholeLineForwardOrbitExtension, ht]
    simpa [hfun] using
      waveResidualWired9_upperBarrier_continuous (waveExponent c)

theorem waveResidualWired9_longTime_time_antitone
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Htime :
      WholeLineTimeMonotonicityFamilyData (waveExponent c) κt D
        Haux.raw_w wt Haux.raw_wx wxx) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ x, Antitone fun t : ℝ =>
        wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t x := by
  intro U hU x t₁ t₂ ht₁₂
  by_cases ht₂ : 0 ≤ t₂
  · by_cases ht₁ : 0 ≤ t₁
    · by_cases heq : t₂ = t₁
      · subst t₂
        rfl
      · have hlt : t₁ < t₂ := by
          exact lt_of_le_of_ne ht₁₂ (fun h => heq h.symm)
        let s : ℝ := t₂ - t₁
        have hs : 0 < s := by
          dsimp [s]
          linarith
        have hT : 0 < t₂ := lt_of_le_of_lt ht₁ hlt
        rcases Htime U hU s t₂ hs hT with ⟨a, b, A, Bb, Hmono⟩
        have hmono := wholeLine_time_monotone Hmono t₁ ht₁ (by linarith) x
        have hsum : t₁ + s = t₂ := by
          dsimp [s]
          ring
        simpa [wholeLineForwardOrbitExtension, ht₁, ht₂, hsum]
          using hmono
    · have hupper := wholeLine_orbit_upper_bound Horbit U hU t₂ x
      simpa [wholeLineForwardOrbitExtension, ht₁] using hupper
  · have ht₁ : ¬ 0 ≤ t₁ := by
      intro ht₁
      exact ht₂ (le_trans ht₁ ht₁₂)
    simp [wholeLineForwardOrbitExtension, ht₁, ht₂]

theorem waveResidualWired9_longTime_evolution_eq
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ} :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        concreteLongTimeAuxiliaryWt p c (waveExponent c)
            Haux.raw_w Haux.raw_wx wxx U t x =
          wxx U t x + c * Haux.raw_wx U t x +
            auxiliaryFrozenNonlinearity p
              (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t)
              (Haux.raw_wx U t)
              (frozenSignal p.γ U)
              (fun y => deriv (frozenSignal p.γ U) y) x := by
  intro U _hU t x
  exact concreteLongTimeAuxiliaryWt_evolution_eq
    p c (waveExponent c) Haux.raw_w Haux.raw_wx wxx U t x

theorem waveResidualWired9_translate_limit_identification
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {p3 : CM2Params}
    (Hid : TranslateLimitIdentificationParabolicData p c p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ∀ L : ℝ,
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L →
          ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
            p3 L :=
  translate_limit_identification_of_T10 Hid

theorem waveResidualWired9_translate_limit_eq_one
    {p : CMParams} {c : ℝ} {p3 : CM2Params}
    (hχ : p3.χ₀ ≤ 0)
    (Hid : TranslateLimitIdentificationParabolicData p c p3)
    {U : ℝ → ℝ} {L : ℝ}
    (hcompact :
      ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
        p c U L) :
    L = 1 :=
  translate_limit_eq_one_of_T10_chi_nonpos hχ Hid hcompact

def wholeLineWaveExistenceConsolidatedResidualData_wired9
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    {w0 : ℝ → ℝ → ℝ} {V0 Vx0 : ℝ → ℝ}
    (Hparams : WholeLineOrbitTrappingData p c κt D w0 V0 Vx0)
    (hχ : p.χ ≤ 0) (hχ0 : p3.χ₀ = p.χ)
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Hduhamel :
      ∀ t,
        ShenWork.Paper1.LocalUniformContinuousOn
          (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
          (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t))
    (Hslice : WholeLineAuxiliaryMildSliceContinuityData p c κt D Haux)
    (Htime :
      WholeLineTimeMonotonicityFamilyData (waveExponent c) κt D
        Haux.raw_w
        (concreteLongTimeAuxiliaryWt p c (waveExponent c)
          Haux.raw_w Haux.raw_wx wxx)
        Haux.raw_wx wxx)
    (Htail :
      LongTimeMapUniformTail (waveExponent c) κt D
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w))
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
        Haux.raw_w Haux.raw_wx)
    (Hderiv :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        WholeLineParabolicDerivativeConvergence
          (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)
          (concreteLongTimeAuxiliaryWt p c (waveExponent c)
            Haux.raw_w Haux.raw_wx wxx U)
          (Haux.raw_wx U) (wxx U)
          (wholeLineLongTimeLimit
            (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)))
    (Hprofile :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
            U = U →
          ∃ Ux Uxx : ℝ → ℝ,
            WholeLineProfileRegularityData p U (frozenSignal p.γ U) Ux Uxx)
    (Hflat :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
            U = U →
          ShenWork.Paper1.FrozenStationaryFlatAtLeft p U)
    (Hid : TranslateLimitIdentificationParabolicData p c p3) :
    WholeLineWaveExistenceConsolidatedResidualData p c κt D Λ Haux
      (concreteLongTimeAuxiliaryWt p c (waveExponent c)
        Haux.raw_w Haux.raw_wx wxx)
      wxx p3 where
  kappa_lt_kappat := waveResidualWired9_kappa_lt_kappat Hparams
  D_ge_one := waveResidualWired9_D_ge_one Hparams
  paper3_chi_nonpos := waveResidualWired9_paper3_chi_nonpos hχ hχ0
  spatial_antitone := waveResidualWired9_spatial_antitone Horbit
  auxiliaryDuhamel_continuity :=
    waveResidualWired9_auxiliaryDuhamel_continuity Hduhamel
  finite_time_slice_continuity :=
    waveResidualWired9_finite_time_slice_continuity Hslice
  longTime_uniform_tail := Htail
  longTime_image_derivative_bridge := Himage
  longTime_time_antitone :=
    waveResidualWired9_longTime_time_antitone Horbit Htime
  longTime_derivative_convergence := Hderiv
  longTime_evolution_eq := waveResidualWired9_longTime_evolution_eq
  fixedPoint_profile_regularity := Hprofile
  fixedPoint_flat_left := Hflat
  translate_limit_identification :=
    waveResidualWired9_translate_limit_identification Hid

#print axioms WholeLineAuxiliaryMildSliceContinuityData
#print axioms WholeLineTimeMonotonicityFamilyData
#print axioms waveResidualWired9_upperBarrier_continuous
#print axioms waveResidualWired9_kappa_lt_kappat
#print axioms waveResidualWired9_D_ge_one
#print axioms waveResidualWired9_paper3_chi_nonpos
#print axioms waveResidualWired9_spatial_antitone
#print axioms waveResidualWired9_auxiliaryDuhamel_continuity
#print axioms waveResidualWired9_auxiliaryReactionDuhamel_continuity
#print axioms waveResidualWired9_finite_time_slice_continuity
#print axioms waveResidualWired9_longTime_time_antitone
#print axioms waveResidualWired9_longTime_evolution_eq
#print axioms waveResidualWired9_translate_limit_identification
#print axioms waveResidualWired9_translate_limit_eq_one
#print axioms wholeLineWaveExistenceConsolidatedResidualData_wired9

end ShenWork.PaperOne
