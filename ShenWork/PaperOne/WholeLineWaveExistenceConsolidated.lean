import ShenWork.PaperOne.WholeLineWaveExistenceReduced
import Mathlib.Tactic

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

private theorem differentiableAt_deriv_of_contDiff_two_consolidated
    {V : ℝ → ℝ} (hV : ContDiff ℝ 2 V) :
    ∀ x, DifferentiableAt ℝ (deriv V) x := by
  have hD : Differentiable ℝ (iteratedDeriv 1 V) :=
    hV.differentiable_iteratedDeriv 1 (by norm_num)
  intro x
  simpa [iteratedDeriv_one] using hD x

/--
Honest residual after discharging the type-matching whole-line banked fields.

The Schauder principle and the global auxiliary family are theorem arguments,
not fields of this residual record.  The remaining fields are exactly the
interfaces not derivable from `WholeLineAuxiliaryGlobalFamilyData` by an
available type-matching banked theorem.
-/
structure WholeLineWaveExistenceConsolidatedResidualData
    (p : CMParams) (c κt D Λ : ℝ)
    (Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D)
    (wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (p3 : CM2Params) where
  kappa_lt_kappat : waveExponent c < κt
  D_ge_one : 1 ≤ D
  paper3_chi_nonpos : p3.χ₀ ≤ 0
  spatial_antitone :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineSpatialAntitoneWitness (waveExponent c) (Haux.raw_w U)
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
  longTime_time_antitone :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ x, Antitone fun t : ℝ =>
        wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t x
  longTime_derivative_convergence :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineParabolicDerivativeConvergence
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)
        (wt U) (Haux.raw_wx U) (wxx U)
        (wholeLineLongTimeLimit
          (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U))
  longTime_evolution_eq :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        wt U t x =
          wxx U t x + c * Haux.raw_wx U t x +
            auxiliaryFrozenNonlinearity p
              (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t)
              (Haux.raw_wx U t)
              (frozenSignal p.γ U)
              (fun y => deriv (frozenSignal p.γ U) y) x
  fixedPoint_profile_regularity :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ∃ Ux Uxx : ℝ → ℝ,
          WholeLineProfileRegularityData p U (frozenSignal p.γ U) Ux Uxx
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

namespace WholeLineWaveExistenceConsolidatedResidualData

theorem orbit_lower_bound
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
    (hc : 2 < c) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        lowerBarrier (waveExponent c) κt D x ≤
          wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t x := by
  intro U hU t x
  by_cases ht : 0 ≤ t
  · have hT : 0 < t + 1 := by linarith
    have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hsol := Haux.raw_solution U hU (t + 1) hT
    simpa [wholeLineForwardOrbitExtension, ht] using
      (hsol.2.2 t ht_mem x).1
  · have hκ : 0 ≤ waveExponent c :=
      (waveExponent_pos (le_of_lt hc)).le
    simpa [wholeLineForwardOrbitExtension, ht] using
      lowerBarrier_le_upper
        (κ := waveExponent c) (κt := κt) (D := D) (x := x)
        hκ H.kappa_lt_kappat H.D_ge_one

theorem orbit_upper_bound
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (_H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t x ≤
          upperBarrier (waveExponent c) x := by
  intro U hU t x
  by_cases ht : 0 ≤ t
  · have hT : 0 < t + 1 := by linarith
    have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hsol := Haux.raw_solution U hU (t + 1) hT
    simpa [wholeLineForwardOrbitExtension, ht] using
      (hsol.2.2 t ht_mem x).2
  · simp [wholeLineForwardOrbitExtension, ht]

theorem orbit_spatial_antitone
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
    (hc : 2 < c) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t, Antitone
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U t) := by
  intro U hU t
  have hκ : 0 < waveExponent c := waveExponent_pos (le_of_lt hc)
  by_cases ht : 0 ≤ t
  · rcases H.spatial_antitone U hU with ⟨q, qt, qx, qxx, a, b, Hspace⟩
    intro x y hxy
    have hanti := orbit_spatial_antitone_forward Hspace hκ t ht hxy
    simpa [wholeLineForwardOrbitExtension, ht] using hanti
  · intro x y hxy
    have hanti := upperBarrier_antitone (κ := waveExponent c) hκ hxy
    simpa [wholeLineForwardOrbitExtension, ht] using hanti

theorem mild_decomp
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D} :
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

def finiteTimeContinuity
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3) :
    LongTimeMapFiniteTimeContinuity (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) :=
  longTime_finite_time_continuity_of_mildmap
    (κ := waveExponent c) (κt := κt) (D := D) (χ := p.χ)
    (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
    (semigroupTerm := residualAuxSemigroupTerm c (waveExponent c))
    (chemDuhamel := residualAuxChemDuhamel)
    (reactionDuhamel :=
      residualAuxReactionDuhamel p c (waveExponent c) κt D
        Haux.raw_w Haux.raw_wx)
    mild_decomp
    (fun _ =>
      localUniformContinuousOn_zero
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D))
    (fun t =>
      residualAuxReactionDuhamel_continuity
        (H.auxiliaryDuhamel_continuity t))

theorem longTime_image_continuity
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3) :
    LongTimeMapImageContinuity (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) :=
  longTime_image_continuity_of_uniform_time_limit
    H.finite_time_slice_continuity H.longTime_uniform_tail

def longTimeStationarity
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
    (hc : 2 < c) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineLongTimeStationarityData p c
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)
        (wt U) (Haux.raw_wx U) (wxx U)
        (wholeLineLongTimeLimit
          (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x) := by
  intro U hU
  exact
    longTime_stationarity_of_convergence
      (p := p) (c := c) (κ := waveExponent c) (κt := κt) (D := D)
      (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)
      (wt := wt U) (wx := Haux.raw_wx U) (wxx := wxx U)
      (V := frozenSignal p.γ U)
      (Vx := fun x => deriv (frozenSignal p.γ U) x)
      (H.longTime_time_antitone U hU)
      (H.orbit_lower_bound hc U hU)
      (H.longTime_derivative_convergence U hU)
      (H.longTime_evolution_eq U hU)

theorem fixedPoint_profile_contDiff2
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ContDiff ℝ 2 U := by
  intro U hU hfixed
  rcases H.fixedPoint_profile_regularity U hU hfixed with
    ⟨Ux, Uxx, Hreg⟩
  exact Hreg.waveProfile_contDiff_two

theorem fixedPoint_signal_contDiff2
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ContDiff ℝ 2 (frozenSignal p.γ U) := by
  intro U hU hfixed
  rcases H.fixedPoint_profile_regularity U hU hfixed with
    ⟨Ux, Uxx, Hreg⟩
  simpa using Hreg.waveSignal_contDiff_two

theorem fixedPoint_differentiable
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
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
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
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
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
    (hc : 2 < c)
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
      (H.longTimeStationarity hc U hU)
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
    differentiableAt_deriv_of_contDiff_two_consolidated hV_contDiff
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
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
    (hc : 2 < c) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ∀ L : ℝ, Tendsto U atBot (𝓝 L) → L < 1 →
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L := by
  intro U hU hfixed L hlim _hL_lt_one
  have hκ : 0 < waveExponent c := waveExponent_pos (le_of_lt hc)
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
      (H.fixedPoint_frozenWaveOperator_zero hc hU hfixed)
      (H.fixedPoint_flat_left U hU hfixed)

def travelingWaveData
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3)
    (hc : 2 < c) :
    WholeLineTravelingWaveData p c (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
      wt Haux.raw_wx wxx p3 where
  kappa_lt_kappat := H.kappa_lt_kappat
  D_ge_one := H.D_ge_one
  orbit_lower_bound := H.orbit_lower_bound hc
  orbit_upper_bound := H.orbit_upper_bound
  orbit_spatial_antitone := H.orbit_spatial_antitone hc
  longTime_image_continuity := H.longTime_image_continuity
  longTime_parabolic_equicontinuity :=
    H.longTime_image_derivative_bridge.parabolicEquicontinuity
  longTime_finite_time_continuity := H.finiteTimeContinuity
  longTime_uniform_tail := H.longTime_uniform_tail
  longTime_stationarity := H.longTimeStationarity hc
  fixedPoint_profile_contDiff2 := H.fixedPoint_profile_contDiff2
  fixedPoint_signal_contDiff2 := H.fixedPoint_signal_contDiff2
  translate_compactness := H.translate_compactness hc
  translate_limit_identification := H.translate_limit_identification
  paper3_chi_nonpos := H.paper3_chi_nonpos

end WholeLineWaveExistenceConsolidatedResidualData

/--
Final consolidated whole-line traveling-wave existence theorem.

The theorem arguments are the abstract Schauder principle and the selected
global auxiliary-flow family; all type-matching banked discharges are consumed
inside `travelingWaveData`.
-/
theorem wholeLine_travelingWave_exists_consolidated
    (p : CMParams)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    {c κt D Λ : ℝ}
    (hc : 2 < c)
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wt wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineWaveExistenceConsolidatedResidualData
      p c κt D Λ Haux wt wxx p3) :
    ∃ Ustar Vstar : ℝ → ℝ,
      WholeLineTravelingWaveProfile p c (waveExponent c) Ustar Vstar := by
  exact
    wholeLine_travelingWave_exists
      (p := p) hχ hα (c := c) (κt := κt) (D := D) hc
      (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
      (wt := wt) (wx := Haux.raw_wx) (wxx := wxx) (p3 := p3)
      (H.travelingWaveData hc)

#print axioms WholeLineWaveExistenceConsolidatedResidualData.orbit_lower_bound
#print axioms WholeLineWaveExistenceConsolidatedResidualData.orbit_upper_bound
#print axioms WholeLineWaveExistenceConsolidatedResidualData.orbit_spatial_antitone
#print axioms WholeLineWaveExistenceConsolidatedResidualData.mild_decomp
#print axioms WholeLineWaveExistenceConsolidatedResidualData.longTimeStationarity
#print axioms WholeLineWaveExistenceConsolidatedResidualData.fixedPoint_profile_contDiff2
#print axioms WholeLineWaveExistenceConsolidatedResidualData.fixedPoint_frozenWaveOperator_zero
#print axioms WholeLineWaveExistenceConsolidatedResidualData.translate_compactness
#print axioms WholeLineWaveExistenceConsolidatedResidualData.travelingWaveData
#print axioms wholeLine_travelingWave_exists_consolidated

end ShenWork.PaperOne
