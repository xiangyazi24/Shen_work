import ShenWork.PaperOne.WaveSpeedExponent
import ShenWork.PaperOne.WholeLineWaveFixedPoint
import ShenWork.PaperOne.WholeLineLongTimeMap
import ShenWork.PaperOne.WholeLineLongTimeStationary
import ShenWork.PaperOne.WholeLineDiagonalEquation
import ShenWork.PaperOne.WholeLineTravelingWave
import ShenWork.PaperOne.WholeLineLeftTail
import Mathlib.Tactic

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/--
The carried analytic frontier for the whole-line traveling-wave assembly.

The fixed point, diagonal stationary conversion, traveling-wave conversion,
right tail, and left tail are proved in the banked bricks.  This structure only
collects the hypotheses still needed to feed those bricks.
-/
structure WholeLineTravelingWaveData
    (p : CMParams) (c κ κt D : ℝ)
    (w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (p3 : CM2Params) where
  kappa_lt_kappat : κ < κt
  D_ge_one : 1 ≤ D
  schauder_principle :
    ShenWork.Paper1.LocalUniformSchauderFixedPointPrinciple
      (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D)
  orbit_lower_bound :
    ∀ U, U ∈ WaveTrap κ κt D →
      ∀ t x, lowerBarrier κ κt D x ≤ w U t x
  orbit_upper_bound :
    ∀ U, U ∈ WaveTrap κ κt D →
      ∀ t x, w U t x ≤ upperBarrier κ x
  orbit_spatial_antitone :
    ∀ U, U ∈ WaveTrap κ κt D → ∀ t, Antitone (w U t)
  longTime_image_continuity :
    LongTimeMapImageContinuity κ κt D w
  longTime_parabolic_equicontinuity :
    LongTimeMapParabolicEquicontinuity κ κt D w
  longTime_finite_time_continuity :
    LongTimeMapFiniteTimeContinuity κ κt D w
  longTime_uniform_tail :
    LongTimeMapUniformTail κ κt D w
  longTime_stationarity :
    ∀ U, U ∈ WaveTrap κ κt D →
      WholeLineLongTimeStationarityData p c
        (w U) (wt U) (wx U) (wxx U)
        (wholeLineLongTimeLimit (w U))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
  fixedPoint_profile_contDiff2 :
    ∀ U, U ∈ WaveTrap κ κt D → longTimeMap w U = U →
      ContDiff ℝ 2 U
  fixedPoint_signal_contDiff2 :
    ∀ U, U ∈ WaveTrap κ κt D → longTimeMap w U = U →
      ContDiff ℝ 2 (frozenSignal p.γ U)
  translate_compactness :
    ∀ U, U ∈ WaveTrap κ κt D → longTimeMap w U = U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → L < 1 →
        ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
          p c U L
  translate_limit_identification :
    ∀ U, U ∈ WaveTrap κ κt D → longTimeMap w U = U →
      ∀ L : ℝ,
        ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
          p c U L →
        ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
          p3 L
  paper3_chi_nonpos : p3.χ₀ ≤ 0

/-- The assembled whole-line traveling-wave profile and its translated fields. -/
structure WholeLineTravelingWaveProfile
    (p : CMParams) (c κ : ℝ) (U V : ℝ → ℝ) : Prop where
  signal_eq : V = frozenSignal p.γ U
  speed_pos : 0 < c
  profile_contDiff2 : ContDiff ℝ 2 U
  signal_contDiff2 : ContDiff ℝ 2 V
  divergence_stationary : wholeLineDivergenceStationaryEquation p c U
  elliptic_stationary :
    ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0
  global_classical_solution :
    IsGlobalClassicalSolution p
      (wholeLineTravelingWaveU c U) (wholeLineTravelingWaveV c V)
  left_limit : Tendsto U atBot (𝓝 1)
  right_limit : Tendsto U atTop (𝓝 0)
  right_tail :
    Tendsto (fun x : ℝ => U x / Real.exp (-(κ * x))) atTop (𝓝 1)
  monotone : Antitone U

/-- A `ContDiff 2` one-dimensional profile has differentiable first derivative. -/
private theorem differentiableAt_deriv_of_contDiff_two
    {V : ℝ → ℝ} (hV : ContDiff ℝ 2 V) :
    ∀ x, DifferentiableAt ℝ (deriv V) x := by
  have hD : Differentiable ℝ (iteratedDeriv 1 V) :=
    hV.differentiable_iteratedDeriv 1 (by norm_num)
  intro x
  simpa [iteratedDeriv_one] using hD x

/--
Conditional whole-line traveling-wave existence in the `χ ≤ 0`,
`α ≤ m + γ - 1`, `c > 2` branch.

The theorem consumes the banked fixed-point, diagonal equation, traveling-wave,
right-tail, and left-tail bricks.  The only remaining analytic assumptions are
the fields of `WholeLineTravelingWaveData`.
-/
theorem wholeLine_travelingWave_exists
    (p : CMParams)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    {c κt D : ℝ}
    (hc : 2 < c)
    {w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveData p c (waveExponent c) κt D
      w wt wx wxx p3) :
    ∃ Ustar Vstar : ℝ → ℝ,
      WholeLineTravelingWaveProfile p c (waveExponent c) Ustar Vstar := by
  let κ := waveExponent c
  have hregime : p.χ ≤ 0 ∧ p.α ≤ p.m + p.γ - 1 := ⟨hχ, hα⟩
  have hκ : 0 < κ := by
    simpa [κ] using waveExponent_pos (le_of_lt hc)
  have hc_pos : 0 < c := by linarith
  have hmap :
      ∀ U, U ∈ WaveTrap κ κt D → longTimeMap w U ∈ WaveTrap κ κt D := by
    simpa [κ] using
      (longTimeMap_mapsTo
        (κ := waveExponent c) (κt := κt) (D := D) (w := w)
        H.orbit_lower_bound H.orbit_upper_bound H.orbit_spatial_antitone)
  have hmapsTo : MapsTo (longTimeMap w) (WaveTrap κ κt D) (WaveTrap κ κt D) := by
    intro U hU
    exact hmap U hU
  have hcont :
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) (longTimeMap w) := by
    simpa [κ] using
      (longTimeMap_continuous
        (κ := waveExponent c) (κt := κt) (D := D) (w := w)
        H.longTime_finite_time_continuity H.longTime_uniform_tail)
  have hcompact :
      ShenWork.Paper1.LocalUniformSequentiallyCompactRange
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) (longTimeMap w) := by
    simpa [κ] using
      (longTimeMap_compact
        (κ := waveExponent c) (κt := κt) (D := D) (w := w)
        (by
          intro U hU
          exact hmap U (by simpa [κ] using hU))
        H.longTime_image_continuity
        H.longTime_parabolic_equicontinuity)
  rcases
      wholeLine_wave_fixedPoint_exists
        (κ := κ) (κt := κt) (D := D) (T := longTimeMap w)
        (by simpa [κ] using H.schauder_principle)
        hmapsTo hcont hcompact with
    ⟨Ustar, hUstar, hfixed⟩
  have hUstar_original : Ustar ∈ WaveTrap (waveExponent c) κt D := by
    simpa [κ] using hUstar
  have hfixed_original : longTimeMap w Ustar = Ustar := hfixed
  have hlim_eq : wholeLineLongTimeLimit (w Ustar) = Ustar := by
    simpa [longTimeMap] using hfixed
  let Vstar : ℝ → ℝ := frozenSignal p.γ Ustar
  have hU_contDiff : ContDiff ℝ 2 Ustar :=
    H.fixedPoint_profile_contDiff2 Ustar hUstar_original hfixed_original
  have hV_contDiff : ContDiff ℝ 2 Vstar := by
    simpa [Vstar] using
      H.fixedPoint_signal_contDiff2 Ustar hUstar_original hfixed_original
  have hU_bdd : IsCUnifBdd Ustar :=
    ⟨hU_contDiff.continuous, waveTrap_bounded hUstar⟩
  have hU_nonneg : ∀ x, 0 ≤ Ustar x :=
    fun x => waveTrap_mem_nonneg hUstar x
  have hU_diff_at : ∀ x, DifferentiableAt ℝ Ustar x := by
    intro x
    exact hU_contDiff.differentiable two_ne_zero x
  have hV_deriv_diff : ∀ x, DifferentiableAt ℝ (deriv Vstar) x :=
    differentiableAt_deriv_of_contDiff_two hV_contDiff
  have hstationary_long :=
    wholeLine_longTime_stationary
      (p := p) (c := c) (u := Ustar)
      (w := w Ustar) (wt := wt Ustar) (wx := wx Ustar) (wxx := wxx Ustar)
      (H.longTime_stationarity Ustar hUstar_original)
  have hresidual :
      ∀ x,
        auxiliaryStationaryResidual p c Ustar
          (fun y => deriv Ustar y)
          (fun y => iteratedDeriv 2 Ustar y)
          Vstar (fun y => deriv Vstar y) x = 0 := by
    intro x
    simpa [Vstar, hlim_eq] using hstationary_long x
  have haux : wholeLineAuxStationaryEquation p c Ustar := by
    intro x
    rw [wholeLine_aux_operator_eq_residual p c Ustar x]
    exact hresidual x
  have hdiv : wholeLineDivergenceStationaryEquation p c Ustar :=
    (wholeLine_diagonal_stationary p hU_bdd hU_nonneg hU_diff_at
      (by simpa [Vstar] using hV_deriv_diff)).mp haux
  have hU_stationary :
      ∀ x,
        iteratedDeriv 2 Ustar x + c * deriv Ustar x
          - p.χ * deriv (fun y => (Ustar y) ^ p.m * deriv Vstar y) x
          + Ustar x * (1 - (Ustar x) ^ p.α) = 0 := by
    intro x
    simpa [wholeLineDivergenceStationaryOperator, wholeLineReaction, Vstar]
      using hdiv x
  have hV_stationary :
      ∀ x, iteratedDeriv 2 Vstar x - Vstar x + (Ustar x) ^ p.γ = 0 := by
    intro x
    have hVxx :
        iteratedDeriv 2 Vstar x = Vstar x - (Ustar x) ^ p.γ := by
      simpa [Vstar, iteratedDeriv_succ, iteratedDeriv_one] using
        wholeLine_frozenSignal_second_deriv p hU_bdd hU_nonneg x
    linarith
  have hglobal :
      IsGlobalClassicalSolution p
        (wholeLineTravelingWaveU c Ustar) (wholeLineTravelingWaveV c Vstar) :=
    wholeLine_travelingWave_solves hU_stationary hV_stationary
      hU_contDiff hV_contDiff
  have hright :=
    wholeLine_travelingWave_rightLimit
      (κ := κ) (κt := κt) (D := D) (U := Ustar)
      hκ (by simpa [κ] using H.kappa_lt_kappat) hUstar
  have hmonotoneTrap_long :
      ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 (longTimeMap w Ustar) := by
    simpa [κ] using
      (longTimeMap_mapsTo_InMonotoneWaveTrapSet
        (κ := waveExponent c) (κt := κt) (D := D) (w := w)
        H.orbit_lower_bound H.orbit_upper_bound H.orbit_spatial_antitone
        H.longTime_image_continuity Ustar hUstar_original)
  have hmonotoneTrap :
      ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 Ustar := by
    simpa [hfixed] using hmonotoneTrap_long
  have hT10 :
      ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveEquilibriumStable p3 :=
    ShenWork.Paper1.WholeLineLeftTail.paper3_T10_positiveEquilibriumStable_of_chi_nonpos
      p3 H.paper3_chi_nonpos
  have hleft : Tendsto Ustar atBot (𝓝 1) :=
    ShenWork.Paper1.WholeLineLeftTail.wholeLine_travelingWave_leftLimit
      (p := p) (c := c) (κ := κ) (U := Ustar) (p3 := p3)
      hmonotoneTrap
      (H.translate_compactness Ustar hUstar_original hfixed_original)
      hT10
      (H.translate_limit_identification Ustar hUstar_original hfixed_original)
  exact ⟨Ustar, Vstar,
    { signal_eq := rfl
      speed_pos := hc_pos
      profile_contDiff2 := hU_contDiff
      signal_contDiff2 := hV_contDiff
      divergence_stationary := hdiv
      elliptic_stationary := hV_stationary
      global_classical_solution := hglobal
      left_limit := hleft
      right_limit := hright.1
      right_tail := hright.2.1
      monotone := hright.2.2 }⟩

#print axioms WholeLineTravelingWaveData
#print axioms WholeLineTravelingWaveProfile
#print axioms wholeLine_travelingWave_exists

end ShenWork.PaperOne
