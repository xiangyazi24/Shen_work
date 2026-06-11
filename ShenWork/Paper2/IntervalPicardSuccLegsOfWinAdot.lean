/-
  ShenWork/Paper2/IntervalPicardSuccLegsOfWinAdot.lean

  **K1 endgame W3 — the `hsrc0`-free `(n+1)` legs from `winAdot`.**

  The two `tower_succ` sites that still read the canonical level-`n` source package
  `H.hsrc0 n` (via `shiftedSource_timeC1`) are:

    (A) `hbsum_succ` — the λ-weighted summability of `iterateReprCoeff (n+1) σ`;
    (B) the G2 engine `iterate_abs_deriv2_le_of_windowDecay` — the explicit second
        spatial-derivative sup bound for the next-iterate restart series.

  Both feed the σ/2-shifted canonical source `DuhamelSourceTimeC1` into machinery
  (`restartSeries_eigenvalue_summable`, `restartSeries_abs_deriv2_le_on`) that reads
  the source family ONLY on the integration window `[0, σ/2]` (the `duhamelSpectralCoeff`
  at horizon `σ/2`).  This file supplies the consumer variants that accept a GLOBAL
  CLAMPED package `srcC` (the W3 brick `clampedShiftedSource_duhamelSourceTimeC1`)
  for a family `asrc` AGREEING with the shifted canonical source on `[0, σ/2]`,
  via the `[0,τ]` congruences `duhamelSpectralCoeff_congr_on_Icc` /
  `restartDuhamelCoeff` = `localRestartCoeff` (identical bodies).

  * `hbsum_succ_of_window`  — variant of `hbsum_succ` (A).
  * `iterate_abs_deriv2_le_of_window`  — variant of `iterate_abs_deriv2_le_of_windowDecay` (B).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardShiftedClampedSupply
import ShenWork.Paper2.IntervalPicardSliceWitnessSupply
import ShenWork.Paper2.IntervalDuhamelSourceShift

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardIterateC2Bound
  (restartIterateCoeff restartSeries_eigenvalue_summable)
open ShenWork.IntervalPicardIterateUniform (Benv)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardSliceWitnessSupply (restartSeries_abs_deriv2_le_on)
open ShenWork.IntervalDuhamelSourceShift (duhamelSpectralCoeff_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardSuccLegsOfWinAdot

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §1 — The `[0,τ]` coefficient bridge.

The summability/decay machinery only reads the source family on `[0, σ/2]`, so a
global clamped family `asrc` agreeing with the shifted canonical source there yields
the SAME restart-series coefficient as the canonical `iterateReprCoeff (n+1)`. -/

/-- **`restartDuhamelCoeff` of the clamped family = `iterateReprCoeff (n+1)`.**
For any homogeneous datum `a₀`, if `asrc` agrees with the shifted canonical source on
`[0, σ/2]`, the restart coefficient `restartDuhamelCoeff a₀ asrc (σ/2) k` equals
`restartDuhamelCoeff a₀ (shifted canonical) (σ/2) k` (the spectral Duhamel coefficient
integrates only over `[0, σ/2]`). -/
theorem restartDuhamelCoeff_clamped_eq
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {a₀ : ℕ → ℝ} {asrc : ℝ → ℕ → ℝ}
    (hagree : ∀ s ∈ Set.Icc (0 : ℝ) (σ / 2), ∀ k,
      asrc s k = cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k)
    (k : ℕ) :
    restartDuhamelCoeff a₀ asrc (σ / 2) k
      = restartDuhamelCoeff a₀
          (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k)
          (σ / 2) k := by
  unfold restartDuhamelCoeff
  rw [duhamelSpectralCoeff_congr_on_Icc (by positivity) hagree k]

/-! ## §2 — (A) the `hbsum_succ` variant. -/

/-- **`hbsum_succ_of_window` — λ-weighted summability of `iterateReprCoeff (n+1) σ`
from a clamped shifted-source package.**  Variant of
`IntervalPicardIterateRepresentation.hbsum_succ` reading the GLOBAL clamped package
`srcC` (W3 brick) for `asrc` + the read-window agreement on `[0, σ/2]`. -/
theorem hbsum_succ_of_window
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ M₁ : ℝ} (hσ : 0 < σ)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ M₁)
    {asrc : ℝ → ℕ → ℝ} (srcC : DuhamelSourceTimeC1 asrc)
    (hagree : ∀ s ∈ Set.Icc (0 : ℝ) (σ / 2), ∀ k,
      asrc s k = cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
  have hτ : 0 < σ / 2 := by positivity
  -- summability for the clamped family.
  have hsum := restartSeries_eigenvalue_summable (a₀ :=
      cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))))
    (a := asrc) hτ hM₁ srcC
  -- transport along the `[0,σ/2]` coefficient bridge to the canonical restart coeff.
  have hcoeff : ∀ k,
      unitIntervalCosineEigenvalue k * |restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2)))) asrc
          (σ / 2) k|
        = (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k| := by
    intro k
    rw [restartDuhamelCoeff_clamped_eq p u₀ n hσ hagree k]
    simp only [iterateReprCoeff, restartIterateCoeff]
  exact (Summable.congr hsum hcoeff)

/-! ## §3 — (B) the G2 engine variant. -/

/-- **`iterate_abs_deriv2_le_of_window` — explicit G2 sup bound for the next-iterate
restart series from a clamped shifted-source package.**  Variant of
`IntervalPicardSliceWitnessSupply.iterate_abs_deriv2_le_of_windowDecay` reading the
GLOBAL clamped package `srcC` (W3 brick) for `asrc` + the read-window agreement on
`[0, σ/2]` + the windowed decay (stated on the canonical shifted family). -/
theorem iterate_abs_deriv2_le_of_window
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M M₁ A₂ : ℝ} (ht : 0 < t) (hBenv : 0 ≤ Benv p M A₂ t)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    {asrc : ℝ → ℕ → ℝ} (srcC : DuhamelSourceTimeC1 asrc)
    (hagree : ∀ s ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k,
      asrc s k = cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + s))) k)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (x : ℝ) :
    |deriv (deriv (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x)) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  have hτ : 0 < t / 2 := by positivity
  -- decay for the clamped family on `[0, t/2]` (transport the canonical decay).
  have hdecayC : ∀ σ ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k : ℕ, 1 ≤ k →
      |asrc σ k| ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2 := by
    intro σ hσ k hk
    rw [hagree σ hσ k]
    exact hdecay σ hσ k hk
  have hacont : ∀ k, Continuous (fun σ => asrc σ k) :=
    fun k => continuous_iff_continuousAt.2 (fun σ => (srcC.hderiv σ k).continuousAt)
  -- the windowed G2 bound for the clamped restart series.
  have hbound := restartSeries_abs_deriv2_le_on (a₀ :=
      cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
    (a := asrc) hτ hBenv hM₁ srcC hdecayC hacont x
  -- the clamped restart series coincides with the canonical `restartIterateCoeff`
  -- series coefficient-wise (the `[0, t/2]` bridge), so their deriv² agree.
  have hser : (fun z => ∑' k, restartDuhamelCoeff
        (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2)))) asrc
        (t / 2) k * cosineMode k z)
      = (fun z => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k z) := by
    funext z
    refine tsum_congr (fun k => ?_)
    rw [restartDuhamelCoeff_clamped_eq p u₀ n ht hagree k]
    simp only [restartIterateCoeff]
  rw [hser] at hbound
  exact hbound

end ShenWork.IntervalPicardSuccLegsOfWinAdot
