/-
  ShenWork/Paper2/IntervalPicardSliceWitnessSupply.lean

  **Tower campaign — stage-F witness supply (the witness-decay self-feed closer).**

  The tower's per-level half-step shifted-source witness (`ShiftedSourceWitness`,
  File B/C) was, until now, carried as a residual analytic hypothesis: its `hdecay`
  field demands the σ-shifted logistic source coefficient quadratic decay
  `|aₙ(σ)| ≤ 2·Benv/(kπ)²` for **all** `σ ≥ 0`, which the tower-level K2 facts (only
  on `(0,T]`) cannot supply for `σ` so large that the shifted time `t/2+σ` exceeds
  `T`.

  ## The wall-free route this file builds

  The downstream consumer of the decay — the τ-quarter gain bound inside
  `restartSeries_abs_deriv2_le` (via `duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound`
  → `eigenvalue_mul_coeff_tauQuarter_bound` → `duhamelSpectralCoeff_min_bound`) — reads
  the source family only on the integration window `s ∈ [0, τ] = [0, t/2]`
  (`intervalIntegral.integral_mono_on`).  So the *global* `∀ σ ≥ 0` decay is genuine
  over-kill: only `[0, t/2]` matters.  This file replicates the G2 second-derivative
  chain with `hdecay` weakened to `∀ σ ∈ Set.Icc 0 τ`, then specialises it to the
  CANONICAL restart series of `tower_succ` with:

    * the canonical σ-shifted source `DuhamelSourceTimeC1` package obtained, with NO
      analytic wall, as the non-negative time-shift (`DuhamelSourceTimeC1.shift_nonneg`,
      offset `t/2`) of the level-`n` canonical source package `hsrc0`;
    * the windowed decay `s ∈ [0, t/2] ⊢ |source(t/2+s)| ≤ Benv/(kπ)² ≤ 2·Benv/(kπ)²`
      supplied by stage F (`slice_source_coeff_decay`), evaluating the K2 profiles at
      the shifted time `t/2+s ∈ [t/2, t] ⊆ (0,T]` — the level's own
      representation + ball + G1/G2 facts, NO global C² of the lift anywhere.

  The reconciliation is definitional: stage F's `windowSourceConst p M G1 G2`
  evaluated at the half-step profiles `(G1profile p M (t/2), G2profile A₂ (t/2))`
  IS `Benv p M A₂ t` (both unfold to `iterateSourceEnvelopeConst p.a p.b p.α M …`),
  with the factor-2 slack absorbed by `Benv ≤ 2·Benv`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateC2Bound
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.Paper2.IntervalPicardWeightedC2Bootstrap
import ShenWork.Paper2.IntervalPicardIterateRestartLocal

open MeasureTheory Filter Topology
open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateUniform
  (Benv G1profile G2profile CL G1profile_nonneg CL_nonneg)
open ShenWork.IntervalLogisticSourceQuantBound (B_log B_log_nonneg)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.IntervalPicardIterateC2Bound
  (restartIterateCoeff hom_eig_summable duh_eig_summable
   cosineSeries_abs_deriv2_le_eig_tsum)
open ShenWork.IntervalDuhamelSourceShift (duhamelSpectralCoeff_congr_on_Icc)
open ShenWork.IntervalPicardIterateRestartLocal (canonicalShiftedSource)
open ShenWork.IntervalPicardWeightedC2Bootstrap
  (windowSourceConst slice_source_coeff_decay)

noncomputable section

namespace ShenWork.IntervalPicardSliceWitnessSupply

/-! ## §1 — Windowed per-mode bounds (decay consumed only on `[0,τ]`).

These mirror `IntervalDuhamelQuantGain.duhamelSpectralCoeff_min_bound` /
`eigenvalue_mul_coeff_tauQuarter_bound` /
`duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound` verbatim, except the decay
hypothesis is the WINDOWED `∀ σ ∈ Set.Icc 0 τ` form — which is all the integral
`∫₀^τ …` actually reads. -/

/-- **Windowed per-mode min bound.**  Identical to `duhamelSpectralCoeff_min_bound`
but the decay is required only on the integration window `[0,τ]`. -/
theorem duhamelSpectralCoeff_min_bound_on {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k))
    {k : ℕ} (hk : 1 ≤ k) :
    |duhamelSpectralCoeff a τ k|
      ≤ (2 * B / ((k : ℝ) * Real.pi) ^ 2) * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hCnn : (0 : ℝ) ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  have hkernel : Continuous
      (fun s : ℝ => Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k)) := by fun_prop
  have hII : IntervalIntegrable
      (fun s => Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k)
      volume 0 τ := (hkernel.mul (hcont k)).intervalIntegrable 0 τ
  have hstep : |duhamelSpectralCoeff a τ k|
      ≤ (2 * B / ((k : ℝ) * Real.pi) ^ 2)
          * ∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
    unfold duhamelSpectralCoeff
    calc |∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k|
        = ‖∫ s in (0:ℝ)..τ,
            Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in (0:ℝ)..τ,
            ‖Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k‖ :=
          intervalIntegral.norm_integral_le_integral_norm hτ.le
      _ ≤ ∫ s in (0:ℝ)..τ,
            (2 * B / ((k : ℝ) * Real.pi) ^ 2)
              * Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
          apply intervalIntegral.integral_mono_on hτ.le hII.norm
            (by apply Continuous.intervalIntegrable; fun_prop)
          intro s hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
            mul_comm (2 * B / ((k : ℝ) * Real.pi) ^ 2)]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          exact hdecay s hs k hk
      _ = (2 * B / ((k : ℝ) * Real.pi) ^ 2)
            * ∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
          rw [intervalIntegral.integral_const_mul]
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hCnn
  rw [hlam_eq]
  exact ShenWork.IntervalDuhamelQuantGain.gainIntegral_le_min hτ hlampos

/-- **Windowed per-mode `τ^{1/4}` bound.**  Mirror of
`eigenvalue_mul_coeff_tauQuarter_bound`, windowed decay. -/
theorem eigenvalue_mul_coeff_tauQuarter_bound_on {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k))
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B * τ ^ ((1 : ℝ) / 4) / ((k : ℝ) * Real.pi) ^ ((3 : ℝ) / 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkπpos : (0 : ℝ) < (k : ℝ) * Real.pi := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  have hlamnn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by rw [hlam_eq]; positivity
  have hinvnn : (0 : ℝ) ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hmin := duhamelSpectralCoeff_min_bound_on hτ hB hdecay hcont hk
  have hstep1 : unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
    calc unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
        ≤ unitIntervalCosineEigenvalue k
            * ((2 * B / ((k : ℝ) * Real.pi) ^ 2) * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmin hlamnn
      _ = 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
          rw [hlam_eq]
          rw [show ((k : ℝ) * Real.pi) ^ 2
              * (2 * B / ((k : ℝ) * Real.pi) ^ 2 * min τ (1 / ((k : ℝ) * Real.pi) ^ 2))
              = (((k : ℝ) * Real.pi) ^ 2 / ((k : ℝ) * Real.pi) ^ 2)
                  * (2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) by ring,
            div_self (by positivity : ((k : ℝ) * Real.pi) ^ 2 ≠ 0), one_mul]
  have hinterp := ShenWork.IntervalDuhamelQuantGain.min_le_rpow_mul_rpow
    (x := τ) (y := 1 / ((k : ℝ) * Real.pi) ^ 2)
    hτ.le hinvnn (by norm_num : (0:ℝ) ≤ (1:ℝ)/4) (by norm_num : (1:ℝ)/4 ≤ 1)
  have hrpow_inv : (1 / ((k : ℝ) * Real.pi) ^ 2) ^ (1 - (1:ℝ)/4)
      = 1 / ((k : ℝ) * Real.pi) ^ ((3:ℝ)/2) := by
    rw [show (1 : ℝ) - 1/4 = 3/4 by norm_num]
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
    congr 1
    rw [← Real.rpow_natCast ((k : ℝ) * Real.pi) 2, ← Real.rpow_mul hkπpos.le]
    norm_num
  rw [hrpow_inv] at hinterp
  have hstep2 : 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)
      ≤ 2 * B * (τ ^ ((1:ℝ)/4) * (1 / ((k : ℝ) * Real.pi) ^ ((3:ℝ)/2))) :=
    mul_le_mul_of_nonneg_left hinterp (by positivity)
  refine (hstep1.trans hstep2).trans (le_of_eq ?_)
  rw [mul_one_div, mul_div_assoc]

/-- **Windowed λ-weighted `τ^{1/4}` sum bound.**  Mirror of
`duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound`, windowed decay.  The proof
is identical save the per-mode bound is the windowed one above. -/
theorem duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound_on {a : ℝ → ℕ → ℝ}
    {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k)) :
    (∑' k : ℕ, unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|)
      ≤ (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) / Real.pi ^ ((3 : ℝ) / 2))
          * τ ^ ((1 : ℝ) / 4) * B := by
  set C : ℝ := 2 * B * τ ^ ((1 : ℝ) / 4) / Real.pi ^ ((3 : ℝ) / 2) with hC_def
  have hCnn : 0 ≤ C := by rw [hC_def]; positivity
  set f : ℕ → ℝ := fun k => unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
    with hf_def
  have hfnn : ∀ k, 0 ≤ f k := by
    intro k
    refine mul_nonneg ?_ (abs_nonneg _)
    simp only [unitIntervalCosineEigenvalue]; positivity
  set g : ℕ → ℝ := fun k => C * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) with hg_def
  have hg_summable : Summable g :=
    ShenWork.IntervalDuhamelQuantGain.summable_one_div_natShift_rpow_threeHalves.mul_left C
  have hshift_le : ∀ k : ℕ, f (k + 1) ≤ g k := by
    intro k
    have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hbound := eigenvalue_mul_coeff_tauQuarter_bound_on hτ hB hdecay hcont hk
    refine hbound.trans (le_of_eq ?_)
    have hkπpos : (0 : ℝ) < ((k : ℝ) + 1) * Real.pi := by positivity
    rw [hg_def, hC_def]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    rw [Real.mul_rpow (by positivity) Real.pi_nonneg]
    field_simp
  have hf_shift_summable : Summable (fun k => f (k + 1)) :=
    hg_summable.of_nonneg_of_le (fun k => hfnn (k + 1)) hshift_le
  have hf_summable : Summable f :=
    (summable_nat_add_iff (f := f) 1).1 hf_shift_summable
  have hf0 : f 0 = 0 := by
    rw [hf_def]; simp only [unitIntervalCosineEigenvalue]
    norm_num
  have hsum_shift : (∑' k, f k) = ∑' k, f (k + 1) := by
    rw [hf_summable.tsum_eq_zero_add, hf0, zero_add]
  rw [hsum_shift]
  refine (hf_shift_summable.tsum_le_tsum hshift_le hg_summable).trans (le_of_eq ?_)
  rw [hg_def, tsum_mul_left, hC_def]
  ring

/-! ## §2 — The windowed restart-series G2 bound.

`restartSeries_eig_tsum_le` / `restartSeries_abs_deriv2_le` re-derived with the
windowed decay.  The homogeneous + Duhamel summable legs (`hom_eig_summable`,
`duh_eig_summable`) need only `src` (NOT the decay), so they are reused verbatim. -/

/-- **Windowed λ-weighted restart sum bound (G2).** -/
theorem restartSeries_eig_tsum_le_on
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1 a)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) :
    (∑' n, unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|)
      ≤ M₁ * eigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv := by
  have hhom_sum := hom_eig_summable (M₁ := M₁) hτ ha₀
  have hduh_sum := duh_eig_summable src hτ
  have hsplit_le : ∀ n,
      unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|
        ≤ unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
          + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| := by
    intro n
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by unfold unitIntervalCosineEigenvalue; positivity)
    simpa [restartDuhamelCoeff] using
      abs_add_le (Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n)
        (duhamelSpectralCoeff a τ n)
  calc (∑' n, unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|)
      ≤ ∑' n, (unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
          + unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n|) :=
        Summable.tsum_le_tsum hsplit_le
          (Summable.of_nonneg_of_le
            (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
              (abs_nonneg _)) hsplit_le (hhom_sum.add hduh_sum))
          (hhom_sum.add hduh_sum)
    _ = (∑' n, unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
          + ∑' n, unitIntervalCosineEigenvalue n *
            |duhamelSpectralCoeff a τ n| := hhom_sum.tsum_add hduh_sum
    _ ≤ M₁ * eigExpWeight τ
          + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
              Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv := by
        gcongr
        · exact ShenWork.IntervalHomogeneousQuantBound.homogeneous_eigenvalue_tsum_le
            hτ ha₀
        · exact duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound_on
            hτ hBenv hdecay hacont

/-- **Windowed explicit G2 sup bound for the restart series.** -/
theorem restartSeries_abs_deriv2_le_on
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1 a)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (hacont : ∀ k, Continuous (fun σ => a σ k)) (x : ℝ) :
    |deriv (deriv (fun x => ∑' n, restartDuhamelCoeff a₀ a τ n * cosineMode n x)) x|
      ≤ M₁ * eigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv :=
  (cosineSeries_abs_deriv2_le_eig_tsum
      (ShenWork.IntervalMildRegularityBootstrap.restartDuhamelCoeff_eigenvalue_summable
        hτ ha₀ src) x).trans
    (restartSeries_eig_tsum_le_on hτ hBenv ha₀ src hdecay hacont)

/-! ## §3 — The canonical-series specialisation (the `tower_succ` G2 input).

This is the wall-free replacement for
`IntervalPicardIterateC2BoundLocal.iterate_abs_deriv2_le_of_shiftedWitness`: the
canonical `restartIterateCoeff` series' G2 bound, fed from the canonical σ-shifted
source `DuhamelSourceTimeC1` package + a windowed decay on `[0, t/2]`. -/

/-- **Canonical-series G2 bound from a windowed shifted-source decay.**
The σ-shifted source family `srcσ k = cosineCoeffs (logisticLifted p (uₙ(t/2+σ))) k`
with its `DuhamelSourceTimeC1` package and the windowed decay on `[0, t/2]` give the
explicit second-derivative sup bound for the canonical next-iterate restart series. -/
theorem iterate_abs_deriv2_le_of_windowDecay
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M M₁ A₂ : ℝ} (ht : 0 < t) (hBenv : 0 ≤ Benv p M A₂ t)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (x : ℝ) :
    |deriv (deriv (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x)) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  have hτ : 0 < t / 2 := by positivity
  have hσcont : ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k) :=
    fun k => continuous_iff_continuousAt.2 (fun σ => (srcσ.hderiv σ k).continuousAt)
  simpa only [restartIterateCoeff] using
    restartSeries_abs_deriv2_le_on (a₀ :=
        cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
      (a := fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)
      hτ hBenv hM₁ srcσ hdecay hσcont x

/-! ## §4 — The shifted-source `DuhamelSourceTimeC1` package, wall-free.

The σ-shifted canonical source package is the non-negative time-shift of the
level-`n` canonical source `hsrc0`. -/

/-- **The σ-shifted canonical source `DuhamelSourceTimeC1`.**  From the level-`n`
canonical source package `hsrc0` (the unshifted family `s ↦ cosineCoeffs (Lₙ(s))`),
the non-negative shift by `t/2` yields the σ-shifted package whose family is
`σ ↦ cosineCoeffs (Lₙ(t/2+σ))` — *definitionally* `canonicalShiftedSource p u₀ n t`. -/
def shiftedSource_timeC1
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)) :
    DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k) :=
  ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
    hsrc0 (offset := t / 2) (by positivity)

/-! ## §5 — The stage-F windowed decay for the σ-shifted source.

`slice_source_coeff_decay` evaluated at the shifted time `s = t/2 + σ ∈ [t/2, t]`,
with the level's own K2 facts there (`G1profile p M s`, `G2profile A₂ s`), gives the
windowed decay with the explicit constant
`windowSourceConst p M (G1profile p M s) (G2profile A₂ s)`.  The reconciliation to
`2·Benv p M A₂ t = 2·windowSourceConst p M (G1profile p M (t/2)) (G2profile A₂ (t/2))`
uses the factor-2 slack exactly:

  * `G2profile A₂ s = A₂/s² ≤ A₂/(t/2)² = G2profile A₂ (t/2)` (decreasing);
  * `G1profile p M s ≤ √2 · G1profile p M (t/2)` for `t/2 ≤ s ≤ t` (the decreasing
    `Cg/√s·M` piece is `≤` its value at `t/2`, the increasing `Cg·2√s·CL` piece is
    `≤ √2·` its value at `t/2` since `√s ≤ √t = √2·√(t/2)`), hence
    `G1profile(s)² ≤ 2·G1profile(t/2)²`;
  * `B_log` is linear-increasing in `G2` and quadratic-increasing in `G1²` (both
    coefficients `≥ 0`), so `B_log(G1(s),G2(s)) ≤ 2·B_log(G1(t/2),G2(t/2))`, and the
    `max` with the `G`-free zeroth-mode constant gives
    `windowSourceConst(s) ≤ 2·windowSourceConst(t/2)`. -/

/-- `G1profile p M s ≤ √2 · G1profile p M (t/2)` on the half-step window
`t/2 ≤ s ≤ t` (`0 < t`). -/
theorem G1profile_le_sqrt2_halfStep
    (p : CM2Params) {M t s : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (hs1 : t / 2 ≤ s) (hs2 : s ≤ t) :
    G1profile p M s ≤ Real.sqrt 2 * G1profile p M (t / 2) := by
  have hτ : 0 < t / 2 := by positivity
  have hs : 0 < s := lt_of_lt_of_le hτ hs1
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsτ : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.mpr hτ
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  -- piece 1: Cg/√s·M ≤ Cg/√(t/2)·M ≤ √2·(Cg/√(t/2)·M).
  have hp1' : heatGradientLinftyLinftyConstant / Real.sqrt s * M
      ≤ heatGradientLinftyLinftyConstant / Real.sqrt (t / 2) * M := by
    apply mul_le_mul_of_nonneg_right _ hM
    exact div_le_div_of_nonneg_left hCg hsτ (Real.sqrt_le_sqrt hs1)
  have hp1 : heatGradientLinftyLinftyConstant / Real.sqrt s * M
      ≤ Real.sqrt 2 * (heatGradientLinftyLinftyConstant / Real.sqrt (t / 2) * M) := by
    refine hp1'.trans ?_
    nlinarith [mul_nonneg (div_nonneg hCg hsτ.le) hM]
  -- piece 2: Cg·2√s·CL ≤ Cg·2√t·CL = √2·(Cg·2√(t/2)·CL).
  have hsqrt_t_eq : Real.sqrt t = Real.sqrt 2 * Real.sqrt (t / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; ring
  have hp2 : heatGradientLinftyLinftyConstant * (2 * Real.sqrt s) * CL p M
      ≤ Real.sqrt 2 * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt (t / 2)) * CL p M) := by
    have hstep : heatGradientLinftyLinftyConstant * (2 * Real.sqrt s) * CL p M
        ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * CL p M := by
      apply mul_le_mul_of_nonneg_right _ hCL
      apply mul_le_mul_of_nonneg_left _ hCg
      have := Real.sqrt_le_sqrt hs2
      linarith
    refine hstep.trans (le_of_eq ?_)
    rw [hsqrt_t_eq]; ring
  unfold G1profile
  calc heatGradientLinftyLinftyConstant / Real.sqrt s * M
        + heatGradientLinftyLinftyConstant * (2 * Real.sqrt s) * CL p M
      ≤ Real.sqrt 2 * (heatGradientLinftyLinftyConstant / Real.sqrt (t / 2) * M)
        + Real.sqrt 2 * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt (t / 2)) * CL p M) :=
        add_le_add hp1 hp2
    _ = Real.sqrt 2 * (heatGradientLinftyLinftyConstant / Real.sqrt (t / 2) * M
          + heatGradientLinftyLinftyConstant * (2 * Real.sqrt (t / 2)) * CL p M) := by ring

/-- The stage-F window constant at the shifted slice `s ∈ [t/2, t]` is dominated by
`2·Benv p M A₂ t`.  Recall `Benv p M A₂ t = windowSourceConst p M (G1profile p M (t/2))
(G2profile A₂ (t/2))` definitionally. -/
theorem windowSourceConst_slice_le_twoBenv
    {p : CM2Params} {M A₂ t s : ℝ} (hα : 1 ≤ p.α)
    (hM : 0 ≤ M) (hA₂ : 0 ≤ A₂) (ht : 0 < t)
    (hs1 : t / 2 ≤ s) (hs2 : s ≤ t) :
    windowSourceConst p M (G1profile p M s) (G2profile A₂ s)
      ≤ 2 * Benv p M A₂ t := by
  have hτ : 0 < t / 2 := by positivity
  have hs : 0 < s := lt_of_lt_of_le hτ hs1
  have hG1s : 0 ≤ G1profile p M s := G1profile_nonneg hM hs
  have hG1τ : 0 ≤ G1profile p M (t / 2) := G1profile_nonneg hM hτ
  have hG2s : 0 ≤ G2profile A₂ s := by unfold G2profile; positivity
  have hG2τ : 0 ≤ G2profile A₂ (t / 2) := by unfold G2profile; positivity
  -- G2 piece: A₂/s² ≤ A₂/(t/2)².
  have hG2le : G2profile A₂ s ≤ G2profile A₂ (t / 2) := by
    unfold G2profile
    have hsq : (t / 2) ^ 2 ≤ s ^ 2 := by nlinarith [hτ.le, hs1]
    exact div_le_div_of_nonneg_left hA₂ (by positivity) hsq
  -- G1² piece: G1profile(s)² ≤ 2·G1profile(t/2)².
  have hG1sq : G1profile p M s ^ 2 ≤ 2 * G1profile p M (t / 2) ^ 2 := by
    have hle := G1profile_le_sqrt2_halfStep p hM ht hs1 hs2
    have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc G1profile p M s ^ 2
        ≤ (Real.sqrt 2 * G1profile p M (t / 2)) ^ 2 := by
          apply pow_le_pow_left₀ hG1s hle
      _ = 2 * G1profile p M (t / 2) ^ 2 := by rw [mul_pow, hsqrt2sq]
  -- B_log monotone: coefficients ≥ 0.
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  have hMα1 : 0 ≤ M ^ (p.α - 1) := Real.rpow_nonneg hM _
  have hMα : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have hcoeff1 : 0 ≤ p.b * p.α * (1 + p.α) * M ^ (p.α - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg p.hb hαpos.le) (by linarith)) hMα1
  have hcoeff2 : 0 ≤ p.a + p.b * (1 + p.α) * M ^ p.α := by
    have h1 : 0 ≤ p.b * (1 + p.α) * M ^ p.α :=
      mul_nonneg (mul_nonneg p.hb (by linarith)) hMα
    linarith [p.ha]
  have hBlog_le : B_log p.a p.b p.α M (G1profile p M s) (G2profile A₂ s)
      ≤ 2 * B_log p.a p.b p.α M (G1profile p M (t / 2)) (G2profile A₂ (t / 2)) := by
    unfold B_log
    calc p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1profile p M s ^ 2
            + (p.a + p.b * (1 + p.α) * M ^ p.α) * G2profile A₂ s
        ≤ p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * (2 * G1profile p M (t / 2) ^ 2)
            + (p.a + p.b * (1 + p.α) * M ^ p.α) * G2profile A₂ (t / 2) := by
          gcongr
      _ = 2 * (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1profile p M (t / 2) ^ 2
            + (p.a + p.b * (1 + p.α) * M ^ p.α) * G2profile A₂ (t / 2))
            - (p.a + p.b * (1 + p.α) * M ^ p.α) * G2profile A₂ (t / 2) := by ring
      _ ≤ 2 * (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1profile p M (t / 2) ^ 2
            + (p.a + p.b * (1 + p.α) * M ^ p.α) * G2profile A₂ (t / 2)) := by
          have : 0 ≤ (p.a + p.b * (1 + p.α) * M ^ p.α) * G2profile A₂ (t / 2) :=
            mul_nonneg hcoeff2 hG2τ
          linarith
  -- assemble through the `max`.
  have hC0nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by
    have : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
    have := mul_nonneg p.hb this
    exact mul_nonneg hM (by linarith [p.ha])
  have hBnnτ : 0 ≤ B_log p.a p.b p.α M (G1profile p M (t / 2)) (G2profile A₂ (t / 2)) :=
    B_log_nonneg hα p.ha p.hb hM hG1τ hG2τ
  -- `windowSourceConst(s) = max (2·B_log(s)) C0 ≤ 2·max (2·B_log(τ)) C0 = 2·Benv`.
  unfold windowSourceConst Benv
    ShenWork.IntervalPicardIterateSourceC1.iterateSourceEnvelopeConst
  rw [show (2 : ℝ) * max (2 * B_log p.a p.b p.α M (G1profile p M (t / 2)) (G2profile A₂ (t / 2)))
        (M * (p.a + p.b * M ^ p.α))
      = max (2 * (2 * B_log p.a p.b p.α M (G1profile p M (t / 2)) (G2profile A₂ (t / 2))))
        (2 * (M * (p.a + p.b * M ^ p.α))) by
    rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]]
  apply max_le_max
  · linarith [hBlog_le]
  · linarith [hC0nn]

/-! ## §6 — The windowed decay of the σ-shifted canonical source (stage F).

For `0 < t ≤ T` and `σ ∈ [0, t/2]`, the shifted time `s = t/2 + σ ∈ [t/2, t] ⊆ (0,T]`,
so the level-`n` representation triple + ball + G1/G2 facts at `s` feed
`slice_source_coeff_decay`, yielding the quadratic decay with the stage-F constant
`windowSourceConst p M (G1profile p M s) (G2profile A₂ s) ≤ 2·Benv p M A₂ t`. -/

/-- **The wall-free windowed decay** of the σ-shifted canonical logistic source.
This is the `hdecay` leg of `iterate_abs_deriv2_le_of_windowDecay`, derived from the
level-`n` cosine representation triple + ball + K2 profile facts (the tower-level
data) via stage F — NO global C² of the lift. -/
theorem shifted_source_windowDecay
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M A₂ T t : ℝ} (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hA₂ : 0 ≤ A₂)
    (ht : 0 < t) (htT : t ≤ T)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ s, 0 < s → s ≤ T →
      Summable (fun m => unitIntervalCosineEigenvalue m * |bc s m|))
    (hagree : ∀ s, 0 < s → s ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n s))
        (fun x => ∑' m, bc s m * cosineMode m x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ s, 0 < s → s ≤ T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (picardIter p u₀ n s) x)
    (hub : ∀ s, 0 < s → s ≤ T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (picardIter p u₀ n s) x ≤ M)
    (hG1 : ∀ s, 0 < s → s ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n s)) x| ≤ G1profile p M s)
    (hG2 : ∀ s, 0 < s → s ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n s))) x| ≤ G2profile A₂ s) :
    ∀ σ ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2 := by
  intro σ hσ k hk
  set s := t / 2 + σ with hs_def
  have hs1 : t / 2 ≤ s := by rw [hs_def]; linarith [hσ.1]
  have hs2 : s ≤ t := by rw [hs_def]; linarith [hσ.2]
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs1
  have hsT : s ≤ T := le_trans hs2 htT
  -- transport logisticLifted ↦ logisticSourceFun (equal on [0,1]).
  have hfam : cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k
      = cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (picardIter p u₀ n s))) k :=
    ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
        p (picardIter p u₀ n s)) k
  rw [hfam]
  -- stage-F per-slice decay at slice `s`, with the level's K2 facts there.
  have hdecay := slice_source_coeff_decay p (M := M)
    (G1 := G1profile p M s) (G2 := G2profile A₂ s) hα
    (bc s) (hbsum s hspos hsT) (hagree s hspos hsT)
    (hpos s hspos hsT) (hub s hspos hsT)
    (fun x _hx => hG1 s hspos hsT x) (fun x _hx => hG2 s hspos hsT x) k hk
  -- reconcile the stage-F constant to `2·Benv`.
  refine hdecay.trans ?_
  have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    positivity
  apply div_le_div_of_nonneg_right
    (windowSourceConst_slice_le_twoBenv hα hM hA₂ ht hs1 hs2) hden.le

end ShenWork.IntervalPicardSliceWitnessSupply
