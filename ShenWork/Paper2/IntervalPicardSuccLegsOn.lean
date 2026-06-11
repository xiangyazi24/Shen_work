import ShenWork.Paper2.IntervalPicardSliceWitnessSupply
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardIterateC2Bound
  (restartIterateCoeff hom_eig_summable cosineSeries_abs_deriv2_le_eig_tsum)
open ShenWork.IntervalPicardIterateUniform (Benv)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelSpectralCoeff_eigenvalue_summable_on)

noncomputable section

namespace ShenWork.IntervalPicardSuccLegsOn

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Windowed per-mode min bound driven by a closed-window `TimeC1On` source. -/
theorem duhamelSpectralCoeff_min_bound_timeC1On
    {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (src : DuhamelSourceTimeC1On a 0 τ)
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    |duhamelSpectralCoeff a τ k|
      ≤ (2 * B / ((k : ℝ) * Real.pi) ^ 2) *
        min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) :=
    by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hCnn : (0 : ℝ) ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  have hkernel : Continuous
      (fun s : ℝ => Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k)) := by
    fun_prop
  have ha_cont : ContinuousOn (fun s : ℝ => a s k) (Set.Icc (0 : ℝ) τ) := by
    intro s hs
    exact (src.hderiv s hs k).continuousWithinAt
  have hII : IntervalIntegrable
      (fun s => Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k)
      volume 0 τ :=
    (hkernel.continuousOn.mul ha_cont).intervalIntegrable_of_Icc hτ.le
  have hstep : |duhamelSpectralCoeff a τ k|
      ≤ (2 * B / ((k : ℝ) * Real.pi) ^ 2)
          * ∫ s in (0 : ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
    unfold duhamelSpectralCoeff
    calc |∫ s in (0 : ℝ)..τ,
            Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k|
        = ‖∫ s in (0 : ℝ)..τ,
            Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in (0 : ℝ)..τ,
            ‖Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k‖ :=
          intervalIntegral.norm_integral_le_integral_norm hτ.le
      _ ≤ ∫ s in (0 : ℝ)..τ,
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
            * ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
          rw [intervalIntegral.integral_const_mul]
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hCnn
  rw [hlam_eq]
  exact ShenWork.IntervalDuhamelQuantGain.gainIntegral_le_min hτ hlampos

/-- Windowed per-mode `τ^(1/4)` bound from a closed-window `TimeC1On` source. -/
theorem eigenvalue_mul_coeff_tauQuarter_bound_timeC1On
    {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (src : DuhamelSourceTimeC1On a 0 τ)
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B * τ ^ ((1 : ℝ) / 4) / ((k : ℝ) * Real.pi) ^ ((3 : ℝ) / 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) :=
    by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkπpos : (0 : ℝ) < (k : ℝ) * Real.pi := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  have hlamnn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by
    rw [hlam_eq]
    positivity
  have hinvnn : (0 : ℝ) ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hmin := duhamelSpectralCoeff_min_bound_timeC1On src hτ hB hdecay hk
  have hstep1 : unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
    calc unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
        ≤ unitIntervalCosineEigenvalue k
            * ((2 * B / ((k : ℝ) * Real.pi) ^ 2) *
              min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmin hlamnn
      _ = 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
          rw [hlam_eq]
          rw [show ((k : ℝ) * Real.pi) ^ 2
              * (2 * B / ((k : ℝ) * Real.pi) ^ 2 *
                min τ (1 / ((k : ℝ) * Real.pi) ^ 2))
              = (((k : ℝ) * Real.pi) ^ 2 / ((k : ℝ) * Real.pi) ^ 2)
                  * (2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) by ring,
            div_self (by positivity : ((k : ℝ) * Real.pi) ^ 2 ≠ 0), one_mul]
  have hinterp := ShenWork.IntervalDuhamelQuantGain.min_le_rpow_mul_rpow
    (x := τ) (y := 1 / ((k : ℝ) * Real.pi) ^ 2)
    hτ.le hinvnn (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 1)
  have hrpow_inv : (1 / ((k : ℝ) * Real.pi) ^ 2) ^ (1 - (1 : ℝ) / 4)
      = 1 / ((k : ℝ) * Real.pi) ^ ((3 : ℝ) / 2) := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
    congr 1
    rw [← Real.rpow_natCast ((k : ℝ) * Real.pi) 2, ← Real.rpow_mul hkπpos.le]
    norm_num
  rw [hrpow_inv] at hinterp
  have hstep2 : 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)
      ≤ 2 * B * (τ ^ ((1 : ℝ) / 4) *
        (1 / ((k : ℝ) * Real.pi) ^ ((3 : ℝ) / 2))) :=
    mul_le_mul_of_nonneg_left hinterp (by positivity)
  refine (hstep1.trans hstep2).trans (le_of_eq ?_)
  rw [mul_one_div, mul_div_assoc]

/-- Windowed λ-weighted Duhamel `τ^(1/4)` bound for a `TimeC1On` source. -/
theorem duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound_timeC1On
    {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (src : DuhamelSourceTimeC1On a 0 τ)
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2) :
    (∑' k : ℕ, unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|)
      ≤ (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))
          / Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * B := by
  set C : ℝ := 2 * B * τ ^ ((1 : ℝ) / 4) / Real.pi ^ ((3 : ℝ) / 2) with hC_def
  have hCnn : 0 ≤ C := by rw [hC_def]; positivity
  set f : ℕ → ℝ := fun k =>
    unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k| with hf_def
  have hfnn : ∀ k, 0 ≤ f k := by
    intro k
    refine mul_nonneg ?_ (abs_nonneg _)
    simp only [unitIntervalCosineEigenvalue]
    positivity
  set g : ℕ → ℝ := fun k => C * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))
    with hg_def
  have hg_summable : Summable g :=
    ShenWork.IntervalDuhamelQuantGain.summable_one_div_natShift_rpow_threeHalves.mul_left C
  have hshift_le : ∀ k : ℕ, f (k + 1) ≤ g k := by
    intro k
    have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hbound := eigenvalue_mul_coeff_tauQuarter_bound_timeC1On src hτ hB hdecay hk
    refine hbound.trans (le_of_eq ?_)
    rw [hg_def, hC_def]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hkπpos : (0 : ℝ) < ((k : ℝ) + 1) * Real.pi := by positivity
    rw [Real.mul_rpow (by positivity) Real.pi_nonneg]
    field_simp
  have hf_shift_summable : Summable (fun k => f (k + 1)) :=
    hg_summable.of_nonneg_of_le (fun k => hfnn (k + 1)) hshift_le
  have hf_summable : Summable f :=
    (summable_nat_add_iff (f := f) 1).1 hf_shift_summable
  have hf0 : f 0 = 0 := by
    rw [hf_def]
    simp only [unitIntervalCosineEigenvalue]
    norm_num
  have hsum_shift : (∑' k, f k) = ∑' k, f (k + 1) := by
    rw [hf_summable.tsum_eq_zero_add, hf0, zero_add]
  calc (∑' k : ℕ, unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|)
      = ∑' k : ℕ, f k := by rfl
    _ = ∑' k : ℕ, f (k + 1) := hsum_shift
    _ ≤ ∑' k : ℕ, g k :=
        Summable.tsum_le_tsum hshift_le hf_shift_summable hg_summable
    _ = C * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) :=
        by rw [hg_def, tsum_mul_left]
    _ = (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))
          / Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * B := by
        rw [hC_def]
        ring

/-- λ-weighted restart summability from a closed-window `TimeC1On` source. -/
theorem restartDuhamelCoeff_eigenvalue_summable_timeC1On
    {τ M₁ : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1On a 0 τ) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |restartDuhamelCoeff a₀ a τ n|) := by
  have hhom_sum := hom_eig_summable (M₁ := M₁) hτ ha₀
  have hduh_sum :=
    duhamelSpectralCoeff_eigenvalue_summable_on src hτ (le_refl τ)
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
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)) hsplit_le (hhom_sum.add hduh_sum)

/-- Windowed λ-weighted restart sum bound from a closed-window `TimeC1On` source. -/
theorem restartSeries_eig_tsum_le_timeC1On
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1On a 0 τ)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2) :
    (∑' n, unitIntervalCosineEigenvalue n * |restartDuhamelCoeff a₀ a τ n|)
      ≤ M₁ * eigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv := by
  have hhom_sum := hom_eig_summable (M₁ := M₁) hτ ha₀
  have hduh_sum :=
    duhamelSpectralCoeff_eigenvalue_summable_on src hτ (le_refl τ)
  have hsum_restart := restartDuhamelCoeff_eigenvalue_summable_timeC1On hτ ha₀ src
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
        Summable.tsum_le_tsum hsplit_le hsum_restart (hhom_sum.add hduh_sum)
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
        · exact duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound_timeC1On
            src hτ hBenv hdecay

/-- Windowed explicit G2 sup bound from a closed-window `TimeC1On` source. -/
theorem restartSeries_abs_deriv2_le_timeC1On
    {τ M₁ Benv : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hBenv : 0 ≤ Benv)
    (ha₀ : ∀ n, |a₀ n| ≤ M₁)
    (src : DuhamelSourceTimeC1On a 0 τ)
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ k : ℕ, 1 ≤ k →
      |a σ k| ≤ 2 * Benv / ((k : ℝ) * Real.pi) ^ 2)
    (x : ℝ) :
    |deriv (deriv (fun x => ∑' n, restartDuhamelCoeff a₀ a τ n * cosineMode n x)) x|
      ≤ M₁ * eigExpWeight τ
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * τ ^ ((1 : ℝ) / 4) * Benv :=
  (cosineSeries_abs_deriv2_le_eig_tsum
      (restartDuhamelCoeff_eigenvalue_summable_timeC1On hτ ha₀ src) x).trans
    (restartSeries_eig_tsum_le_timeC1On hτ hBenv ha₀ src hdecay)

/-- `hbsum_succ` variant reading a closed-window shifted-source package. -/
theorem hbsum_succ_on
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ M₁ : ℝ}
    (hσ : 0 < σ)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k)
      0 (σ / 2)) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
  have hτ : 0 < σ / 2 := by positivity
  simpa only [iterateReprCoeff, restartIterateCoeff] using
    restartDuhamelCoeff_eigenvalue_summable_timeC1On (a₀ :=
        cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))))
      hτ hM₁ srcσ

/-- `iterate_abs_deriv2_le_of_windowDecay` variant reading a shifted `TimeC1On`. -/
theorem iterate_abs_deriv2_le_of_windowDecay_on
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M M₁ A₂ : ℝ} (ht : 0 < t) (hBenv : 0 ≤ Benv p M A₂ t)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1On
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)
      0 (t / 2))
    (hdecay : ∀ σ ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
        ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (x : ℝ) :
    |deriv (deriv (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x)) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  have hτ : 0 < t / 2 := by positivity
  simpa only [restartIterateCoeff] using
    restartSeries_abs_deriv2_le_timeC1On (a₀ :=
        cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
      (a := fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)
      hτ hBenv hM₁ srcσ hdecay x

end ShenWork.IntervalPicardSuccLegsOn
