import ShenWork.Paper2.IntervalBFormCron2MildToWeakSpectral
import ShenWork.Paper2.IntervalBFormCron2NegativePartEnergy
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import Mathlib.Analysis.PSeries

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainIntegral intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalNeumannCosineCoeff unitIntervalCosineRawCoeff
   unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelSpectralCoeff_eigenvalue_summable_on)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildRegularityBootstrap
  (restartHomogeneousCoeff_eigenvalue_summable)

/-- Bottom summability atom:
`(k*pi)^2 * exp (-c * (k*pi)^2)` is summable for `c > 0`. -/
theorem unitIntervalEigenvalue_mul_exp_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        Real.exp (-c * unitIntervalCosineEigenvalue k)) := by
  have hcp : 0 < c * Real.pi ^ 2 := by
    positivity
  have hbase :
      Summable (fun k : ℕ =>
        Real.pi ^ 2 *
          ((k : ℝ) ^ 2 * Real.exp (-(c * Real.pi ^ 2) * (k : ℝ)))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 2 (r := c * Real.pi ^ 2) hcp).mul_left
        (Real.pi ^ 2)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _))
    (fun k => ?_) hbase
  simp only [unitIntervalCosineEigenvalue]
  calc ((k : ℝ) * Real.pi) ^ 2 *
        Real.exp (-c * ((k : ℝ) * Real.pi) ^ 2)
      = (k : ℝ) ^ 2 * Real.pi ^ 2 *
          Real.exp (-(c * Real.pi ^ 2) * (k : ℝ) ^ 2) := by
          ring_nf
    _ ≤ (k : ℝ) ^ 2 * Real.pi ^ 2 *
          Real.exp (-(c * Real.pi ^ 2) * (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp_of_le
        have hk_le_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos k with hk | hk
          · simp [hk]
          · exact le_self_pow₀ (Nat.one_le_cast.2 hk) (by norm_num)
        nlinarith
    _ = Real.pi ^ 2 *
          ((k : ℝ) ^ 2 * Real.exp (-(c * Real.pi ^ 2) * (k : ℝ))) := by
          ring

/-- Cosine coefficients are bounded by twice an interval sup bound. -/
theorem truncated_cosineCoeffs_abs_le
    {f : ℝ → ℝ} {B : ℝ}
    (hf : IntervalIntegrable (fun x : ℝ => (f x : ℂ)) volume 0 1)
    (_hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n : ℕ, |cosineCoeffs f n| ≤ 2 * B := by
  intro n
  have hcoeff :=
    unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
      (f := fun x : ℝ => (f x : ℂ)) hf n
  have hnorm_le :
      ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ ≤ B := by
    have hmono :
        ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ ≤
          ∫ _x in (0 : ℝ)..1, B := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hf.norm) intervalIntegrable_const
      intro x hx
      have hnorm : ‖(f x : ℂ)‖ = |f x| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      exact hfb x hx
    calc
      ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ ≤ ∫ _x in (0 : ℝ)..1, B := hmono
      _ = B := by simp
  calc
    |cosineCoeffs f n|
        ≤ 2 * ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ := by
          simpa [cosineCoeffs] using hcoeff
    _ ≤ 2 * B := by
          nlinarith

/-- Continuous-on-`[0,1]` wrapper for the coefficient sup bound. -/
theorem truncated_cosineCoeffs_abs_le_of_continuous
    {f : ℝ → ℝ} {B : ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n : ℕ, |cosineCoeffs f n| ≤ 2 * B := by
  have hfC : ContinuousOn (fun x : ℝ => (f x : ℂ)) (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hint : IntervalIntegrable (fun x : ℝ => (f x : ℂ)) volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact truncated_cosineCoeffs_abs_le hint hB hfb

/-- The zeroth normalized Neumann cosine coefficient is exactly the interval integral. -/
theorem zeroth_cosineCoeff_eq_integral (f : ℝ → ℝ) :
    cosineCoeffs f 0 = ∫ x in (0 : ℝ)..1, f x := by
  simp only [cosineCoeffs, unitIntervalNeumannCosineCoeff, unitIntervalCosineRawCoeff]
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, if_true]
  have hfun :
      (fun x : ℝ => ((1 : ℝ) : ℂ) * ((f x : ℝ) : ℂ)) =
        fun x : ℝ => ((f x : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_one, one_mul]
  rw [hfun, intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- Alias with the interval-integral spelling used by older B-form files. -/
theorem cosineCoeffs_zero_eq_intervalIntegral (f : ℝ → ℝ) :
    cosineCoeffs f 0 = ∫ x in (0 : ℝ)..1, f x :=
  zeroth_cosineCoeff_eq_integral f

/-- Explicit real/complex conversion form of the zeroth coefficient identity. -/
theorem cosineCoeffs_zero_eq_intervalIntegral_explicit (f : ℝ → ℝ) :
    cosineCoeffs f 0 = ∫ x in (0 : ℝ)..1, f x :=
  zeroth_cosineCoeff_eq_integral f

/-- Zeroth coefficient of the lifted interval profile equals interval-domain mass. -/
theorem hmassCoeff (u : intervalDomainPoint → ℝ) :
    cosineCoeffs (intervalDomainLift u) 0 =
      intervalDomain.integral u := by
  simpa [intervalDomain, intervalDomainIntegral] using
    zeroth_cosineCoeff_eq_integral (intervalDomainLift u)

/-- Bottom M-test for the weak Laplacian pairing at positive time. -/
theorem lap_summable_of_exp_duhamel_bound
    {t C0 CD Mtest : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C0) (hCD : 0 ≤ CD) (_hMtest : 0 ≤ Mtest)
    {a0 duh testCoeff : ℕ → ℝ}
    (ha0 : ∀ k, |a0 k| ≤ C0)
    (hduh : ∀ k, |duh k| ≤ CD * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k))
    (htest : ∀ k, |testCoeff k| ≤ Mtest) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
          testCoeff k|) := by
  have ht2 : 0 < t / 2 := by
    linarith
  have hbase :=
    unitIntervalEigenvalue_mul_exp_summable (c := t / 2) ht2
  have hmajor :
      Summable (fun k : ℕ =>
        ((C0 + CD) * Mtest) *
          (unitIntervalCosineEigenvalue k *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k))) :=
    hbase.mul_left ((C0 + CD) * Mtest)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
    (fun k => ?_) hmajor
  have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hhalf_nonneg :
      0 ≤ Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) :=
    Real.exp_nonneg _
  have hexp_le :
      Real.exp (-t * unitIntervalCosineEigenvalue k) ≤
        Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hhom :
      |Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k|
        ≤ C0 * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) := by
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      Real.exp (-t * unitIntervalCosineEigenvalue k) * |a0 k|
          ≤ Real.exp (-t * unitIntervalCosineEigenvalue k) * C0 :=
            mul_le_mul_of_nonneg_left (ha0 k) (Real.exp_nonneg _)
      _ ≤ Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) * C0 :=
            mul_le_mul_of_nonneg_right hexp_le hC0
      _ = C0 * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) := by
            ring
  have hsum_part :
      |Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k|
        ≤ (C0 + CD) *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) := by
    calc
      |Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k|
          ≤ |Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k| +
              |duh k| := abs_add_le _ _
      _ ≤ C0 * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) +
            CD * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) :=
            add_le_add hhom (hduh k)
      _ = (C0 + CD) * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k) := by
            ring
  have hprod :
      |(Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
          testCoeff k|
        ≤ ((C0 + CD) *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k)) * Mtest := by
    rw [abs_mul]
    exact mul_le_mul hsum_part (htest k) (abs_nonneg _)
      (mul_nonneg (add_nonneg hC0 hCD) hhalf_nonneg)
  calc
    unitIntervalCosineEigenvalue k *
        |(Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
          testCoeff k|
        ≤ unitIntervalCosineEigenvalue k *
          (((C0 + CD) *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k)) * Mtest) :=
          mul_le_mul_of_nonneg_left hprod hlam
    _ = ((C0 + CD) * Mtest) *
          (unitIntervalCosineEigenvalue k *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k)) := by
          ring

/-- The downstream `lap_summable` atom for coefficient-route weak testing. -/
theorem lap_summable
    {t C0 CD Mtest : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C0) (hCD : 0 ≤ CD) (hMtest : 0 ≤ Mtest)
    {a0 duh : ℕ → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (ha0 : ∀ k, |a0 k| ≤ C0)
    (hduh : ∀ k, |duh k| ≤ CD * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k))
    (htest : ∀ k,
      |cosineTestCoeff (negativePartTest u t) k| ≤ Mtest) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
          cosineTestCoeff (negativePartTest u t) k|) :=
  lap_summable_of_exp_duhamel_bound ht hC0 hCD hMtest ha0 hduh htest

/-- Signed version of `lap_summable_of_exp_duhamel_bound`, for weak-test fields. -/
theorem lap_signed_summable_of_exp_duhamel_bound
    {t C0 CD Mtest : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C0) (hCD : 0 ≤ CD) (hMtest : 0 ≤ Mtest)
    {a0 duh testCoeff : ℕ → ℝ}
    (ha0 : ∀ k, |a0 k| ≤ C0)
    (hduh : ∀ k, |duh k| ≤ CD * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k))
    (htest : ∀ k, |testCoeff k| ≤ Mtest) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        ((Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
          testCoeff k)) := by
  have habs :=
    lap_summable_of_exp_duhamel_bound ht hC0 hCD hMtest ha0 hduh htest
  refine Summable.of_norm ?_
  have hnorm :
      (fun k : ℕ =>
        ‖unitIntervalCosineEigenvalue k *
          ((Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
            testCoeff k)‖) =
        fun k : ℕ =>
          unitIntervalCosineEigenvalue k *
            |(Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
              testCoeff k| := by
    funext k
    have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlam]
  simpa only [hnorm] using habs

/-- Downstream signed Laplacian summability for the negative-part test. -/
theorem lap_signed_summable
    {t C0 CD Mtest : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C0) (hCD : 0 ≤ CD) (hMtest : 0 ≤ Mtest)
    {a0 duh : ℕ → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (ha0 : ∀ k, |a0 k| ≤ C0)
    (hduh : ∀ k, |duh k| ≤ CD * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue k))
    (htest : ∀ k,
      |cosineTestCoeff (negativePartTest u t) k| ≤ Mtest) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        ((Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k + duh k) *
          cosineTestCoeff (negativePartTest u t) k)) :=
  lap_signed_summable_of_exp_duhamel_bound ht hC0 hCD hMtest ha0 hduh htest

/-- Public windowed restart summability wrapper. -/
theorem localRestartCoeff_eigenvalue_summable_of_on
    {τ M W : ℝ} {a0 : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (hτW : τ ≤ W)
    (ha0 : ∀ n, |a0 n| ≤ M)
    (src : DuhamelSourceTimeC1On a 0 W) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a0 a τ n|) := by
  have hhom := restartHomogeneousCoeff_eigenvalue_summable (τ := τ) hτ ha0
  have hduh0 :
      Summable (fun n : ℕ =>
        unitIntervalCosineEigenvalue n *
          |∫ s in (0 : ℝ)..τ,
            Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) * a s n|) :=
    duhamelSpectralCoeff_eigenvalue_summable_on src hτ hτW
  have hduh :
      Summable (fun n : ℕ =>
        unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n|) := by
    simpa [duhamelSpectralCoeff] using hduh0
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _))
    (fun n => ?_) (hhom.add hduh)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (by simp only [localRestartCoeff]; exact abs_add_le _ _)
    (by unfold unitIntervalCosineEigenvalue; positivity)

end ShenWork.Paper2.BFormPositiveDatumNegPart
