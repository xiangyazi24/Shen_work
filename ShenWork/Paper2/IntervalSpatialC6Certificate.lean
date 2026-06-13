import ShenWork.PDE.IntervalResolverSpectralJointC2Closed
import ShenWork.Paper2.IntervalCD6HeatSmoothness

noncomputable section
namespace ShenWork.Paper2.SpatialC6Certificate
open ShenWork.IntervalDomain ShenWork.Paper2.CD6HeatSmoothness
open ShenWork.Paper2.CD6CosineModeBounds
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalResolverSpectralJointC2Closed
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
theorem unitIntervalCosineHeatValue_contDiff_six
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 6 (fun x => unitIntervalCosineHeatValue t a x) :=
  (unitIntervalCosineHeatValue_contDiff_seven ht hM).of_le (by norm_num)

theorem intervalDomainLift_contDiffOn_six_of_eqOn_heatValue
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M)
    {f : intervalDomainPoint → ℝ}
    (hf : Set.EqOn (intervalDomainLift f)
      (fun x => unitIntervalCosineHeatValue t a x) (Set.Ioo (0 : ℝ) 1)) :
    ContDiffOn ℝ 6 (intervalDomainLift f) (Set.Ioo (0 : ℝ) 1) :=
  ((unitIntervalCosineHeatValue_contDiff_six ht hM).contDiffOn).congr hf

theorem cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable
    {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * |b n|)))) :
    ContDiff ℝ 6 (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x) := by
  let v : ℕ → ℕ → ℝ := fun _ n =>
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |b n|))
  refine contDiff_tsum_of_eventually
    (f := fun n x => b n * cosineMode n x) (v := v)
    (N := (6 : ℕ∞)) ?_ ?_ ?_
  · intro n
    unfold cosineMode
    fun_prop
  · intro k _hk
    simpa [v] using hb
  · intro k hk
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn x
    have hk_nat : k ≤ 6 := by exact_mod_cast hk
    have hcd : ContDiffAt ℝ (k : WithTop ℕ∞) (cosineMode n) x := by
      unfold cosineMode
      fun_prop
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_const_mul (b n) hcd, Real.norm_eq_abs, abs_mul]
    have hmode : |iteratedDeriv k (cosineMode n) x| ≤
        |(n : ℝ) * Real.pi| ^ k := by
      simpa [cosineMode, unitIntervalCosineMode,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        using unitIntervalCosineMode_iteratedFDeriv_bound k n x
    have hfreq1 : (1 : ℝ) ≤ |(n : ℝ) * Real.pi| := by
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
      nlinarith [Real.two_le_pi, hn1]
    have hpow : |(n : ℝ) * Real.pi| ^ k ≤
        |(n : ℝ) * Real.pi| ^ (6 : ℕ) :=
      pow_le_pow_right₀ hfreq1 hk_nat
    have hlam : unitIntervalCosineEigenvalue n =
        |(n : ℝ) * Real.pi| ^ (2 : ℕ) := by
      unfold unitIntervalCosineEigenvalue
      rw [sq_abs]
    calc |b n| * |iteratedDeriv k (cosineMode n) x|
        ≤ |b n| * |(n : ℝ) * Real.pi| ^ k :=
          mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
      _ ≤ |b n| * |(n : ℝ) * Real.pi| ^ (6 : ℕ) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = v k n := by
          dsimp [v]
          rw [hlam]
          ring

theorem duhamel_cosine_series_contDiff_six
    {a : ℝ → ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (src : DuhamelSourceTimeC2Coeff a) :
    ContDiff ℝ 6 (fun x : ℝ =>
      ∑' n : ℕ, duhamelSpectralCoeff a t n * cosineMode n x) :=
  cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable
    (duhamelSpectralCoeff_eigenvalue_cube_summable src ht)

theorem intervalIterate_contDiff_six_of_positive_time
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ContDiff ℝ 6 (fun x : ℝ =>
      ∑' n : ℕ, localRestartCoeff a₀ a τ n * cosineMode n x) :=
  cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable
    (localRestartCoeff_eigenvalue_cube_summable hτ ha₀ src)

end ShenWork.Paper2.SpatialC6Certificate
