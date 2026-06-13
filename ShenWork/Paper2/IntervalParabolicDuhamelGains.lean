import ShenWork.Paper2.IntervalSpatialC6Certificate
import ShenWork.Paper2.IntervalChiNegSourceTail

open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff duhamelSpectral_eq_cosineSeries)
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalResolverSpectralJointC2Closed
  (duhamelSpectralCoeff_eigenvalue_sq_summable)
open ShenWork.IntervalResolverJointC2 (ResolverHasSpectralAgreementC2Coeff)
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.SpatialC6Certificate
open ShenWork.Paper2.CD6CosineModeBounds
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.ChiNegSourceTail
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.ParabolicDuhamelGains

theorem cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |b n|))) :
    ContDiff ℝ 4 (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x) := by
  let v : ℕ → ℕ → ℝ := fun _ n =>
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |b n|)
  refine contDiff_tsum_of_eventually
    (f := fun n x => b n * cosineMode n x) (v := v)
    (N := (4 : ℕ∞)) ?_ ?_ ?_
  · intro n
    unfold cosineMode
    fun_prop
  · intro k _hk
    simpa [v] using hb
  · intro k hk
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn x
    have hk_nat : k ≤ 4 := by exact_mod_cast hk
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
        |(n : ℝ) * Real.pi| ^ (4 : ℕ) :=
      pow_le_pow_right₀ hfreq1 hk_nat
    have hlam : unitIntervalCosineEigenvalue n =
        |(n : ℝ) * Real.pi| ^ (2 : ℕ) := by
      unfold unitIntervalCosineEigenvalue
      rw [sq_abs]
    calc |b n| * |iteratedDeriv k (cosineMode n) x|
        ≤ |b n| * |(n : ℝ) * Real.pi| ^ k :=
          mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
      _ ≤ |b n| * |(n : ℝ) * Real.pi| ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = v k n := by
          dsimp [v]
          rw [hlam]
          ring

theorem duhamel_cosine_series_contDiff_four
    {a : ℝ → ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (src : DuhamelSourceTimeC2Coeff a) :
    ContDiff ℝ 4 (fun x : ℝ =>
      ∑' n : ℕ, duhamelSpectralCoeff a t n * cosineMode n x) :=
  cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    (duhamelSpectralCoeff_eigenvalue_sq_summable src ht)

theorem intervalDuhamelTerm_contDiff_four_of_timeC2Coeff
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (ht : 0 < t) :
    ContDiff ℝ 4
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) := by
  have hseries := duhamel_cosine_series_contDiff_four ht src
  have hEq :
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x)
        =
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a t n * cosineMode n x) := by
    funext x
    exact duhamelSpectral_eq_cosineSeries src.toTimeC1 ht
  rwa [hEq]

theorem intervalDuhamelTerm_contDiff_six_of_timeC2Coeff
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (ht : 0 < t) :
    ContDiff ℝ 6
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) := by
  have hseries : ContDiff ℝ 6
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a t n * cosineMode n x) :=
    duhamel_cosine_series_contDiff_six ht src
  have hEq :
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x)
        =
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a t n * cosineMode n x) := by
    funext x
    exact duhamelSpectral_eq_cosineSeries src.toTimeC1 ht
  rwa [hEq]

theorem duhamelGain_C1_to_C3
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (ht : 0 < t) :
    ContDiff ℝ 3
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) :=
  (intervalDuhamelTerm_contDiff_four_of_timeC2Coeff src ht).of_le (by norm_num)

theorem duhamelGain_C2_to_C4
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (ht : 0 < t) :
    ContDiff ℝ 4
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) :=
  intervalDuhamelTerm_contDiff_four_of_timeC2Coeff src ht

theorem duhamelGain_C3_to_C5
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (ht : 0 < t) :
    ContDiff ℝ 5
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) :=
  (intervalDuhamelTerm_contDiff_six_of_timeC2Coeff src ht).of_le (by norm_num)

theorem duhamelGain_C4_to_C6
    {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (ht : 0 < t) :
    ContDiff ℝ 6
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (a s) x) :=
  intervalDuhamelTerm_contDiff_six_of_timeC2Coeff src ht

def assembleParabolicGainAtoms
    {U V F : ℕ → intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 (U 2))
    (resolverAhead :
      ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) (V k))
    (chemDivLosesOne :
      ∀ k, 2 ≤ k → k < 6 →
        CoupledSlice k (U k) (V k) → SpatialSlice (k - 1) (F k))
    (duhamelGainsTwo :
      ∀ k, 2 ≤ k → k < 6 →
        SpatialSlice (k - 1) (F k) → SpatialSlice (k + 1) (U (k + 1))) :
    ParabolicGainAtoms U V F where
  baseC2 := baseC2
  resolverAhead := resolverAhead
  chemDivLosesOne := chemDivLosesOne
  duhamelGainsTwo := duhamelGainsTwo

theorem assembledAtoms_climb_C2_to_C6
    {U V F : ℕ → intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 (U 2))
    (resolverAhead :
      ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) (V k))
    (chemDivLosesOne :
      ∀ k, 2 ≤ k → k < 6 →
        CoupledSlice k (U k) (V k) → SpatialSlice (k - 1) (F k))
    (duhamelGainsTwo :
      ∀ k, 2 ≤ k → k < 6 →
        SpatialSlice (k - 1) (F k) → SpatialSlice (k + 1) (U (k + 1))) :
    SpatialSlice 6 (U 6) :=
  intervalIterate_contDiff_six
    (assembleParabolicGainAtoms baseC2 resolverAhead
      chemDivLosesOne duhamelGainsTwo)

theorem chiNeg_resolverC2_of_eigenCubeTail
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ResolverHasSpectralAgreementC2Coeff T u :=
  resolverHasSpectralAgreementC2Coeff_of_eigenCubeTail
    H mkL C0 C C0dot Cdot hC6 hCdot6 tail

end ShenWork.Paper2.ParabolicDuhamelGains
