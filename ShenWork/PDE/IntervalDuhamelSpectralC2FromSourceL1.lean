import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalParabolicDuhamelSecondDerivBoundedWeight

/-!
# Spectral Duhamel `C²` from source-`ℓ¹` (parabolic-IBP discharge)

The committed regularity route feeds `cosineCoeffSeries_contDiff_two` with
`bₙ = duhamelSpectralCoeff a t n`, which DEMANDS
`Summable (fun n => λₙ · |Ûₙ(t)|)` — the eigenvalue-weighted (eigen-cube-adjacent)
over-ask.  This lane PRODUCES that summability from the strictly weaker physical
data: source ℓ¹ (`Summable Bv`) plus bounded time-derivative coeffs
(`Summable (fun n => Bv'ₙ / λₙ)`), via the parabolic-IBP cancellation — the time
integral's `1/λ` smoothing kills the `∂ₓₓ` eigenvalue.  This is the parabolic
analog of the committed elliptic bounded-weight resolver `C²`, and it is the
discharge that collapses the eigenvalue over-ask for the Duhamel iterate's `∂ₓₓ`.

The crux is the **KEY IDENTITY**
`λₙ · |duhamelSpectralCoeff a t n| = |duhamelSecondMode λₙ t (a·,n)|`,
proved genuinely from `duhamelSecondMode = -(λ · ∫ …)`, the exponent commute
`-(t-s)·λ = -(λ·(t-s))`, and `|-(λ·X)| = λ·|X|` for `λ ≥ 0`.
-/

open ShenWork.IntervalParabolicDuhamelSecondDerivBoundedWeight
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.CosineSpectrum (cosineMode)

namespace ShenWork.IntervalDuhamelSpectralC2FromSourceL1

open scoped Real

/-- **KEY IDENTITY.**  For `λ = unitIntervalCosineEigenvalue n ≥ 0`,
`λ · |duhamelSpectralCoeff a t n| = |duhamelSecondMode λ t (fun s => a s n)|`.
The exponent commute `-(t-s)·λ = -(λ·(t-s))` makes the two integrands equal, so
`duhamelSecondMode λ t (a·,n) = -(λ · duhamelSpectralCoeff a t n)`; then
`|-(λ·X)| = λ·|X|` since `λ ≥ 0`. -/
theorem eigen_smul_abs_spectralCoeff_eq
    (a : ℝ → ℕ → ℝ) (t : ℝ) (n : ℕ) :
    unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a t n|
      = |duhamelSecondMode (unitIntervalCosineEigenvalue n) t (fun s => a s n)| := by
  set lam := unitIntervalCosineEigenvalue n with hlam_def
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam_def]; unfold unitIntervalCosineEigenvalue; positivity
  -- the two integrands agree pointwise (exponent commute)
  have hint : (∫ s in (0 : ℝ)..t, parabolicWeight lam t s * a s n)
      = duhamelSpectralCoeff a t n := by
    unfold duhamelSpectralCoeff parabolicWeight
    apply intervalIntegral.integral_congr
    intro s _
    simp only []
    rw [← hlam_def]
    have hexp : -(lam * (t - s)) = -(t - s) * lam := by ring
    rw [hexp]
  -- duhamelSecondMode = -(lam * duhamelSpectralCoeff)
  have hsecond : duhamelSecondMode lam t (fun s => a s n)
      = -(lam * duhamelSpectralCoeff a t n) := by
    unfold duhamelSecondMode
    simp only []
    rw [hint]
  rw [hsecond, abs_neg, abs_mul, abs_of_nonneg hlam_nonneg]

/-- **Main: eigenvalue-weighted summability from source-`ℓ¹`.**  The eigenvalue
over-ask `Summable (λₙ·|Ûₙ(t)|)` is discharged from the honest physical data: the
source ℓ¹ bound `Summable Bv` and the bounded-time-derivative ℓ¹ bound
`Summable (Bv'/λ)`, via the parabolic-IBP cancellation.  `n = 0` (`λ₀ = 0`) is
handled by `summable_nat_add_iff 1`: the `n ≥ 1` tail uses `λₙ > 0` through the
committed per-mode summable lemma, and the `n = 0` term is `0·|…| = 0`. -/
theorem duhamelSpectral_eigenvalueSummable_of_sourceL1
    {a adot : ℝ → ℕ → ℝ} {Bv Bv' : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hderiv : ∀ n s, HasDerivAt (fun r => a r n) (adot s n) s)
    (hadotc : ∀ n, Continuous (fun s => adot s n))
    (hBv  : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) t, |a s n| ≤ Bv n)
    (hBv' : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) t, |adot s n| ≤ Bv' n)
    (hsumBv  : Summable Bv)
    (hsumBv' : Summable (fun n => Bv' n / unitIntervalCosineEigenvalue n)) :
    Summable (fun n => unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a t n|) := by
  -- Shifted families (index `k ↦ k+1`), where the eigenvalue is strictly positive.
  set lamS : ℕ → ℝ := fun k => unitIntervalCosineEigenvalue (k + 1) with hlamS
  have hlamS_pos : ∀ k, 0 < lamS k := by
    intro k; rw [hlamS]; unfold unitIntervalCosineEigenvalue
    have : (0 : ℝ) < ((k : ℝ) + 1) * Real.pi := by positivity
    have hne : ((k : ℝ) + 1) * Real.pi ≠ 0 := ne_of_gt this
    push_cast; positivity
  -- The shifted honest ℓ¹ inputs.
  have hsumBvS : Summable (fun k => Bv (k + 1)) :=
    (summable_nat_add_iff 1).mpr hsumBv
  have hsumBv'S : Summable (fun k => Bv' (k + 1) / lamS k) := by
    have := (summable_nat_add_iff (f := fun n => Bv' n / unitIntervalCosineEigenvalue n) 1).mpr
      hsumBv'
    simpa [hlamS] using this
  -- Apply the committed per-mode summable lemma at the shifted index.
  have hsumSecond : Summable
      (fun k => |duhamelSecondMode (lamS k) t (fun s => a s (k + 1))|) :=
    parabolicDuhamel_sndDeriv_Linfty_perMode_summable
      (t := t) (lam := lamS) (Bv := fun k => Bv (k + 1)) (Bv' := fun k => Bv' (k + 1))
      (fhat := fun k s => a s (k + 1)) (fhat' := fun k s => adot s (k + 1))
      ht hlamS_pos (fun k s => hderiv (k + 1) s) (fun k => hadotc (k + 1))
      (fun k s hs => hBv (k + 1) s hs) (fun k s hs => hBv' (k + 1) s hs)
      hsumBvS hsumBv'S
  -- Rewrite the shifted summand via the KEY IDENTITY.
  have htail : Summable
      (fun k => unitIntervalCosineEigenvalue (k + 1) * |duhamelSpectralCoeff a t (k + 1)|) := by
    refine hsumSecond.congr (fun k => ?_)
    rw [hlamS, eigen_smul_abs_spectralCoeff_eq a t (k + 1)]
  -- Lift the `n ≥ 1` tail to the full series (`n = 0` term is `λ₀·|…| = 0`).
  exact (summable_nat_add_iff
    (f := fun n => unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a t n|) 1).mp htail

/-- **Corollary: spectral Duhamel profile is `C²`.**  Composing the discharged
eigenvalue summability with the committed `cosineCoeffSeries_contDiff_two`. -/
theorem duhamelSpectral_profile_contDiff_two_of_sourceL1
    {a adot : ℝ → ℕ → ℝ} {Bv Bv' : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hderiv : ∀ n s, HasDerivAt (fun r => a r n) (adot s n) s)
    (hadotc : ∀ n, Continuous (fun s => adot s n))
    (hBv  : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) t, |a s n| ≤ Bv n)
    (hBv' : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) t, |adot s n| ≤ Bv' n)
    (hsumBv  : Summable Bv)
    (hsumBv' : Summable (fun n => Bv' n / unitIntervalCosineEigenvalue n)) :
    ContDiff ℝ 2 (fun x => ∑' n, duhamelSpectralCoeff a t n * cosineMode n x) :=
  ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
    (duhamelSpectral_eigenvalueSummable_of_sourceL1 ht hderiv hadotc hBv hBv' hsumBv hsumBv')

end ShenWork.IntervalDuhamelSpectralC2FromSourceL1
