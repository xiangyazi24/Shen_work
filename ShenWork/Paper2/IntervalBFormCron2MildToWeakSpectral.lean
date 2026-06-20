import ShenWork.Paper2.IntervalBFormCron2MildToWeak
import ShenWork.PDE.IntervalSolutionCoeffDeriv
import ShenWork.PDE.IntervalSemigroupNeumann

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalSemigroupNeumann
open ShenWork.IntervalSolutionCoeffDeriv

/-- Raw test coefficient against the Neumann cosine mode. -/
def cosineTestCoeff (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, cosineMode n x * φ x

/-- Raw test-Laplacian coefficient against the Neumann cosine mode. -/
def cosineTestSecondCoeff (φ'' : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, cosineMode n x * φ'' x

/-- The tested spectral Neumann heat value, after interchanging the spatial
integral with the cosine series. -/
def spectralTestPairing (a : ℕ → ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    Real.exp (-t * unitIntervalCosineEigenvalue n) * a n * cosineTestCoeff φ n

/-- The tested spectral Laplacian value, after the same interchange. -/
def spectralTestLaplacianPairing (a : ℕ → ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    -unitIntervalCosineEigenvalue n *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * a n * cosineTestCoeff φ n

/-- The tested spectral Laplacian before using the cosine-mode IBP. -/
def spectralTestSecondPairing (a : ℕ → ℝ) (φ'' : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    Real.exp (-t * unitIntervalCosineEigenvalue n) * a n *
      cosineTestSecondCoeff φ'' n

/-- Scalar spectral heat series: term-by-term time differentiation under the
minimal bounded-coefficient hypothesis. -/
theorem spectralScalarHeatSeries_hasDerivAt
    {t : ℝ} (ht : 0 < t) {b : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |b n| ≤ M) :
    HasDerivAt
      (fun s : ℝ =>
        ∑' n : ℕ, Real.exp (-s * unitIntervalCosineEigenvalue n) * b n)
      (∑' n : ℕ,
        -unitIntervalCosineEigenvalue n *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * b n) t := by
  classical
  set δ : ℝ := t / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith
  set sset : Set ℝ := Set.Ioi δ with hsset
  set u : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n *
      |Real.exp (-δ * unitIntervalCosineEigenvalue n) * b n| with hu_def
  have hu : Summable u := by
    simpa [u, δ, hδdef] using
      (heatCoeff_eigenvalue_summable (t := δ) hδpos (a := b) (M := M) hM)
  have ht_mem : t ∈ sset := by
    rw [hsset, hδdef]
    exact Set.mem_Ioi.mpr (by linarith)
  have hderiv : ∀ n : ℕ, ∀ w ∈ sset,
      HasDerivAt
        (fun r : ℝ => Real.exp (-r * unitIntervalCosineEigenvalue n) * b n)
        (-unitIntervalCosineEigenvalue n *
          Real.exp (-w * unitIntervalCosineEigenvalue n) * b n) w := by
    intro n w _hw
    set lam : ℝ := unitIntervalCosineEigenvalue n with hlam
    have hlin : HasDerivAt (fun r : ℝ => -r * lam) (-lam) w := by
      convert (hasDerivAt_id w).const_mul (-lam) using 1
      · ext r
        simp only [id_eq]
        ring
      · ring
    have hexp := hlin.exp
    have hmul := hexp.mul_const (b n)
    simpa [lam, hlam, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hbound : ∀ n : ℕ, ∀ w ∈ sset,
      ‖-unitIntervalCosineEigenvalue n *
          Real.exp (-w * unitIntervalCosineEigenvalue n) * b n‖ ≤ u n := by
    intro n w hw
    have hwδ : δ < w := by
      simpa [sset, hsset] using hw
    have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
      simp [unitIntervalCosineEigenvalue]
      positivity
    have hexp_le :
        Real.exp (-w * unitIntervalCosineEigenvalue n)
          ≤ Real.exp (-δ * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg hlam_nonneg, abs_of_nonneg (Real.exp_nonneg _)]
    rw [hu_def]
    calc
      unitIntervalCosineEigenvalue n *
          Real.exp (-w * unitIntervalCosineEigenvalue n) * |b n|
          ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-δ * unitIntervalCosineEigenvalue n) * |b n| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp_le hlam_nonneg) (abs_nonneg _)
      _ = unitIntervalCosineEigenvalue n *
            |Real.exp (-δ * unitIntervalCosineEigenvalue n) * b n| := by
            rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
            ring
  have hsum_at : Summable
      (fun n : ℕ => Real.exp (-t * unitIntervalCosineEigenvalue n) * b n) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ =>
        Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        (t := t) ht).mul_right |M|) ?_
    intro n
    have hbM : |b n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left hbM (Real.exp_nonneg _)
  have hmain :=
    hasDerivAt_tsum_of_isPreconnected
      (u := u)
      (t := sset)
      (g := fun (n : ℕ) (r : ℝ) =>
        Real.exp (-r * unitIntervalCosineEigenvalue n) * b n)
      (g' := fun (n : ℕ) (r : ℝ) =>
        -unitIntervalCosineEigenvalue n *
          Real.exp (-r * unitIntervalCosineEigenvalue n) * b n)
      hu isOpen_Ioi (convex_Ioi δ).isPreconnected hderiv hbound
      ht_mem hsum_at ht_mem
  simpa using hmain

/-- Term-by-term time differentiation for the tested spectral pairing. -/
theorem spectralTestPairing_hasDerivAt
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {φ : ℝ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n * cosineTestCoeff φ n| ≤ M) :
    HasDerivAt (fun s : ℝ => spectralTestPairing a φ s)
      (spectralTestLaplacianPairing a φ t) t := by
  simpa [spectralTestPairing, spectralTestLaplacianPairing, mul_assoc]
    using spectralScalarHeatSeries_hasDerivAt
      (t := t) ht (b := fun n => a n * cosineTestCoeff φ n) hM

/-- Cosine-mode IBP twice for a Neumann test function.  This is the exact
coefficient identity
`∫ cos(nπx) φ'' = -λₙ ∫ cos(nπx) φ`; the endpoint cancellations are
`φ'(0)=φ'(1)=0` and `cosineMode'` vanishing at both endpoints. -/
theorem cosineMode_test_laplacian_coeff_eq
    (n : ℕ) {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ' (φ'' x) x)
    (hφ'int : IntervalIntegrable φ' volume 0 1)
    (hφ''int : IntervalIntegrable φ'' volume 0 1)
    (hbc0 : φ' 0 = 0) (hbc1 : φ' 1 = 0) :
    (∫ x in (0 : ℝ)..1, cosineMode n x * φ'' x) =
      -unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
  have h :=
    intervalCosineLaplacianCoeff_eq n hφ hφ' hφ'int hφ''int hbc0 hbc1
  simpa [cosineTestCoeff, cosineMode, unitIntervalCosineEigenvalue, mul_assoc]
    using h

/-- The spectral tested weak semigroup identity in coefficient form.  The two
`h*_series` hypotheses are precisely the spatial integral/tsum interchanges
for `S_N(t)` and its tested Laplacian; the differentiability itself is supplied
by `spectralTestPairing_hasDerivAt`, and the Laplacian coefficients are supplied
by `cosineMode_test_laplacian_coeff_eq`. -/
theorem spectralTestedSemigroupWeak_hasDerivAt
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {φ φ' φ'' : ℝ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n * cosineTestCoeff φ n| ≤ M)
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ' (φ'' x) x)
    (hφ'int : IntervalIntegrable φ' volume 0 1)
    (hφ''int : IntervalIntegrable φ'' volume 0 1)
    (hbc0 : φ' 0 = 0) (hbc1 : φ' 1 = 0)
    (hvalue_series :
      (fun s : ℝ =>
        ∫ x in (0 : ℝ)..1, unitIntervalCosineHeatValue s a x * φ x)
        = fun s : ℝ => spectralTestPairing a φ s)
    (hlap_series :
      (∫ x in (0 : ℝ)..1, unitIntervalCosineHeatValue t a x * φ'' x)
        = spectralTestSecondPairing a φ'' t) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x in (0 : ℝ)..1, unitIntervalCosineHeatValue s a x * φ x)
      (∫ x in (0 : ℝ)..1, unitIntervalCosineHeatValue t a x * φ'' x) t := by
  have hcoeff : ∀ n : ℕ,
      cosineTestSecondCoeff φ'' n =
        -unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
    intro n
    exact cosineMode_test_laplacian_coeff_eq n hφ hφ' hφ'int hφ''int hbc0 hbc1
  have hlap :
      spectralTestSecondPairing a φ'' t = spectralTestLaplacianPairing a φ t := by
    unfold spectralTestSecondPairing spectralTestLaplacianPairing
    refine tsum_congr (fun n => ?_)
    rw [hcoeff n]
    ring
  rw [hvalue_series, hlap_series, hlap]
  exact spectralTestPairing_hasDerivAt ht hM

/-- The same tested weak identity stated for the full Neumann semigroup
operator `S_N`.  The hypotheses `hvalue_series` and `hlap_series` are exactly
the spectral representation plus the two spatial integral/tsum interchanges. -/
theorem intervalFullSemigroupOperator_spectralTestedWeak_hasDerivAt
    {t : ℝ} (ht : 0 < t) {g φ φ' φ'' : ℝ → ℝ} {M : ℝ}
    (hM : ∀ n, |cosineCoeffs g n * cosineTestCoeff φ n| ≤ M)
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ' (φ'' x) x)
    (hφ'int : IntervalIntegrable φ' volume 0 1)
    (hφ''int : IntervalIntegrable φ'' volume 0 1)
    (hbc0 : φ' 0 = 0) (hbc1 : φ' 1 = 0)
    (hvalue_series :
      (fun s : ℝ =>
        ∫ x in (0 : ℝ)..1, intervalFullSemigroupOperator s g x * φ x)
        = fun s : ℝ => spectralTestPairing (cosineCoeffs g) φ s)
    (hlap_series :
      (∫ x in (0 : ℝ)..1, intervalFullSemigroupOperator t g x * φ'' x)
        = spectralTestSecondPairing (cosineCoeffs g) φ'' t) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x in (0 : ℝ)..1, intervalFullSemigroupOperator s g x * φ x)
      (∫ x in (0 : ℝ)..1, intervalFullSemigroupOperator t g x * φ'' x) t := by
  have hcoeff : ∀ n : ℕ,
      cosineTestSecondCoeff φ'' n =
        -unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
    intro n
    exact cosineMode_test_laplacian_coeff_eq n hφ hφ' hφ'int hφ''int hbc0 hbc1
  have hlap :
      spectralTestSecondPairing (cosineCoeffs g) φ'' t =
        spectralTestLaplacianPairing (cosineCoeffs g) φ t := by
    unfold spectralTestSecondPairing spectralTestLaplacianPairing
    refine tsum_congr (fun n => ?_)
    rw [hcoeff n]
    ring
  rw [hvalue_series, hlap_series, hlap]
  exact spectralTestPairing_hasDerivAt ht hM

/-!
Precise remaining stall for the cron2 interface:
`intervalFullSemigroupOperator_spectralTestedWeak_hasDerivAt` proves the
homogeneous semigroup tested identity from the cosine spectral form.  To turn it
into `TruncatedMildSemigroupWeakAfterBNDualityOn`, the repo still needs the
Duhamel assembly lemma that applies this identity to the initial, logistic, and
chemotaxis legs, including the time-integral endpoint term and the two
spatial integral/tsum interchanges recorded as `hvalue_series` and
`hlap_series` above.  This file does not assume that final interface as a
hypothesis.
-/

end ShenWork.Paper2.BFormPositiveDatumNegPart
