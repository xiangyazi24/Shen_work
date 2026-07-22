import ShenWork.Paper2.IntervalSharpSpectralCalculus
import ShenWork.Paper2.IntervalNeumannHeatGradientL2

/-!
# Physical sine-Parseval realization of sharp fractional divergence decay

This is the physical `L^2([0,1])` realization of the `q = 2` branch of
Paper 2, Lemma 2.4.  The output is the explicit sine series obtained by
applying `(1 - Delta) ^ sigma` to the derivative of the shifted Neumann heat
series.
-/

open MeasureTheory

noncomputable section

namespace ShenWork.Paper2.IntervalSharpSpectralPhysicalFractionalDivergenceL2

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates
open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.FractionalPower
open ShenWork.Paper2.IntervalSharpSpectralCalculus
open ShenWork.IntervalNeumannHeatGradientL2
open ShenWork.IntervalNeumannFullKernel

/-- Real sine amplitude of
`(1 - Delta)^sigma div exp(-t(omega - Delta_N))`. -/
def intervalShiftOneFractionalDivergenceAmp
    (omega sigma t : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  shiftedNeumannEigenvalue 1 n ^ sigma *
    ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n ^
      (1 / 2 : ℝ) *
    Real.exp (-(shiftedNeumannEigenvalue omega n * t)) * a n

/-- The real amplitude is exactly the real form of the complex coefficient
multiplier proved in the spectral-calculus file. -/
theorem intervalShiftOneFractionalDivergenceAmp_ofReal
    (omega sigma t : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    (intervalShiftOneFractionalDivergenceAmp omega sigma t a n : ℂ) =
      shiftedSpectralFractionalCoeff 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t
          (fun k => (a k : ℂ))) n := by
  unfold intervalShiftOneFractionalDivergenceAmp
    shiftedSpectralFractionalCoeff shiftedNeumannDivergenceHeatCoeff
    shiftedNeumannHeatCoeff
  push_cast
  ring

theorem intervalShiftOneFractionalDivergenceAmp_sq_eq_norm_sq
    (omega sigma t : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    (intervalShiftOneFractionalDivergenceAmp omega sigma t a n) ^ 2 =
      ‖shiftedSpectralFractionalCoeff 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t
          (fun k => (a k : ℂ))) n‖ ^ 2 := by
  rw [← intervalShiftOneFractionalDivergenceAmp_ofReal]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem intervalShiftOneFractionalDivergenceAmp_sq_summable
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => (a n) ^ 2) :
    Summable fun n : ℕ =>
      (intervalShiftOneFractionalDivergenceAmp omega sigma t a n) ^ 2 := by
  have haComplex : Summable fun n : ℕ => ‖(a n : ℂ)‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using ha
  have hweightedOmega := shiftedFractionalDivergenceHeatCoeff_l2_summable
    homega hsigma ht haComplex
  have hone := shiftedSpectralFractionalCoeff_l2_summable_of_pos
    (alpha := (1 : ℝ)) (beta := omega) (sigma := sigma)
    (by norm_num) homega hsigma hweightedOmega
  exact hone.congr fun n =>
    (intervalShiftOneFractionalDivergenceAmp_sq_eq_norm_sq
      omega sigma t a n).symm

theorem intervalShiftOneFractionalDivergenceAmp_time_split
    (omega sigma t : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    intervalShiftOneFractionalDivergenceAmp omega sigma t a n =
      Real.exp
          (-(shiftedNeumannEigenvalue omega n * (t / 2))) *
        intervalShiftOneFractionalDivergenceAmp
          omega sigma (t / 2) a n := by
  unfold intervalShiftOneFractionalDivergenceAmp
  rw [show
      -(shiftedNeumannEigenvalue omega n * t) =
        -(shiftedNeumannEigenvalue omega n * (t / 2)) +
          -(shiftedNeumannEigenvalue omega n * (t / 2)) by ring,
    Real.exp_add]
  ring

/-- Positive heat time makes the fractional-divergence amplitudes absolutely
summable, so their physical sine series is pointwise meaningful. -/
theorem intervalShiftOneFractionalDivergenceAmp_abs_summable
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => (a n) ^ 2) :
    Summable fun n : ℕ =>
      ‖intervalShiftOneFractionalDivergenceAmp omega sigma t a n‖ := by
  let u : ℕ → ℝ := fun n =>
    Real.exp (-(shiftedNeumannEigenvalue omega n * (t / 2)))
  let b : ℕ → ℝ := fun n =>
    intervalShiftOneFractionalDivergenceAmp omega sigma (t / 2) a n
  have ht_half : 0 < t / 2 := by linarith
  have hb_sq : Summable fun n : ℕ => (b n) ^ 2 := by
    simpa [b] using
      intervalShiftOneFractionalDivergenceAmp_sq_summable
        homega hsigma ht_half ha
  have htrace : Summable fun n : ℕ =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    unitIntervalCosineHeatTrace_single_exp_summable ht
  have hu_sq : Summable fun n : ℕ => (u n) ^ 2 := by
    refine (htrace.mul_left (Real.exp (-(omega * t)))).congr fun n => ?_
    dsimp [u]
    calc
      Real.exp (-(omega * t)) *
          Real.exp (-t * unitIntervalCosineEigenvalue n) =
        Real.exp
          (-(omega * t) + -t * unitIntervalCosineEigenvalue n) := by
            rw [Real.exp_add]
      _ = Real.exp
          (-(shiftedNeumannEigenvalue omega n * (t / 2))) *
            Real.exp
              (-(shiftedNeumannEigenvalue omega n * (t / 2))) := by
        rw [← Real.exp_add]
        congr 1
        unfold shiftedNeumannEigenvalue unitIntervalCosineEigenvalue
          ShenWork.Paper3.unitIntervalNeumannSpectrum
        ring
      _ = (Real.exp
          (-(shiftedNeumannEigenvalue omega n * (t / 2)))) ^ 2 := by
        ring
  have hproduct := real_summable_abs_mul_of_summable_sq hu_sq hb_sq
  refine hproduct.congr fun n => ?_
  rw [Real.norm_eq_abs,
    intervalShiftOneFractionalDivergenceAmp_time_split]

/-- The physical fractional-divergence sine series. -/
def intervalShiftOneFractionalDivergenceValue
    (omega sigma t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    intervalShiftOneFractionalDivergenceAmp omega sigma t a n *
      Real.sin ((n : ℝ) * Real.pi * x)

theorem intervalShiftOneFractionalDivergenceAmp_zero
    (omega sigma t : ℝ) (a : ℕ → ℝ) :
    intervalShiftOneFractionalDivergenceAmp omega sigma t a 0 = 0 := by
  simp [intervalShiftOneFractionalDivergenceAmp,
    shiftedNeumannEigenvalue,
    ShenWork.Paper3.unitIntervalNeumannSpectrum]

/-- Exact sine Parseval identity for the physical fractional-divergence
series. -/
theorem intervalShiftOneFractionalDivergenceValue_energy_eq
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => (a n) ^ 2) :
    (∫ x,
      (intervalShiftOneFractionalDivergenceValue
        omega sigma t a x) ^ 2 ∂ intervalMeasure 1) =
      (1 / 2 : ℝ) * ∑' n : ℕ,
        (intervalShiftOneFractionalDivergenceAmp
          omega sigma t a n) ^ 2 := by
  exact unitInterval_sineSeries_l2_sq_of_absSummable
    (intervalShiftOneFractionalDivergenceAmp_zero omega sigma t a)
    (intervalShiftOneFractionalDivergenceAmp_abs_summable
      homega hsigma ht ha)
    (intervalShiftOneFractionalDivergenceAmp_sq_summable
      homega hsigma ht ha)

theorem intervalShiftOneFractionalDivergenceAmp_norm_eq
    (omega sigma t : ℝ) (a : ℕ → ℝ) :
    Real.sqrt (∑' n : ℕ,
      (intervalShiftOneFractionalDivergenceAmp omega sigma t a n) ^ 2) =
      shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t
          (fun n => (a n : ℂ))) := by
  unfold shiftedSpectralFractionalNorm coeffL2Norm coeffL2Energy
  congr 1
  exact tsum_congr fun n =>
    intervalShiftOneFractionalDivergenceAmp_sq_eq_norm_sq
      omega sigma t a n

theorem realCoeff_coeffL2Norm_eq
    (a : ℕ → ℝ) :
    coeffL2Norm (fun n => (a n : ℂ)) =
      Real.sqrt (∑' n : ℕ, (a n) ^ 2) := by
  unfold coeffL2Norm coeffL2Energy
  congr 1
  apply tsum_congr
  intro n
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The physical sine-series norm is no larger than its coefficient norm
(the exact factor is `1/sqrt 2`). -/
theorem intervalShiftOneFractionalDivergenceValue_l2_le_spectralNorm
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => (a n) ^ 2) :
    Real.sqrt
        (∫ x,
          (intervalShiftOneFractionalDivergenceValue
            omega sigma t a x) ^ 2 ∂ intervalMeasure 1) ≤
      shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t
          (fun n => (a n : ℂ))) := by
  rw [intervalShiftOneFractionalDivergenceValue_energy_eq
    homega hsigma ht ha]
  let E : ℝ := ∑' n : ℕ,
    (intervalShiftOneFractionalDivergenceAmp omega sigma t a n) ^ 2
  have hE : 0 ≤ E := tsum_nonneg fun n => sq_nonneg _
  have hhalf : (1 / 2 : ℝ) * E ≤ E := by nlinarith
  calc
    Real.sqrt ((1 / 2 : ℝ) * E) ≤ Real.sqrt E :=
      Real.sqrt_le_sqrt hhalf
    _ = shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t
          (fun n => (a n : ℂ))) := by
      exact intervalShiftOneFractionalDivergenceAmp_norm_eq
        omega sigma t a

/-- Physical `L^2([0,1])` sharp Lemma-2.4 estimate, with the fixed
`(1 - Delta)^sigma` graph norm and the independently shifted heat generator. -/
theorem intervalShiftOneFractionalDivergenceValue_l2_decay_exists
    {omega sigma : ℝ} (homega : 0 < omega) (hsigma : 0 < sigma) :
    ∃ C > 0, ∀ t : ℝ, 0 < t → ∀ a : ℕ → ℝ,
      Summable (fun n : ℕ => (a n) ^ 2) →
      Real.sqrt
          (∫ x,
            (intervalShiftOneFractionalDivergenceValue
              omega sigma t a x) ^ 2 ∂ intervalMeasure 1) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) *
            Real.sqrt (∑' n : ℕ, (a n) ^ 2) := by
  rcases shiftOneFractionalDivergenceHeatCoeff_l2_decay_exists
      homega hsigma with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  have haComplex : Summable fun n : ℕ => ‖(a n : ℂ)‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using ha
  calc
    Real.sqrt
        (∫ x,
          (intervalShiftOneFractionalDivergenceValue
            omega sigma t a x) ^ 2 ∂ intervalMeasure 1) ≤
      shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t
          (fun n => (a n : ℂ))) :=
      intervalShiftOneFractionalDivergenceValue_l2_le_spectralNorm
        homega hsigma.le ht ha
    _ ≤ C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) *
            coeffL2Norm (fun n => (a n : ℂ)) :=
      hbase t ht (fun n => (a n : ℂ)) haComplex
    _ = C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) *
            Real.sqrt (∑' n : ℕ, (a n) ^ 2) := by
      rw [realCoeff_coeffL2Norm_eq]

/-- The same physical fractional-gradient series with coefficients extracted
from an actual real interval input. -/
def intervalShiftOneFractionalFullHeatGradientValue
    (omega sigma t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  intervalShiftOneFractionalDivergenceValue
    omega sigma t (cosineCoeffs f) x

/-- Sharp physical Lemma-2.4 estimate for every real `L^2([0,1])` input.
The factor `2` in the witness comes from the repository's unnormalized cosine
coefficient Bessel bound. -/
theorem intervalShiftOneFractionalFullHeatGradientValue_l2_decay_exists
    {omega sigma : ℝ} (homega : 0 < omega) (hsigma : 0 < sigma) :
    ∃ C > 0, ∀ t : ℝ, 0 < t → ∀ f : ℝ → ℝ,
      MemLp f 2 (intervalMeasure 1) →
      Real.sqrt
          (∫ x,
            (intervalShiftOneFractionalFullHeatGradientValue
              omega sigma t f x) ^ 2 ∂ intervalMeasure 1) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) *
            Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1) := by
  rcases intervalShiftOneFractionalDivergenceValue_l2_decay_exists
      homega hsigma with ⟨C0, hC0, hbase⟩
  let C : ℝ := 2 * C0
  have hC : 0 < C := mul_pos (by norm_num) hC0
  refine ⟨C, hC, ?_⟩
  intro t ht f hf
  rcases ShenWork.IntervalNeumannHeatGradientL2.cosineCoeffs_l2_of_memLp hf with
    ⟨hcoeff, hbessel⟩
  have hmeasure :
      (∫ x in (0 : ℝ)..1, (f x) ^ 2) =
        ∫ x, (f x) ^ 2 ∂ intervalMeasure 1 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalMeasure, intervalSet,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hmeasure] at hbessel
  let F : ℝ := C0 * t ^ (-sigma) *
    (1 + t ^ (-(1 / 2 : ℝ))) * Real.exp (-((omega / 2) * t))
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hcoeffBase := hbase t ht (cosineCoeffs f) hcoeff
  change
    Real.sqrt
        (∫ x,
          (intervalShiftOneFractionalDivergenceValue
            omega sigma t (cosineCoeffs f) x) ^ 2
              ∂ intervalMeasure 1) ≤
      C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((omega / 2) * t)) *
          Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)
  calc
    Real.sqrt
        (∫ x,
          (intervalShiftOneFractionalDivergenceValue
            omega sigma t (cosineCoeffs f) x) ^ 2
              ∂ intervalMeasure 1) ≤
      F * Real.sqrt (∑' n : ℕ, (cosineCoeffs f n) ^ 2) := by
        simpa [F] using hcoeffBase
    _ ≤ F *
        (2 * Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_left hbessel hF
    _ = C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((omega / 2) * t)) *
          Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1) := by
      dsimp [F, C]
      ring

#print axioms intervalShiftOneFractionalDivergenceAmp_ofReal
#print axioms intervalShiftOneFractionalDivergenceAmp_sq_eq_norm_sq
#print axioms intervalShiftOneFractionalDivergenceAmp_sq_summable
#print axioms intervalShiftOneFractionalDivergenceAmp_time_split
#print axioms intervalShiftOneFractionalDivergenceAmp_abs_summable
#print axioms intervalShiftOneFractionalDivergenceAmp_zero
#print axioms intervalShiftOneFractionalDivergenceValue_energy_eq
#print axioms intervalShiftOneFractionalDivergenceAmp_norm_eq
#print axioms realCoeff_coeffL2Norm_eq
#print axioms intervalShiftOneFractionalDivergenceValue_l2_le_spectralNorm
#print axioms intervalShiftOneFractionalDivergenceValue_l2_decay_exists
#print axioms intervalShiftOneFractionalFullHeatGradientValue_l2_decay_exists

end ShenWork.Paper2.IntervalSharpSpectralPhysicalFractionalDivergenceL2
