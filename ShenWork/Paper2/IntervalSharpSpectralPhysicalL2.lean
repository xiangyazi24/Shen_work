import ShenWork.Paper2.IntervalSharpSpectralCalculus
import ShenWork.Paper2.IntervalNeumannHeatGradientL2

/-!
# Parseval realization of the sharp spectral estimates in physical interval `L^2`

The normalized cosine Hilbert basis is complete in
`Lp C 2 (intervalMeasure 1)`.  This file reconstructs the sharp fractional
heat and heat-difference coefficient sequences as actual interval `L^2`
vectors and transfers the coefficient estimates without loss.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalSharpSpectralPhysicalL2

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates
open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.F1ProbeFractionalMultiplier
open ShenWork.PDE.F1ProbeFractionalSmoothing
open ShenWork.Paper2.IntervalSharpSpectralCalculus
open ShenWork.IntervalNeumannFullKernel

/-- Parseval identifies the norm of cosine reconstruction with the
coefficient norm used by the sharp spectral calculus. -/
theorem cosineLpFromCoeffs_norm_eq_coeffL2Norm
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs a ha‖ =
      coeffL2Norm a := by
  have hsq :=
    ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs_norm_sq a ha
  have hsq' :
      ‖ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs a ha‖ ^ 2 =
        coeffL2Energy a := by
    simpa [ShenWork.PDE.SectorialOperator.coeffL2Energy,
      coeffL2Energy] using hsq
  have hright_sq : (coeffL2Norm a) ^ 2 = coeffL2Energy a := by
    rw [coeffL2Norm, Real.sq_sqrt]
    exact tsum_nonneg fun n => sq_nonneg _
  exact (sq_eq_sq₀
    (norm_nonneg (ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs a ha))
    (Real.sqrt_nonneg (coeffL2Energy a))).mp
      (hsq'.trans hright_sq.symm)

/-- Parseval for the coefficient sequence of an arbitrary interval `L^2`
vector. -/
theorem coeffL2Norm_cosine_repr_eq_norm
    (f : Lp ℂ 2 (intervalMeasure 1)) :
    coeffL2Norm
        (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) = ‖f‖ := by
  rw [coeffL2Norm]
  have henergy :=
    ShenWork.Paper2.IntervalDomainLemma21.unitIntervalCosineHilbertBasis_repr_energy_eq_norm_sq f
  have henergy' :
      coeffL2Energy
          (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) =
        ‖f‖ ^ 2 := by
    simpa [coeffL2Energy,
      ShenWork.Paper2.IntervalDomainLemma21.spectralCoeffL2Energy] using henergy
  rw [henergy', Real.sqrt_sq (norm_nonneg f)]

/-- The fractional heat coefficient sequence is square summable. -/
theorem shiftedSpectralFractionalHeatCoeff_l2_summable
    {omega sigma t : ℝ} (homega : 0 ≤ omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannHeatCoeff omega t a) n‖ ^ 2 := by
  simpa [shiftedSpectralFractionalCoeff,
    shiftedNeumannFractionalGeneratorHeatCoeff] using
    shiftedNeumannFractionalGeneratorHeatCoeff_l2_summable
      homega hsigma ht ha

/-- Actual interval `L^2` vector representing
`(-Delta_N+omega)^sigma exp(-t(-Delta_N+omega))a`. -/
def intervalShiftedFractionalHeatLp
    {omega sigma t : ℝ} (homega : 0 ≤ omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs
    (shiftedSpectralFractionalCoeff omega sigma
      (shiftedNeumannHeatCoeff omega t a))
    (shiftedSpectralFractionalHeatCoeff_l2_summable
      homega hsigma ht ha)

theorem intervalShiftedFractionalHeatLp_repr
    {omega sigma t : ℝ} (homega : 0 ≤ omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (intervalShiftedFractionalHeatLp homega hsigma ht a ha) n =
      shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannHeatCoeff omega t a) n := by
  exact ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs_repr _ _ n

/-- Physical-interval Parseval form of sharp `t^{-sigma}` smoothing. -/
theorem intervalShiftedFractionalHeatLp_norm_le
    {omega sigma t : ℝ} (homega : 0 ≤ omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖intervalShiftedFractionalHeatLp homega hsigma ht a ha‖ ≤
      ((sigma / Real.exp 1) ^ sigma * t ^ (-sigma)) * coeffL2Norm a := by
  rw [intervalShiftedFractionalHeatLp,
    cosineLpFromCoeffs_norm_eq_coeffL2Norm]
  exact shiftedSpectralFractionalNorm_heat_le homega hsigma ht ha

/-- Physical-interval Parseval form with the exponential spectral-gap factor. -/
theorem intervalShiftedFractionalHeatLp_norm_le_with_decay
    {omega delta sigma t : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖intervalShiftedFractionalHeatLp homega.le hsigma ht a ha‖ ≤
      ((sigma / Real.exp 1) ^ sigma *
          (1 - delta / omega) ^ (-sigma)) *
        t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a := by
  rw [intervalShiftedFractionalHeatLp,
    cosineLpFromCoeffs_norm_eq_coeffL2Norm]
  exact shiftedSpectralFractionalNorm_heat_le_with_decay
    homega hdelta hdeltaomega hsigma ht ha

/-! ### Fixed shift-one graph norm with an independent heat shift -/

theorem shiftOneSpectralFractionalHeatCoeff_l2_summable
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff 1 sigma
        (shiftedNeumannHeatCoeff omega t a) n‖ ^ 2 := by
  have homegaSum := shiftedSpectralFractionalHeatCoeff_l2_summable
    homega.le hsigma ht ha
  exact shiftedSpectralFractionalCoeff_l2_summable_of_pos
    (alpha := (1 : ℝ)) (beta := omega) (sigma := sigma)
    (by norm_num) homega hsigma homegaSum

/-- Physical `L^2` realization of
`(1 - Delta_N)^sigma exp(-t(omega - Delta_N))a`. -/
def intervalShiftOneFractionalHeatLp
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs
    (shiftedSpectralFractionalCoeff 1 sigma
      (shiftedNeumannHeatCoeff omega t a))
    (shiftOneSpectralFractionalHeatCoeff_l2_summable
      homega hsigma ht ha)

theorem intervalShiftOneFractionalHeatLp_repr
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (intervalShiftOneFractionalHeatLp homega hsigma ht a ha) n =
      shiftedSpectralFractionalCoeff 1 sigma
        (shiftedNeumannHeatCoeff omega t a) n := by
  exact ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs_repr _ _ n

theorem intervalShiftOneFractionalHeatLp_norm_eq
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖intervalShiftOneFractionalHeatLp homega hsigma ht a ha‖ =
      shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannHeatCoeff omega t a) := by
  exact cosineLpFromCoeffs_norm_eq_coeffL2Norm _ _

/-- Physical Parseval packaging of the sharp Lemma-2.1 smoothing branch with
the fixed graph norm and independent positive shift. -/
theorem intervalShiftOneFractionalHeatLp_decay_exists
    {omega delta sigma : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) :
    ∃ C > 0, ∀ t : ℝ, ∀ ht : 0 < t, ∀ a : ℕ → ℂ,
      ∀ ha : Summable (fun n : ℕ => ‖a n‖ ^ 2),
      ‖intervalShiftOneFractionalHeatLp homega hsigma ht a ha‖ ≤
        C * t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a := by
  rcases shiftOneSpectralFractionalNorm_heat_decay_exists
      homega hdelta hdeltaomega hsigma with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  rw [intervalShiftOneFractionalHeatLp_norm_eq]
  exact hbase t ht a ha

/-- The fixed-shift smoothing output for an arbitrary interval `L^2` input,
using its complete cosine-Hilbert representation. -/
def intervalShiftOneFractionalHeatLpOfLp
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (f : Lp ℂ 2 (intervalMeasure 1)) :
    Lp ℂ 2 (intervalMeasure 1) :=
  intervalShiftOneFractionalHeatLp homega hsigma ht
    (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n)
    (ShenWork.Paper2.IntervalDomainLemma21.unitIntervalCosineHilbertBasis_repr_l2_summable f)

/-- Sharp Lemma-2.1 smoothing stated directly on the interval `L^2` space. -/
theorem intervalShiftOneFractionalHeatLpOfLp_decay_exists
    {omega delta sigma : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) :
    ∃ C > 0, ∀ t : ℝ, ∀ ht : 0 < t,
      ∀ f : Lp ℂ 2 (intervalMeasure 1),
      ‖intervalShiftOneFractionalHeatLpOfLp homega hsigma ht f‖ ≤
        C * t ^ (-sigma) * Real.exp (-(delta * t)) * ‖f‖ := by
  rcases intervalShiftOneFractionalHeatLp_decay_exists
      homega hdelta hdeltaomega hsigma with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht f
  unfold intervalShiftOneFractionalHeatLpOfLp
  calc
    ‖intervalShiftOneFractionalHeatLp homega hsigma ht
        (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n)
        (ShenWork.Paper2.IntervalDomainLemma21.unitIntervalCosineHilbertBasis_repr_l2_summable f)‖ ≤
      C * t ^ (-sigma) * Real.exp (-(delta * t)) *
        coeffL2Norm
          (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) :=
      hbase t ht _ _
    _ = C * t ^ (-sigma) * Real.exp (-(delta * t)) * ‖f‖ := by
      rw [coeffL2Norm_cosine_repr_eq_norm]

/-- Square summability of the physical heat-difference coefficients under the
genuine fractional-domain hypothesis. -/
theorem shiftedNeumannHeatDifferenceCoeff_l2_summable
    {omega t sigma : ℝ} (homega : 0 ≤ omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    {a : ℕ → ℂ}
    (hfrac : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖shiftedNeumannHeatDifferenceCoeff omega t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    (shiftedNeumannHeatDifferenceCoeff_sq_le
      homega ht hsigma hsigma_one a)
    (hfrac.mul_left ((t ^ sigma) ^ 2))

/-- Actual interval `L^2` vector representing `(exp(-tA)-I)a`. -/
def intervalShiftedHeatDifferenceLp
    {omega t sigma : ℝ} (homega : 0 ≤ omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (a : ℕ → ℂ)
    (hfrac : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs
    (shiftedNeumannHeatDifferenceCoeff omega t a)
    (shiftedNeumannHeatDifferenceCoeff_l2_summable
      homega ht hsigma hsigma_one hfrac)

theorem intervalShiftedHeatDifferenceLp_repr
    {omega t sigma : ℝ} (homega : 0 ≤ omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (a : ℕ → ℂ)
    (hfrac : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2)
    (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (intervalShiftedHeatDifferenceLp
          homega ht hsigma hsigma_one a hfrac) n =
      shiftedNeumannHeatDifferenceCoeff omega t a n := by
  exact ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs_repr _ _ n

/-- Physical-interval Parseval form of the sharp difference estimate. -/
theorem intervalShiftedHeatDifferenceLp_norm_le
    {omega t sigma : ℝ} (homega : 0 ≤ omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (a : ℕ → ℂ)
    (hfrac : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2) :
    ‖intervalShiftedHeatDifferenceLp
        homega ht hsigma hsigma_one a hfrac‖ ≤
      t ^ sigma * shiftedSpectralFractionalNorm omega sigma a := by
  rw [intervalShiftedHeatDifferenceLp,
    cosineLpFromCoeffs_norm_eq_coeffL2Norm]
  exact shiftedNeumannHeatDifferenceCoeff_l2_norm_le
    homega ht hsigma hsigma_one hfrac

/-- Physical heat-difference vector whose domain is measured by the fixed
shift-one graph norm, while the heat generator uses the independent shift
`omega`. -/
def intervalShiftedHeatDifferenceLpShiftOne
    {omega t sigma : ℝ} (homega : 0 < omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (a : ℕ → ℂ)
    (hfracOne : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff 1 sigma a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  let hfracOmega : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2 :=
    shiftedSpectralFractionalCoeff_l2_summable_of_pos
      homega (by norm_num) hsigma.le hfracOne
  intervalShiftedHeatDifferenceLp
    homega.le ht hsigma hsigma_one a hfracOmega

theorem intervalShiftedHeatDifferenceLpShiftOne_repr
    {omega t sigma : ℝ} (homega : 0 < omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (a : ℕ → ℂ)
    (hfracOne : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff 1 sigma a n‖ ^ 2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (intervalShiftedHeatDifferenceLpShiftOne
          homega ht hsigma hsigma_one a hfracOne) n =
      shiftedNeumannHeatDifferenceCoeff omega t a n := by
  exact ShenWork.PDE.SectorialOperator.cosineLpFromCoeffs_repr _ _ n

/-- Physical Parseval packaging of the sharp Lemma-2.1 difference branch. -/
theorem intervalShiftedHeatDifferenceLpShiftOne_norm_exists
    {omega sigma : ℝ} (homega : 0 < omega)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t : ℝ, ∀ ht : 0 < t, ∀ a : ℕ → ℂ,
      ∀ hfracOne : Summable (fun n : ℕ =>
        ‖shiftedSpectralFractionalCoeff 1 sigma a n‖ ^ 2),
      ‖intervalShiftedHeatDifferenceLpShiftOne
          homega ht hsigma hsigma_one a hfracOne‖ ≤
        C * t ^ sigma * shiftedSpectralFractionalNorm 1 sigma a := by
  rcases shiftedNeumannHeatDifferenceCoeff_shiftOneNorm_exists
      homega hsigma hsigma_one with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht a hfracOne
  rw [intervalShiftedHeatDifferenceLpShiftOne,
    intervalShiftedHeatDifferenceLp,
    cosineLpFromCoeffs_norm_eq_coeffL2Norm]
  exact hbase t ht a hfracOne

/-- Heat difference for an arbitrary interval `L^2` vector in the genuine
shift-one fractional domain. -/
def intervalShiftedHeatDifferenceLpShiftOneOfLp
    {omega t sigma : ℝ} (homega : 0 < omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (f : Lp ℂ 2 (intervalMeasure 1))
    (hfrac : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff 1 sigma
        (fun k : ℕ => unitIntervalCosineHilbertBasis.repr f k) n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  intervalShiftedHeatDifferenceLpShiftOne
    homega ht hsigma hsigma_one
    (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) hfrac

/-- Sharp Lemma-2.1 difference estimate stated directly on its interval
fractional domain. -/
theorem intervalShiftedHeatDifferenceLpShiftOneOfLp_norm_exists
    {omega sigma : ℝ} (homega : 0 < omega)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t : ℝ, ∀ ht : 0 < t,
      ∀ f : Lp ℂ 2 (intervalMeasure 1),
      ∀ hfrac : Summable (fun n : ℕ =>
        ‖shiftedSpectralFractionalCoeff 1 sigma
          (fun k : ℕ => unitIntervalCosineHilbertBasis.repr f k) n‖ ^ 2),
      ‖intervalShiftedHeatDifferenceLpShiftOneOfLp
          homega ht hsigma hsigma_one f hfrac‖ ≤
        C * t ^ sigma * shiftedSpectralFractionalNorm 1 sigma
          (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) := by
  rcases intervalShiftedHeatDifferenceLpShiftOne_norm_exists
      homega hsigma hsigma_one with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht f hfrac
  exact hbase t ht
    (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) hfrac

/-! ## Physical full-kernel divergence estimate -/

/-- Actual shifted full-kernel heat gradient.  This definition exposes the
spatial derivative already used by the repository's real sine-Parseval
theorem, with the spectral shift factored out. -/
def intervalShiftedFullHeatGradient
    (omega t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(omega * t)) *
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x

/-- Physical `L^2([0,1])` form of Lemma 2.3 for the shifted full Neumann
kernel.  It follows from the repository's cosine-to-sine Parseval estimate;
the constant is independent of time and of the input. -/
theorem intervalShiftedFullHeatGradient_l2_decay_exists
    (omega : ℝ) :
    ∃ C > 0, ∀ t > 0, ∀ f : ℝ → ℝ,
      MemLp f 2 (intervalMeasure 1) →
      Real.sqrt
          (∫ x, (intervalShiftedFullHeatGradient omega t f x) ^ 2
            ∂ intervalMeasure 1) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(omega * t)) *
            Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1) := by
  rcases
      ShenWork.IntervalNeumannHeatGradientL2.neumannHeatGradientTMinusHalfBound_proof
    with ⟨C0, hC0, hbase⟩
  let C : ℝ := max C0 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right C0 1)
  refine ⟨C, hC, ?_⟩
  intro t ht f hf
  have hb := hbase t ht f hf
  let e : ℝ := Real.exp (-(omega * t))
  have he : 0 < e := Real.exp_pos _
  let g : ℝ → ℝ := fun x =>
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x
  have henergy :
      (∫ x, (e * g x) ^ 2 ∂ intervalMeasure 1) =
        e ^ 2 * ∫ x, (g x) ^ 2 ∂ intervalMeasure 1 := by
    calc
      (∫ x, (e * g x) ^ 2 ∂ intervalMeasure 1) =
          ∫ x, e ^ 2 * (g x) ^ 2 ∂ intervalMeasure 1 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = e ^ 2 * ∫ x, (g x) ^ 2 ∂ intervalMeasure 1 := by
        rw [integral_const_mul]
  have hscaled :
      Real.sqrt (∫ x, (e * g x) ^ 2 ∂ intervalMeasure 1) =
        e * Real.sqrt (∫ x, (g x) ^ 2 ∂ intervalMeasure 1) := by
    rw [henergy, Real.sqrt_mul (sq_nonneg e), Real.sqrt_sq he.le]
  have hx : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  have hC0C : C0 ≤ C := le_max_left C0 1
  have hfactor :
      C0 * t ^ (-(1 / 2 : ℝ)) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) := by
    calc
      C0 * t ^ (-(1 / 2 : ℝ)) ≤
          C * t ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC0C hx
      _ ≤ C * (1 + t ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hC.le
  have htail :
      0 ≤ e * Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1) :=
    mul_nonneg he.le (Real.sqrt_nonneg _)
  change
    Real.sqrt (∫ x, (e * g x) ^ 2 ∂ intervalMeasure 1) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) * e *
        Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)
  rw [hscaled]
  calc
    e * Real.sqrt (∫ x, (g x) ^ 2 ∂ intervalMeasure 1) ≤
        e * (C0 * t ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_left hb he.le
    _ = (C0 * t ^ (-(1 / 2 : ℝ))) *
        (e * Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)) := by ring
    _ ≤ (C * (1 + t ^ (-(1 / 2 : ℝ)))) *
        (e * Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_right hfactor htail
    _ = C * (1 + t ^ (-(1 / 2 : ℝ))) * e *
        Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1) := by ring

#print axioms cosineLpFromCoeffs_norm_eq_coeffL2Norm
#print axioms coeffL2Norm_cosine_repr_eq_norm
#print axioms shiftedSpectralFractionalHeatCoeff_l2_summable
#print axioms intervalShiftedFractionalHeatLp_repr
#print axioms intervalShiftedFractionalHeatLp_norm_le
#print axioms intervalShiftedFractionalHeatLp_norm_le_with_decay
#print axioms shiftOneSpectralFractionalHeatCoeff_l2_summable
#print axioms intervalShiftOneFractionalHeatLp_repr
#print axioms intervalShiftOneFractionalHeatLp_norm_eq
#print axioms intervalShiftOneFractionalHeatLp_decay_exists
#print axioms intervalShiftOneFractionalHeatLpOfLp_decay_exists
#print axioms shiftedNeumannHeatDifferenceCoeff_l2_summable
#print axioms intervalShiftedHeatDifferenceLp_repr
#print axioms intervalShiftedHeatDifferenceLp_norm_le
#print axioms intervalShiftedHeatDifferenceLpShiftOne_repr
#print axioms intervalShiftedHeatDifferenceLpShiftOne_norm_exists
#print axioms intervalShiftedHeatDifferenceLpShiftOneOfLp_norm_exists
#print axioms intervalShiftedFullHeatGradient_l2_decay_exists

end ShenWork.Paper2.IntervalSharpSpectralPhysicalL2
