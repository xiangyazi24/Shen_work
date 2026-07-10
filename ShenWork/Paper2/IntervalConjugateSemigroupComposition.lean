/-
  Semigroup composition for the interval conjugate-kernel operator.

  The identity

    S(a) (B(b) Q) = B(a + b) Q

  is proved from the already established cosine series.  This is the
  positive-lag factorisation needed to smooth the early-time part of the
  faithful conjugate Duhamel term without assuming regularity of `Q` near
  time zero.
-/
import ShenWork.Paper2.IntervalConjugateSourceBridge
import ShenWork.Paper2.IntervalConjugateKernelHolder
import ShenWork.Paper2.IntervalConjugateKernelIBP

open MeasureTheory Filter

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries
  (intervalConjugateKernelOperator_cosineSeries intervalSineInner)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardIterateRestart
  (cosineCoeffs_of_l1_cosineSeries)

/-- Cosine coefficients of a positive-time conjugate-kernel output, in the
normalisation used by its explicit cosine series. -/
theorem intervalConjugateKernelOperator_cosineCoeff_native
    {t : ℝ} (ht : 0 < t) {Q : ℝ → ℝ} (hQ : Continuous Q) (n : ℕ) :
    cosineCoeffs (fun x => intervalConjugateKernelOperator t Q x) n =
      Real.exp (-t * unitIntervalCosineEigenvalue n) *
        (((n : ℝ) * Real.pi) * intervalSineInner Q n) := by
  have hseries :
      (fun x => intervalConjugateKernelOperator t Q x) =
        fun x => ∑' k : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue k) *
            (((k : ℝ) * Real.pi) * intervalSineInner Q k)) * cosineMode k x :=
    funext fun x => intervalConjugateKernelOperator_cosineSeries ht hQ x
  rw [hseries]
  exact cosineCoeffs_of_l1_cosineSeries
    (ShenWork.Paper2.IntervalConjugateSourceBridge.conjugateKernel_coeff_summable
      ht hQ) n

/-- The conjugate-kernel output has uniformly bounded cosine coefficients at
every positive time. -/
theorem intervalConjugateKernelOperator_cosineCoeff_bounded
    {t : ℝ} (ht : 0 < t) {Q : ℝ → ℝ} (hQ : Continuous Q) :
    ∃ M : ℝ, ∀ n,
      |cosineCoeffs (fun x => intervalConjugateKernelOperator t Q x) n| ≤ M := by
  let c : ℕ → ℝ := fun n =>
    Real.exp (-t * unitIntervalCosineEigenvalue n) *
      (((n : ℝ) * Real.pi) * intervalSineInner Q n)
  have hsum : Summable (fun n => |c n|) := by
    simpa [c] using
      ShenWork.Paper2.IntervalConjugateSourceBridge.conjugateKernel_coeff_summable
        ht hQ
  refine ⟨∑' n, |c n|, fun n => ?_⟩
  rw [intervalConjugateKernelOperator_cosineCoeff_native ht hQ n]
  exact hsum.le_tsum n (fun j _ => abs_nonneg (c j))

/-- A positive Neumann heat step after a positive conjugate-kernel step is the
single conjugate-kernel step at the sum of the two times. -/
theorem intervalFullSemigroupOperator_comp_conjugateKernel
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator a
        (fun y => intervalConjugateKernelOperator b Q y) x =
      intervalConjugateKernelOperator (a + b) Q x := by
  have hBcont : Continuous
      (fun y => intervalConjugateKernelOperator b Q y) := by
    have hBdiff : Differentiable ℝ
        (fun y => intervalConjugateKernelOperator b Q y) := fun y =>
      (ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
        hb hQint hQbound y).differentiableAt
    exact hBdiff.continuous
  obtain ⟨M, hM⟩ :=
    intervalConjugateKernelOperator_cosineCoeff_bounded hb hQcont
  rw [ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    ha hBcont hM hx]
  rw [ShenWork.IntervalConjugateCosineSeries.intervalConjugateKernelOperator_cosineSeries
    (by linarith : 0 < a + b) hQcont x]
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
  apply tsum_congr
  intro n
  rw [intervalConjugateKernelOperator_cosineCoeff_native hb hQcont n]
  simp only [unitIntervalCosineMode, cosineMode]
  rw [show
      Real.exp (-a * unitIntervalCosineEigenvalue n) *
          Real.cos ((n : ℝ) * Real.pi * x) *
            (Real.exp (-b * unitIntervalCosineEigenvalue n) *
              ((n : ℝ) * Real.pi * intervalSineInner Q n)) =
        (Real.exp (-a * unitIntervalCosineEigenvalue n) *
          Real.exp (-b * unitIntervalCosineEigenvalue n)) *
            ((n : ℝ) * Real.pi * intervalSineInner Q n) *
              Real.cos ((n : ℝ) * Real.pi * x) by ring]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Positive-time factorisation converts the spatial derivative of a
conjugate-kernel output into a standard heat-semigroup gradient. -/
theorem intervalConjugateKernelOperator_deriv_eq_splitSemigroup
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z => intervalConjugateKernelOperator r Q z) x =
      deriv (fun z => intervalFullSemigroupOperator (r / 2)
        (fun y => intervalConjugateKernelOperator (r / 2) Q y) z) x := by
  have hr2 : 0 < r / 2 := by positivity
  have hev :
      (fun z => intervalFullSemigroupOperator (r / 2)
        (fun y => intervalConjugateKernelOperator (r / 2) Q y) z)
        =ᶠ[nhds x]
      (fun z => intervalConjugateKernelOperator r Q z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hcomp := intervalFullSemigroupOperator_comp_conjugateKernel
      hr2 hr2 hQcont hQint hQbound (Set.Ioo_subset_Icc_self hz)
    simpa [show r / 2 + r / 2 = r by ring] using hcomp
  exact hev.deriv_eq.symm

/-- For bounded data, a positive conjugate-kernel slice has a Holder spatial
derivative after splitting its elapsed time into two heat steps. -/
theorem intervalConjugateKernelOperator_deriv_holder_of_split
    {r eta : ℝ} (hr : 0 < r) (heta0 : 0 < eta) (heta1 : eta < 1)
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ)
    {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z => intervalConjugateKernelOperator r Q z) x -
        deriv (fun z => intervalConjugateKernelOperator r Q z) y| ≤
      (2 : ℝ) ^ (1 - eta) *
          (secondDerivSmoothingConst ^ eta *
            gradSmoothingConst ^ (1 - eta)) *
        (r / 2) ^ (-((1 + eta) / 2) : ℝ) *
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (r / 2) ^ (-(1 / 2) : ℝ) * CQ) * |x - y| ^ eta := by
  have hr2 : 0 < r / 2 := by positivity
  let B : ℝ → ℝ := fun z => intervalConjugateKernelOperator (r / 2) Q z
  have hBdiff : Differentiable ℝ B := fun z =>
    (ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
      hr2 hQint hQbound z).differentiableAt
  have hBmeas : AEStronglyMeasurable B (intervalMeasure 1) :=
    hBdiff.continuous.aestronglyMeasurable
  have hBbound : ∀ z,
      |B z| ≤
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (r / 2) ^ (-(1 / 2) : ℝ) * CQ := by
    intro z
    exact ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_abs_le
      hr2 hQint hQbound z
  have hsmooth := neumannHeatGradient_Linf_to_Ctheta
    hr2 heta0 heta1 hBmeas hBbound x y
  rw [intervalConjugateKernelOperator_deriv_eq_splitSemigroup
      hr hQcont hQint hQbound hx,
    intervalConjugateKernelOperator_deriv_eq_splitSemigroup
      hr hQcont hQint hQbound hy]
  simpa [B] using hsmooth

/-- After the flux integration-by-parts identity, a bounded weak derivative is
smoothed by the ordinary Neumann heat gradient. -/
theorem intervalConjugateKernelOperator_deriv_holder_of_deriv
    {r eta : ℝ} (hr : 0 < r) (heta0 : 0 < eta) (heta1 : eta < 1)
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt Q (deriv Q z) z)
    (hQderiv_int : IntervalIntegrable (deriv Q) volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    {CQd : ℝ} (hQderiv_bound : ∀ z, |deriv Q z| ≤ CQd)
    {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z => intervalConjugateKernelOperator r Q z) x -
        deriv (fun z => intervalConjugateKernelOperator r Q z) y| ≤
      (2 : ℝ) ^ (1 - eta) *
          (secondDerivSmoothingConst ^ eta *
            gradSmoothingConst ^ (1 - eta)) *
        r ^ (-((1 + eta) / 2) : ℝ) * CQd * |x - y| ^ eta := by
  have hIBP : ∀ z,
      intervalConjugateKernelOperator r Q z =
        intervalFullSemigroupOperator r (deriv Q) z := fun z =>
    ShenWork.Paper2.IntervalConjugateKernelIBP.intervalConjugateKernelOperator_eq_semigroup_deriv
      hr hQcont.continuousOn hQderiv hQderiv_int hQ0 hQ1
  have heqx :
      (fun z => intervalConjugateKernelOperator r Q z) =ᶠ[nhds x]
        (fun z => intervalFullSemigroupOperator r (deriv Q) z) :=
    Filter.Eventually.of_forall hIBP
  have heqy :
      (fun z => intervalConjugateKernelOperator r Q z) =ᶠ[nhds y]
        (fun z => intervalFullSemigroupOperator r (deriv Q) z) :=
    Filter.Eventually.of_forall hIBP
  have hQderiv_meas := hQderiv_int.aestronglyMeasurable
  rw [ShenWork.HeatKernelGradientEstimates.unitIntervalIocMeasure_eq_intervalMeasure]
    at hQderiv_meas
  have hsmooth := neumannHeatGradient_Linf_to_Ctheta
    hr heta0 heta1 hQderiv_meas hQderiv_bound x y
  rw [heqx.deriv_eq, heqy.deriv_eq]
  simpa using hsmooth

end ShenWork.Paper2
