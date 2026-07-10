/-
  Second spatial derivative interfaces for the interval conjugate operator.

  Early elapsed times are kept away from zero and use a half-step semigroup
  factorisation.  Late elapsed times use flux integration by parts followed by
  the cancellative heat-Hessian estimate on the flux derivative.
-/
import ShenWork.Paper2.IntervalConjugateSemigroupComposition
import ShenWork.Paper2.IntervalFullKernelSecondDerivInteriorHolder

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator weightedHeatHessConst)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)

/-- Equality on the closed physical interval implies local equality of the
first derivative functions at every interior point. -/
theorem deriv_eventuallyEq_of_eqOn_Icc
    {f g : ℝ → ℝ} (hfg : Set.EqOn f g (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (fun z => deriv f z) =ᶠ[nhds x] fun z => deriv g z := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
  have hev : f =ᶠ[nhds z] g := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
    exact hfg (Set.Ioo_subset_Icc_self hw)
  exact hev.deriv_eq

/-- After flux IBP, the first derivative of the conjugate operator is itself
differentiable, with second derivative equal to the heat Hessian applied to
the weak flux derivative. -/
theorem intervalConjugateKernelOperator_hasDerivAt_deriv_of_deriv
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ}
    (hQcont : ContinuousOn Q (Set.uIcc (0 : ℝ) 1))
    (hQderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt Q (deriv Q z) z)
    (hQderiv_int : IntervalIntegrable (deriv Q) volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    (hQderiv_meas : AEStronglyMeasurable (deriv Q) (intervalMeasure 1))
    {CQd : ℝ} (hQderiv_bound : ∀ z, |deriv Q z| ≤ CQd)
    (x : ℝ) :
    HasDerivAt
      (fun z => deriv (fun w => intervalConjugateKernelOperator r Q w) z)
      (deriv (fun z => deriv
        (fun w => intervalFullSemigroupOperator r (deriv Q) w) z) x) x := by
  have heq : (fun w => intervalConjugateKernelOperator r Q w) =
      fun w => intervalFullSemigroupOperator r (deriv Q) w := by
    funext w
    exact ShenWork.Paper2.IntervalConjugateKernelIBP.intervalConjugateKernelOperator_eq_semigroup_deriv
      hr hQcont hQderiv hQderiv_int hQ0 hQ1
  rw [heq]
  exact (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
    hr hQderiv_meas hQderiv_bound x).differentiableAt.hasDerivAt

/-- Cancellative late-time bound for the actual second derivative of a
conjugate-operator slice.  Only interior Holder control of `deriv Q` is needed. -/
theorem intervalConjugateKernelOperator_secondDeriv_abs_le_of_deriv_holder
    {r theta : ℝ} (hr : 0 < r)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) {Q : ℝ → ℝ}
    (hQcont : ContinuousOn Q (Set.uIcc (0 : ℝ) 1))
    (hQderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt Q (deriv Q z) z)
    (hQderiv_int : IntervalIntegrable (deriv Q) volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    (hQderiv_meas : AEStronglyMeasurable (deriv Q) (intervalMeasure 1))
    {CQd HQd : ℝ} (hQderiv_bound : ∀ z, |deriv Q z| ≤ CQd)
    (hHQd : 0 ≤ HQd)
    (hQderiv_holder : ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |deriv Q a - deriv Q b| ≤ HQd * |a - b| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z => deriv
      (fun w => intervalConjugateKernelOperator r Q w) z) x| ≤
      weightedHeatHessConst theta * r ^ (-1 + theta / 2 : ℝ) * HQd := by
  have heq : (fun w => intervalConjugateKernelOperator r Q w) =
      fun w => intervalFullSemigroupOperator r (deriv Q) w := by
    funext w
    exact ShenWork.Paper2.IntervalConjugateKernelIBP.intervalConjugateKernelOperator_eq_semigroup_deriv
      hr hQcont hQderiv hQderiv_int hQ0 hQ1
  rw [heq]
  exact ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_interiorCtheta_to_Linfty
    hr htheta0 htheta1 hQderiv_meas hQderiv_bound hHQd
      hQderiv_holder hx

/-- The early-time semigroup split makes the first derivative of a conjugate
slice differentiable without requiring any derivative of the source. -/
theorem intervalConjugateKernelOperator_hasDerivAt_deriv_of_split
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ
      (fun z => deriv (fun w => intervalConjugateKernelOperator r Q w) z) x := by
  have hr2 : 0 < r / 2 := by positivity
  let B : ℝ → ℝ := fun z => intervalConjugateKernelOperator (r / 2) Q z
  let F : ℝ → ℝ := fun z => intervalFullSemigroupOperator (r / 2) B z
  let J : ℝ → ℝ := fun z => intervalConjugateKernelOperator r Q z
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
  have hEqOn : Set.EqOn F J (Set.Icc (0 : ℝ) 1) := by
    intro z hz
    dsimp [F, J, B]
    simpa [show r / 2 + r / 2 = r by ring] using
      intervalFullSemigroupOperator_comp_conjugateKernel
        hr2 hr2 hQcont hQint hQbound hz
  have hdev : (fun z => deriv F z) =ᶠ[nhds x] fun z => deriv J z :=
    deriv_eventuallyEq_of_eqOn_Icc hEqOn hx
  have hF2 :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
      hr2 hBmeas hBbound x
  exact (hdev.hasDerivAt_iff.mp hF2).differentiableAt

/-- Explicit early-time Hessian bound obtained from the half-step split. -/
theorem intervalConjugateKernelOperator_secondDeriv_abs_le_of_split
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z => deriv
      (fun w => intervalConjugateKernelOperator r Q w) z) x| ≤
      (5 * Real.sqrt 2 / 2) * (r / 2) ^ (-(1 : ℝ)) *
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (r / 2) ^ (-(1 / 2) : ℝ) * CQ) := by
  have hr2 : 0 < r / 2 := by positivity
  let B : ℝ → ℝ := fun z => intervalConjugateKernelOperator (r / 2) Q z
  let F : ℝ → ℝ := fun z => intervalFullSemigroupOperator (r / 2) B z
  let J : ℝ → ℝ := fun z => intervalConjugateKernelOperator r Q z
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
  have hEqOn : Set.EqOn F J (Set.Icc (0 : ℝ) 1) := by
    intro z hz
    dsimp [F, J, B]
    simpa [show r / 2 + r / 2 = r by ring] using
      intervalFullSemigroupOperator_comp_conjugateKernel
        hr2 hr2 hQcont hQint hQbound hz
  have hdev : (fun z => deriv F z) =ᶠ[nhds x] fun z => deriv J z :=
    deriv_eventuallyEq_of_eqOn_Icc hEqOn hx
  have hsecond_eq : deriv (fun z => deriv J z) x =
      deriv (fun z => deriv F z) x := hdev.deriv_eq.symm
  rw [hsecond_eq]
  exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
    hr2 hBmeas hBbound x

end ShenWork.Paper2
