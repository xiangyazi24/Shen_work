/-
  Second spatial derivative interfaces for the interval conjugate operator.

  Early elapsed times are kept away from zero and use a half-step semigroup
  factorisation.  Late elapsed times use flux integration by parts followed by
  the cancellative heat-Hessian estimate on the flux derivative.
-/
import ShenWork.Paper2.IntervalConjugateSemigroupComposition
import ShenWork.Paper2.IntervalFullKernelSecondDerivInteriorHolder
import ShenWork.Paper2.IntervalFullSemigroupSecondDerivContinuous

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

/-- The half-step semigroup factorisation, originally stated only on the
physical interval, holds on a full neighbourhood of every point of that
interval.  At the endpoints this is obtained by reflecting both sides through
the Neumann symmetries about `0` and `1`. -/
theorem intervalFullSemigroup_comp_conjugate_eventuallyEq_Icc
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (fun z ↦ intervalFullSemigroupOperator (r / 2)
        (fun w ↦ intervalConjugateKernelOperator (r / 2) Q w) z) =ᶠ[nhds x]
      (fun z ↦ intervalConjugateKernelOperator r Q z) := by
  have hr2 : 0 < r / 2 := by positivity
  let B : ℝ → ℝ := fun z ↦ intervalConjugateKernelOperator (r / 2) Q z
  let F : ℝ → ℝ := fun z ↦ intervalFullSemigroupOperator (r / 2) B z
  let J : ℝ → ℝ := fun z ↦ intervalConjugateKernelOperator r Q z
  have hEqOn : Set.EqOn F J (Set.Icc (0 : ℝ) 1) := by
    intro z hz
    dsimp [F, J, B]
    simpa [show r / 2 + r / 2 = r by ring] using
      intervalFullSemigroupOperator_comp_conjugateKernel
        hr2 hr2 hQcont hQint hQbound hz
  have hEqOpen : Set.EqOn F J (Set.Ioo (-1 : ℝ) 2) := by
    intro z hz
    by_cases hz0 : z < 0
    · have hnz : -z ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hz.1, hz.2]
      calc
        F z = F (-z) := by
          dsimp [F]
          exact
            (ShenWork.intervalFullSemigroupOperator_even_zero
              (r / 2) B z).symm
        _ = J (-z) := hEqOn hnz
        _ = J z := by
          dsimp [J]
          exact
            ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_even_zero
              r Q z
    · by_cases hz1 : z ≤ 1
      · exact hEqOn ⟨le_of_not_gt hz0, hz1⟩
      · have htwoz : 2 - z ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [hz.1, hz.2]
        calc
          F z = F (2 - z) := by
            dsimp [F]
            exact
              (ShenWork.intervalFullSemigroupOperator_even_one
                (r / 2) B z).symm
          _ = J (2 - z) := hEqOn htwoz
          _ = J z := by
            dsimp [J]
            exact
              ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_even_one
                r Q z
  have hxOpen : x ∈ Set.Ioo (-1 : ℝ) 2 := by
    constructor <;> linarith [hx.1, hx.2]
  filter_upwards [isOpen_Ioo.mem_nhds hxOpen] with z hz
  simpa [F, J, B] using hEqOpen hz

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

/-- The late-time cancellative Hessian bound extends to the two endpoints by
continuity of the IBP semigroup representative and density of `(0,1)` in
`[0,1]`. -/
theorem intervalConjugateKernelOperator_secondDeriv_abs_le_of_deriv_holder_Icc
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
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun z => deriv
      (fun w => intervalConjugateKernelOperator r Q w) z) x| ≤
      weightedHeatHessConst theta * r ^ (-1 + theta / 2 : ℝ) * HQd := by
  have heq : (fun w => intervalConjugateKernelOperator r Q w) =
      fun w => intervalFullSemigroupOperator r (deriv Q) w := by
    funext w
    exact ShenWork.Paper2.IntervalConjugateKernelIBP.intervalConjugateKernelOperator_eq_semigroup_deriv
      hr hQcont hQderiv hQderiv_int hQ0 hQ1
  have hQint : Integrable (deriv Q) (intervalMeasure 1) := by
    simpa [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (by norm_num : (0 : ℝ) ≤ 1)).mp hQderiv_int
  have hcont : ContinuousOn
      (fun y => |deriv (fun z => deriv
        (fun w => intervalConjugateKernelOperator r Q w) z) y|)
      (Set.Icc (0 : ℝ) 1) := by
    rw [heq]
    exact
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
        hr hQint hQderiv_bound).abs
  have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hxcl : x ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [hcl]
    exact hx
  refine le_on_closure (s := Set.Ioo (0 : ℝ) 1)
    (f := fun y => |deriv (fun z => deriv
      (fun w => intervalConjugateKernelOperator r Q w) z) y|)
    (g := fun _ => weightedHeatHessConst theta *
      r ^ (-1 + theta / 2 : ℝ) * HQd) ?_ ?_ continuousOn_const hxcl
  · intro y hy
    exact intervalConjugateKernelOperator_secondDeriv_abs_le_of_deriv_holder
      hr htheta0 htheta1 hQcont hQderiv hQderiv_int hQ0 hQ1
        hQderiv_meas hQderiv_bound hHQd hQderiv_holder hy
  · simpa [hcl] using hcont

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

/-- The early-time half-step factorisation also supplies second
differentiability at the two endpoints, after reflecting its `Icc` equality to
a genuine neighbourhood equality. -/
theorem intervalConjugateKernelOperator_hasDerivAt_deriv_of_split_Icc
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
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
  have hev : F =ᶠ[nhds x] J := by
    simpa [F, J, B] using
      intervalFullSemigroup_comp_conjugate_eventuallyEq_Icc
        hr hQcont hQint hQbound hx
  have hF2 :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
      hr2 hBmeas hBbound x
  exact (hev.deriv.hasDerivAt_iff.mp hF2).differentiableAt

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

/-- The explicit early-time Hessian bound is valid on the closed physical
interval by the reflected half-step neighbourhood equality. -/
theorem intervalConjugateKernelOperator_secondDeriv_abs_le_of_split_Icc
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
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
  have hev : F =ᶠ[nhds x] J := by
    simpa [F, J, B] using
      intervalFullSemigroup_comp_conjugate_eventuallyEq_Icc
        hr hQcont hQint hQbound hx
  have hsecond_eq : deriv (fun z => deriv J z) x =
      deriv (fun z => deriv F z) x := hev.deriv.deriv_eq.symm
  rw [hsecond_eq]
  exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
    hr2 hBmeas hBbound x

end ShenWork.Paper2
