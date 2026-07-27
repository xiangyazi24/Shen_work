import ShenWork.Paper3.MinimalSteadyWASignalEquation

/-!
# The classical population equation on the minimal steady branch

The inverse-free branch identity is first rescaled by the physical amplitude.
It then becomes the coefficient-space zero-flux equation

`(1 + v) uₓ - χ u³ vₓ = 0`.

Wiener evaluation turns this into a pointwise real identity.  Positivity of
`v` permits division by `1 + v`, and differentiating the resulting functional
identity proves the divergence-form population steady equation.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open Filter Topology
open ShenWork.Wiener

/-! ## Physical derivatives in coefficient space -/

theorem derivative21_signalResolverAmbient
    (h : BranchSpace) :
    derivative21CLM (signalResolverAmbientCLM h) =
      branchDerivResolvedAmbient21CLM h := by
  apply WA.ext
  funext n
  rw [derivative21CLM_coeff,
    branchDerivResolvedAmbient21CLM_coeff]
  rw [show
    (signalResolverAmbientCLM h).toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        h.1.1.toFun n by
      exact branchResolvedAmbient21CLM_coeff h n]
  push_cast
  ring

theorem derivative21_minimalSteadyPopulationCoeff (a : ℝ) :
    derivative21CLM (minimalSteadyPopulationCoeff a) =
      a • branchDerivativeAmbientCLM (minimalSteadyProfile a) := by
  rw [minimalSteadyPopulationCoeff_formula]
  change
    WA.wD
        (1 + a •
          branchSpaceAmbientCLM (minimalSteadyProfile a)) =
      a • branchDerivativeAmbientCLM (minimalSteadyProfile a)
  rw [wD_add, wD_one, zero_add, wD_real_smul]
  rfl

theorem derivative21_minimalSteadySignalCoeff (a : ℝ) :
    derivative21CLM (minimalSteadySignalCoeff a) =
      a • branchDerivResolvedAmbient21CLM
        (minimalSteadyProfile a) := by
  rw [minimalSteadySignalCoeff_formula]
  change
    WA.wD
        (1 + a •
          signalResolverAmbientCLM (minimalSteadyProfile a)) =
      a • branchDerivResolvedAmbient21CLM
        (minimalSteadyProfile a)
  rw [wD_add, wD_one, zero_add, wD_real_smul,
    show WA.wD
        (signalResolverAmbientCLM (minimalSteadyProfile a)) =
          branchDerivResolvedAmbient21CLM
            (minimalSteadyProfile a) by
      exact derivative21_signalResolverAmbient
        (minimalSteadyProfile a)]

/-! ## The amplitude-rescaled polynomial flux -/

def minimalSteadyPhysicalFluxResidual (a : ℝ) : WA 1 :=
  incl21 (blownDenominator (minimalSteadyBranchPoint a)) *
      derivative21CLM (minimalSteadyPopulationCoeff a) -
    minimalSteadySensitivity a •
      (incl21 (minimalSteadyPopulationCoeff a ^ 3) *
        derivative21CLM (minimalSteadySignalCoeff a))

theorem minimalSteadyPhysicalFluxResidual_eq_amplitude (a : ℝ) :
    minimalSteadyPhysicalFluxResidual a =
      a • blownPolynomialFluxResidual
        (minimalSteadyBranchPoint a) := by
  unfold minimalSteadyPhysicalFluxResidual
    blownPolynomialFluxResidual
  rw [derivative21_minimalSteadyPopulationCoeff,
    derivative21_minimalSteadySignalCoeff]
  change
    incl21 (blownDenominator (minimalSteadyBranchPoint a)) *
          (a • branchDerivativeAmbientCLM
            (minimalSteadyProfile a)) -
        minimalSteadySensitivity a •
          (incl21 (minimalSteadyPopulationCoeff a ^ 3) *
            (a • branchDerivResolvedAmbient21CLM
              (minimalSteadyProfile a))) =
      a •
        (incl21 (blownDenominator (minimalSteadyBranchPoint a)) *
            branchDerivativeAmbientCLM
              (minimalSteadyProfile a) -
          minimalSteadySensitivity a •
            (incl21 (minimalSteadyPopulationCoeff a ^ 3) *
              branchDerivResolvedAmbient21CLM
                (minimalSteadyProfile a)))
  rw [mul_smul_comm, mul_smul_comm, smul_sub,
    smul_smul, smul_smul]
  congr 2
  ring

theorem eventually_minimalSteadyPhysicalFluxResidual_zero :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      minimalSteadyPhysicalFluxResidual a = 0 := by
  filter_upwards
    [eventually_blownPolynomialFluxResidual_branch] with a hzero
  rw [minimalSteadyPhysicalFluxResidual_eq_amplitude,
    hzero, smul_zero]

/-! ## Evaluation of the physical flux residual -/

@[simp]
theorem toZero_incl21 (a : WA 2) :
    WA.toZero (incl21 a) = WA.toZero a := by
  apply WA.ext
  rfl

theorem minimalSteadyDenominator_staticEval (a x : ℝ) :
    staticEval
        (blownDenominator (minimalSteadyBranchPoint a)) x =
      1 + minimalSteadySignal a x := by
  have hcoeff :
      blownDenominator (minimalSteadyBranchPoint a) =
        1 + minimalSteadySignalCoeff a := by
    unfold minimalSteadySignalCoeff
    abel
  rw [hcoeff,
    congrFun (staticEval_add 1
      (minimalSteadySignalCoeff a)) x,
    Pi.add_apply, congrFun (staticEval_one 2) x]
  rfl

theorem evalC_minimalSteadyDenominator (a x : ℝ) :
    WA.evalC
        (WA.toZero
          (incl21
            (blownDenominator (minimalSteadyBranchPoint a))))
        (x : WA.Circ) =
      ((1 + minimalSteadySignal a x : ℝ) : ℂ) := by
  rw [toZero_incl21]
  have heval :=
    evalC_evenReal_eq_ofReal_staticEval
      (blownDenominatorEvenReal
        (minimalSteadyBranchPoint a)) x
  change
    WA.evalC
        (WA.toZero
          (blownDenominator (minimalSteadyBranchPoint a)))
        (x : WA.Circ) =
      ((staticEval
        (blownDenominator (minimalSteadyBranchPoint a)) x : ℝ) : ℂ)
      at heval
  rw [heval, minimalSteadyDenominator_staticEval]

theorem evalC_derivative21_minimalSteadyPopulation (a x : ℝ) :
    WA.evalC
        (WA.toZero
          (derivative21CLM (minimalSteadyPopulationCoeff a)))
        (x : WA.Circ) =
      ((deriv (minimalSteadyPopulation a) x : ℝ) : ℂ) := by
  change
    WA.evalC
        (WA.toZero
          (WA.wD (minimalSteadyPopulationCoeff a)))
        (x : WA.Circ) =
      ((deriv
        (staticEval (minimalSteadyPopulationCoeff a)) x : ℝ) : ℂ)
  exact
    evalC_wD_evenReal_eq_ofReal_deriv
      (minimalSteadyPopulationEvenReal a) x

theorem evalC_derivative21_minimalSteadySignal (a x : ℝ) :
    WA.evalC
        (WA.toZero
          (derivative21CLM (minimalSteadySignalCoeff a)))
        (x : WA.Circ) =
      ((deriv (minimalSteadySignal a) x : ℝ) : ℂ) := by
  change
    WA.evalC
        (WA.toZero
          (WA.wD (minimalSteadySignalCoeff a)))
        (x : WA.Circ) =
      ((deriv
        (staticEval (minimalSteadySignalCoeff a)) x : ℝ) : ℂ)
  exact
    evalC_wD_evenReal_eq_ofReal_deriv
      (minimalSteadySignalEvenReal a) x

theorem evalC_minimalSteadyPopulation_cube (a x : ℝ) :
    WA.evalC
        (WA.toZero
          (incl21 (minimalSteadyPopulationCoeff a ^ 3)))
        (x : WA.Circ) =
      ((minimalSteadyPopulation a x ^ 3 : ℝ) : ℂ) := by
  rw [toZero_incl21, evalC_toZero_pow]
  have heval :=
    evalC_evenReal_eq_ofReal_staticEval
      (minimalSteadyPopulationEvenReal a) x
  change
    WA.evalC
        (WA.toZero (minimalSteadyPopulationCoeff a))
        (x : WA.Circ) =
      ((minimalSteadyPopulation a x : ℝ) : ℂ) at heval
  rw [heval]
  norm_cast

theorem evalC_minimalSteadyPhysicalFluxResidual (a x : ℝ) :
    WA.evalC
        (WA.toZero (minimalSteadyPhysicalFluxResidual a))
        (x : WA.Circ) =
      (((1 + minimalSteadySignal a x) *
          deriv (minimalSteadyPopulation a) x -
        minimalSteadySensitivity a *
          minimalSteadyPopulation a x ^ 3 *
            deriv (minimalSteadySignal a) x : ℝ) : ℂ) := by
  unfold minimalSteadyPhysicalFluxResidual
  rw [evalC_toZero_sub, evalC_toZero_mul,
    evalC_minimalSteadyDenominator,
    evalC_derivative21_minimalSteadyPopulation,
    evalC_toZero_real_smul, evalC_toZero_mul,
    evalC_minimalSteadyPopulation_cube,
    evalC_derivative21_minimalSteadySignal]
  push_cast
  ring

theorem minimalSteady_polynomial_zeroFlux
    {a : ℝ} (hzero : minimalSteadyPhysicalFluxResidual a = 0)
    (x : ℝ) :
    (1 + minimalSteadySignal a x) *
          deriv (minimalSteadyPopulation a) x -
        minimalSteadySensitivity a *
          minimalSteadyPopulation a x ^ 3 *
            deriv (minimalSteadySignal a) x = 0 := by
  have hc :
      (((1 + minimalSteadySignal a x) *
            deriv (minimalSteadyPopulation a) x -
          minimalSteadySensitivity a *
            minimalSteadyPopulation a x ^ 3 *
              deriv (minimalSteadySignal a) x : ℝ) : ℂ) = 0 := by
    calc
      (((1 + minimalSteadySignal a x) *
              deriv (minimalSteadyPopulation a) x -
            minimalSteadySensitivity a *
              minimalSteadyPopulation a x ^ 3 *
                deriv (minimalSteadySignal a) x : ℝ) : ℂ) =
          WA.evalC
            (WA.toZero (minimalSteadyPhysicalFluxResidual a))
            (x : WA.Circ) :=
        (evalC_minimalSteadyPhysicalFluxResidual a x).symm
      _ = WA.evalC (WA.toZero (0 : WA 1)) (x : WA.Circ) := by
        rw [hzero]
      _ = 0 := by rw [toZero_zero, map_zero]; rfl
  exact_mod_cast hc

theorem minimalSteady_zeroFlux
    {a : ℝ} (hzero : minimalSteadyPhysicalFluxResidual a = 0)
    (hv : ∀ x : ℝ, 0 < minimalSteadySignal a x)
    (x : ℝ) :
    deriv (minimalSteadyPopulation a) x =
      (minimalSteadySensitivity a *
          minimalSteadyPopulation a x ^ 3 *
            deriv (minimalSteadySignal a) x) /
        (1 + minimalSteadySignal a x) := by
  have hden : 1 + minimalSteadySignal a x ≠ 0 := by
    nlinarith [hv x]
  apply (eq_div_iff hden).2
  have hpoly := minimalSteady_polynomial_zeroFlux hzero x
  nlinarith

theorem minimalSteadyPopulation_equation
    {a : ℝ} (hzero : minimalSteadyPhysicalFluxResidual a = 0)
    (hv : ∀ x : ℝ, 0 < minimalSteadySignal a x)
    (x : ℝ) :
    deriv (deriv (minimalSteadyPopulation a)) x -
      minimalSteadySensitivity a *
        deriv
          (fun y =>
            minimalSteadyPopulation a y ^ 3 *
                deriv (minimalSteadySignal a) y /
              (1 + minimalSteadySignal a y)) x = 0 := by
  have hfun :
      deriv (minimalSteadyPopulation a) =
        fun y =>
          minimalSteadySensitivity a *
            (minimalSteadyPopulation a y ^ 3 *
                deriv (minimalSteadySignal a) y /
              (1 + minimalSteadySignal a y)) := by
    funext y
    rw [minimalSteady_zeroFlux hzero hv y]
    ring
  have hderiv :=
    congrArg (fun f : ℝ → ℝ => deriv f x) hfun
  change
    deriv (deriv (minimalSteadyPopulation a)) x =
      deriv
        (fun y =>
          minimalSteadySensitivity a *
            (minimalSteadyPopulation a y ^ 3 *
                deriv (minimalSteadySignal a) y /
              (1 + minimalSteadySignal a y))) x at hderiv
  rw [deriv_const_mul_field] at hderiv
  linarith

end ShenWork.M3Counterexample
