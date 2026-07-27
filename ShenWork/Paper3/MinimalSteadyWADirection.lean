import ShenWork.Paper3.MinimalSteadyWAImplicitBranch
import ShenWork.Wiener.WeightedL1EvalDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Direction of the local `m = 3` steady branch

The inverse in the blown-up residual is convenient for the implicit function
theorem but inconvenient for the finite harmonic calculation.  This file
first differentiates the inverse-derivative identity and multiplies by the
signal denominator.  Near the bifurcation point this gives the polynomial
flux equation

`(2 + a R h) D h = χ (1 + a h)³ D R h`.

The first two derivatives of its modes `2` and `1`, respectively, determine
the second-harmonic slope and the second derivative of the sensitivity.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener
open scoped Topology

/-! ## Dropping one Wiener weight and differentiating -/

/-- The coefficient-preserving inclusion `WA 2 → WA 1`. -/
def incl21Lin : WA 2 →ₗ[ℂ] WA 1 where
  toFun a := ⟨a.toFun, memW_mono (Nat.le_succ 1) a.mem⟩
  map_add' _ _ := by
    apply WA.ext
    rfl
  map_smul' _ _ := by
    apply WA.ext
    rfl

/-- The inclusion `WA 2 →A[ℂ] WA 1`. -/
def incl21 : WA 2 →A[ℂ] WA 1 where
  toFun := incl21Lin
  map_zero' := incl21Lin.map_zero
  map_add' := incl21Lin.map_add
  map_one' := by
    apply WA.ext
    rfl
  map_mul' _ _ := by
    apply WA.ext
    rfl
  commutes' _ := by
    apply WA.ext
    rfl
  cont := by
    refine AddMonoidHomClass.continuous_of_bound incl21Lin 1 ?_
    intro a
    rw [one_mul, WA.norm_def, WA.norm_def]
    exact wNorm_mono_le (Nat.le_succ 1) a.mem

@[simp]
theorem incl21_toFun (a : WA 2) :
    (incl21 a).toFun = a.toFun :=
  rfl

/-- Fourier differentiation `WA 2 →L[ℂ] WA 1`. -/
def derivative21Lin : WA 2 →ₗ[ℂ] WA 1 where
  toFun a := WA.wD a
  map_add' a b := by
    apply WA.ext
    funext n
    change
      wDeriv (a.toFun + b.toFun) n =
        wDeriv a.toFun n + wDeriv b.toFun n
    simp only [wDeriv, Pi.add_apply]
    ring
  map_smul' c a := by
    apply WA.ext
    funext n
    change
      wDeriv (c • a.toFun) n =
        c • wDeriv a.toFun n
    simp only [wDeriv, Pi.smul_apply, smul_eq_mul]
    ring

def derivative21CLM : WA 2 →L[ℂ] WA 1 :=
  derivative21Lin.mkContinuous Real.pi (fun a => by
    rw [WA.norm_def, WA.norm_def]
    exact wNorm_wDeriv_le a.mem)

@[simp]
theorem derivative21CLM_coeff (a : WA 2) (n : ℤ) :
    (derivative21CLM a).toFun n =
      (Complex.I * Real.pi * (n : ℂ)) * a.toFun n :=
  rfl

/-- Real-linear inclusion used by the branch calculus. -/
def incl21RCLM : WA 2 →L[ℝ] WA 1 :=
  realifyWACLM incl21.toContinuousLinearMap

/-- Derivative of a mean-zero even branch profile, in `WA 1`. -/
def branchDerivativeAmbientCLM : BranchSpace →L[ℝ] WA 1 :=
  (realifyWACLM derivative21CLM).comp branchSpaceAmbientCLM

/-- Inclusion of a branch profile in `WA 1`. -/
def branchProfileAmbient21CLM : BranchSpace →L[ℝ] WA 1 :=
  incl21RCLM.comp branchSpaceAmbientCLM

/-- Inclusion of its resolved signal in `WA 1`. -/
def branchResolvedAmbient21CLM : BranchSpace →L[ℝ] WA 1 :=
  incl21RCLM.comp signalResolverAmbientCLM

/-- Inclusion of `D R h` in `WA 1`. -/
def branchDerivResolvedAmbient21CLM : BranchSpace →L[ℝ] WA 1 :=
  incl21RCLM.comp branchDerivResolverAmbientCLM

@[simp]
theorem branchDerivativeAmbientCLM_coeff
    (h : BranchSpace) (n : ℤ) :
    (branchDerivativeAmbientCLM h).toFun n =
      (Complex.I * Real.pi * (n : ℂ)) * h.1.1.toFun n :=
  rfl

@[simp]
theorem branchProfileAmbient21CLM_coeff
    (h : BranchSpace) (n : ℤ) :
    (branchProfileAmbient21CLM h).toFun n = h.1.1.toFun n :=
  rfl

@[simp]
theorem branchResolvedAmbient21CLM_coeff
    (h : BranchSpace) (n : ℤ) :
    (branchResolvedAmbient21CLM h).toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        h.1.1.toFun n :=
  rfl

@[simp]
theorem branchDerivResolvedAmbient21CLM_coeff
    (h : BranchSpace) (n : ℤ) :
    (branchDerivResolvedAmbient21CLM h).toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          h.1.1.toFun n :=
  rfl

/-! ## Cancellation of derivative and inverse derivative -/

theorem derivative_inverseDeriv_symbol (n : ℤ) :
    (Complex.I * Real.pi * (n : ℂ)) * inverseDerivSymbol n =
      if n = 0 then 0 else 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [inverseDerivSymbol, if_neg hn, if_neg hn]
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hnC : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn
    field_simp [hpi, hnC]

theorem oddImag_coeff_zero (a : OddImagWA r) :
    a.1.toFun 0 = 0 := by
  have h := OddImagWA.coeff_neg a 0
  simp only [neg_zero] at h
  exact CharZero.eq_neg_self_iff.mp h

theorem derivative21_inverseDerivative (a : OddImagWA 2) :
    derivative21CLM
        (inverseDerivativeCLM a).1.1 =
      incl21 a.1 := by
  apply WA.ext
  funext n
  rw [derivative21CLM_coeff,
    inverseDerivativeToMeanZeroCLM_coeff, incl21_toFun,
    ← mul_assoc, derivative_inverseDeriv_symbol]
  split_ifs with hn
  · subst n
    rw [oddImag_coeff_zero]
    simp
  · simp

theorem derivative_projectedInverse_rawFlux
    (p : BranchVariables) :
    branchDerivativeAmbientCLM
        (projectedInverseDerivativeCLM (blownRawFlux p)) =
      incl21 (blownRawFlux p) := by
  change
    derivative21CLM
        (inverseDerivativeCLM (blownFlux p)).1.1 =
      incl21 (blownRawFlux p)
  rw [derivative21_inverseDerivative]
  congr 1
  rw [blownFlux_eq_raw]
  exact blownRawFluxOddImag_coe p

/-! ## Polynomial flux residual -/

/-- The inverse-free polynomial flux equation in `WA 1`. -/
def blownPolynomialFluxResidual (p : BranchVariables) : WA 1 :=
  incl21 (blownDenominator p) *
      branchDerivativeAmbientCLM (blownProfile p) -
    branchSensitivityCLM p •
      (incl21 (blownPopulation p ^ 3) *
        branchDerivResolvedAmbient21CLM (blownProfile p))

theorem denominator_mul_rawFlux
    (p : BranchVariables) (hu : IsUnit (blownDenominator p)) :
    blownDenominator p * blownRawFlux p =
      blownPopulation p ^ 3 *
        branchDerivResolverAmbientCLM (blownProfile p) := by
  unfold blownRawFlux blownMobility
  calc
    blownDenominator p *
          (blownPopulation p ^ 3 *
            Ring.inverse (blownDenominator p) *
              branchDerivResolverAmbientCLM (blownProfile p)) =
        (blownDenominator p *
          Ring.inverse (blownDenominator p)) *
            (blownPopulation p ^ 3 *
              branchDerivResolverAmbientCLM (blownProfile p)) := by
          ring
    _ = _ := by
      rw [Ring.mul_inverse_cancel _ hu, one_mul]

theorem blownResidual_zero_imp_polynomialFlux_zero
    {p : BranchVariables} (hzero : blownResidual p = 0)
    (hu : IsUnit (blownDenominator p)) :
    blownPolynomialFluxResidual p = 0 := by
  have hprofile :
      blownProfile p =
        branchSensitivityCLM p •
          projectedInverseDerivativeCLM (blownRawFlux p) := by
    exact sub_eq_zero.mp hzero
  have hderiv :
      branchDerivativeAmbientCLM (blownProfile p) =
        branchSensitivityCLM p • incl21 (blownRawFlux p) := by
    rw [hprofile, map_smul, derivative_projectedInverse_rawFlux]
  unfold blownPolynomialFluxResidual
  rw [hderiv, mul_smul_comm]
  rw [← map_mul, denominator_mul_rawFlux p hu, map_mul]
  change
    branchSensitivityCLM p •
          (incl21 (blownPopulation p ^ 3) *
            incl21
              (branchDerivResolverAmbientCLM (blownProfile p))) -
        branchSensitivityCLM p •
          (incl21 (blownPopulation p ^ 3) *
            incl21
              (branchDerivResolverAmbientCLM (blownProfile p))) =
      0
  exact sub_self _

/-! ## The IFT branch satisfies the polynomial equation -/

def minimalSteadyBranchPoint (a : ℝ) : BranchVariables :=
  (a, minimalSteadyImplicitBranch a)

@[simp]
theorem minimalSteadyBranchPoint_zero :
    minimalSteadyBranchPoint 0 = blownBase := by
  rw [minimalSteadyBranchPoint,
    minimalSteadyImplicitBranch_base]
  rfl

theorem minimalSteadyBranchPoint_contDiffAt :
    @ContDiffAt
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchVariables branchVariablesNormedAddCommGroup
        branchVariablesNormedSpace
      3 minimalSteadyBranchPoint 0 := by
  have hid : ContDiffAt ℝ 3 (fun a : ℝ => a) 0 :=
    contDiffAt_id
  exact
    @ContDiffAt.prodMk
      ℝ ℝ ℝ BranchImplicit
      inferInstance
      inferInstance inferInstance
      inferInstance inferInstance
      branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      0 3 (fun a : ℝ => a) minimalSteadyImplicitBranch
      hid minimalSteadyImplicitBranch_contDiffAt

theorem eventually_isUnit_minimalSteady_denominator :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      IsUnit (blownDenominator (minimalSteadyBranchPoint a)) := by
  have hcont :
      ContinuousAt
        (fun a : ℝ =>
          blownDenominator (minimalSteadyBranchPoint a)) 0 :=
    blownDenominator_contDiff.continuous.continuousAt.comp'
      minimalSteadyBranchPoint_contDiffAt.continuousAt
  apply hcont.eventually
  simpa only [minimalSteadyBranchPoint_zero,
    blownDenominator_base] using
      (Units.isOpen.mem_nhds isUnit_two_smul_one)

theorem eventually_blownPolynomialFluxResidual_branch :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      blownPolynomialFluxResidual (minimalSteadyBranchPoint a) = 0 := by
  filter_upwards
    [eventually_blownResidual_minimalSteadyImplicitBranch,
      eventually_isUnit_minimalSteady_denominator] with a hzero hu
  exact blownResidual_zero_imp_polynomialFlux_zero hzero hu

/-! ## Branch component curves and their jets -/

def minimalSteadyComplement (a : ℝ) : BranchComplement :=
  branchComplementCLM (minimalSteadyBranchPoint a)

def minimalSteadySensitivity (a : ℝ) : ℝ :=
  branchSensitivityCLM (minimalSteadyBranchPoint a)

def minimalSteadyProfile (a : ℝ) : BranchSpace :=
  blownProfile (minimalSteadyBranchPoint a)

@[simp]
theorem minimalSteadyComplement_zero :
    minimalSteadyComplement 0 = 0 := by
  rw [minimalSteadyComplement, minimalSteadyBranchPoint_zero]
  rfl

@[simp]
theorem minimalSteadySensitivity_zero :
    minimalSteadySensitivity 0 = minimalChiLin := by
  rw [minimalSteadySensitivity, minimalSteadyBranchPoint_zero]
  rfl

@[simp]
theorem minimalSteadyProfile_zero :
    minimalSteadyProfile 0 = firstModeMeanZero 2 := by
  rw [minimalSteadyProfile, minimalSteadyBranchPoint_zero,
    blownProfile_base]

theorem minimalSteadyProfile_formula (a : ℝ) :
    minimalSteadyProfile a =
      firstModeMeanZero 2 + (minimalSteadyComplement a).1 :=
  rfl

theorem minimalSteadySensitivity_contDiffAt :
    ContDiffAt ℝ 3 minimalSteadySensitivity 0 := by
  have hc : ContDiff ℝ 3 branchSensitivityCLM :=
    branchSensitivityCLM.contDiff
  simpa only [minimalSteadySensitivity, Function.comp_apply] using
    hc.contDiffAt.comp 0 minimalSteadyBranchPoint_contDiffAt

theorem minimalSteadyProfile_contDiffAt :
    ContDiffAt ℝ 3 minimalSteadyProfile 0 := by
  simpa only [minimalSteadyProfile, Function.comp_apply] using
    blownProfile_contDiff.contDiffAt.comp
      0 minimalSteadyBranchPoint_contDiffAt

/-- First jet of the full implicit coordinate `(z, χ)`. -/
def minimalImplicitFirstJet : BranchImplicit :=
  deriv minimalSteadyImplicitBranch 0

/-- Second jet of the full implicit coordinate `(z, χ)`. -/
def minimalImplicitSecondJet : BranchImplicit :=
  deriv (deriv minimalSteadyImplicitBranch) 0

/-- First complement jet `z'(0)`. -/
def minimalComplementFirstJet : BranchComplement :=
  minimalImplicitFirstJet.1

/-- Second complement jet `z''(0)`. -/
def minimalComplementSecondJet : BranchComplement :=
  minimalImplicitSecondJet.1

/-- First sensitivity jet `χ'(0)`. -/
def minimalSensitivityFirstJet : ℝ :=
  minimalImplicitFirstJet.2

/-- Second sensitivity jet `χ''(0)`. -/
def minimalSensitivitySecondJet : ℝ :=
  minimalImplicitSecondJet.2

theorem minimalSteadyImplicitBranch_hasDerivAt :
    HasDerivAt minimalSteadyImplicitBranch
      minimalImplicitFirstJet 0 := by
  have hd :=
    @ContDiffAt.differentiableAt
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      minimalSteadyImplicitBranch 0 3
      minimalSteadyImplicitBranch_contDiffAt (by norm_num)
  exact
    @DifferentiableAt.hasDerivAt
      ℝ inferInstance BranchImplicit
      branchImplicitNormedAddCommGroup branchImplicitNormedSpace
      minimalSteadyImplicitBranch 0 hd

theorem deriv_minimalSteadyImplicitBranch_hasDerivAt :
    HasDerivAt (deriv minimalSteadyImplicitBranch)
      minimalImplicitSecondJet 0 := by
  have hc :=
    @ContDiffAt.derivWithin
      ℝ BranchImplicit inferInstance
      branchImplicitNormedAddCommGroup branchImplicitNormedSpace
      1 3 minimalSteadyImplicitBranch 0
      minimalSteadyImplicitBranch_contDiffAt (by norm_num)
  have hd :=
    @ContDiffAt.differentiableAt
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      (deriv minimalSteadyImplicitBranch) 0 1 hc (by norm_num)
  exact
    @DifferentiableAt.hasDerivAt
      ℝ inferInstance BranchImplicit
      branchImplicitNormedAddCommGroup branchImplicitNormedSpace
      (deriv minimalSteadyImplicitBranch) 0 hd

/-! ## Selected derivatives of the normalized profile and sensitivity -/

def implicitSensitivityCLM : BranchImplicit →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ BranchComplement ℝ

def minimalSteadySensitivityDeriv (a : ℝ) : ℝ :=
  implicitSensitivityCLM
    (deriv minimalSteadyImplicitBranch a)

@[simp]
theorem minimalSteadySensitivityDeriv_zero :
    minimalSteadySensitivityDeriv 0 =
      minimalSensitivityFirstJet :=
  rfl

theorem implicitSensitivity_comp_hasDerivAt
    {q : ℝ → BranchImplicit} {q' : BranchImplicit} {a : ℝ}
    (hq : HasDerivAt q q' a) :
    HasDerivAt
      (fun t : ℝ => implicitSensitivityCLM (q t))
      (implicitSensitivityCLM q') a := by
  have hcomp :=
    @HasFDerivAt.comp
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
      branchImplicitNormedSpace
      ℝ inferInstance inferInstance
      q (ContinuousLinearMap.toSpanSingleton ℝ q') a
      (fun x : BranchImplicit => implicitSensitivityCLM x)
      implicitSensitivityCLM
      implicitSensitivityCLM.hasFDerivAt hq.hasFDerivAt
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hcomp.hasDerivAt

set_option synthInstance.maxHeartbeats 1000000 in
theorem minimalSteadySensitivity_hasDerivAt :
    HasDerivAt minimalSteadySensitivity
      minimalSensitivityFirstJet 0 := by
  have hcomp := implicitSensitivity_comp_hasDerivAt
    minimalSteadyImplicitBranch_hasDerivAt
  simpa only [minimalSteadySensitivity, minimalSteadyBranchPoint,
    branchSensitivityCLM_apply] using hcomp

set_option synthInstance.maxHeartbeats 1000000 in
theorem minimalSteadySensitivityDeriv_hasDerivAt :
    HasDerivAt minimalSteadySensitivityDeriv
      minimalSensitivitySecondJet 0 := by
  exact implicitSensitivity_comp_hasDerivAt
    deriv_minimalSteadyImplicitBranch_hasDerivAt

/-! ## The four `WA 1` profile factors -/

def implicitProfileAmbient21CLM :
    BranchImplicit →L[ℝ] WA 1 :=
  branchProfileAmbient21CLM.comp implicitProfileDerivativeCLM

def implicitResolvedAmbient21CLM :
    BranchImplicit →L[ℝ] WA 1 :=
  branchResolvedAmbient21CLM.comp implicitProfileDerivativeCLM

def implicitDerivativeAmbient21CLM :
    BranchImplicit →L[ℝ] WA 1 :=
  branchDerivativeAmbientCLM.comp implicitProfileDerivativeCLM

def implicitDerivResolvedAmbient21CLM :
    BranchImplicit →L[ℝ] WA 1 :=
  branchDerivResolvedAmbient21CLM.comp implicitProfileDerivativeCLM

@[simp]
theorem implicitProfileAmbient21CLM_coeff
    (q : BranchImplicit) (n : ℤ) :
    (implicitProfileAmbient21CLM q).toFun n =
      q.1.1.1.1.toFun n :=
  rfl

@[simp]
theorem implicitResolvedAmbient21CLM_coeff
    (q : BranchImplicit) (n : ℤ) :
    (implicitResolvedAmbient21CLM q).toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        q.1.1.1.1.toFun n :=
  rfl

@[simp]
theorem implicitDerivativeAmbient21CLM_coeff
    (q : BranchImplicit) (n : ℤ) :
    (implicitDerivativeAmbient21CLM q).toFun n =
      (Complex.I * Real.pi * (n : ℂ)) *
        q.1.1.1.1.toFun n :=
  rfl

@[simp]
theorem implicitDerivResolvedAmbient21CLM_coeff
    (q : BranchImplicit) (n : ℤ) :
    (implicitDerivResolvedAmbient21CLM q).toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          q.1.1.1.1.toFun n :=
  rfl

def directionProfile21 (q : BranchImplicit) : WA 1 :=
  branchProfileAmbient21CLM (firstModeMeanZero 2) +
    implicitProfileAmbient21CLM q

def directionResolved21 (q : BranchImplicit) : WA 1 :=
  branchResolvedAmbient21CLM (firstModeMeanZero 2) +
    implicitResolvedAmbient21CLM q

def directionDerivative21 (q : BranchImplicit) : WA 1 :=
  branchDerivativeAmbientCLM (firstModeMeanZero 2) +
    implicitDerivativeAmbient21CLM q

def directionDerivResolved21 (q : BranchImplicit) : WA 1 :=
  branchDerivResolvedAmbient21CLM (firstModeMeanZero 2) +
    implicitDerivResolvedAmbient21CLM q

def directionPopulation21 (a : ℝ) (q : BranchImplicit) : WA 1 :=
  1 + a • directionProfile21 q

def directionDenominator21 (a : ℝ) (q : BranchImplicit) : WA 1 :=
  (2 : ℝ) • (1 : WA 1) + a • directionResolved21 q

def directionPolynomialFlux (a : ℝ) (q : BranchImplicit) : WA 1 :=
  directionDenominator21 a q * directionDerivative21 q -
    q.2 •
      (directionPopulation21 a q ^ 3 *
        directionDerivResolved21 q)

@[simp]
theorem directionProfile21_coeff (q : BranchImplicit) (n : ℤ) :
    (directionProfile21 q).toFun n =
      (firstModeMeanZero 2).1.1.toFun n +
        q.1.1.1.1.toFun n :=
  rfl

@[simp]
theorem directionResolved21_coeff (q : BranchImplicit) (n : ℤ) :
    (directionResolved21 q).toFun n =
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        ((firstModeMeanZero 2).1.1.toFun n +
          q.1.1.1.1.toFun n) := by
  change
    (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        (firstModeMeanZero 2).1.1.toFun n) +
      (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        q.1.1.1.1.toFun n) =
      _
  ring

@[simp]
theorem directionDerivative21_coeff (q : BranchImplicit) (n : ℤ) :
    (directionDerivative21 q).toFun n =
      (Complex.I * Real.pi * (n : ℂ)) *
        ((firstModeMeanZero 2).1.1.toFun n +
          q.1.1.1.1.toFun n) := by
  change
    (Complex.I * Real.pi * (n : ℂ)) *
          (firstModeMeanZero 2).1.1.toFun n +
        (Complex.I * Real.pi * (n : ℂ)) *
          q.1.1.1.1.toFun n =
      _
  ring

@[simp]
theorem directionDerivResolved21_coeff
    (q : BranchImplicit) (n : ℤ) :
    (directionDerivResolved21 q).toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
          ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          ((firstModeMeanZero 2).1.1.toFun n +
            q.1.1.1.1.toFun n) := by
  change
    (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
          ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
            (firstModeMeanZero 2).1.1.toFun n +
        (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
          ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
            q.1.1.1.1.toFun n =
      _
  ring

theorem directionPolynomialFlux_eq_blown
    (a : ℝ) (q : BranchImplicit) :
    directionPolynomialFlux a q =
      blownPolynomialFluxResidual (a, q) := by
  unfold directionPolynomialFlux directionDenominator21
    directionPopulation21 directionProfile21
    directionResolved21 directionDerivative21
    directionDerivResolved21 blownPolynomialFluxResidual
  simp only [blownDenominator, blownPopulation, blownProfile_apply,
    branchAmplitudeCLM_apply, branchSensitivityCLM_apply,
    map_add, map_one, map_pow,
    branchProfileAmbient21CLM, branchResolvedAmbient21CLM,
    branchDerivativeAmbientCLM, branchDerivResolvedAmbient21CLM,
    implicitProfileAmbient21CLM, implicitResolvedAmbient21CLM,
    implicitDerivativeAmbient21CLM,
    implicitDerivResolvedAmbient21CLM,
    ContinuousLinearMap.comp_apply, implicitProfileDerivativeCLM_apply]
  rfl

theorem eventually_directionPolynomialFlux_branch :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      directionPolynomialFlux a
        (minimalSteadyImplicitBranch a) = 0 := by
  filter_upwards
    [eventually_blownPolynomialFluxResidual_branch] with a ha
  rw [directionPolynomialFlux_eq_blown]
  simpa only [minimalSteadyBranchPoint] using ha

/-! ## First derivative of the polynomial equation -/

theorem implicitWA1_comp_hasDerivAt
    (L : BranchImplicit →L[ℝ] WA 1)
    {q : ℝ → BranchImplicit} {q' : BranchImplicit} {a : ℝ}
    (hq : HasDerivAt q q' a) :
    HasDerivAt (fun t : ℝ => L (q t)) (L q') a := by
  have hcomp :=
    @HasFDerivAt.comp
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
      branchImplicitNormedSpace
      (WA 1) inferInstance inferInstance
      q (ContinuousLinearMap.toSpanSingleton ℝ q') a
      (fun x : BranchImplicit => L x) L
      L.hasFDerivAt hq.hasFDerivAt
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hcomp.hasDerivAt

theorem implicitWA1_const_add_comp_hasDerivAt
    (c : WA 1) (L : BranchImplicit →L[ℝ] WA 1)
    {q : ℝ → BranchImplicit} {q' : BranchImplicit} {a : ℝ}
    (hq : HasDerivAt q q' a) :
    HasDerivAt (fun t : ℝ => c + L (q t)) (L q') a :=
  HasDerivAt.const_add c (implicitWA1_comp_hasDerivAt L hq)

def directionPopulationDot
    (a : ℝ) (q qdot : BranchImplicit) : WA 1 :=
  directionProfile21 q + a • implicitProfileAmbient21CLM qdot

def directionDenominatorDot
    (a : ℝ) (q qdot : BranchImplicit) : WA 1 :=
  directionResolved21 q + a • implicitResolvedAmbient21CLM qdot

def directionPopulationCubeDot
    (a : ℝ) (q qdot : BranchImplicit) : WA 1 :=
  (3 : WA 1) * directionPopulation21 a q ^ 2 *
    directionPopulationDot a q qdot

def directionFluxCore
    (a : ℝ) (q : BranchImplicit) : WA 1 :=
  directionPopulation21 a q ^ 3 *
    directionDerivResolved21 q

def directionFluxCoreDot
    (a : ℝ) (q qdot : BranchImplicit) : WA 1 :=
  directionPopulationCubeDot a q qdot *
      directionDerivResolved21 q +
    directionPopulation21 a q ^ 3 *
      implicitDerivResolvedAmbient21CLM qdot

def directionPolynomialFirstJet
    (a : ℝ) (q qdot : BranchImplicit) : WA 1 :=
  directionDenominatorDot a q qdot *
      directionDerivative21 q +
    directionDenominator21 a q *
      implicitDerivativeAmbient21CLM qdot -
    (qdot.2 • directionFluxCore a q +
      q.2 • directionFluxCoreDot a q qdot)

set_option synthInstance.maxHeartbeats 1000000 in
theorem directionPolynomialFlux_hasDerivAt
    {q : ℝ → BranchImplicit} {qdot : BranchImplicit} {a : ℝ}
    (hq : HasDerivAt q qdot a) :
    HasDerivAt
      (fun t : ℝ => directionPolynomialFlux t (q t))
      (directionPolynomialFirstJet a (q a) qdot) a := by
  have ha : HasDerivAt (fun t : ℝ => t) 1 a :=
    hasDerivAt_id a
  have hH :
      HasDerivAt (fun t : ℝ => directionProfile21 (q t))
        (implicitProfileAmbient21CLM qdot) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchProfileAmbient21CLM (firstModeMeanZero 2))
      implicitProfileAmbient21CLM hq
  have hR :
      HasDerivAt (fun t : ℝ => directionResolved21 (q t))
        (implicitResolvedAmbient21CLM qdot) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchResolvedAmbient21CLM (firstModeMeanZero 2))
      implicitResolvedAmbient21CLM hq
  have hD :
      HasDerivAt (fun t : ℝ => directionDerivative21 (q t))
        (implicitDerivativeAmbient21CLM qdot) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchDerivativeAmbientCLM (firstModeMeanZero 2))
      implicitDerivativeAmbient21CLM hq
  have hDR :
      HasDerivAt (fun t : ℝ => directionDerivResolved21 (q t))
        (implicitDerivResolvedAmbient21CLM qdot) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchDerivResolvedAmbient21CLM (firstModeMeanZero 2))
      implicitDerivResolvedAmbient21CLM hq
  have hpopulation :
      HasDerivAt
        (fun t : ℝ => directionPopulation21 t (q t))
        (directionPopulationDot a (q a) qdot) a := by
    have hp := HasDerivAt.const_add (1 : WA 1) (ha.smul hH)
    convert hp using 1
    · simp only [directionPopulationDot, one_smul]
      abel
  have hdenominator :
      HasDerivAt
        (fun t : ℝ => directionDenominator21 t (q t))
        (directionDenominatorDot a (q a) qdot) a := by
    have hd := HasDerivAt.const_add
      ((2 : ℝ) • (1 : WA 1)) (ha.smul hR)
    convert hd using 1
    · simp only [directionDenominatorDot, one_smul]
      abel
  have hpopulationCube :
      HasDerivAt
        (fun t : ℝ => directionPopulation21 t (q t) ^ 3)
        (directionPopulationCubeDot a (q a) qdot) a := by
    simpa only [directionPopulationCubeDot] using
      hpopulation.pow 3
  have hcore :
      HasDerivAt
        (fun t : ℝ => directionFluxCore t (q t))
        (directionFluxCoreDot a (q a) qdot) a := by
    simpa only [directionFluxCore, directionFluxCoreDot] using
      hpopulationCube.mul hDR
  have hchi :
      HasDerivAt (fun t : ℝ => (q t).2) qdot.2 a :=
    implicitSensitivity_comp_hasDerivAt hq
  have hleft :
      HasDerivAt
        (fun t : ℝ =>
          directionDenominator21 t (q t) *
            directionDerivative21 (q t))
        (directionDenominatorDot a (q a) qdot *
            directionDerivative21 (q a) +
          directionDenominator21 a (q a) *
            implicitDerivativeAmbient21CLM qdot) a :=
    hdenominator.mul hD
  have hright :
      HasDerivAt
        (fun t : ℝ => (q t).2 • directionFluxCore t (q t))
        (qdot.2 • directionFluxCore a (q a) +
          (q a).2 • directionFluxCoreDot a (q a) qdot) a := by
    simpa only [Pi.smul_apply, add_comm] using
      hchi.smul hcore
  simpa only [directionPolynomialFlux, directionFluxCore,
    directionPolynomialFirstJet] using hleft.sub hright

def minimalDirectionPolynomial (a : ℝ) : WA 1 :=
  directionPolynomialFlux a (minimalSteadyImplicitBranch a)

def minimalDirectionPolynomialFirstDeriv (a : ℝ) : WA 1 :=
  directionPolynomialFirstJet a
    (minimalSteadyImplicitBranch a)
      (deriv minimalSteadyImplicitBranch a)

set_option synthInstance.maxHeartbeats 1000000 in
theorem minimalDirectionPolynomial_hasDerivAt :
    HasDerivAt minimalDirectionPolynomial
      (directionPolynomialFirstJet 0 implicitBase
        minimalImplicitFirstJet) 0 := by
  simpa only [minimalDirectionPolynomial,
    minimalSteadyImplicitBranch_base] using
      directionPolynomialFlux_hasDerivAt
        minimalSteadyImplicitBranch_hasDerivAt

theorem minimalDirectionPolynomialFirstJet_zero :
    directionPolynomialFirstJet 0 implicitBase
      minimalImplicitFirstJet = 0 := by
  have heq :
      minimalDirectionPolynomial =ᶠ[𝓝 (0 : ℝ)]
        (fun _ : ℝ => (0 : WA 1)) := by
    simpa only [minimalDirectionPolynomial] using
      eventually_directionPolynomialFlux_branch
  calc
    directionPolynomialFirstJet 0 implicitBase
        minimalImplicitFirstJet =
        deriv minimalDirectionPolynomial 0 :=
      minimalDirectionPolynomial_hasDerivAt.deriv.symm
    _ = deriv (fun _ : ℝ => (0 : WA 1)) 0 :=
      heq.deriv_eq
    _ = 0 := by simp

/-! ## Two-mode convolution bookkeeping -/

theorem wConv_twoMode_left
    (f g : ℤ → ℂ)
    (hf : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → f n = 0)
    (n : ℤ) :
    wConv f g n =
      f 1 * g (n - 1) + f (-1) * g (n + 1) := by
  have hpoint :
      (fun m : ℤ => f m * g (n - m)) =
        (fun m : ℤ =>
          (if m = 1 then f 1 * g (n - 1) else 0) +
            (if m = -1 then f (-1) * g (n + 1) else 0)) := by
    funext m
    by_cases hm1 : m = 1
    · subst m
      simp
    · by_cases hmn1 : m = -1
      · subst m
        simp
      · rw [hf m hm1 hmn1]
        simp [hm1, hmn1]
  have hs1 :
      Summable
        (fun m : ℤ =>
          if m = 1 then f 1 * g (n - 1) else 0) := by
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton (1 : ℤ)).subset (by
      intro m hm
      simp only [Set.mem_singleton_iff]
      by_contra hne
      apply hm
      simp [hne])
  have hsn1 :
      Summable
        (fun m : ℤ =>
          if m = -1 then f (-1) * g (n + 1) else 0) := by
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton (-1 : ℤ)).subset (by
      intro m hm
      simp only [Set.mem_singleton_iff]
      by_contra hne
      apply hm
      simp [hne])
  rw [wConv, hpoint, hs1.tsum_add hsn1]
  simp

theorem firstMode_support
    (n : ℤ) (hn1 : n ≠ 1) (hn1' : n ≠ -1) :
    firstModeSeq n = 0 := by
  simp [firstModeSeq, hn1, hn1']

theorem firstMode_mul_coeff
    (a : WA 1) (n : ℤ) :
    ((incl21 (firstModeWA 2)) * a).toFun n =
      (1 / 2 : ℂ) * a.toFun (n - 1) +
        (1 / 2 : ℂ) * a.toFun (n + 1) := by
  change
    wConv firstModeSeq a.toFun n =
      (1 / 2 : ℂ) * a.toFun (n - 1) +
        (1 / 2 : ℂ) * a.toFun (n + 1)
  rw [wConv_twoMode_left firstModeSeq a.toFun firstMode_support]
  simp

@[simp]
theorem directionProfile21_base_coeff (n : ℤ) :
    (directionProfile21 implicitBase).toFun n =
      firstModeSeq n := by
  rw [directionProfile21_coeff]
  simp [implicitBase, firstModeMeanZero, firstModeEvenReal,
    firstModeWA]

@[simp]
theorem directionResolved21_base_coeff (n : ℤ) :
    (directionResolved21 implicitBase).toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        firstModeSeq n := by
  rw [directionResolved21_coeff]
  simp [implicitBase, firstModeMeanZero, firstModeEvenReal,
    firstModeWA]

@[simp]
theorem directionDerivative21_base_coeff (n : ℤ) :
    (directionDerivative21 implicitBase).toFun n =
      (Complex.I * Real.pi * (n : ℂ)) * firstModeSeq n := by
  rw [directionDerivative21_coeff]
  simp [implicitBase, firstModeMeanZero, firstModeEvenReal,
    firstModeWA]

@[simp]
theorem directionDerivResolved21_base_coeff (n : ℤ) :
    (directionDerivResolved21 implicitBase).toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          firstModeSeq n := by
  rw [directionDerivResolved21_coeff]
  simp [implicitBase, firstModeMeanZero, firstModeEvenReal,
    firstModeWA]

theorem directionProfile21_base_support
    (n : ℤ) (hn1 : n ≠ 1) (hn1' : n ≠ -1) :
    (directionProfile21 implicitBase).toFun n = 0 := by
  rw [directionProfile21_base_coeff,
    firstMode_support n hn1 hn1']

theorem directionResolved21_base_support
    (n : ℤ) (hn1 : n ≠ 1) (hn1' : n ≠ -1) :
    (directionResolved21 implicitBase).toFun n = 0 := by
  rw [directionResolved21_base_coeff,
    firstMode_support n hn1 hn1', mul_zero]

theorem directionDerivative21_base_support
    (n : ℤ) (hn1 : n ≠ 1) (hn1' : n ≠ -1) :
    (directionDerivative21 implicitBase).toFun n = 0 := by
  rw [directionDerivative21_base_coeff,
    firstMode_support n hn1 hn1', mul_zero]

theorem directionDerivResolved21_base_support
    (n : ℤ) (hn1 : n ≠ 1) (hn1' : n ≠ -1) :
    (directionDerivResolved21 implicitBase).toFun n = 0 := by
  rw [directionDerivResolved21_base_coeff,
    firstMode_support n hn1 hn1', mul_zero]

theorem mul_coeff_one_of_twoMode
    (a b : WA 1)
    (ha : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → a.toFun n = 0)
    (hb : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → b.toFun n = 0) :
    (a * b).toFun 1 = 0 := by
  change wConv a.toFun b.toFun 1 = 0
  rw [wConv_twoMode_left a.toFun b.toFun ha]
  change
    a.toFun 1 * b.toFun 0 +
      a.toFun (-1) * b.toFun 2 = 0
  rw [hb 0 (by norm_num) (by norm_num),
    hb 2 (by norm_num) (by norm_num)]
  simp

theorem mul_coeff_two_of_twoMode
    (a b : WA 1)
    (ha : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → a.toFun n = 0)
    (hb : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → b.toFun n = 0) :
    (a * b).toFun 2 = a.toFun 1 * b.toFun 1 := by
  change wConv a.toFun b.toFun 2 = _
  rw [wConv_twoMode_left a.toFun b.toFun ha]
  change
    a.toFun 1 * b.toFun 1 +
      a.toFun (-1) * b.toFun 3 =
        a.toFun 1 * b.toFun 1
  rw [hb 3 (by norm_num) (by norm_num)]
  simp

theorem directionPolynomialFirstJet_base_formula
    (qdot : BranchImplicit) :
    directionPolynomialFirstJet 0 implicitBase qdot =
      directionResolved21 implicitBase *
          directionDerivative21 implicitBase +
        (2 : ℝ) • implicitDerivativeAmbient21CLM qdot -
        (qdot.2 • directionDerivResolved21 implicitBase +
          minimalChiLin •
            (((3 : WA 1) * directionProfile21 implicitBase) *
                directionDerivResolved21 implicitBase +
              implicitDerivResolvedAmbient21CLM qdot)) := by
  unfold directionPolynomialFirstJet directionDenominatorDot
    directionFluxCore directionFluxCoreDot
    directionPopulationCubeDot directionPopulationDot
    directionDenominator21 directionPopulation21
  simp only [zero_smul, add_zero, implicitBase,
    one_pow, pow_two, one_mul]
  rw [smul_mul_assoc, one_mul]
  ring_nf

theorem three_mul_eq_add (x : WA 1) :
    (3 : WA 1) * x = x + x + x := by
  ring

theorem real_smul_coeff (c : ℝ) (x : WA 1) (n : ℤ) :
    (c • x).toFun n = (c : ℂ) * x.toFun n := by
  rfl

theorem minimalSensitivityFirstJet_eq_zero :
    minimalSensitivityFirstJet = 0 := by
  let H := directionProfile21 implicitBase
  let R := directionResolved21 implicitBase
  let D := directionDerivative21 implicitBase
  let DR := directionDerivResolved21 implicitBase
  have hRD : (R * D).toFun 1 = 0 := by
    exact mul_coeff_one_of_twoMode R D
      directionResolved21_base_support
      directionDerivative21_base_support
  have hHDR : (H * DR).toFun 1 = 0 := by
    exact mul_coeff_one_of_twoMode H DR
      directionProfile21_base_support
      directionDerivResolved21_base_support
  have h3HDR : (((3 : WA 1) * H) * DR).toFun 1 = 0 := by
    rw [three_mul_eq_add, add_mul, add_mul]
    simp only [WA.add_toFun, Pi.add_apply, hHDR, add_zero]
  have helem :
      R * D +
          (2 : ℝ) •
            implicitDerivativeAmbient21CLM minimalImplicitFirstJet -
          (minimalSensitivityFirstJet • DR +
            minimalChiLin •
              (((3 : WA 1) * H) * DR +
                implicitDerivResolvedAmbient21CLM
                  minimalImplicitFirstJet)) =
        0 := by
    exact
      (directionPolynomialFirstJet_base_formula
        minimalImplicitFirstJet).symm.trans
          minimalDirectionPolynomialFirstJet_zero
  have hc := congrArg (fun x : WA 1 => x.toFun 1) helem
  simp only [WA.add_toFun, WA.sub_toFun, real_smul_coeff,
    Pi.add_apply, Pi.sub_apply,
    WA.zero_toFun, Pi.zero_apply] at hc
  rw [hRD, h3HDR,
    implicitDerivativeAmbient21CLM_coeff,
    implicitDerivResolvedAmbient21CLM_coeff,
    FirstComplementWA.coeff_one] at hc
  simp only [mul_zero, add_zero, zero_sub] at hc
  dsimp [DR] at hc
  change
    -((minimalSensitivityFirstJet : ℂ) *
      (directionDerivResolved21 implicitBase).toFun 1) = 0 at hc
  have hDR :
      (directionDerivResolved21 implicitBase).toFun 1 ≠ 0 := by
    rw [directionDerivResolved21_base_coeff, firstModeSeq_one]
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero
      Complex.I_ne_zero ?_) ?_) ?_
    · simpa using hpi
    · norm_num only [one_mul]
      exact_mod_cast (one_div_ne_zero (ne_of_gt (by positivity :
        (0 : ℝ) < 1 + Real.pi ^ 2)))
    · norm_num
  have hmul :
      (minimalSensitivityFirstJet : ℂ) *
          (directionDerivResolved21 implicitBase).toFun 1 = 0 := by
    exact neg_eq_zero.mp hc
  have hcast : (minimalSensitivityFirstJet : ℂ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hDR
  exact_mod_cast hcast

theorem minimalComplementFirstJet_coeff_two :
    minimalComplementFirstJet.1.1.1.toFun 2 =
      (((4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
        (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1)) : ℝ) : ℂ) := by
  let H := directionProfile21 implicitBase
  let R := directionResolved21 implicitBase
  let D := directionDerivative21 implicitBase
  let DR := directionDerivResolved21 implicitBase
  have hRD :
      (R * D).toFun 2 = R.toFun 1 * D.toFun 1 := by
    exact mul_coeff_two_of_twoMode R D
      directionResolved21_base_support
      directionDerivative21_base_support
  have hHDR :
      (H * DR).toFun 2 = H.toFun 1 * DR.toFun 1 := by
    exact mul_coeff_two_of_twoMode H DR
      directionProfile21_base_support
      directionDerivResolved21_base_support
  have h3HDR :
      (((3 : WA 1) * H) * DR).toFun 2 =
        (3 : ℂ) * (H.toFun 1 * DR.toFun 1) := by
    rw [three_mul_eq_add, add_mul, add_mul]
    simp only [WA.add_toFun, Pi.add_apply, hHDR]
    ring
  have helem :
      R * D +
          (2 : ℝ) •
            implicitDerivativeAmbient21CLM minimalImplicitFirstJet -
          (minimalSensitivityFirstJet • DR +
            minimalChiLin •
              (((3 : WA 1) * H) * DR +
                implicitDerivResolvedAmbient21CLM
                  minimalImplicitFirstJet)) =
        0 := by
    exact
      (directionPolynomialFirstJet_base_formula
        minimalImplicitFirstJet).symm.trans
          minimalDirectionPolynomialFirstJet_zero
  have hc := congrArg (fun x : WA 1 => x.toFun 2) helem
  simp only [WA.add_toFun, WA.sub_toFun, real_smul_coeff,
    Pi.add_apply, Pi.sub_apply, WA.zero_toFun, Pi.zero_apply] at hc
  rw [hRD, h3HDR, minimalSensitivityFirstJet_eq_zero,
    implicitDerivativeAmbient21CLM_coeff,
    implicitDerivResolvedAmbient21CLM_coeff] at hc
  simp only [Complex.ofReal_zero, zero_mul] at hc
  rw [directionResolved21_base_coeff,
    directionDerivative21_base_coeff,
    directionDerivResolved21_base_coeff,
    firstModeSeq_one] at hc
  have hcim := congrArg Complex.im hc
  have hH :
      H.toFun 1 = (1 / 2 : ℂ) := by
    dsimp [H]
    change firstModeSeq 1 + 0 = (1 / 2 : ℂ)
    rw [firstModeSeq_one, add_zero]
  rw [hH] at hcim
  have hzim :
      (minimalImplicitFirstJet.1.1.1.1.toFun 2).im = 0 :=
    MeanZeroEvenRealWA.coeff_im_eq_zero
      minimalComplementFirstJet.1 2
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.zero_im, hzim] at hcim
  norm_num at hcim
  have hcast :
      (1 : ℂ) + (Real.pi : ℂ) ^ 2 =
        ((1 + Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast] at hcim
  simp only [Complex.normSq_ofReal] at hcim
  have hrepow :
      ((Real.pi : ℂ) ^ 2).re = Real.pi ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [hrepow] at hcim
  apply Complex.ext
  · change
      (minimalImplicitFirstJet.1.1.1.1.toFun 2).re =
        (4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
          (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1))
    unfold minimalChiLin at hcim
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    have h1 : 1 + Real.pi ^ 2 ≠ 0 := by positivity
    have h4 : 1 + (2 * Real.pi) ^ 2 ≠ 0 := by positivity
    field_simp [hp, h1, h4] at hcim ⊢
    nlinarith [Real.pi_pos]
  · exact hzim

/-! ## Second derivative of the polynomial equation -/

def directionPopulationDDot
    (a : ℝ) (_q qdot qddot : BranchImplicit) : WA 1 :=
  (2 : ℝ) • implicitProfileAmbient21CLM qdot +
    a • implicitProfileAmbient21CLM qddot

def directionDenominatorDDot
    (a : ℝ) (_q qdot qddot : BranchImplicit) : WA 1 :=
  (2 : ℝ) • implicitResolvedAmbient21CLM qdot +
    a • implicitResolvedAmbient21CLM qddot

def directionPopulationCubeDDot
    (a : ℝ) (q qdot qddot : BranchImplicit) : WA 1 :=
  (6 : WA 1) * directionPopulation21 a q *
      directionPopulationDot a q qdot ^ 2 +
    (3 : WA 1) * directionPopulation21 a q ^ 2 *
      directionPopulationDDot a q qdot qddot

def directionFluxCoreDDot
    (a : ℝ) (q qdot qddot : BranchImplicit) : WA 1 :=
  directionPopulationCubeDDot a q qdot qddot *
      directionDerivResolved21 q +
    (2 : WA 1) * directionPopulationCubeDot a q qdot *
      implicitDerivResolvedAmbient21CLM qdot +
    directionPopulation21 a q ^ 3 *
      implicitDerivResolvedAmbient21CLM qddot

def directionPolynomialSecondJet
    (a : ℝ) (q qdot qddot : BranchImplicit) : WA 1 :=
  directionDenominatorDDot a q qdot qddot *
      directionDerivative21 q +
    (2 : WA 1) * directionDenominatorDot a q qdot *
      implicitDerivativeAmbient21CLM qdot +
    directionDenominator21 a q *
      implicitDerivativeAmbient21CLM qddot -
    (qddot.2 • directionFluxCore a q +
      (2 : ℝ) • qdot.2 • directionFluxCoreDot a q qdot +
      q.2 • directionFluxCoreDDot a q qdot qddot)

set_option synthInstance.maxHeartbeats 1000000 in
theorem directionPolynomialFirstJet_hasDerivAt
    {q qdot : ℝ → BranchImplicit} {qddot : BranchImplicit} {a : ℝ}
    (hq : HasDerivAt q (qdot a) a)
    (hqdot : HasDerivAt qdot qddot a) :
    HasDerivAt
      (fun t : ℝ =>
        directionPolynomialFirstJet t (q t) (qdot t))
      (directionPolynomialSecondJet a (q a) (qdot a) qddot) a := by
  have ha : HasDerivAt (fun t : ℝ => t) 1 a :=
    hasDerivAt_id a
  have hH :
      HasDerivAt (fun t : ℝ => directionProfile21 (q t))
        (implicitProfileAmbient21CLM (qdot a)) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchProfileAmbient21CLM (firstModeMeanZero 2))
      implicitProfileAmbient21CLM hq
  have hHdot :
      HasDerivAt
        (fun t : ℝ => implicitProfileAmbient21CLM (qdot t))
        (implicitProfileAmbient21CLM qddot) a :=
    implicitWA1_comp_hasDerivAt implicitProfileAmbient21CLM hqdot
  have hR :
      HasDerivAt (fun t : ℝ => directionResolved21 (q t))
        (implicitResolvedAmbient21CLM (qdot a)) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchResolvedAmbient21CLM (firstModeMeanZero 2))
      implicitResolvedAmbient21CLM hq
  have hRdot :
      HasDerivAt
        (fun t : ℝ => implicitResolvedAmbient21CLM (qdot t))
        (implicitResolvedAmbient21CLM qddot) a :=
    implicitWA1_comp_hasDerivAt implicitResolvedAmbient21CLM hqdot
  have hD :
      HasDerivAt (fun t : ℝ => directionDerivative21 (q t))
        (implicitDerivativeAmbient21CLM (qdot a)) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchDerivativeAmbientCLM (firstModeMeanZero 2))
      implicitDerivativeAmbient21CLM hq
  have hDdot :
      HasDerivAt
        (fun t : ℝ => implicitDerivativeAmbient21CLM (qdot t))
        (implicitDerivativeAmbient21CLM qddot) a :=
    implicitWA1_comp_hasDerivAt implicitDerivativeAmbient21CLM hqdot
  have hDR :
      HasDerivAt (fun t : ℝ => directionDerivResolved21 (q t))
        (implicitDerivResolvedAmbient21CLM (qdot a)) a :=
    implicitWA1_const_add_comp_hasDerivAt
      (branchDerivResolvedAmbient21CLM (firstModeMeanZero 2))
      implicitDerivResolvedAmbient21CLM hq
  have hDRdot :
      HasDerivAt
        (fun t : ℝ => implicitDerivResolvedAmbient21CLM (qdot t))
        (implicitDerivResolvedAmbient21CLM qddot) a :=
    implicitWA1_comp_hasDerivAt
      implicitDerivResolvedAmbient21CLM hqdot
  have hpopulation :
      HasDerivAt
        (fun t : ℝ => directionPopulation21 t (q t))
        (directionPopulationDot a (q a) (qdot a)) a := by
    have hp := HasDerivAt.const_add (1 : WA 1) (ha.smul hH)
    convert hp using 1
    simp only [directionPopulationDot, one_smul]
    abel
  have hpopulationDot :
      HasDerivAt
        (fun t : ℝ => directionPopulationDot t (q t) (qdot t))
        (directionPopulationDDot a (q a) (qdot a) qddot) a := by
    have hp := hH.add (ha.smul hHdot)
    convert hp using 1
    simp only [directionPopulationDDot, one_smul]
    module
  have hdenominator :
      HasDerivAt
        (fun t : ℝ => directionDenominator21 t (q t))
        (directionDenominatorDot a (q a) (qdot a)) a := by
    have hd := HasDerivAt.const_add
      ((2 : ℝ) • (1 : WA 1)) (ha.smul hR)
    convert hd using 1
    simp only [directionDenominatorDot, one_smul]
    abel
  have hdenominatorDot :
      HasDerivAt
        (fun t : ℝ => directionDenominatorDot t (q t) (qdot t))
        (directionDenominatorDDot a (q a) (qdot a) qddot) a := by
    have hd := hR.add (ha.smul hRdot)
    convert hd using 1
    simp only [directionDenominatorDDot, one_smul]
    module
  have hpopulationCube :
      HasDerivAt
        (fun t : ℝ => directionPopulation21 t (q t) ^ 3)
        (directionPopulationCubeDot a (q a) (qdot a)) a := by
    simpa only [directionPopulationCubeDot] using
      hpopulation.pow 3
  have hpopulationCubeDot :
      HasDerivAt
        (fun t : ℝ =>
          directionPopulationCubeDot t (q t) (qdot t))
        (directionPopulationCubeDDot
          a (q a) (qdot a) qddot) a := by
    have hthree : HasDerivAt
        (fun _ : ℝ => (3 : WA 1)) 0 a :=
      hasDerivAt_const a (3 : WA 1)
    have hp :=
      (hthree.mul (hpopulation.pow 2)).mul hpopulationDot
    convert hp using 1
    simp only [directionPopulationCubeDDot, Pi.mul_apply, pow_two]
    ring
  have hcore :
      HasDerivAt
        (fun t : ℝ => directionFluxCore t (q t))
        (directionFluxCoreDot a (q a) (qdot a)) a := by
    simpa only [directionFluxCore, directionFluxCoreDot] using
      hpopulationCube.mul hDR
  have hcoreDot :
      HasDerivAt
        (fun t : ℝ =>
          directionFluxCoreDot t (q t) (qdot t))
        (directionFluxCoreDDot a (q a) (qdot a) qddot) a := by
    have hc :=
      (hpopulationCubeDot.mul hDR).add
        (hpopulationCube.mul hDRdot)
    convert hc using 1
    simp only [directionFluxCoreDDot]
    ring
  have hchi :
      HasDerivAt (fun t : ℝ => (q t).2) (qdot a).2 a :=
    implicitSensitivity_comp_hasDerivAt hq
  have hchidot :
      HasDerivAt (fun t : ℝ => (qdot t).2) qddot.2 a :=
    implicitSensitivity_comp_hasDerivAt hqdot
  have hleft :
      HasDerivAt
        (fun t : ℝ =>
          directionDenominatorDot t (q t) (qdot t) *
              directionDerivative21 (q t) +
            directionDenominator21 t (q t) *
              implicitDerivativeAmbient21CLM (qdot t))
        (directionDenominatorDDot a (q a) (qdot a) qddot *
              directionDerivative21 (q a) +
            (2 : WA 1) *
              directionDenominatorDot a (q a) (qdot a) *
                implicitDerivativeAmbient21CLM (qdot a) +
            directionDenominator21 a (q a) *
              implicitDerivativeAmbient21CLM qddot) a := by
    have hl :=
      (hdenominatorDot.mul hD).add
        (hdenominator.mul hDdot)
    convert hl using 1
    ring
  have hright :
      HasDerivAt
        (fun t : ℝ =>
          (qdot t).2 • directionFluxCore t (q t) +
            (q t).2 • directionFluxCoreDot t (q t) (qdot t))
        (qddot.2 • directionFluxCore a (q a) +
          (2 : ℝ) • (qdot a).2 •
            directionFluxCoreDot a (q a) (qdot a) +
          (q a).2 •
            directionFluxCoreDDot a (q a) (qdot a) qddot) a := by
    have hr :=
      (hchidot.smul hcore).add (hchi.smul hcoreDot)
    convert hr using 1
    module
  simpa only [directionPolynomialFirstJet,
    directionPolynomialSecondJet] using hleft.sub hright

set_option synthInstance.maxHeartbeats 1000000 in
theorem minimalDirectionPolynomialFirstDeriv_hasDerivAt :
    HasDerivAt minimalDirectionPolynomialFirstDeriv
      (directionPolynomialSecondJet 0 implicitBase
        minimalImplicitFirstJet minimalImplicitSecondJet) 0 := by
  simpa only [minimalDirectionPolynomialFirstDeriv,
    minimalSteadyImplicitBranch_base] using
      directionPolynomialFirstJet_hasDerivAt
        minimalSteadyImplicitBranch_hasDerivAt
        deriv_minimalSteadyImplicitBranch_hasDerivAt

theorem eventually_minimalDirectionPolynomialFirstDeriv_zero :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      minimalDirectionPolynomialFirstDeriv a = 0 := by
  have heq :
      minimalDirectionPolynomial =ᶠ[𝓝 (0 : ℝ)]
        (fun _ : ℝ => (0 : WA 1)) := by
    simpa only [minimalDirectionPolynomial] using
      eventually_directionPolynomialFlux_branch
  have hdiff :
      ∀ᶠ a in 𝓝 (0 : ℝ),
        @ContDiffAt
          ℝ inferInstance
          ℝ inferInstance inferInstance
          BranchImplicit branchImplicitNormedAddCommGroup
            branchImplicitNormedSpace
          3 minimalSteadyImplicitBranch a :=
    @ContDiffAt.eventually
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      minimalSteadyImplicitBranch 0 3
      minimalSteadyImplicitBranch_contDiffAt (by norm_num)
  filter_upwards [heq.deriv, hdiff] with a hderiv hcont
  have hq :=
    @ContDiffAt.differentiableAt
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      minimalSteadyImplicitBranch a 3 hcont (by norm_num)
  have hqderiv :=
    @DifferentiableAt.hasDerivAt
      ℝ inferInstance BranchImplicit
      branchImplicitNormedAddCommGroup branchImplicitNormedSpace
      minimalSteadyImplicitBranch a hq
  have hp :=
    directionPolynomialFlux_hasDerivAt hqderiv
  calc
    minimalDirectionPolynomialFirstDeriv a =
        deriv minimalDirectionPolynomial a := by
      simpa only [minimalDirectionPolynomialFirstDeriv,
        minimalDirectionPolynomial] using hp.deriv.symm
    _ = deriv (fun _ : ℝ => (0 : WA 1)) a := hderiv
    _ = 0 := by simp

theorem minimalDirectionPolynomialSecondJet_zero :
    directionPolynomialSecondJet 0 implicitBase
      minimalImplicitFirstJet minimalImplicitSecondJet = 0 := by
  have heq :
      minimalDirectionPolynomialFirstDeriv =ᶠ[𝓝 (0 : ℝ)]
        (fun _ : ℝ => (0 : WA 1)) :=
    eventually_minimalDirectionPolynomialFirstDeriv_zero
  calc
    directionPolynomialSecondJet 0 implicitBase
        minimalImplicitFirstJet minimalImplicitSecondJet =
        deriv minimalDirectionPolynomialFirstDeriv 0 :=
      minimalDirectionPolynomialFirstDeriv_hasDerivAt.deriv.symm
    _ = deriv (fun _ : ℝ => (0 : WA 1)) 0 :=
      heq.deriv_eq
    _ = 0 := by simp

theorem directionPolynomialSecondJet_base_formula
    (qdot qddot : BranchImplicit) (hchi : qdot.2 = 0) :
    directionPolynomialSecondJet 0 implicitBase qdot qddot =
      (2 : WA 1) *
          (implicitResolvedAmbient21CLM qdot *
            directionDerivative21 implicitBase) +
        (2 : WA 1) *
          (directionResolved21 implicitBase *
            implicitDerivativeAmbient21CLM qdot) +
        (2 : WA 1) * implicitDerivativeAmbient21CLM qddot -
        (qddot.2 • directionDerivResolved21 implicitBase +
          minimalChiLin •
            ((6 : WA 1) *
                (directionProfile21 implicitBase ^ 2 *
                  directionDerivResolved21 implicitBase) +
              (6 : WA 1) *
                (implicitProfileAmbient21CLM qdot *
                  directionDerivResolved21 implicitBase) +
              (6 : WA 1) *
                (directionProfile21 implicitBase *
                  implicitDerivResolvedAmbient21CLM qdot) +
              implicitDerivResolvedAmbient21CLM qddot)) := by
  unfold directionPolynomialSecondJet directionDenominatorDDot
    directionDenominatorDot
    directionFluxCore directionFluxCoreDot directionFluxCoreDDot
    directionPopulationCubeDot directionPopulationCubeDDot
    directionPopulationDDot directionPopulationDot directionDenominator21
    directionPopulation21
  simp only [zero_smul, add_zero, implicitBase, one_pow, pow_two,
    one_mul, hchi]
  simp only [two_smul, zero_add]
  ring_nf

theorem natCast_mul_coeff (k : ℕ) (x : WA 1) (n : ℤ) :
    (((k : WA 1) * x).toFun n) =
      (k : ℂ) * x.toFun n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.cast_succ, add_mul, WA.add_toFun, Pi.add_apply,
        ih, one_mul]
      push_cast
      ring

theorem two_mul_coeff (x : WA 1) (n : ℤ) :
    (((2 : WA 1) * x).toFun n) =
      (2 : ℂ) * x.toFun n :=
  natCast_mul_coeff 2 x n

theorem six_mul_coeff (x : WA 1) (n : ℤ) :
    (((6 : WA 1) * x).toFun n) =
      (6 : ℂ) * x.toFun n :=
  natCast_mul_coeff 6 x n

theorem mul_coeff_one_of_twoMode_left
    (a b : WA 1)
    (ha : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → a.toFun n = 0) :
    (a * b).toFun 1 =
      a.toFun 1 * b.toFun 0 +
        a.toFun (-1) * b.toFun 2 := by
  change wConv a.toFun b.toFun 1 = _
  rw [wConv_twoMode_left a.toFun b.toFun ha]
  norm_num

theorem directionProfile_sq_base_coeff_zero :
    (directionProfile21 implicitBase ^ 2).toFun 0 =
      (1 / 2 : ℂ) := by
  rw [pow_two]
  change
    wConv (directionProfile21 implicitBase).toFun
      (directionProfile21 implicitBase).toFun 0 =
        (1 / 2 : ℂ)
  rw [wConv_twoMode_left
    (directionProfile21 implicitBase).toFun
    (directionProfile21 implicitBase).toFun
    directionProfile21_base_support]
  simp only [directionProfile21_base_coeff,
    firstModeSeq_one, firstModeSeq_neg_one]
  norm_num

theorem directionProfile_sq_base_coeff_two :
    (directionProfile21 implicitBase ^ 2).toFun 2 =
      (1 / 4 : ℂ) := by
  rw [pow_two]
  change
    (directionProfile21 implicitBase *
      directionProfile21 implicitBase).toFun 2 =
        (1 / 4 : ℂ)
  rw [mul_coeff_two_of_twoMode
    (directionProfile21 implicitBase)
    (directionProfile21 implicitBase)
    directionProfile21_base_support
    directionProfile21_base_support,
    directionProfile21_base_coeff, firstModeSeq_one]
  norm_num

set_option maxHeartbeats 1000000 in
theorem minimalSensitivitySecondJet_eq :
    minimalSensitivitySecondJet =
      -(6 * Real.pi ^ 4 + 37 * Real.pi ^ 2 + 25) /
        (24 * Real.pi ^ 2 * (Real.pi ^ 2 + 1)) := by
  have hZ0 :
      (implicitProfileAmbient21CLM
        minimalImplicitFirstJet).toFun 0 = 0 := by
    rw [implicitProfileAmbient21CLM_coeff]
    exact FirstComplementWA.coeff_zero minimalComplementFirstJet
  have hZ2 :
      (implicitProfileAmbient21CLM
        minimalImplicitFirstJet).toFun 2 =
          (((4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
            (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1)) : ℝ) : ℂ) := by
    rw [implicitProfileAmbient21CLM_coeff]
    exact minimalComplementFirstJet_coeff_two
  have hRZ0 :
      (implicitResolvedAmbient21CLM
        minimalImplicitFirstJet).toFun 0 = 0 := by
    rw [implicitResolvedAmbient21CLM_coeff,
      FirstComplementWA.coeff_zero]
    simp
  have hRZ2 :
      (implicitResolvedAmbient21CLM
        minimalImplicitFirstJet).toFun 2 =
        ((1 / (1 + (2 * Real.pi) ^ 2) : ℝ) : ℂ) *
          (((4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
            (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1)) : ℝ) : ℂ) := by
    rw [implicitResolvedAmbient21CLM_coeff]
    change
      ((1 / (1 + (2 * Real.pi) ^ 2) : ℝ) : ℂ) *
          (implicitProfileAmbient21CLM
            minimalImplicitFirstJet).toFun 2 =
        _
    rw [hZ2]
  have hDZ0 :
      (implicitDerivativeAmbient21CLM
        minimalImplicitFirstJet).toFun 0 = 0 := by
    rw [implicitDerivativeAmbient21CLM_coeff,
      FirstComplementWA.coeff_zero]
    simp
  have hDZ2 :
      (implicitDerivativeAmbient21CLM
        minimalImplicitFirstJet).toFun 2 =
        Complex.I * (2 * Real.pi : ℝ) *
          (((4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
            (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1)) : ℝ) : ℂ) := by
    rw [implicitDerivativeAmbient21CLM_coeff]
    change
      (Complex.I * Real.pi * (2 : ℂ)) *
          (implicitProfileAmbient21CLM
            minimalImplicitFirstJet).toFun 2 =
        _
    rw [hZ2]
    push_cast
    ring
  have hDRZ0 :
      (implicitDerivResolvedAmbient21CLM
        minimalImplicitFirstJet).toFun 0 = 0 := by
    rw [implicitDerivResolvedAmbient21CLM_coeff,
      FirstComplementWA.coeff_zero]
    simp
  have hDRZ2 :
      (implicitDerivResolvedAmbient21CLM
        minimalImplicitFirstJet).toFun 2 =
        Complex.I * (2 * Real.pi : ℝ) *
          ((1 / (1 + (2 * Real.pi) ^ 2) : ℝ) : ℂ) *
          (((4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
            (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1)) : ℝ) : ℂ) := by
    rw [implicitDerivResolvedAmbient21CLM_coeff]
    change
      Complex.I * (2 * Real.pi : ℝ) *
          ((1 / (1 + (2 * Real.pi) ^ 2) : ℝ) : ℂ) *
          (implicitProfileAmbient21CLM
            minimalImplicitFirstJet).toFun 2 =
        _
    rw [hZ2]
  have hD2one :
      (implicitDerivativeAmbient21CLM
        minimalImplicitSecondJet).toFun 1 = 0 := by
    rw [implicitDerivativeAmbient21CLM_coeff,
      FirstComplementWA.coeff_one]
    simp
  have hDR2one :
      (implicitDerivResolvedAmbient21CLM
        minimalImplicitSecondJet).toFun 1 = 0 := by
    rw [implicitDerivResolvedAmbient21CLM_coeff,
      FirstComplementWA.coeff_one]
    simp
  have hHone :
      (directionProfile21 implicitBase).toFun 1 =
        (1 / 2 : ℂ) := by
    rw [directionProfile21_base_coeff, firstModeSeq_one]
  have hHnegone :
      (directionProfile21 implicitBase).toFun (-1) =
        (1 / 2 : ℂ) := by
    rw [directionProfile21_base_coeff, firstModeSeq_neg_one]
  have hRone :
      (directionResolved21 implicitBase).toFun 1 =
        ((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) * (1 / 2 : ℂ) := by
    rw [directionResolved21_base_coeff, firstModeSeq_one]
    norm_num
  have hRnegone :
      (directionResolved21 implicitBase).toFun (-1) =
        ((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) * (1 / 2 : ℂ) := by
    rw [directionResolved21_base_coeff, firstModeSeq_neg_one]
    norm_num
  have hDone :
      (directionDerivative21 implicitBase).toFun 1 =
        Complex.I * (Real.pi : ℂ) * (1 / 2 : ℂ) := by
    rw [directionDerivative21_base_coeff, firstModeSeq_one]
    norm_num
  have hDnegone :
      (directionDerivative21 implicitBase).toFun (-1) =
        -(Complex.I * (Real.pi : ℂ) * (1 / 2 : ℂ)) := by
    rw [directionDerivative21_base_coeff, firstModeSeq_neg_one]
    norm_num
  have hDRone :
      (directionDerivResolved21 implicitBase).toFun 1 =
        Complex.I * (Real.pi : ℂ) *
          ((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) * (1 / 2 : ℂ) := by
    rw [directionDerivResolved21_base_coeff, firstModeSeq_one]
    norm_num
  have hDRnegone :
      (directionDerivResolved21 implicitBase).toFun (-1) =
        -(Complex.I * (Real.pi : ℂ) *
          ((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) * (1 / 2 : ℂ)) := by
    rw [directionDerivResolved21_base_coeff, firstModeSeq_neg_one]
    norm_num
  have hRZD :
      (implicitResolvedAmbient21CLM minimalImplicitFirstJet *
        directionDerivative21 implicitBase).toFun 1 =
          (directionDerivative21 implicitBase).toFun 1 *
              (implicitResolvedAmbient21CLM
                minimalImplicitFirstJet).toFun 0 +
            (directionDerivative21 implicitBase).toFun (-1) *
              (implicitResolvedAmbient21CLM
                minimalImplicitFirstJet).toFun 2 := by
    calc
      _ = (directionDerivative21 implicitBase *
          implicitResolvedAmbient21CLM
            minimalImplicitFirstJet).toFun 1 := by
        rw [mul_comm]
      _ = _ := mul_coeff_one_of_twoMode_left _ _
        directionDerivative21_base_support
  have hRDZ :
      (directionResolved21 implicitBase *
        implicitDerivativeAmbient21CLM
          minimalImplicitFirstJet).toFun 1 =
          (directionResolved21 implicitBase).toFun 1 *
              (implicitDerivativeAmbient21CLM
                minimalImplicitFirstJet).toFun 0 +
            (directionResolved21 implicitBase).toFun (-1) *
              (implicitDerivativeAmbient21CLM
                minimalImplicitFirstJet).toFun 2 :=
    mul_coeff_one_of_twoMode_left _ _
      directionResolved21_base_support
  have hHsqDR :
      (directionProfile21 implicitBase ^ 2 *
        directionDerivResolved21 implicitBase).toFun 1 =
          (directionDerivResolved21 implicitBase).toFun 1 *
              (directionProfile21 implicitBase ^ 2).toFun 0 +
            (directionDerivResolved21 implicitBase).toFun (-1) *
              (directionProfile21 implicitBase ^ 2).toFun 2 := by
    calc
      _ = (directionDerivResolved21 implicitBase *
          directionProfile21 implicitBase ^ 2).toFun 1 := by
        rw [mul_comm]
      _ = _ := mul_coeff_one_of_twoMode_left _ _
        directionDerivResolved21_base_support
  have hZDR :
      (implicitProfileAmbient21CLM minimalImplicitFirstJet *
        directionDerivResolved21 implicitBase).toFun 1 =
          (directionDerivResolved21 implicitBase).toFun 1 *
              (implicitProfileAmbient21CLM
                minimalImplicitFirstJet).toFun 0 +
            (directionDerivResolved21 implicitBase).toFun (-1) *
              (implicitProfileAmbient21CLM
                minimalImplicitFirstJet).toFun 2 := by
    calc
      _ = (directionDerivResolved21 implicitBase *
          implicitProfileAmbient21CLM
            minimalImplicitFirstJet).toFun 1 := by
        rw [mul_comm]
      _ = _ := mul_coeff_one_of_twoMode_left _ _
        directionDerivResolved21_base_support
  have hHDRZ :
      (directionProfile21 implicitBase *
        implicitDerivResolvedAmbient21CLM
          minimalImplicitFirstJet).toFun 1 =
          (directionProfile21 implicitBase).toFun 1 *
              (implicitDerivResolvedAmbient21CLM
                minimalImplicitFirstJet).toFun 0 +
            (directionProfile21 implicitBase).toFun (-1) *
              (implicitDerivResolvedAmbient21CLM
                minimalImplicitFirstJet).toFun 2 :=
    mul_coeff_one_of_twoMode_left _ _
      directionProfile21_base_support
  have helem :
      (2 : WA 1) *
          (implicitResolvedAmbient21CLM minimalImplicitFirstJet *
            directionDerivative21 implicitBase) +
        (2 : WA 1) *
          (directionResolved21 implicitBase *
            implicitDerivativeAmbient21CLM minimalImplicitFirstJet) +
        (2 : WA 1) *
          implicitDerivativeAmbient21CLM minimalImplicitSecondJet -
        (minimalSensitivitySecondJet •
            directionDerivResolved21 implicitBase +
          minimalChiLin •
            ((6 : WA 1) *
                (directionProfile21 implicitBase ^ 2 *
                  directionDerivResolved21 implicitBase) +
              (6 : WA 1) *
                (implicitProfileAmbient21CLM minimalImplicitFirstJet *
                  directionDerivResolved21 implicitBase) +
              (6 : WA 1) *
                (directionProfile21 implicitBase *
                  implicitDerivResolvedAmbient21CLM
                    minimalImplicitFirstJet) +
              implicitDerivResolvedAmbient21CLM
                minimalImplicitSecondJet)) =
        0 := by
    exact
      (directionPolynomialSecondJet_base_formula
        minimalImplicitFirstJet minimalImplicitSecondJet
          minimalSensitivityFirstJet_eq_zero).symm.trans
            minimalDirectionPolynomialSecondJet_zero
  have hc := congrArg (fun x : WA 1 => x.toFun 1) helem
  simp only [WA.add_toFun, WA.sub_toFun, real_smul_coeff,
    Pi.add_apply, Pi.sub_apply, WA.zero_toFun, Pi.zero_apply,
    two_mul_coeff, six_mul_coeff] at hc
  rw [hRZD, hRDZ, hHsqDR, hZDR, hHDRZ] at hc
  rw [hZ0, hZ2, hRZ0, hRZ2, hDZ0, hDZ2, hDRZ0, hDRZ2,
    hD2one, hDR2one] at hc
  rw [hHone, hHnegone, hRone, hRnegone,
    hDone, hDnegone, hDRone, hDRnegone,
    directionProfile_sq_base_coeff_zero,
    directionProfile_sq_base_coeff_two] at hc
  let c : ℝ :=
    (4 * Real.pi ^ 2 + 1) * (6 * Real.pi ^ 2 + 5) /
      (48 * Real.pi ^ 2 * (Real.pi ^ 2 + 1))
  let s₁ : ℝ := 1 / (1 + Real.pi ^ 2)
  let s₂ : ℝ := 1 / (1 + (2 * Real.pi) ^ 2)
  have hcI :
      Complex.I *
        ((2 * (-(Real.pi / 2) * (s₂ * c)) +
          2 * ((s₁ / 2) * (2 * Real.pi * c)) -
          (minimalSensitivitySecondJet * (Real.pi * s₁ / 2) +
            minimalChiLin *
              (6 * (Real.pi * s₁ / 2 * (1 / 2) -
                Real.pi * s₁ / 2 * (1 / 4)) +
              6 * (-(Real.pi * s₁ / 2) * c) +
              6 * ((1 / 2) * (2 * Real.pi * s₂ * c)))) : ℝ) : ℂ) =
        0 := by
    dsimp [c, s₁, s₂]
    convert hc using 1
    push_cast
    ring
  have hreal :
      2 * (-(Real.pi / 2) * (s₂ * c)) +
          2 * ((s₁ / 2) * (2 * Real.pi * c)) -
          (minimalSensitivitySecondJet * (Real.pi * s₁ / 2) +
            minimalChiLin *
              (6 * (Real.pi * s₁ / 2 * (1 / 2) -
                Real.pi * s₁ / 2 * (1 / 4)) +
              6 * (-(Real.pi * s₁ / 2) * c) +
              6 * ((1 / 2) * (2 * Real.pi * s₂ * c)))) =
        0 := by
    have him := congrArg Complex.im hcI
    simpa using him
  dsimp [c, s₁, s₂] at hreal
  unfold minimalChiLin at hreal
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : 1 + Real.pi ^ 2 ≠ 0 := by positivity
  have h4 : 1 + (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp [hp, h1, h4] at hreal ⊢
  nlinarith [Real.pi_pos]

theorem minimalSensitivitySecondJet_neg :
    minimalSensitivitySecondJet < 0 := by
  rw [minimalSensitivitySecondJet_eq]
  have hnum :
      0 < 6 * Real.pi ^ 4 + 37 * Real.pi ^ 2 + 25 := by
    positivity
  have hneg :
      -(6 * Real.pi ^ 4 + 37 * Real.pi ^ 2 + 25) < 0 := by
    linarith
  exact div_neg_of_neg_of_pos hneg (by positivity)

end ShenWork.M3Counterexample
