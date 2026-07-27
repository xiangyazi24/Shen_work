import ShenWork.Paper3.MinimalSteadyWALinearIso
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# The local amplitude-parametrized steady branch

This file identifies the partial derivative of the blown-up residual with the
explicit equivalence constructed in `MinimalSteadyWALinearIso` and invokes
Mathlib's Banach-space implicit function theorem once.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open scoped Topology

/-! ## The zero-amplitude implicit slice -/

def implicitBase : BranchImplicit :=
  (0, minimalChiLin)

def implicitEmbeddingCLM :
    BranchImplicit →L[ℝ] BranchVariables :=
  ContinuousLinearMap.inr ℝ ℝ BranchImplicit

@[simp]
theorem implicitEmbeddingCLM_apply (q : BranchImplicit) :
    implicitEmbeddingCLM q = (0, q) :=
  rfl

@[simp]
theorem implicitEmbedding_base :
    implicitEmbeddingCLM implicitBase = blownBase :=
  rfl

def blownImplicitSlice (q : BranchImplicit) : BranchSpace :=
  blownResidual (implicitEmbeddingCLM q)

theorem blownImplicitSlice_formula (q : BranchImplicit) :
    blownImplicitSlice q =
      blownProfile (implicitEmbeddingCLM q) -
        (q.2 / 2) •
          signalResolverCLM (blownProfile (implicitEmbeddingCLM q)) := by
  have hpop :
      blownPopulation (implicitEmbeddingCLM q) = 1 := by
    simp [blownPopulation]
  have hden :
      blownDenominator (implicitEmbeddingCLM q) =
        (2 : ℝ) • (1 : ShenWork.Wiener.WA 2) := by
    simp [blownDenominator]
  have hflux :
      blownFlux (implicitEmbeddingCLM q) =
        (1 / 2 : ℝ) •
          branchDerivResolverCLM
            (blownProfile (implicitEmbeddingCLM q)) := by
    rw [blownFlux_eq_raw]
    apply Subtype.ext
    rw [blownRawFluxOddImag_coe]
    change
      blownMobility (implicitEmbeddingCLM q) *
          (branchDerivResolverCLM
            (blownProfile (implicitEmbeddingCLM q))).1 =
        (((1 / 2 : ℝ) : ℂ) •
          (branchDerivResolverCLM
            (blownProfile (implicitEmbeddingCLM q))).1)
    rw [blownMobility, hpop, one_pow, hden,
      ringInverse_two_smul_one, one_mul]
    change
      (((1 / 2 : ℝ) : ℂ) •
          (1 : ShenWork.Wiener.WA 2)) *
          (branchDerivResolverCLM
            (blownProfile (implicitEmbeddingCLM q))).1 =
        (((1 / 2 : ℝ) : ℂ) •
          (branchDerivResolverCLM
            (blownProfile (implicitEmbeddingCLM q))).1)
    rw [smul_mul_assoc, one_mul]
  unfold blownImplicitSlice blownResidual
  change
    blownProfile (implicitEmbeddingCLM q) -
        q.2 • inverseDerivativeCLM
          (blownFlux (implicitEmbeddingCLM q)) =
      blownProfile (implicitEmbeddingCLM q) -
        (q.2 / 2) •
          signalResolverCLM (blownProfile (implicitEmbeddingCLM q))
  rw [hflux, map_smul, inverseDerivative_branchDerivResolver]
  congr 1
  rw [← mul_smul]
  congr 1
  ring

/-! ## Direct derivative of the slice -/

def implicitProfileDerivativeCLM :
    BranchImplicit →L[ℝ] BranchSpace :=
  complementSubtypeCLM.comp
    (ContinuousLinearMap.fst ℝ BranchComplement ℝ)

def implicitResolvedDerivativeCLM :
    BranchImplicit →L[ℝ] BranchSpace :=
  signalResolverCLM.comp implicitProfileDerivativeCLM

def implicitHalfSensitivityCLM :
    BranchImplicit →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    ContinuousLinearMap.snd ℝ BranchComplement ℝ

@[simp]
theorem implicitProfileDerivativeCLM_apply
    (q : BranchImplicit) :
    implicitProfileDerivativeCLM q = q.1.1 :=
  rfl

@[simp]
theorem implicitResolvedDerivativeCLM_apply
    (q : BranchImplicit) :
    implicitResolvedDerivativeCLM q =
      signalResolverCLM q.1.1 :=
  rfl

@[simp]
theorem implicitHalfSensitivityCLM_apply
    (q : BranchImplicit) :
    implicitHalfSensitivityCLM q = q.2 / 2 := by
  change (1 / 2 : ℝ) * q.2 = q.2 / 2
  ring

def simplifiedImplicitSlice (q : BranchImplicit) : BranchSpace :=
  (firstModeMeanZero 2 + implicitProfileDerivativeCLM q) -
    implicitHalfSensitivityCLM q •
      (signalResolverCLM (firstModeMeanZero 2) +
        implicitResolvedDerivativeCLM q)

theorem blownImplicitSlice_eq_simplified :
    blownImplicitSlice = simplifiedImplicitSlice := by
  funext q
  rw [blownImplicitSlice_formula]
  change
    (firstModeMeanZero 2 + implicitProfileDerivativeCLM q) -
        (q.2 / 2) •
          signalResolverCLM
            (firstModeMeanZero 2 + implicitProfileDerivativeCLM q) =
      simplifiedImplicitSlice q
  rw [map_add]
  unfold simplifiedImplicitSlice
  rw [implicitHalfSensitivityCLM_apply,
    implicitResolvedDerivativeCLM_apply,
    implicitProfileDerivativeCLM_apply]

def implicitSliceDerivativeCLM :
    BranchImplicit →L[ℝ] BranchSpace :=
  implicitProfileDerivativeCLM -
    ((minimalChiLin / 2 : ℝ) • implicitResolvedDerivativeCLM +
      implicitHalfSensitivityCLM.smulRight
        (signalResolverCLM (firstModeMeanZero 2)))

@[simp]
theorem implicitSliceDerivativeCLM_apply
    (q : BranchImplicit) :
    implicitSliceDerivativeCLM q =
      q.1.1 -
        ((minimalChiLin / 2 : ℝ) • signalResolverCLM q.1.1 +
          (q.2 / 2 : ℝ) •
            signalResolverCLM (firstModeMeanZero 2)) := by
  change
    q.1.1 -
        ((minimalChiLin / 2 : ℝ) • signalResolverCLM q.1.1 +
          implicitHalfSensitivityCLM q •
            signalResolverCLM (firstModeMeanZero 2)) =
      _
  rw [implicitHalfSensitivityCLM_apply]

set_option synthInstance.maxHeartbeats 1000000 in
theorem simplifiedImplicitSlice_hasFDerivAt :
    HasFDerivAt simplifiedImplicitSlice implicitSliceDerivativeCLM
      implicitBase := by
  have hprofileLinear :
      HasFDerivAt
        (fun q : BranchImplicit => implicitProfileDerivativeCLM q)
        implicitProfileDerivativeCLM implicitBase :=
    implicitProfileDerivativeCLM.hasFDerivAt
  have hprofile :
      HasFDerivAt
        (fun q : BranchImplicit =>
          firstModeMeanZero 2 + implicitProfileDerivativeCLM q)
        implicitProfileDerivativeCLM implicitBase := by
    exact
      @HasFDerivAt.const_add
        ℝ inferInstance
        BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
        BranchSpace BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace
        (fun q : BranchImplicit => implicitProfileDerivativeCLM q)
        implicitProfileDerivativeCLM implicitBase
        (firstModeMeanZero 2) hprofileLinear
  have hresolvedLinear :
      HasFDerivAt
        (fun q : BranchImplicit => implicitResolvedDerivativeCLM q)
        implicitResolvedDerivativeCLM implicitBase :=
    implicitResolvedDerivativeCLM.hasFDerivAt
  have hresolved :
      HasFDerivAt
        (fun q : BranchImplicit =>
          signalResolverCLM (firstModeMeanZero 2) +
            implicitResolvedDerivativeCLM q)
        implicitResolvedDerivativeCLM implicitBase := by
    exact
      @HasFDerivAt.const_add
        ℝ inferInstance
        BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
        BranchSpace BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace
        (fun q : BranchImplicit => implicitResolvedDerivativeCLM q)
        implicitResolvedDerivativeCLM implicitBase
        (signalResolverCLM (firstModeMeanZero 2)) hresolvedLinear
  have hsensitivity :
      HasFDerivAt implicitHalfSensitivityCLM
        implicitHalfSensitivityCLM implicitBase :=
    implicitHalfSensitivityCLM.hasFDerivAt
  have hproduct :
      HasFDerivAt
        (fun q : BranchImplicit =>
          implicitHalfSensitivityCLM q •
            (signalResolverCLM (firstModeMeanZero 2) +
              implicitResolvedDerivativeCLM q))
        (implicitHalfSensitivityCLM implicitBase •
            implicitResolvedDerivativeCLM +
          implicitHalfSensitivityCLM.smulRight
            (signalResolverCLM (firstModeMeanZero 2) +
              implicitResolvedDerivativeCLM implicitBase))
        implicitBase :=
    @HasFDerivAt.smul
      ℝ inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
      branchImplicitNormedSpace
      BranchSpace BranchSpace.normedAddCommGroup
      BranchSpace.normedSpace
      (fun q : BranchImplicit =>
        signalResolverCLM (firstModeMeanZero 2) +
          implicitResolvedDerivativeCLM q)
      implicitResolvedDerivativeCLM implicitBase
      ℝ inferInstance inferInstance BranchSpace.module
      inferInstance inferInstance
      (fun q : BranchImplicit => implicitHalfSensitivityCLM q)
      implicitHalfSensitivityCLM hsensitivity hresolved
  have hdifference :=
    @HasFDerivAt.sub
      ℝ inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
      branchImplicitNormedSpace
      BranchSpace BranchSpace.normedAddCommGroup
      BranchSpace.normedSpace
      (fun q : BranchImplicit =>
        firstModeMeanZero 2 + implicitProfileDerivativeCLM q)
      (fun q : BranchImplicit =>
        implicitHalfSensitivityCLM q •
          (signalResolverCLM (firstModeMeanZero 2) +
            implicitResolvedDerivativeCLM q))
      implicitProfileDerivativeCLM
      (implicitHalfSensitivityCLM implicitBase •
          implicitResolvedDerivativeCLM +
        implicitHalfSensitivityCLM.smulRight
          (signalResolverCLM (firstModeMeanZero 2) +
            implicitResolvedDerivativeCLM implicitBase))
      implicitBase hprofile hproduct
  change
    HasFDerivAt
      (fun q : BranchImplicit =>
        (firstModeMeanZero 2 + implicitProfileDerivativeCLM q) -
          implicitHalfSensitivityCLM q •
            (signalResolverCLM (firstModeMeanZero 2) +
              implicitResolvedDerivativeCLM q))
      implicitSliceDerivativeCLM implicitBase
  simpa only [implicitSliceDerivativeCLM, implicitBase,
    implicitHalfSensitivityCLM_apply,
    implicitResolvedDerivativeCLM_apply, Pi.sub_apply,
    ZeroMemClass.coe_zero, map_zero, zero_div, smul_zero,
    add_zero] using hdifference

set_option synthInstance.maxHeartbeats 1000000 in
theorem blownImplicitSlice_hasFDerivAt :
    HasFDerivAt blownImplicitSlice implicitSliceDerivativeCLM
      implicitBase := by
  rw [blownImplicitSlice_eq_simplified]
  exact simplifiedImplicitSlice_hasFDerivAt

theorem signalResolver_firstMode :
    signalResolverCLM (firstModeMeanZero 2) =
      (1 / (1 + Real.pi ^ 2) : ℝ) •
        firstModeMeanZero 2 := by
  calc
    signalResolverCLM (firstModeMeanZero 2) =
        inverseDerivativeCLM
          (branchDerivResolverCLM (firstModeMeanZero 2)) := by
      symm
      exact inverseDerivative_branchDerivResolver
        (firstModeMeanZero 2)
    _ = _ := inverseDerivative_firstModeDerivResolver

theorem implicitSliceDerivative_eq_linearEquiv :
    implicitSliceDerivativeCLM =
      (implicitLinearEquiv :
        BranchImplicit →L[ℝ] BranchSpace) := by
  apply ContinuousLinearMap.ext
  intro q
  rw [implicitSliceDerivativeCLM_apply, signalResolver_firstMode]
  rw [show
    (implicitLinearEquiv :
      BranchImplicit →L[ℝ] BranchSpace) q =
        (criticalComplementCLM q.1).1 -
          (q.2 / minimalChiLin) • firstModeMeanZero 2 by
      exact implicitLinearEquiv_apply q]
  change
    q.1.1 -
        ((minimalChiLin / 2 : ℝ) • signalResolverCLM q.1.1 +
          (q.2 / 2 : ℝ) •
            ((1 / (1 + Real.pi ^ 2) : ℝ) •
              firstModeMeanZero 2)) =
      (criticalBranchCLM q.1.1) -
        (q.2 / minimalChiLin) • firstModeMeanZero 2
  have hhalf :
      minimalChiLin / 2 = 1 + Real.pi ^ 2 := by
    unfold minimalChiLin
    ring
  have hscalar :
      (q.2 / 2) * (1 / (1 + Real.pi ^ 2)) =
        q.2 / minimalChiLin := by
    have hden : 1 + Real.pi ^ 2 ≠ 0 := by positivity
    unfold minimalChiLin
    field_simp
  rw [hhalf, ← mul_smul, hscalar]
  change
    q.1.1 -
        ((1 + Real.pi ^ 2 : ℝ) • signalResolverCLM q.1.1 +
          (q.2 / minimalChiLin) • firstModeMeanZero 2) =
      (q.1.1 -
        (1 + Real.pi ^ 2 : ℝ) • signalResolverCLM q.1.1) -
          (q.2 / minimalChiLin) • firstModeMeanZero 2
  abel

set_option synthInstance.maxHeartbeats 1000000 in
theorem blownImplicitSlice_hasFDerivAt_linearEquiv :
    HasFDerivAt blownImplicitSlice
      (implicitLinearEquiv :
        BranchImplicit →L[ℝ] BranchSpace)
      implicitBase := by
  rw [← implicitSliceDerivative_eq_linearEquiv]
  exact blownImplicitSlice_hasFDerivAt

/-! ## Identification with the partial derivative of the full residual -/

set_option synthInstance.maxHeartbeats 1000000 in
theorem blownResidual_partial_fderiv :
    (fderiv ℝ blownResidual blownBase).comp
        (ContinuousLinearMap.inr ℝ ℝ BranchImplicit) =
      (implicitLinearEquiv :
        BranchImplicit →L[ℝ] BranchSpace) := by
  have hfull :=
    (blownResidual_contDiffAt.differentiableAt
      (by norm_num)).hasFDerivAt
  have hembed :
      HasFDerivAt
        (fun q : BranchImplicit => ((0, q) : BranchVariables))
        (ContinuousLinearMap.inr ℝ ℝ BranchImplicit) implicitBase :=
    (ContinuousLinearMap.inr ℝ ℝ BranchImplicit).hasFDerivAt
  have hcomp :=
    @HasFDerivAt.comp
      ℝ inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
      branchImplicitNormedSpace
      BranchVariables branchVariablesNormedAddCommGroup
      branchVariablesNormedSpace
      BranchSpace BranchSpace.normedAddCommGroup
      BranchSpace.normedSpace
      (fun q : BranchImplicit => ((0, q) : BranchVariables))
      (ContinuousLinearMap.inr ℝ ℝ BranchImplicit)
      implicitBase
      blownResidual
      (fderiv ℝ blownResidual blownBase)
      hfull hembed
  have hslice :
      HasFDerivAt blownImplicitSlice
        ((fderiv ℝ blownResidual blownBase).comp
          (ContinuousLinearMap.inr ℝ ℝ
            BranchImplicit)) implicitBase := by
    simpa only [blownImplicitSlice, Function.comp_apply,
      implicitEmbedding_base] using hcomp
  exact hslice.unique blownImplicitSlice_hasFDerivAt_linearEquiv

set_option synthInstance.maxHeartbeats 1000000 in
theorem blownResidual_partial_isInvertible :
    ((fderiv ℝ blownResidual blownBase).comp
      (ContinuousLinearMap.inr ℝ ℝ
        BranchImplicit)).IsInvertible := by
  rw [blownResidual_partial_fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

/-! ## The single Banach-space IFT application -/

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def minimalSteadyImplicitBranch :
    ℝ → BranchImplicit :=
  @ContDiffAt.implicitFunction
    ℝ inferInstance
    ℝ inferInstance inferInstance inferInstance
    BranchImplicit branchImplicitNormedAddCommGroup
      branchImplicitNormedSpace branchImplicitCompleteSpace
    BranchSpace BranchSpace.normedAddCommGroup
      BranchSpace.normedSpace (meanZeroEvenRealWACompleteSpace 2)
    blownBase blownResidual 3
    blownResidual_contDiffAt (by norm_num)
    blownResidual_partial_isInvertible

set_option synthInstance.maxHeartbeats 1000000 in
theorem minimalSteadyImplicitBranch_base :
    minimalSteadyImplicitBranch 0 = implicitBase := by
  exact
    @ContDiffAt.implicitFunction_apply_self
      ℝ inferInstance
      ℝ inferInstance inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace branchImplicitCompleteSpace
      BranchSpace BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace (meanZeroEvenRealWACompleteSpace 2)
      blownBase blownResidual 3
      blownResidual_contDiffAt (by norm_num)
      blownResidual_partial_isInvertible

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem eventually_blownResidual_minimalSteadyImplicitBranch :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      blownResidual (a, minimalSteadyImplicitBranch a) = 0 := by
  have h :=
    @ContDiffAt.eventually_apply_implicitFunction
      ℝ inferInstance
      ℝ inferInstance inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace branchImplicitCompleteSpace
      BranchSpace BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace (meanZeroEvenRealWACompleteSpace 2)
      blownBase blownResidual 3
      blownResidual_contDiffAt (by norm_num)
      blownResidual_partial_isInvertible
  simpa only [blownResidual_base] using h

set_option synthInstance.maxHeartbeats 1000000 in
theorem minimalSteadyImplicitBranch_contDiffAt :
    @ContDiffAt
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      3 minimalSteadyImplicitBranch 0 := by
  exact
    @ContDiffAt.contDiffAt_implicitFunction
      ℝ inferInstance
      ℝ inferInstance inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace branchImplicitCompleteSpace
      BranchSpace BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace (meanZeroEvenRealWACompleteSpace 2)
      blownBase blownResidual 3
      blownResidual_contDiffAt (by norm_num)
      blownResidual_partial_isInvertible

end ShenWork.M3Counterexample
