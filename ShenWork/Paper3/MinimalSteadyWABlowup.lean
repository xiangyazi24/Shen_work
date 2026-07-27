import ShenWork.Paper3.StaticWAParityProjection
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The amplitude-blown-up steady residual for the fixed `m = 3` tuple

We fix

`m = 3`, `β = γ = μ = ν = U = 1`

and use amplitude/complement coordinates

`h = cos (π x) + z`, `z ∈ BranchComplement`.

The residual below is defined for every amplitude, complement profile, and
sensitivity by the total ring inverse.  At the bifurcation base point its
denominator is the unit `2`, so the residual is `C³` there.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## Fixed coordinates and constants -/

/-- Complement profile and sensitivity, packaged with canonical product
instances to avoid instance diamonds from the nested closed subspaces. -/
@[reducible]
def BranchImplicit := BranchComplement × ℝ

noncomputable instance branchImplicitAddCommGroup :
    AddCommGroup BranchImplicit :=
  @Prod.instAddCommGroup BranchComplement ℝ
    BranchComplement.addCommGroup inferInstance

noncomputable instance branchImplicitNormedAddCommGroup :
    NormedAddCommGroup BranchImplicit :=
  inferInstanceAs
    (NormedAddCommGroup (BranchComplement × ℝ))

noncomputable instance branchImplicitNormedSpace :
    NormedSpace ℝ BranchImplicit :=
  @Prod.normedSpace ℝ BranchComplement ℝ _ _ _
    BranchComplement.normedSpace
    (inferInstanceAs (NormedSpace ℝ ℝ))

noncomputable instance branchImplicitCompleteSpace :
    CompleteSpace BranchImplicit :=
  @CompleteSpace.prod BranchComplement ℝ _ _
    (firstComplementWACompleteSpace 2) inferInstance

/-- Amplitude, complement profile, and sensitivity. -/
def BranchVariables := ℝ × BranchImplicit

noncomputable instance branchVariablesNormedAddCommGroup :
    NormedAddCommGroup BranchVariables :=
  inferInstanceAs
    (NormedAddCommGroup (ℝ × BranchImplicit))

noncomputable instance branchVariablesNormedSpace :
    NormedSpace ℝ BranchVariables :=
  @Prod.normedSpace ℝ ℝ BranchImplicit _ _ _
    (inferInstanceAs (NormedSpace ℝ ℝ))
    branchImplicitNormedSpace

/-- The exact first-mode linear threshold for the fixed tuple. -/
def minimalChiLin : ℝ :=
  2 * (1 + Real.pi ^ 2)

theorem minimalChiLin_pos : 0 < minimalChiLin := by
  unfold minimalChiLin
  positivity

def branchAmplitudeCLM : BranchVariables →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ BranchImplicit

def branchComplementCLM : BranchVariables →L[ℝ] BranchComplement :=
  (ContinuousLinearMap.fst ℝ BranchComplement ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ BranchImplicit)

def branchSensitivityCLM : BranchVariables →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ BranchComplement ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ BranchImplicit)

@[simp]
theorem branchAmplitudeCLM_apply (p : BranchVariables) :
    branchAmplitudeCLM p = p.1 :=
  rfl

@[simp]
theorem branchComplementCLM_apply (p : BranchVariables) :
    branchComplementCLM p = p.2.1 :=
  rfl

@[simp]
theorem branchSensitivityCLM_apply (p : BranchVariables) :
    branchSensitivityCLM p = p.2.2 :=
  rfl

/-- Inclusion of the fixed branch space into the ambient real normed algebra. -/
def branchSpaceAmbientCLM : BranchSpace →L[ℝ] WA 2 :=
  (evenRealSubmodule 2).subtypeL.comp
    (meanZeroEvenRealSubmodule 2).subtypeL

@[simp]
theorem branchSpaceAmbientCLM_apply (h : BranchSpace) :
    branchSpaceAmbientCLM h = h.1.1 :=
  rfl

@[simp]
theorem branchSpace_smul_coeff (c : ℝ) (h : BranchSpace) (n : ℤ) :
    (c • h).1.1.toFun n = (c : ℂ) * h.1.1.toFun n :=
  rfl

/-- The normalized profile `h = cos (π x) + z`. -/
def blownProfileLinearCLM : BranchVariables →L[ℝ] BranchSpace :=
  complementSubtypeCLM.comp branchComplementCLM

/-- The normalized profile `h = cos (π x) + z`. -/
def blownProfile (p : BranchVariables) : BranchSpace :=
  firstModeMeanZero 2 + blownProfileLinearCLM p

@[simp]
theorem blownProfile_apply (p : BranchVariables) :
    blownProfile p =
      firstModeMeanZero 2 + p.2.1.1 :=
  rfl

/-- The differentiated resolver with its odd subtype forgotten. -/
def branchDerivResolverAmbientCLM : BranchSpace →L[ℝ] WA 2 :=
  (oddImagSubmodule 2).subtypeL.comp branchDerivResolverCLM

/-- Resolve the signal and include it in the ambient algebra. -/
def signalResolverAmbientCLM : BranchSpace →L[ℝ] WA 2 :=
  branchSpaceAmbientCLM.comp signalResolverCLM

/-- The IFT base point `(a,z,χ) = (0,0,χlin)`. -/
def blownBase : BranchVariables :=
  (0, (0, minimalChiLin))

@[simp]
theorem blownProfile_base :
    blownProfile blownBase = firstModeMeanZero 2 := by
  change
    firstModeMeanZero 2 +
        complementSubtypeCLM (0 : BranchComplement) =
      firstModeMeanZero 2
  have hz : complementSubtypeCLM (0 : BranchComplement) = 0 := by
    apply Subtype.ext
    rfl
  rw [hz, add_zero]

/-! ## Ambient nonlinear factors -/

/-- Population factor `1 + a h`. -/
def blownPopulation (p : BranchVariables) : WA 2 :=
  1 + branchAmplitudeCLM p • branchSpaceAmbientCLM (blownProfile p)

/-- Signal denominator `2 + a R h`. -/
def blownDenominator (p : BranchVariables) : WA 2 :=
  (2 : ℝ) • (1 : WA 2) +
    branchAmplitudeCLM p •
      branchSpaceAmbientCLM (signalResolverCLM (blownProfile p))

/-- Cubic mobility factor `(1 + a h)³ (2 + a R h)⁻¹`. -/
def blownMobility (p : BranchVariables) : WA 2 :=
  blownPopulation p ^ 3 * Ring.inverse (blownDenominator p)

/-- The ambient odd flux before applying the parity projector. -/
def blownRawFlux (p : BranchVariables) : WA 2 :=
  blownMobility p * branchDerivResolverAmbientCLM (blownProfile p)

/-- Project the ambient formula continuously into the odd-imaginary space. -/
def blownFlux (p : BranchVariables) : OddImagWA 2 :=
  oddImagProjectionCLM 2 (blownRawFlux p)

/-- Project an ambient flux to the odd space and integrate it once. -/
def projectedInverseDerivativeCLM : WA 2 →L[ℝ] BranchSpace :=
  inverseDerivativeCLM.comp (oddImagProjectionCLM 2)

/-- The globally defined amplitude-blown-up residual. -/
def blownResidual (p : BranchVariables) : BranchSpace :=
  blownProfile p -
    branchSensitivityCLM p •
      projectedInverseDerivativeCLM (blownRawFlux p)

/-! ## The ambient flux really has the required parity -/

theorem one_mem_evenReal (r : ℕ) :
    (1 : WA r) ∈ evenRealSubmodule r := by
  rw [evenReal_iff_fixed]
  exact ⟨waRefl_one, waConj_one⟩

def blownPopulationEvenReal (p : BranchVariables) : EvenRealWA 2 :=
  ⟨blownPopulation p, by
    exact (evenRealSubmodule 2).add_mem (one_mem_evenReal 2)
      ((evenRealSubmodule 2).smul_mem (branchAmplitudeCLM p)
        (blownProfile p).1.2)⟩

def blownDenominatorEvenReal (p : BranchVariables) : EvenRealWA 2 :=
  ⟨blownDenominator p, by
    exact (evenRealSubmodule 2).add_mem
      ((evenRealSubmodule 2).smul_mem (2 : ℝ) (one_mem_evenReal 2))
      ((evenRealSubmodule 2).smul_mem (branchAmplitudeCLM p)
        (signalResolverCLM (blownProfile p)).1.2)⟩

def blownInverseDenominatorEvenReal (p : BranchVariables) : EvenRealWA 2 :=
  ⟨Ring.inverse (blownDenominator p),
    ringInverse_mem_evenReal (blownDenominatorEvenReal p)⟩

def blownPopulationSqEvenReal (p : BranchVariables) : EvenRealWA 2 :=
  evenRealMul (blownPopulationEvenReal p) (blownPopulationEvenReal p)

def blownPopulationCubeEvenReal (p : BranchVariables) : EvenRealWA 2 :=
  evenRealMul (blownPopulationSqEvenReal p) (blownPopulationEvenReal p)

def blownMobilityEvenReal (p : BranchVariables) : EvenRealWA 2 :=
  evenRealMul (blownPopulationCubeEvenReal p)
    (blownInverseDenominatorEvenReal p)

def blownRawFluxOddImag (p : BranchVariables) : OddImagWA 2 :=
  evenOddMul (blownMobilityEvenReal p)
    (branchDerivResolverCLM (blownProfile p))

@[simp]
theorem blownPopulationEvenReal_coe (p : BranchVariables) :
    (blownPopulationEvenReal p : WA 2) = blownPopulation p :=
  rfl

@[simp]
theorem blownDenominatorEvenReal_coe (p : BranchVariables) :
    (blownDenominatorEvenReal p : WA 2) = blownDenominator p :=
  rfl

@[simp]
theorem blownMobilityEvenReal_coe (p : BranchVariables) :
    (blownMobilityEvenReal p : WA 2) = blownMobility p := by
  change
    ((blownPopulation p * blownPopulation p) * blownPopulation p) *
        Ring.inverse (blownDenominator p) =
      blownPopulation p ^ 3 * Ring.inverse (blownDenominator p)
  ring

@[simp]
theorem blownRawFluxOddImag_coe (p : BranchVariables) :
    (blownRawFluxOddImag p : WA 2) = blownRawFlux p := by
  change
    (blownMobilityEvenReal p : WA 2) *
        (branchDerivResolverCLM (blownProfile p)).1 =
      blownRawFlux p
  rw [blownMobilityEvenReal_coe]
  rfl

theorem blownFlux_eq_raw (p : BranchVariables) :
    blownFlux p = blownRawFluxOddImag p := by
  rw [blownFlux, ← blownRawFluxOddImag_coe,
    oddImagProjection_eq_self]

/-! ## Exact base value -/

theorem isUnit_two_smul_one :
    IsUnit ((2 : ℝ) • (1 : WA 2)) := by
  have h :=
    IsUnit.smul (Units.mk0 (2 : ℝ) (by norm_num)) (isUnit_one : IsUnit (1 : WA 2))
  simpa using h

theorem ringInverse_two_smul_one :
    Ring.inverse ((2 : ℝ) • (1 : WA 2)) =
      (1 / 2 : ℝ) • (1 : WA 2) := by
  symm
  rw [← one_mul (Ring.inverse ((2 : ℝ) • (1 : WA 2)))]
  apply (Ring.eq_mul_inverse_iff_mul_eq
    ((1 / 2 : ℝ) • (1 : WA 2)) 1
      ((2 : ℝ) • (1 : WA 2)) isUnit_two_smul_one).mpr
  change
    (((1 / 2 : ℝ) : ℂ) • (1 : WA 2)) *
        (((2 : ℝ) : ℂ) • (1 : WA 2)) =
      1
  rw [smul_mul_smul, one_mul]
  norm_num

@[simp]
theorem blownPopulation_base :
    blownPopulation blownBase = 1 := by
  simp [blownPopulation, blownBase]

@[simp]
theorem blownDenominator_base :
    blownDenominator blownBase = (2 : ℝ) • (1 : WA 2) := by
  simp [blownDenominator, blownBase]

theorem inverseDerivative_firstModeDerivResolver :
    inverseDerivativeCLM
        (branchDerivResolverCLM (firstModeMeanZero 2)) =
      (1 / (1 + Real.pi ^ 2) : ℝ) • firstModeMeanZero 2 := by
  rw [inverseDerivative_branchDerivResolver]
  apply Subtype.ext
  apply Subtype.ext
  apply WA.ext
  funext n
  rw [signalResolverCLM_coeff]
  by_cases hn : n = 1 ∨ n = -1
  · have hnSq : ((n : ℝ) * Real.pi) ^ 2 = Real.pi ^ 2 := by
      rcases hn with rfl | rfl <;> norm_num
    rw [hnSq]
    change
      (((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) *
          firstModeSeq n) =
        (((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) *
          firstModeSeq n)
    rfl
  · rw [show (firstModeMeanZero 2).1.1.toFun n = 0 by
      exact if_neg hn]
    rw [branchSpace_smul_coeff]
    change
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) * 0 =
        (((1 / (1 + Real.pi ^ 2) : ℝ) : ℂ) * firstModeSeq n)
    rw [show firstModeSeq n = 0 by exact if_neg hn]
    simp

theorem blownResidual_base :
    blownResidual blownBase = 0 := by
  rw [blownResidual, blownProfile_base]
  change
    firstModeMeanZero 2 -
        branchSensitivityCLM blownBase •
          inverseDerivativeCLM (blownFlux blownBase) =
      0
  have hflux :
      blownFlux blownBase =
        (1 / 2 : ℝ) •
          branchDerivResolverCLM (firstModeMeanZero 2) := by
    rw [blownFlux_eq_raw]
    apply Subtype.ext
    rw [blownRawFluxOddImag_coe]
    change
      blownMobility blownBase *
          (branchDerivResolverCLM (blownProfile blownBase)).1 =
        (((1 / 2 : ℝ) : ℂ) •
          (branchDerivResolverCLM (firstModeMeanZero 2)).1)
    rw [blownMobility, blownPopulation_base, one_pow,
      blownDenominator_base, ringInverse_two_smul_one, one_mul,
      blownProfile_base]
    change
      (((1 / 2 : ℝ) : ℂ) • (1 : WA 2)) *
          (branchDerivResolverCLM (firstModeMeanZero 2)).1 =
        (((1 / 2 : ℝ) : ℂ) •
          (branchDerivResolverCLM (firstModeMeanZero 2)).1)
    rw [smul_mul_assoc, one_mul]
  rw [hflux, map_smul, inverseDerivative_firstModeDerivResolver]
  simp only [blownBase, branchSensitivityCLM_apply]
  change
    firstModeMeanZero 2 -
        minimalChiLin •
          ((1 / 2 : ℝ) •
            ((1 / (1 + Real.pi ^ 2) : ℝ) •
              firstModeMeanZero 2)) =
      0
  rw [← mul_smul, ← mul_smul]
  have hden : 1 + Real.pi ^ 2 ≠ 0 := by positivity
  unfold minimalChiLin
  field_simp
  simp

/-! ## `C³` regularity at the bifurcation point -/

theorem contDiffAt_ringInverse_comp
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A]
    {f : E → A} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) (hu : IsUnit (f x)) :
    ContDiffAt ℝ n (fun y => Ring.inverse (f y)) x := by
  rcases hu with ⟨u, hu⟩
  have hi : ContDiffAt ℝ n Ring.inverse (f x) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  simpa only [Function.comp_apply] using hi.comp x hf

theorem blownProfile_contDiff :
    ContDiff ℝ 3 blownProfile := by
  have hl : ContDiff ℝ 3 blownProfileLinearCLM :=
    @ContinuousLinearMap.contDiff ℝ BranchVariables BranchSpace
      inferInstance branchVariablesNormedAddCommGroup
      branchVariablesNormedSpace BranchSpace.normedAddCommGroup
      BranchSpace.normedSpace 3 blownProfileLinearCLM
  simpa only [blownProfile] using
    (contDiff_const.add hl)

theorem blownPopulation_contDiff :
    ContDiff ℝ 3 blownPopulation := by
  have ha : ContDiff ℝ 3 branchAmplitudeCLM :=
    @ContinuousLinearMap.contDiff ℝ BranchVariables ℝ
      inferInstance branchVariablesNormedAddCommGroup
      branchVariablesNormedSpace inferInstance inferInstance
      3 branchAmplitudeCLM
  have hamb :
      ContDiff ℝ 3 (fun p =>
        branchSpaceAmbientCLM (blownProfile p)) := by
    have hi :=
      @ContinuousLinearMap.contDiff ℝ BranchSpace (WA 2)
        inferInstance BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace inferInstance inferInstance
        3 branchSpaceAmbientCLM
    simpa only [Function.comp_apply] using
      hi.comp blownProfile_contDiff
  simpa only [blownPopulation] using
    (contDiff_const.add (ha.smul hamb))

theorem blownDenominator_contDiff :
    ContDiff ℝ 3 blownDenominator := by
  have ha : ContDiff ℝ 3 branchAmplitudeCLM :=
    @ContinuousLinearMap.contDiff ℝ BranchVariables ℝ
      inferInstance branchVariablesNormedAddCommGroup
      branchVariablesNormedSpace inferInstance inferInstance
      3 branchAmplitudeCLM
  have hresolve :
      ContDiff ℝ 3 (fun p =>
        signalResolverAmbientCLM (blownProfile p)) := by
    have hi :=
      @ContinuousLinearMap.contDiff ℝ BranchSpace (WA 2)
        inferInstance BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace inferInstance inferInstance
        3 signalResolverAmbientCLM
    simpa only [Function.comp_apply] using
      hi.comp blownProfile_contDiff
  simpa only [blownDenominator, signalResolverAmbientCLM,
    ContinuousLinearMap.comp_apply] using
      (contDiff_const.add (ha.smul hresolve))

theorem blownInverseDenominator_contDiffAt :
    ContDiffAt ℝ 3 (fun p => Ring.inverse (blownDenominator p))
      blownBase := by
  apply contDiffAt_ringInverse_comp blownDenominator_contDiff.contDiffAt
  rw [blownDenominator_base]
  exact isUnit_two_smul_one

theorem blownRawFlux_contDiffAt :
    ContDiffAt ℝ 3 blownRawFlux blownBase := by
  have hderiv :
      ContDiff ℝ 3 (fun p =>
        branchDerivResolverAmbientCLM (blownProfile p)) := by
    have hi :=
      @ContinuousLinearMap.contDiff ℝ BranchSpace (WA 2)
        inferInstance BranchSpace.normedAddCommGroup
        BranchSpace.normedSpace inferInstance inferInstance
        3 branchDerivResolverAmbientCLM
    simpa only [Function.comp_apply] using
      hi.comp blownProfile_contDiff
  unfold blownRawFlux blownMobility
  exact
    ((blownPopulation_contDiff.contDiffAt.pow 3).mul
      blownInverseDenominator_contDiffAt).mul
        hderiv.contDiffAt

theorem blownFlux_contDiffAt :
    ContDiffAt ℝ 3 blownFlux blownBase := by
  have hi :=
    @ContinuousLinearMap.contDiff ℝ (WA 2) (OddImagWA 2)
      inferInstance inferInstance inferInstance
      (OddImagWA 2).normedAddCommGroup
      (OddImagWA 2).normedSpace 3 (oddImagProjectionCLM 2)
  simpa only [blownFlux, Function.comp_apply] using
    hi.contDiffAt.comp blownBase blownRawFlux_contDiffAt

theorem blownResidual_contDiffAt :
    ContDiffAt ℝ 3 blownResidual blownBase := by
  have hchi : ContDiff ℝ 3 branchSensitivityCLM :=
    @ContinuousLinearMap.contDiff ℝ BranchVariables ℝ
      inferInstance branchVariablesNormedAddCommGroup
      branchVariablesNormedSpace inferInstance inferInstance
      3 branchSensitivityCLM
  have hintegrated :
      ContDiffAt ℝ 3
        (fun p => projectedInverseDerivativeCLM (blownRawFlux p))
        blownBase := by
    have hi :=
      @ContinuousLinearMap.contDiff ℝ (WA 2) BranchSpace
        inferInstance inferInstance inferInstance
        BranchSpace.normedAddCommGroup BranchSpace.normedSpace
        3 projectedInverseDerivativeCLM
    simpa only [Function.comp_apply] using
      hi.contDiffAt.comp blownBase blownRawFlux_contDiffAt
  unfold blownResidual
  exact blownProfile_contDiff.contDiffAt.sub
    (hchi.contDiffAt.smul hintegrated)

end ShenWork.M3Counterexample
