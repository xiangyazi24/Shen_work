import ShenWork.Paper3.StaticWANeumann
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# First-mode projection and amplitude coordinates

The bilateral coefficient of `cos (π x)` is `1 / 2` at mode `1`.  Therefore
the physical cosine amplitude of `x : BranchSpace` is twice the real part of
its first bilateral coefficient.  Removing this multiple of the first mode
lands continuously in `BranchComplement`.

The resulting maps give the explicit Banach-space equivalence

`BranchComplement × ℝ ≃L[ℝ] BranchSpace`.
-/

noncomputable section

namespace ShenWork.M3Counterexample

/-! ## Amplitude and projection -/

/-- Physical first-cosine amplitude: twice the bilateral coefficient at `1`. -/
def amplitudeCLM : BranchSpace →L[ℝ] ℝ :=
  (2 : ℝ) • meanZeroCoeffCLM 2 1

@[simp]
theorem amplitudeCLM_apply (x : BranchSpace) :
    amplitudeCLM x = 2 * (x.1.1.toFun 1).re := by
  rfl

@[simp]
theorem amplitude_firstMode :
    amplitudeCLM (firstModeMeanZero 2) = 1 := by
  norm_num [amplitudeCLM_apply, firstModeMeanZero_coeff_one_re]

/-- The first-mode line component of a mean-zero profile. -/
def firstLineCLM : BranchSpace →L[ℝ] BranchSpace :=
  amplitudeCLM.smulRight (firstModeMeanZero 2)

@[simp]
theorem firstLineCLM_apply (x : BranchSpace) :
    firstLineCLM x = amplitudeCLM x • firstModeMeanZero 2 :=
  rfl

/-- Remove the first cosine mode, still viewed in the ambient mean-zero space. -/
def removeFirstCLM : BranchSpace →L[ℝ] BranchSpace :=
  ContinuousLinearMap.id ℝ BranchSpace - firstLineCLM

@[simp]
theorem removeFirstCLM_apply (x : BranchSpace) :
    removeFirstCLM x = x - amplitudeCLM x • firstModeMeanZero 2 := by
  rfl

theorem removeFirst_mem_complement (x : BranchSpace) :
    removeFirstCLM x ∈ firstComplementSubmodule 2 := by
  rw [mem_firstComplementSubmodule_iff]
  change
    (x.1.1.toFun 1 -
      ((amplitudeCLM x : ℂ) * (firstModeMeanZero 2).1.1.toFun 1)).re = 0
  rw [Complex.sub_re, Complex.mul_re]
  have him : ((amplitudeCLM x : ℂ)).im = 0 := by simp
  have hphiIm : ((firstModeMeanZero 2).1.1.toFun 1).im = 0 :=
    MeanZeroEvenRealWA.coeff_im_eq_zero (firstModeMeanZero 2) 1
  rw [him, hphiIm, zero_mul, sub_zero]
  rw [amplitudeCLM_apply, firstModeMeanZero_coeff_one_re]
  norm_num
  ring

/-- Continuous projection from the ambient mean-zero space to the first-mode
complement. -/
def complementProjectionCLM : BranchSpace →L[ℝ] BranchComplement :=
  removeFirstCLM.codRestrict (firstComplementSubmodule 2) removeFirst_mem_complement

@[simp]
theorem complementProjectionCLM_coe (x : BranchSpace) :
    (complementProjectionCLM x : BranchSpace) = removeFirstCLM x :=
  rfl

@[simp]
theorem amplitude_complement (z : BranchComplement) :
    amplitudeCLM z.1 = 0 := by
  rw [amplitudeCLM_apply]
  have hz := (mem_firstComplementSubmodule_iff 2 z.1).mp z.2
  rw [hz]
  ring

@[simp]
theorem complementProjection_complement (z : BranchComplement) :
    complementProjectionCLM z.1 = z := by
  apply Subtype.ext
  rw [complementProjectionCLM_coe, removeFirstCLM_apply,
    amplitude_complement, zero_smul, sub_zero]

@[simp]
theorem complementProjection_firstMode :
    complementProjectionCLM (firstModeMeanZero 2) = 0 := by
  apply Subtype.ext
  rw [complementProjectionCLM_coe, removeFirstCLM_apply,
    amplitude_firstMode, one_smul, sub_self]
  rfl

theorem branch_decomposition (x : BranchSpace) :
    (complementProjectionCLM x : BranchSpace) +
        amplitudeCLM x • firstModeMeanZero 2 = x := by
  rw [complementProjectionCLM_coe, removeFirstCLM_apply]
  abel

/-! ## Product coordinates -/

/-- Inclusion of the complement in the ambient branch space. -/
def complementSubtypeCLM : BranchComplement →L[ℝ] BranchSpace :=
  (firstComplementSubmodule 2).subtypeL

/-- The map `a ↦ a • cos (π x)`. -/
def scalarFirstModeCLM : ℝ →L[ℝ] BranchSpace :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (firstModeMeanZero 2)

/-- Assemble complement and amplitude coordinates. -/
def assembleBranchCLM : BranchComplement × ℝ →L[ℝ] BranchSpace :=
  complementSubtypeCLM.comp
      (ContinuousLinearMap.fst ℝ BranchComplement ℝ) +
    scalarFirstModeCLM.comp
      (ContinuousLinearMap.snd ℝ BranchComplement ℝ)

@[simp]
theorem assembleBranchCLM_apply (p : BranchComplement × ℝ) :
    assembleBranchCLM p = p.1.1 + p.2 • firstModeMeanZero 2 := by
  rfl

/-- Split an ambient profile into complement and physical amplitude. -/
def splitBranchCLM : BranchSpace →L[ℝ] BranchComplement × ℝ :=
  complementProjectionCLM.prod amplitudeCLM

@[simp]
theorem splitBranchCLM_apply (x : BranchSpace) :
    splitBranchCLM x = (complementProjectionCLM x, amplitudeCLM x) :=
  rfl

@[simp]
theorem amplitude_assemble (p : BranchComplement × ℝ) :
    amplitudeCLM (assembleBranchCLM p) = p.2 := by
  rw [assembleBranchCLM_apply, map_add, map_smul,
    amplitude_complement, amplitude_firstMode, smul_eq_mul]
  ring

@[simp]
theorem projection_assemble (p : BranchComplement × ℝ) :
    complementProjectionCLM (assembleBranchCLM p) = p.1 := by
  apply Subtype.ext
  rw [complementProjectionCLM_coe, removeFirstCLM_apply,
    amplitude_assemble, assembleBranchCLM_apply]
  abel

theorem split_assemble_leftInverse :
    Function.LeftInverse splitBranchCLM assembleBranchCLM := by
  intro p
  apply Prod.ext
  · exact projection_assemble p
  · exact amplitude_assemble p

theorem assemble_split_rightInverse :
    Function.RightInverse splitBranchCLM assembleBranchCLM := by
  intro x
  rw [splitBranchCLM_apply, assembleBranchCLM_apply]
  exact branch_decomposition x

/-- Explicit amplitude/complement coordinates on the branch space. -/
def branchCoordinates :
    (BranchComplement × ℝ) ≃L[ℝ] BranchSpace :=
  ContinuousLinearEquiv.equivOfInverse assembleBranchCLM splitBranchCLM
    split_assemble_leftInverse assemble_split_rightInverse

@[simp]
theorem branchCoordinates_apply (p : BranchComplement × ℝ) :
    branchCoordinates p = p.1.1 + p.2 • firstModeMeanZero 2 :=
  rfl

@[simp]
theorem branchCoordinates_symm_apply (x : BranchSpace) :
    branchCoordinates.symm x =
      (complementProjectionCLM x, amplitudeCLM x) :=
  rfl

end ShenWork.M3Counterexample
