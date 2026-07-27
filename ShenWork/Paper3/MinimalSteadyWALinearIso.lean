import ShenWork.Paper3.MinimalSteadyWABlowup
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The nonsingular implicit-variable linearization

At the bifurcation point the profile part of the derivative is

`L = id - (1 + π²) R`.

Its only zero Fourier modes on the mean-zero even space are `±1`.  The
amplitude complement removes those modes, and the explicit reciprocal
multiplier below gives a bounded inverse.  The sensitivity direction supplies
the missing first-mode line, producing a continuous linear equivalence

`BranchComplement × ℝ ≃L[ℝ] BranchSpace`.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## The diagonal complement inverse -/

def isExceptionalMode (n : ℤ) : Prop :=
  n = 0 ∨ n = 1 ∨ n = -1

noncomputable instance isExceptionalModeDecidable (n : ℤ) :
    Decidable (isExceptionalMode n) :=
  Classical.propDecidable _

/-- Reciprocal of the critical linear multiplier, set to zero on `0,±1`. -/
def complementInverseRealSymbol (n : ℤ) : ℝ :=
  if isExceptionalMode n then 0
  else
    (1 + ((n : ℝ) * Real.pi) ^ 2) /
      (((n : ℝ) ^ 2 - 1) * Real.pi ^ 2)

def complementInverseSymbol (n : ℤ) : ℂ :=
  (complementInverseRealSymbol n : ℂ)

theorem four_le_intCast_sq_of_not_exceptional
    {n : ℤ} (hn : ¬isExceptionalMode n) :
    (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hn0 : n ≠ 0 := fun h => hn (Or.inl h)
  have hn1 : n ≠ 1 := fun h => hn (Or.inr (Or.inl h))
  have hnm1 : n ≠ -1 := fun h => hn (Or.inr (Or.inr h))
  by_cases hnonneg : 0 ≤ n
  · have htwoZ : (2 : ℤ) ≤ n := by omega
    have htwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast htwoZ
    nlinarith
  · have htwoZ : n ≤ (-2 : ℤ) := by omega
    have htwo : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast htwoZ
    nlinarith

theorem complementInverseRealSymbol_nonneg (n : ℤ) :
    0 ≤ complementInverseRealSymbol n := by
  rw [complementInverseRealSymbol]
  split_ifs with hn
  · exact le_rfl
  · have hn2 := four_le_intCast_sq_of_not_exceptional hn
    have hpi2 : 0 < Real.pi ^ 2 := by positivity
    have hden :
        0 < (((n : ℝ) ^ 2 - 1) * Real.pi ^ 2) := by
      have hx : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
      exact mul_pos hx hpi2
    exact div_nonneg (by positivity) hden.le

theorem complementInverseRealSymbol_le_two (n : ℤ) :
    complementInverseRealSymbol n ≤ 2 := by
  rw [complementInverseRealSymbol]
  split_ifs with hn
  · norm_num
  · have hn2 := four_le_intCast_sq_of_not_exceptional hn
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hpi2 : 9 < Real.pi ^ 2 := by nlinarith
    have hden :
        0 < (((n : ℝ) ^ 2 - 1) * Real.pi ^ 2) := by
      have hx : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
      exact mul_pos hx (by positivity)
    rw [div_le_iff₀ hden]
    have hsq :
        ((n : ℝ) * Real.pi) ^ 2 =
          (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
    rw [hsq]
    nlinarith

theorem complementInverseSymbol_norm_le_two (n : ℤ) :
    ‖complementInverseSymbol n‖ ≤ 2 := by
  rw [complementInverseSymbol, Complex.norm_real,
    Real.norm_of_nonneg (complementInverseRealSymbol_nonneg n)]
  exact complementInverseRealSymbol_le_two n

theorem complementInverseRealSymbol_neg (n : ℤ) :
    complementInverseRealSymbol (-n) =
      complementInverseRealSymbol n := by
  unfold complementInverseRealSymbol isExceptionalMode
  by_cases hn : n = 0 ∨ n = 1 ∨ n = -1
  · rw [if_pos hn, if_pos (by omega)]
  · rw [if_neg hn, if_neg (by omega)]
    push_cast
    ring

def complementInverseLM : WA 2 →ₗ[ℂ] WA 2 where
  toFun a := ⟨wMul complementInverseSymbol a.toFun,
    memW_wMul complementInverseSymbol_norm_le_two a.mem⟩
  map_add' a b := by
    apply WA.ext
    funext n
    simp [wMul]
    ring
  map_smul' c a := by
    apply WA.ext
    funext n
    simp [wMul]
    ring

def complementInverseAmbientCLM : WA 2 →L[ℂ] WA 2 :=
  complementInverseLM.mkContinuous 2 (fun a => by
    change
      wNorm 2 (wMul complementInverseSymbol a.toFun) ≤
        2 * wNorm 2 a.toFun
    exact wNorm_wMul_le (by norm_num)
      complementInverseSymbol_norm_le_two a.mem)

@[simp]
theorem complementInverseAmbientCLM_coeff (a : WA 2) (n : ℤ) :
    (complementInverseAmbientCLM a).toFun n =
      complementInverseSymbol n * a.toFun n :=
  rfl

/-- Inclusion of the first-mode complement into ambient `WA 2`. -/
def branchComplementAmbientCLM : BranchComplement →L[ℝ] WA 2 :=
  branchSpaceAmbientCLM.comp complementSubtypeCLM

def complementInverseFromComplementAmbientCLM :
    BranchComplement →L[ℝ] WA 2 :=
  (realifyWACLM complementInverseAmbientCLM).comp
    branchComplementAmbientCLM

theorem complementInverse_coeff_im_zero
    (z : BranchComplement) (n : ℤ) :
    ((complementInverseFromComplementAmbientCLM z).toFun n).im = 0 := by
  rw [complementInverseFromComplementAmbientCLM,
    ContinuousLinearMap.comp_apply, realifyWACLM_apply,
    complementInverseAmbientCLM_coeff]
  change
    (((complementInverseRealSymbol n : ℂ) *
      z.1.1.1.toFun n).im = 0)
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul]
  rw [EvenRealWA.coeff_im_eq_zero z.1.1 n]
  ring

theorem complementInverse_coeff_neg
    (z : BranchComplement) (n : ℤ) :
    (complementInverseFromComplementAmbientCLM z).toFun (-n) =
      (complementInverseFromComplementAmbientCLM z).toFun n := by
  rw [complementInverseFromComplementAmbientCLM,
    ContinuousLinearMap.comp_apply, realifyWACLM_apply,
    complementInverseAmbientCLM_coeff,
    complementInverseAmbientCLM_coeff]
  change
    (complementInverseRealSymbol (-n) : ℂ) *
        z.1.1.1.toFun (-n) =
      (complementInverseRealSymbol n : ℂ) * z.1.1.1.toFun n
  rw [complementInverseRealSymbol_neg,
    MeanZeroEvenRealWA.coeff_neg z.1 n]

def complementInverseEvenCLM :
    BranchComplement →L[ℝ] EvenRealWA 2 :=
  complementInverseFromComplementAmbientCLM.codRestrict
    (evenRealSubmodule 2) (fun z =>
      (mem_evenRealSubmodule_iff 2
        (complementInverseFromComplementAmbientCLM z)).mpr
          ⟨complementInverse_coeff_im_zero z,
            complementInverse_coeff_neg z⟩)

theorem complementInverse_zeroMode
    (z : BranchComplement) :
    ((complementInverseEvenCLM z).1.toFun 0).re = 0 := by
  change
    (complementInverseSymbol 0 * z.1.1.1.toFun 0).re = 0
  simp [complementInverseSymbol, complementInverseRealSymbol,
    isExceptionalMode]

def complementInverseMeanZeroCLM :
    BranchComplement →L[ℝ] BranchSpace :=
  complementInverseEvenCLM.codRestrict
    (meanZeroEvenRealSubmodule 2)
      complementInverse_zeroMode

theorem complementInverse_firstMode
    (z : BranchComplement) :
    ((complementInverseMeanZeroCLM z).1.1.toFun 1).re = 0 := by
  change
    (complementInverseSymbol 1 * z.1.1.1.toFun 1).re = 0
  simp [complementInverseSymbol, complementInverseRealSymbol,
    isExceptionalMode]

/-- The bounded reciprocal multiplier on the first-mode complement. -/
def complementInverseCLM :
    BranchComplement →L[ℝ] BranchComplement :=
  complementInverseMeanZeroCLM.codRestrict
    (firstComplementSubmodule 2)
      complementInverse_firstMode

@[simp]
theorem complementInverseCLM_coeff (z : BranchComplement) (n : ℤ) :
    (complementInverseCLM z).1.1.1.toFun n =
      complementInverseSymbol n * z.1.1.1.toFun n :=
  rfl

/-! ## The critical linear map on the complement -/

/-- `L = id - (1 + π²) R` on the mean-zero even branch space. -/
def criticalBranchCLM : BranchSpace →L[ℝ] BranchSpace :=
  ContinuousLinearMap.id ℝ BranchSpace -
    (1 + Real.pi ^ 2 : ℝ) • signalResolverCLM

@[simp]
theorem criticalBranchCLM_coeff (h : BranchSpace) (n : ℤ) :
    (criticalBranchCLM h).1.1.toFun n =
      (1 -
        (1 + Real.pi ^ 2) /
          (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) *
        h.1.1.toFun n := by
  change
    h.1.1.toFun n -
        (((1 + Real.pi ^ 2 : ℝ) : ℂ) *
          (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
            h.1.1.toFun n)) =
      (((1 -
        (1 + Real.pi ^ 2) /
          (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        h.1.1.toFun n)
  push_cast
  ring

theorem criticalBranch_mem_complement (z : BranchComplement) :
    criticalBranchCLM z.1 ∈ firstComplementSubmodule 2 := by
  rw [mem_firstComplementSubmodule_iff]
  rw [criticalBranchCLM_coeff, FirstComplementWA.coeff_one]
  simp

/-- The critical linear map restricted to the first-mode complement. -/
def criticalComplementCLM :
    BranchComplement →L[ℝ] BranchComplement :=
  (criticalBranchCLM.comp complementSubtypeCLM).codRestrict
    (firstComplementSubmodule 2) criticalBranch_mem_complement

@[simp]
theorem criticalComplementCLM_coeff (z : BranchComplement) (n : ℤ) :
    (criticalComplementCLM z).1.1.1.toFun n =
      (1 -
        (1 + Real.pi ^ 2) /
          (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) *
        z.1.1.1.toFun n :=
  criticalBranchCLM_coeff z.1 n

theorem critical_inverse_symbol_mul
    {n : ℤ} (hn : ¬isExceptionalMode n) :
    (1 -
        (1 + Real.pi ^ 2) /
          (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) *
      complementInverseRealSymbol n = 1 := by
  rw [complementInverseRealSymbol, if_neg hn]
  have hn2 := four_le_intCast_sq_of_not_exceptional hn
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  have hden1 :
      1 + ((n : ℝ) * Real.pi) ^ 2 ≠ 0 := by positivity
  have hden2 :
      ((n : ℝ) ^ 2 - 1) * Real.pi ^ 2 ≠ 0 := by
    have hx : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
    exact ne_of_gt (mul_pos hx hpi2)
  have hnm : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp : Real.pi ^ 2 ≠ 0 := ne_of_gt hpi2
  have hsq :
      ((n : ℝ) * Real.pi) ^ 2 =
        (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
  rw [hsq]
  field_simp [hnm, hp]
  ring

theorem criticalComplement_leftInverse :
    Function.LeftInverse complementInverseCLM criticalComplementCLM := by
  intro z
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply WA.ext
  funext n
  rw [complementInverseCLM_coeff, criticalComplementCLM_coeff]
  by_cases hn : isExceptionalMode n
  · rcases hn with rfl | rfl | rfl
    · simp [FirstComplementWA.coeff_zero]
    · simp [FirstComplementWA.coeff_one]
    · simp [FirstComplementWA.coeff_neg_one]
  · change
      (complementInverseRealSymbol n : ℂ) *
          (((1 -
            (1 + Real.pi ^ 2) /
              (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
            z.1.1.1.toFun n) =
        z.1.1.1.toFun n
    rw [← mul_assoc, ← Complex.ofReal_mul]
    have hreal :
        complementInverseRealSymbol n *
            (1 -
              (1 + Real.pi ^ 2) /
                (1 + ((n : ℝ) * Real.pi) ^ 2)) =
          1 := by
      rw [mul_comm]
      exact critical_inverse_symbol_mul hn
    rw [hreal]
    simp

theorem criticalComplement_rightInverse :
    Function.RightInverse complementInverseCLM criticalComplementCLM := by
  intro z
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply WA.ext
  funext n
  rw [criticalComplementCLM_coeff, complementInverseCLM_coeff]
  by_cases hn : isExceptionalMode n
  · rcases hn with rfl | rfl | rfl
    · simp [FirstComplementWA.coeff_zero]
    · simp [FirstComplementWA.coeff_one]
    · simp [FirstComplementWA.coeff_neg_one]
  · change
      (((1 -
          (1 + Real.pi ^ 2) /
            (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          ((complementInverseRealSymbol n : ℂ) *
            z.1.1.1.toFun n)) =
        z.1.1.1.toFun n
    rw [← mul_assoc, ← Complex.ofReal_mul,
      critical_inverse_symbol_mul hn]
    simp

/-- Diagonal equivalence on the complement. -/
def criticalComplementEquiv :
    BranchComplement ≃L[ℝ] BranchComplement :=
  ContinuousLinearEquiv.equivOfInverse criticalComplementCLM
    complementInverseCLM criticalComplement_leftInverse
      criticalComplement_rightInverse

/-! ## Add the sensitivity direction -/

def implicitCoordinateForwardCLM :
    BranchComplement × ℝ →L[ℝ] BranchComplement × ℝ :=
  criticalComplementCLM.comp
      (ContinuousLinearMap.fst ℝ BranchComplement ℝ) |>.prod
    (((-1 / minimalChiLin : ℝ) •
      ContinuousLinearMap.id ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ BranchComplement ℝ))

def implicitCoordinateInverseCLM :
    BranchComplement × ℝ →L[ℝ] BranchComplement × ℝ :=
  complementInverseCLM.comp
      (ContinuousLinearMap.fst ℝ BranchComplement ℝ) |>.prod
    (((-minimalChiLin : ℝ) •
      ContinuousLinearMap.id ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ BranchComplement ℝ))

@[simp]
theorem implicitCoordinateForwardCLM_apply
    (p : BranchComplement × ℝ) :
    implicitCoordinateForwardCLM p =
      (criticalComplementCLM p.1,
        (-1 / minimalChiLin) * p.2) :=
  rfl

@[simp]
theorem implicitCoordinateInverseCLM_apply
    (p : BranchComplement × ℝ) :
    implicitCoordinateInverseCLM p =
      (complementInverseCLM p.1,
        (-minimalChiLin) * p.2) :=
  rfl

theorem implicitCoordinate_leftInverse :
    Function.LeftInverse implicitCoordinateInverseCLM
      implicitCoordinateForwardCLM := by
  intro p
  apply Prod.ext
  · exact criticalComplement_leftInverse p.1
  · change (-minimalChiLin) * ((-1 / minimalChiLin) * p.2) = p.2
    have hχ : minimalChiLin ≠ 0 := ne_of_gt minimalChiLin_pos
    field_simp

theorem implicitCoordinate_rightInverse :
    Function.RightInverse implicitCoordinateInverseCLM
      implicitCoordinateForwardCLM := by
  intro p
  apply Prod.ext
  · exact criticalComplement_rightInverse p.1
  · change (-1 / minimalChiLin) * ((-minimalChiLin) * p.2) = p.2
    have hχ : minimalChiLin ≠ 0 := ne_of_gt minimalChiLin_pos
    field_simp

def implicitCoordinateEquiv :
    (BranchComplement × ℝ) ≃L[ℝ] (BranchComplement × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse implicitCoordinateForwardCLM
    implicitCoordinateInverseCLM implicitCoordinate_leftInverse
      implicitCoordinate_rightInverse

/-- The exact implicit-variable derivative equivalence. -/
def implicitLinearEquiv :
    (BranchComplement × ℝ) ≃L[ℝ] BranchSpace :=
  implicitCoordinateEquiv.trans branchCoordinates

@[simp]
theorem implicitLinearEquiv_apply (p : BranchComplement × ℝ) :
    implicitLinearEquiv p =
      (criticalComplementCLM p.1).1 -
        (p.2 / minimalChiLin) • firstModeMeanZero 2 := by
  change
    branchCoordinates (implicitCoordinateForwardCLM p) =
      (criticalComplementCLM p.1).1 -
        (p.2 / minimalChiLin) • firstModeMeanZero 2
  rw [branchCoordinates_apply, implicitCoordinateForwardCLM_apply]
  change
    (criticalComplementCLM p.1).1 +
        ((-1 / minimalChiLin) * p.2) • firstModeMeanZero 2 =
      (criticalComplementCLM p.1).1 -
        (p.2 / minimalChiLin) • firstModeMeanZero 2
  rw [sub_eq_add_neg]
  congr 1
  have hχ : minimalChiLin ≠ 0 := ne_of_gt minimalChiLin_pos
  field_simp [hχ]
  module

end ShenWork.M3Counterexample
