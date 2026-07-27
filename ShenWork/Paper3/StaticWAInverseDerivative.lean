import ShenWork.Paper3.StaticWAProjections
import ShenWork.Wiener.WeightedL1Resolver

/-!
# Static resolver and inverse differentiation

For the fixed signal parameters `μ = ν = 1`, the Neumann resolver and its
derivative are diagonal multipliers

`R_n = 1 / (1 + (nπ)²)`,

`(DR)_n = i n π / (1 + (nπ)²)`.

This file bundles those multipliers as continuous maps on `WA r`, restricts
them to the real parity spaces, and constructs inverse differentiation on the
zero-mode-free odd space.  The key exact identity is

`D₀⁻¹ (D R h) = R h`

for every mean-zero even-real profile `h`.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## Real restriction of a complex continuous linear map -/

/-- Regard a complex-linear map between historical `WA` spaces as real-linear.
This direct wrapper avoids requiring an unavailable scalar-tower instance for
the repository's custom `WA` scalar action. -/
def realifyWACLM {r s : ℕ} (f : WA r →L[ℂ] WA s) : WA r →L[ℝ] WA s where
  toFun := f
  map_add' := f.map_add
  map_smul' c a := by
    change f ((c : ℂ) • a) = (c : ℂ) • f a
    exact f.map_smul (c : ℂ) a
  cont := f.continuous

@[simp]
theorem realifyWACLM_apply {r s : ℕ} (f : WA r →L[ℂ] WA s) (a : WA r) :
    realifyWACLM f a = f a :=
  rfl

/-! ## The fixed elliptic resolver -/

/-- The fixed-parameter resolver `(-∂ₓₓ + 1)⁻¹` on `WA r`. -/
def resolverLM (r : ℕ) : WA r →ₗ[ℂ] WA r where
  toFun a := ⟨resolverMul 1 a.toFun, memW_resolverMul one_pos a.mem⟩
  map_add' a b := by
    apply WA.ext
    funext n
    simp [resolverMul, wMul]
    ring
  map_smul' c a := by
    apply WA.ext
    funext n
    simp [resolverMul, wMul]
    ring

/-- The fixed resolver is a contraction in every `WA r`. -/
def resolverCLM (r : ℕ) : WA r →L[ℂ] WA r :=
  (resolverLM r).mkContinuous 1 (fun a => by
    change wNorm r (resolverMul 1 a.toFun) ≤ 1 * wNorm r a.toFun
    simpa using resolverMul_bound (r := r) (a := a.toFun) one_pos a.mem)

@[simp]
theorem resolverCLM_coeff (r : ℕ) (a : WA r) (n : ℤ) :
    (resolverCLM r a).toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) * a.toFun n :=
  rfl

theorem resolver_coeff_im_zero_of_evenReal (r : ℕ) (a : EvenRealWA r) (n : ℤ) :
    ((resolverCLM r a.1).toFun n).im = 0 := by
  let s : ℝ := 1 / (1 + ((n : ℝ) * Real.pi) ^ 2)
  change (((s : ℂ) * a.1.toFun n).im = 0)
  rw [Complex.mul_im]
  have ha := EvenRealWA.coeff_im_eq_zero a n
  simp [ha]

theorem resolver_coeff_neg_of_evenReal (r : ℕ) (a : EvenRealWA r) (n : ℤ) :
    (resolverCLM r a.1).toFun (-n) = (resolverCLM r a.1).toFun n := by
  rw [resolverCLM_coeff, resolverCLM_coeff, EvenRealWA.coeff_neg a n]
  congr 1
  push_cast
  ring

/-- The resolver restricted to even-real coefficients. -/
def resolverEvenRealCLM (r : ℕ) : EvenRealWA r →L[ℝ] EvenRealWA r :=
  ((realifyWACLM (resolverCLM r)).comp (evenRealSubmodule r).subtypeL).codRestrict
    (evenRealSubmodule r) (fun a =>
      (mem_evenRealSubmodule_iff r (resolverCLM r a.1)).mpr
        ⟨resolver_coeff_im_zero_of_evenReal r a,
          resolver_coeff_neg_of_evenReal r a⟩)

@[simp]
theorem resolverEvenRealCLM_coe (r : ℕ) (a : EvenRealWA r) :
    (resolverEvenRealCLM r a : WA r) = resolverCLM r a.1 :=
  rfl

theorem resolver_meanZero_mem (r : ℕ) (a : MeanZeroEvenRealWA r) :
    resolverEvenRealCLM r a.1 ∈ meanZeroEvenRealSubmodule r := by
  rw [mem_meanZeroEvenRealSubmodule_iff]
  have hzero := MeanZeroEvenRealWA.coeff_zero a
  change
    (((1 / (1 + (((0 : ℤ) : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
      a.1.1.toFun 0).re = 0
  rw [hzero, mul_zero]
  rfl

/-- The resolver restricted to the mean-zero even-real space. -/
def resolverMeanZeroCLM (r : ℕ) :
    MeanZeroEvenRealWA r →L[ℝ] MeanZeroEvenRealWA r :=
  ((resolverEvenRealCLM r).comp (meanZeroEvenRealSubmodule r).subtypeL).codRestrict
    (meanZeroEvenRealSubmodule r) (resolver_meanZero_mem r)

@[simp]
theorem resolverMeanZeroCLM_coeff (r : ℕ) (a : MeanZeroEvenRealWA r) (n : ℤ) :
    (resolverMeanZeroCLM r a).1.1.toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        a.1.1.toFun n :=
  rfl

/-- Signal resolver on the fixed branch space. -/
abbrev signalResolverCLM : BranchSpace →L[ℝ] BranchSpace :=
  resolverMeanZeroCLM 2

/-! ## Derivative of the resolver -/

/-- The fixed derivative-resolver on `WA r`. -/
def derivResolverLM (r : ℕ) : WA r →ₗ[ℂ] WA r where
  toFun a := ⟨derivResolverMul 1 a.toFun, memW_derivResolverMul one_pos a.mem⟩
  map_add' a b := by
    apply WA.ext
    funext n
    simp [derivResolverMul, wMul]
    ring
  map_smul' c a := by
    apply WA.ext
    funext n
    simp [derivResolverMul, wMul]
    ring

/-- The derivative-resolver is bounded by `1 / 2`. -/
def derivResolverCLM (r : ℕ) : WA r →L[ℂ] WA r :=
  (derivResolverLM r).mkContinuous (1 / 2) (fun a => by
    change wNorm r (derivResolverMul 1 a.toFun) ≤
      (1 / 2) * wNorm r a.toFun
    simpa using derivResolverMul_bound (r := r) (a := a.toFun) one_pos a.mem)

@[simp]
theorem derivResolverCLM_coeff (r : ℕ) (a : WA r) (n : ℤ) :
    (derivResolverCLM r a).toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          a.toFun n :=
  rfl

theorem derivResolver_coeff_re_zero (r : ℕ) (a : EvenRealWA r) (n : ℤ) :
    ((derivResolverCLM r a.1).toFun n).re = 0 := by
  let t : ℝ := (n : ℝ) * Real.pi
  let s : ℝ := 1 / (1 + t ^ 2)
  change ((Complex.I * (t : ℂ) * (s : ℂ) * a.1.toFun n).re = 0)
  have ha := EvenRealWA.coeff_im_eq_zero a n
  rw [Complex.mul_re]
  have hq : (Complex.I * (t : ℂ) * (s : ℂ)).re = 0 := by simp
  rw [hq, ha]
  ring

theorem derivResolver_coeff_neg (r : ℕ) (a : EvenRealWA r) (n : ℤ) :
    (derivResolverCLM r a.1).toFun (-n) =
      -(derivResolverCLM r a.1).toFun n := by
  rw [derivResolverCLM_coeff, derivResolverCLM_coeff,
    EvenRealWA.coeff_neg a n]
  push_cast
  ring

/-- `DR` maps even-real profiles continuously to odd-imaginary profiles. -/
def derivResolverEvenToOddCLM (r : ℕ) : EvenRealWA r →L[ℝ] OddImagWA r :=
  ((realifyWACLM (derivResolverCLM r)).comp
      (evenRealSubmodule r).subtypeL).codRestrict
    (oddImagSubmodule r) (fun a =>
      (mem_oddImagSubmodule_iff r (derivResolverCLM r a.1)).mpr
        ⟨derivResolver_coeff_re_zero r a,
          derivResolver_coeff_neg r a⟩)

@[simp]
theorem derivResolverEvenToOddCLM_coeff (r : ℕ) (a : EvenRealWA r) (n : ℤ) :
    (derivResolverEvenToOddCLM r a).1.toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          a.1.toFun n :=
  rfl

/-- `DR` on the fixed mean-zero branch space. -/
def branchDerivResolverCLM : BranchSpace →L[ℝ] OddImagWA 2 :=
  (derivResolverEvenToOddCLM 2).comp
    (meanZeroEvenRealSubmodule 2).subtypeL

@[simp]
theorem branchDerivResolverCLM_coeff (a : BranchSpace) (n : ℤ) :
    (branchDerivResolverCLM a).1.toFun n =
      (Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
        ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          a.1.1.toFun n :=
  rfl

@[simp]
theorem signalResolverCLM_coeff (a : BranchSpace) (n : ℤ) :
    (signalResolverCLM a).1.1.toFun n =
      ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
        a.1.1.toFun n :=
  rfl

/-! ## Inverse differentiation on odd modes -/

/-- Multiplier of inverse differentiation, with the zero mode set to zero. -/
def inverseDerivSymbol (n : ℤ) : ℂ :=
  if n = 0 then 0
  else 1 / (Complex.I * Real.pi * (n : ℂ))

@[simp]
theorem inverseDerivSymbol_zero :
    inverseDerivSymbol 0 = 0 := by
  simp [inverseDerivSymbol]

theorem inverseDerivSymbol_neg (n : ℤ) :
    inverseDerivSymbol (-n) = -inverseDerivSymbol n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    simp only [inverseDerivSymbol, if_neg hn, if_neg hneg]
    push_cast
    field_simp [Real.pi_ne_zero, hn]

theorem inverseDerivSymbol_norm_le_one (n : ℤ) :
    ‖inverseDerivSymbol n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn, inverseDerivSymbol]
  · rw [inverseDerivSymbol, if_neg hn, norm_div, norm_one,
      norm_mul, norm_mul, Complex.norm_I, one_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg,
      Complex.norm_intCast]
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn
    have hpi : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    have hden : (1 : ℝ) ≤ Real.pi * |(n : ℝ)| := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Real.pi * |(n : ℝ)| :=
          mul_le_mul hpi hnabs zero_le_one (by linarith [hpi])
    exact (div_le_one (by positivity)).mpr hden

/-- Ambient inverse differentiation on `WA r`. -/
def inverseDerivLM (r : ℕ) : WA r →ₗ[ℂ] WA r where
  toFun a := ⟨wMul inverseDerivSymbol a.toFun,
    memW_wMul inverseDerivSymbol_norm_le_one a.mem⟩
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

def inverseDerivCLM (r : ℕ) : WA r →L[ℂ] WA r :=
  (inverseDerivLM r).mkContinuous 1 (fun a => by
    change wNorm r (wMul inverseDerivSymbol a.toFun) ≤ 1 * wNorm r a.toFun
    exact wNorm_wMul_le zero_le_one inverseDerivSymbol_norm_le_one a.mem)

@[simp]
theorem inverseDerivCLM_coeff (r : ℕ) (a : WA r) (n : ℤ) :
    (inverseDerivCLM r a).toFun n = inverseDerivSymbol n * a.toFun n :=
  rfl

theorem oddImag_coeff_eq_im_mul_I (a : OddImagWA r) (n : ℤ) :
    a.1.toFun n = ((a.1.toFun n).im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [OddImagWA.coeff_re_eq_zero a n]
  · simp

theorem inverseDeriv_coeff_im_zero (r : ℕ) (a : OddImagWA r) (n : ℤ) :
    ((inverseDerivCLM r a.1).toFun n).im = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [inverseDerivCLM_coeff, inverseDerivSymbol, if_neg hn,
      oddImag_coeff_eq_im_mul_I a n]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have heq :
        (1 / (Complex.I * Real.pi * (n : ℂ))) *
            (((a.1.toFun n).im : ℂ) * Complex.I) =
          ((a.1.toFun n).im : ℂ) / ((Real.pi : ℂ) * (n : ℂ)) := by
      field_simp [hpi, hnC]
    rw [heq]
    rw [Complex.div_im]
    simp

theorem inverseDeriv_coeff_neg (r : ℕ) (a : OddImagWA r) (n : ℤ) :
    (inverseDerivCLM r a.1).toFun (-n) =
      (inverseDerivCLM r a.1).toFun n := by
  rw [inverseDerivCLM_coeff, inverseDerivCLM_coeff,
    inverseDerivSymbol_neg, OddImagWA.coeff_neg]
  ring

theorem inverseDeriv_meanZero (r : ℕ) (a : OddImagWA r) :
    ((inverseDerivCLM r a.1).toFun 0).re = 0 := by
  simp

/-- Inverse differentiation from odd-imaginary profiles to mean-zero
even-real profiles. -/
def inverseDerivativeToMeanZeroCLM (r : ℕ) :
    OddImagWA r →L[ℝ] MeanZeroEvenRealWA r :=
  (((realifyWACLM (inverseDerivCLM r)).comp
      (oddImagSubmodule r).subtypeL).codRestrict
      (evenRealSubmodule r) (fun a =>
        (mem_evenRealSubmodule_iff r (inverseDerivCLM r a.1)).mpr
          ⟨inverseDeriv_coeff_im_zero r a,
            inverseDeriv_coeff_neg r a⟩)).codRestrict
    (meanZeroEvenRealSubmodule r) (fun a => inverseDeriv_meanZero r a)

@[simp]
theorem inverseDerivativeToMeanZeroCLM_coeff
    (r : ℕ) (a : OddImagWA r) (n : ℤ) :
    (inverseDerivativeToMeanZeroCLM r a).1.1.toFun n =
      inverseDerivSymbol n * a.1.toFun n :=
  rfl

/-- Inverse differentiation into the fixed branch space. -/
abbrev inverseDerivativeCLM : OddImagWA 2 →L[ℝ] BranchSpace :=
  inverseDerivativeToMeanZeroCLM 2

/-! ## Cancellation with the differentiated resolver -/

theorem inverseDeriv_derivResolver_symbol (n : ℤ) :
    inverseDerivSymbol n *
        ((Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
          ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) =
      if n = 0 then 0
      else ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [inverseDerivSymbol, if_neg hn, if_neg hn]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp [hpi, hnC]

/-- Exact cancellation `D₀⁻¹ (D R h) = R h` on the mean-zero branch space. -/
theorem inverseDerivative_branchDerivResolver (h : BranchSpace) :
    inverseDerivativeCLM (branchDerivResolverCLM h) =
      signalResolverCLM h := by
  apply Subtype.ext
  apply Subtype.ext
  apply WA.ext
  funext n
  rw [inverseDerivativeToMeanZeroCLM_coeff,
    branchDerivResolverCLM_coeff, signalResolverCLM_coeff]
  calc
    inverseDerivSymbol n *
          (Complex.I * ((n : ℝ) * Real.pi : ℝ) *
            ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
              h.1.1.toFun n) =
        (inverseDerivSymbol n *
          ((Complex.I * ((n : ℝ) * Real.pi : ℝ)) *
            ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ))) *
              h.1.1.toFun n := by ring
    _ = (if n = 0 then 0
          else ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) *
            h.1.1.toFun n := by
          rw [inverseDeriv_derivResolver_symbol]
    _ = ((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          h.1.1.toFun n := by
      by_cases hn : n = 0
      · rw [if_pos hn, hn, MeanZeroEvenRealWA.coeff_zero h]
        simp
      · rw [if_neg hn]

end ShenWork.M3Counterexample
