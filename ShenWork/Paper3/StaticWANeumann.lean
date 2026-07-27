import ShenWork.Paper3.StaticWAEvenReal

/-!
# Mean-zero Neumann coordinates in the static Wiener algebra

This file introduces the two real Banach spaces used by the amplitude blow-up:

* `MeanZeroEvenRealWA r`, the even-real profiles with zero constant mode;
* `FirstComplementWA r`, the further complement with zero first cosine mode.

It also defines the normalized first Neumann mode `cos (π x)`.  In bilateral
Fourier coordinates this mode has coefficients `1 / 2` at `±1`.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## Continuous cosine coordinates -/

/-- The real part of coefficient `n` on the even-real subspace. -/
def evenRealCoeffCLM (r : ℕ) (n : ℤ) : EvenRealWA r →L[ℝ] ℝ :=
  (realCoeffCLM r n).comp (evenRealSubmodule r).subtypeL

@[simp]
theorem evenRealCoeffCLM_apply (r : ℕ) (n : ℤ) (a : EvenRealWA r) :
    evenRealCoeffCLM r n a = (a.1.toFun n).re :=
  rfl

/-- Even-real profiles with zero Fourier mode. -/
def meanZeroEvenRealSubmodule (r : ℕ) : Submodule ℝ (EvenRealWA r) :=
  (evenRealCoeffCLM r 0).ker

/-- The mean-zero even-real static Wiener space. -/
abbrev MeanZeroEvenRealWA (r : ℕ) := meanZeroEvenRealSubmodule r

theorem mem_meanZeroEvenRealSubmodule_iff (r : ℕ) (a : EvenRealWA r) :
    a ∈ meanZeroEvenRealSubmodule r ↔ (a.1.toFun 0).re = 0 := by
  rw [meanZeroEvenRealSubmodule, LinearMap.mem_ker]
  rfl

theorem isClosed_meanZeroEvenRealSubmodule (r : ℕ) :
    IsClosed (meanZeroEvenRealSubmodule r : Set (EvenRealWA r)) :=
  (evenRealCoeffCLM r 0).isClosed_ker

noncomputable instance meanZeroEvenRealWACompleteSpace (r : ℕ) :
    CompleteSpace (MeanZeroEvenRealWA r) :=
  (isClosed_meanZeroEvenRealSubmodule r).completeSpace_coe

/-- Coefficient `n` on the mean-zero even-real subspace. -/
def meanZeroCoeffCLM (r : ℕ) (n : ℤ) : MeanZeroEvenRealWA r →L[ℝ] ℝ :=
  (evenRealCoeffCLM r n).comp (meanZeroEvenRealSubmodule r).subtypeL

@[simp]
theorem meanZeroCoeffCLM_apply (r : ℕ) (n : ℤ) (a : MeanZeroEvenRealWA r) :
    meanZeroCoeffCLM r n a = (a.1.1.toFun n).re :=
  rfl

/-- The complement of the first cosine line inside the mean-zero space. -/
def firstComplementSubmodule (r : ℕ) : Submodule ℝ (MeanZeroEvenRealWA r) :=
  (meanZeroCoeffCLM r 1).ker

/-- Mean-zero even-real profiles with zero first coefficient. -/
abbrev FirstComplementWA (r : ℕ) := firstComplementSubmodule r

theorem mem_firstComplementSubmodule_iff (r : ℕ) (a : MeanZeroEvenRealWA r) :
    a ∈ firstComplementSubmodule r ↔ (a.1.1.toFun 1).re = 0 := by
  rw [firstComplementSubmodule, LinearMap.mem_ker]
  rfl

theorem isClosed_firstComplementSubmodule (r : ℕ) :
    IsClosed (firstComplementSubmodule r : Set (MeanZeroEvenRealWA r)) :=
  (meanZeroCoeffCLM r 1).isClosed_ker

noncomputable instance firstComplementWACompleteSpace (r : ℕ) :
    CompleteSpace (FirstComplementWA r) :=
  (isClosed_firstComplementSubmodule r).completeSpace_coe

/-! ## The normalized first Neumann mode -/

/-- Bilateral coefficients of `cos (π x)`: `1 / 2` at `±1`, zero elsewhere. -/
def firstModeSeq (n : ℤ) : ℂ :=
  if n = 1 ∨ n = -1 then (1 / 2 : ℂ) else 0

theorem memW_firstModeSeq (r : ℕ) : MemW r firstModeSeq := by
  rw [MemW]
  refine summable_of_hasFiniteSupport ?_
  refine (Set.finite_singleton (-1 : ℤ)).insert (1 : ℤ) |>.subset ?_
  intro n hn
  simp only [Function.mem_support, Set.mem_insert_iff, Set.mem_singleton_iff] at *
  by_contra h
  apply hn
  simp [firstModeSeq, h]

/-- `cos (π x)` as an element of `WA r`. -/
def firstModeWA (r : ℕ) : WA r :=
  ⟨firstModeSeq, memW_firstModeSeq r⟩

@[simp]
theorem firstModeWA_toFun (r : ℕ) :
    (firstModeWA r).toFun = firstModeSeq :=
  rfl

@[simp]
theorem firstModeSeq_zero : firstModeSeq 0 = 0 := by
  norm_num [firstModeSeq]

@[simp]
theorem firstModeSeq_one : firstModeSeq 1 = (1 / 2 : ℂ) := by
  norm_num [firstModeSeq]

@[simp]
theorem firstModeSeq_neg_one : firstModeSeq (-1) = (1 / 2 : ℂ) := by
  norm_num [firstModeSeq]

theorem firstModeSeq_neg (n : ℤ) :
    firstModeSeq (-n) = firstModeSeq n := by
  simp only [firstModeSeq]
  by_cases h : n = 1 ∨ n = -1
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem firstModeSeq_im (n : ℤ) :
    (firstModeSeq n).im = 0 := by
  by_cases h : n = 1 ∨ n = -1 <;> simp [firstModeSeq, h]

/-- The normalized first cosine mode in the even-real subspace. -/
def firstModeEvenReal (r : ℕ) : EvenRealWA r :=
  ⟨firstModeWA r, (mem_evenRealSubmodule_iff r (firstModeWA r)).mpr
    ⟨firstModeSeq_im, firstModeSeq_neg⟩⟩

/-- The normalized first cosine mode in the mean-zero ambient space. -/
def firstModeMeanZero (r : ℕ) : MeanZeroEvenRealWA r :=
  ⟨firstModeEvenReal r, by
    rw [mem_meanZeroEvenRealSubmodule_iff]
    norm_num [firstModeEvenReal, firstModeWA]⟩

@[simp]
theorem firstModeMeanZero_coeff_zero (r : ℕ) :
    (firstModeMeanZero r).1.1.toFun 0 = 0 := by
  rfl

@[simp]
theorem firstModeMeanZero_coeff_one_re (r : ℕ) :
    ((firstModeMeanZero r).1.1.toFun 1).re = 1 / 2 := by
  norm_num [firstModeMeanZero, firstModeEvenReal, firstModeWA]

theorem firstModeMeanZero_ne_zero (r : ℕ) :
    firstModeMeanZero r ≠ 0 := by
  intro h
  have hc := congrArg (fun a : MeanZeroEvenRealWA r => (a.1.1.toFun 1).re) h
  norm_num [firstModeMeanZero, firstModeEvenReal, firstModeWA] at hc

/-! ## Coefficient consequences used later -/

namespace MeanZeroEvenRealWA

theorem coeff_zero (a : MeanZeroEvenRealWA r) :
    a.1.1.toFun 0 = 0 := by
  apply Complex.ext
  · exact (mem_meanZeroEvenRealSubmodule_iff r a.1).mp a.2
  · exact EvenRealWA.coeff_im_eq_zero a.1 0

theorem coeff_neg (a : MeanZeroEvenRealWA r) (n : ℤ) :
    a.1.1.toFun (-n) = a.1.1.toFun n :=
  EvenRealWA.coeff_neg a.1 n

theorem coeff_im_eq_zero (a : MeanZeroEvenRealWA r) (n : ℤ) :
    (a.1.1.toFun n).im = 0 :=
  EvenRealWA.coeff_im_eq_zero a.1 n

end MeanZeroEvenRealWA

namespace FirstComplementWA

theorem coeff_one (a : FirstComplementWA r) :
    a.1.1.1.toFun 1 = 0 := by
  apply Complex.ext
  · exact (mem_firstComplementSubmodule_iff r a.1).mp a.2
  · exact MeanZeroEvenRealWA.coeff_im_eq_zero a.1 1

theorem coeff_neg_one (a : FirstComplementWA r) :
    a.1.1.1.toFun (-1) = 0 := by
  rw [MeanZeroEvenRealWA.coeff_neg a.1 1, coeff_one]

theorem coeff_zero (a : FirstComplementWA r) :
    a.1.1.1.toFun 0 = 0 :=
  MeanZeroEvenRealWA.coeff_zero a.1

end FirstComplementWA

/-! The fixed spaces used in the `m = 3` construction. -/

/-- Ambient even-real, mean-zero Wiener space at regularity weight `2`. -/
abbrev BranchSpace := MeanZeroEvenRealWA 2

/-- Complement of the first cosine line in `BranchSpace`. -/
abbrev BranchComplement := FirstComplementWA 2

end ShenWork.M3Counterexample
