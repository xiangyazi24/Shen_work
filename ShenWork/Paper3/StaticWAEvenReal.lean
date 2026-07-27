import ShenWork.Wiener.WeightedL1Complete
import ShenWork.Wiener.WeightedL1Eval

/-!
# Static real parity subspaces of the weighted Wiener algebra

This file packages the static Fourier spaces used by the `m = 3`
counterexample construction.  Coefficients are indexed by `ℤ` in the
repository's weighted Wiener algebra `WA r`.

* `EvenRealWA r` consists of real, even coefficient sequences.
* `OddImagWA r` consists of purely imaginary, odd coefficient sequences.

Both are closed real subspaces of `WA r`, hence Banach spaces.  The coefficient
maps below are also the basic continuous coordinates used by the zero-mode and
first-mode complements.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## Coefficient maps on `WA r` -/

/-- The identity-on-coefficients inclusion `WA r →ₗ[ℂ] WA 0`. -/
def inclZeroLM (r : ℕ) : WA r →ₗ[ℂ] WA 0 where
  toFun a := ⟨a.toFun, memW_mono (Nat.zero_le r) a.mem⟩
  map_add' a b := by
    apply WA.ext
    rfl
  map_smul' c a := by
    apply WA.ext
    rfl

@[simp]
theorem inclZeroLM_toFun (r : ℕ) (a : WA r) :
    (inclZeroLM r a).toFun = a.toFun :=
  rfl

/-- The continuous identity-on-coefficients inclusion `WA r →L[ℂ] WA 0`. -/
def inclZeroCLM (r : ℕ) : WA r →L[ℂ] WA 0 :=
  (inclZeroLM r).mkContinuous 1 (fun a => by
    change wNorm 0 a.toFun ≤ 1 * wNorm r a.toFun
    simpa using wNorm_mono_le (Nat.zero_le r) a.mem)

@[simp]
theorem inclZeroCLM_toFun (r : ℕ) (a : WA r) :
    (inclZeroCLM r a).toFun = a.toFun :=
  rfl

/-- Extraction of the `n`th coefficient from `WA r`. -/
def coeffCLM (r : ℕ) (n : ℤ) : WA r →L[ℂ] ℂ :=
  (WA.coeff0CLM n).comp (inclZeroCLM r)

@[simp]
theorem coeffCLM_apply (r : ℕ) (n : ℤ) (a : WA r) :
    coeffCLM r n a = a.toFun n :=
  rfl

/-- Coefficient extraction regarded as a real linear map.  This is defined
directly because the historical `WA` scalar instances do not expose an
`IsScalarTower ℝ ℂ (WA r)` instance. -/
def coeffRLM (r : ℕ) (n : ℤ) : WA r →ₗ[ℝ] ℂ where
  toFun a := a.toFun n
  map_add' a b := rfl
  map_smul' c a := by
    change (((c : ℂ) • a).toFun n) = (c : ℂ) • a.toFun n
    rfl

/-- Coefficient extraction as a real continuous linear map. -/
def coeffRCLM (r : ℕ) (n : ℤ) : WA r →L[ℝ] ℂ :=
  (coeffRLM r n).mkContinuous 1 (fun a => by
    change ‖a.toFun n‖ ≤ 1 * ‖a‖
    rw [one_mul]
    calc
      ‖a.toFun n‖ = ‖(inclZeroCLM r a).toFun n‖ := rfl
      _ ≤ ‖inclZeroCLM r a‖ := WA.norm_coeff_le n (inclZeroCLM r a)
      _ ≤ ‖a‖ := by
        change wNorm 0 a.toFun ≤ wNorm r a.toFun
        exact wNorm_mono_le (Nat.zero_le r) a.mem)

@[simp]
theorem coeffRCLM_apply (r : ℕ) (n : ℤ) (a : WA r) :
    coeffRCLM r n a = a.toFun n :=
  rfl

/-- Imaginary part of the `n`th coefficient. -/
def imagCoeffCLM (r : ℕ) (n : ℤ) : WA r →L[ℝ] ℝ :=
  Complex.imCLM.comp (coeffRCLM r n)

@[simp]
theorem imagCoeffCLM_apply (r : ℕ) (n : ℤ) (a : WA r) :
    imagCoeffCLM r n a = (a.toFun n).im :=
  rfl

/-- Real part of the `n`th coefficient. -/
def realCoeffCLM (r : ℕ) (n : ℤ) : WA r →L[ℝ] ℝ :=
  Complex.reCLM.comp (coeffRCLM r n)

@[simp]
theorem realCoeffCLM_apply (r : ℕ) (n : ℤ) (a : WA r) :
    realCoeffCLM r n a = (a.toFun n).re :=
  rfl

/-- Defect from evenness at mode `n`. -/
def evenDefectCLM (r : ℕ) (n : ℤ) : WA r →L[ℝ] ℂ :=
  coeffRCLM r (-n) - coeffRCLM r n

@[simp]
theorem evenDefectCLM_apply (r : ℕ) (n : ℤ) (a : WA r) :
    evenDefectCLM r n a = a.toFun (-n) - a.toFun n := by
  simp [evenDefectCLM]

/-- Defect from oddness at mode `n`. -/
def oddDefectCLM (r : ℕ) (n : ℤ) : WA r →L[ℝ] ℂ :=
  coeffRCLM r (-n) + coeffRCLM r n

@[simp]
theorem oddDefectCLM_apply (r : ℕ) (n : ℤ) (a : WA r) :
    oddDefectCLM r n a = a.toFun (-n) + a.toFun n := by
  simp [oddDefectCLM]

/-! ## Closed parity subspaces -/

/-- The real subspace of `WA r` with real, even Fourier coefficients. -/
def evenRealSubmodule (r : ℕ) : Submodule ℝ (WA r) :=
  (⨅ n : ℤ, (imagCoeffCLM r n).ker) ⊓
    (⨅ n : ℤ, (evenDefectCLM r n).ker)

/-- The real subspace of `WA r` with purely imaginary, odd Fourier coefficients. -/
def oddImagSubmodule (r : ℕ) : Submodule ℝ (WA r) :=
  (⨅ n : ℤ, (realCoeffCLM r n).ker) ⊓
    (⨅ n : ℤ, (oddDefectCLM r n).ker)

/-- Static real-even weighted Wiener coefficients. -/
abbrev EvenRealWA (r : ℕ) := evenRealSubmodule r

/-- Static imaginary-odd weighted Wiener coefficients. -/
abbrev OddImagWA (r : ℕ) := oddImagSubmodule r

theorem mem_evenRealSubmodule_iff (r : ℕ) (a : WA r) :
    a ∈ evenRealSubmodule r ↔
      (∀ n : ℤ, (a.toFun n).im = 0) ∧
      (∀ n : ℤ, a.toFun (-n) = a.toFun n) := by
  constructor
  · intro ha
    rw [evenRealSubmodule, Submodule.mem_inf] at ha
    constructor
    · intro n
      have hn := (Submodule.mem_iInf _).mp ha.1 n
      have hz := LinearMap.mem_ker.mp hn
      change imagCoeffCLM r n a = 0 at hz
      simpa using hz
    · intro n
      have hn := (Submodule.mem_iInf _).mp ha.2 n
      have hz := LinearMap.mem_ker.mp hn
      change evenDefectCLM r n a = 0 at hz
      exact sub_eq_zero.mp (by simpa using hz)
  · rintro ⟨him, heven⟩
    rw [evenRealSubmodule, Submodule.mem_inf]
    constructor
    · exact (Submodule.mem_iInf _).mpr fun n =>
        LinearMap.mem_ker.mpr (by
          change imagCoeffCLM r n a = 0
          simpa using him n)
    · exact (Submodule.mem_iInf _).mpr fun n =>
        LinearMap.mem_ker.mpr (by
          change evenDefectCLM r n a = 0
          simpa [sub_eq_zero] using heven n)

theorem mem_oddImagSubmodule_iff (r : ℕ) (a : WA r) :
    a ∈ oddImagSubmodule r ↔
      (∀ n : ℤ, (a.toFun n).re = 0) ∧
      (∀ n : ℤ, a.toFun (-n) = -a.toFun n) := by
  constructor
  · intro ha
    rw [oddImagSubmodule, Submodule.mem_inf] at ha
    constructor
    · intro n
      have hn := (Submodule.mem_iInf _).mp ha.1 n
      have hz := LinearMap.mem_ker.mp hn
      change realCoeffCLM r n a = 0 at hz
      simpa using hz
    · intro n
      have hn := (Submodule.mem_iInf _).mp ha.2 n
      have hz := LinearMap.mem_ker.mp hn
      change oddDefectCLM r n a = 0 at hz
      exact add_eq_zero_iff_eq_neg.mp (by simpa using hz)
  · rintro ⟨hre, hodd⟩
    rw [oddImagSubmodule, Submodule.mem_inf]
    constructor
    · exact (Submodule.mem_iInf _).mpr fun n =>
        LinearMap.mem_ker.mpr (by
          change realCoeffCLM r n a = 0
          simpa using hre n)
    · exact (Submodule.mem_iInf _).mpr fun n =>
        LinearMap.mem_ker.mpr (by
          change oddDefectCLM r n a = 0
          simpa [add_eq_zero_iff_eq_neg] using hodd n)

theorem isClosed_evenRealSubmodule (r : ℕ) :
    IsClosed (evenRealSubmodule r : Set (WA r)) := by
  have hset :
      (evenRealSubmodule r : Set (WA r)) =
        (⋂ n : ℤ, ((imagCoeffCLM r n).ker : Set (WA r))) ∩
          (⋂ n : ℤ, ((evenDefectCLM r n).ker : Set (WA r))) := by
    ext a
    simp [evenRealSubmodule]
  rw [hset]
  exact (isClosed_iInter fun n => (imagCoeffCLM r n).isClosed_ker).inter
    (isClosed_iInter fun n => (evenDefectCLM r n).isClosed_ker)

theorem isClosed_oddImagSubmodule (r : ℕ) :
    IsClosed (oddImagSubmodule r : Set (WA r)) := by
  have hset :
      (oddImagSubmodule r : Set (WA r)) =
        (⋂ n : ℤ, ((realCoeffCLM r n).ker : Set (WA r))) ∩
          (⋂ n : ℤ, ((oddDefectCLM r n).ker : Set (WA r))) := by
    ext a
    simp [oddImagSubmodule]
  rw [hset]
  exact (isClosed_iInter fun n => (realCoeffCLM r n).isClosed_ker).inter
    (isClosed_iInter fun n => (oddDefectCLM r n).isClosed_ker)

noncomputable instance evenRealWACompleteSpace (r : ℕ) :
    CompleteSpace (EvenRealWA r) :=
  (isClosed_evenRealSubmodule r).completeSpace_coe

noncomputable instance oddImagWACompleteSpace (r : ℕ) :
    CompleteSpace (OddImagWA r) :=
  (isClosed_oddImagSubmodule r).completeSpace_coe

namespace EvenRealWA

theorem coeff_im_eq_zero (a : EvenRealWA r) (n : ℤ) :
    (a.1.toFun n).im = 0 :=
  (mem_evenRealSubmodule_iff r a.1).mp a.2 |>.1 n

theorem coeff_neg (a : EvenRealWA r) (n : ℤ) :
    a.1.toFun (-n) = a.1.toFun n :=
  (mem_evenRealSubmodule_iff r a.1).mp a.2 |>.2 n

end EvenRealWA

namespace OddImagWA

theorem coeff_re_eq_zero (a : OddImagWA r) (n : ℤ) :
    (a.1.toFun n).re = 0 :=
  (mem_oddImagSubmodule_iff r a.1).mp a.2 |>.1 n

theorem coeff_neg (a : OddImagWA r) (n : ℤ) :
    a.1.toFun (-n) = -a.1.toFun n :=
  (mem_oddImagSubmodule_iff r a.1).mp a.2 |>.2 n

end OddImagWA

end ShenWork.M3Counterexample
