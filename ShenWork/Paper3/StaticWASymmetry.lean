import ShenWork.Paper3.StaticWAInverseDerivative

/-!
# Reflection and conjugation symmetries of static `WA`

The nonlinear residual uses the total algebra inverse `Ring.inverse`.  To keep
that residual in the real Neumann parity spaces, we package the two involutive
ring symmetries of the bilateral Wiener algebra:

* reflection `aₙ ↦ a₋ₙ`;
* coefficient conjugation `aₙ ↦ conj (aₙ)`.

Both commute with `Ring.inverse`.  Consequently the inverse of an even-real
element is again even-real, including the nonunit case where `Ring.inverse`
is defined to be zero.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## Reflection -/

theorem memW_refl {r : ℕ} (a : WA r) :
    MemW r (fun n => a.toFun (-n)) := by
  have heq := ((Equiv.neg ℤ).summable_iff
    (f := fun n => wWeight r n * ‖a.toFun n‖)).2 a.mem
  refine heq.congr (fun n => ?_)
  simp only [Function.comp_apply, Equiv.neg_apply]
  rw [show wWeight r (-n) = wWeight r n by simp [wWeight, abs_neg]]

def waRefl {r : ℕ} (a : WA r) : WA r :=
  ⟨fun n => a.toFun (-n), memW_refl a⟩

@[simp]
theorem waRefl_coeff {r : ℕ} (a : WA r) (n : ℤ) :
    (waRefl a).toFun n = a.toFun (-n) :=
  rfl

theorem waRefl_add {r : ℕ} (a b : WA r) :
    waRefl (a + b) = waRefl a + waRefl b := by
  apply WA.ext
  funext n
  rfl

theorem waRefl_mul {r : ℕ} (a b : WA r) :
    waRefl (a * b) = waRefl a * waRefl b := by
  apply WA.ext
  funext n
  change (∑' m, a.toFun m * b.toFun (-n - m)) =
    ∑' m, a.toFun (-m) * b.toFun (-(n - m))
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun m => a.toFun m * b.toFun (-n - m))]
  refine tsum_congr (fun m => ?_)
  simp only [Equiv.neg_apply]
  congr 2
  ring

theorem waRefl_one {r : ℕ} :
    waRefl (1 : WA r) = 1 := by
  apply WA.ext
  funext n
  change wOne (-n) = wOne n
  by_cases hn : n = 0
  · simp [hn]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    simp [wOne, hn, hneg]

def waReflRH (r : ℕ) : WA r →+* WA r where
  toFun := waRefl
  map_one' := waRefl_one
  map_mul' := waRefl_mul
  map_zero' := by
    apply WA.ext
    funext n
    rfl
  map_add' := waRefl_add

@[simp]
theorem waReflRH_apply (r : ℕ) (a : WA r) :
    waReflRH r a = waRefl a :=
  rfl

@[simp]
theorem waRefl_involutive {r : ℕ} (a : WA r) :
    waRefl (waRefl a) = a := by
  apply WA.ext
  funext n
  simp

/-! ## Coefficient conjugation -/

theorem memW_conj {r : ℕ} (a : WA r) :
    MemW r (fun n => star (a.toFun n)) := by
  exact a.mem.congr (fun n => by rw [norm_star])

def waConj {r : ℕ} (a : WA r) : WA r :=
  ⟨fun n => star (a.toFun n), memW_conj a⟩

@[simp]
theorem waConj_coeff {r : ℕ} (a : WA r) (n : ℤ) :
    (waConj a).toFun n = star (a.toFun n) :=
  rfl

theorem waConj_add {r : ℕ} (a b : WA r) :
    waConj (a + b) = waConj a + waConj b := by
  apply WA.ext
  funext n
  simp [star_add]

theorem waConj_mul {r : ℕ} (a b : WA r) :
    waConj (a * b) = waConj a * waConj b := by
  apply WA.ext
  funext n
  change star (∑' m, a.toFun m * b.toFun (n - m)) =
    ∑' m, star (a.toFun m) * star (b.toFun (n - m))
  rw [tsum_star]
  exact tsum_congr (fun m => star_mul' _ _)

theorem waConj_one {r : ℕ} :
    waConj (1 : WA r) = 1 := by
  apply WA.ext
  funext n
  change star (wOne n) = wOne n
  by_cases hn : n = 0 <;> simp [wOne, hn]

def waConjRH (r : ℕ) : WA r →+* WA r where
  toFun := waConj
  map_one' := waConj_one
  map_mul' := waConj_mul
  map_zero' := by
    apply WA.ext
    funext n
    simp
  map_add' := waConj_add

@[simp]
theorem waConjRH_apply (r : ℕ) (a : WA r) :
    waConjRH r a = waConj a :=
  rfl

@[simp]
theorem waConj_involutive {r : ℕ} (a : WA r) :
    waConj (waConj a) = a := by
  apply WA.ext
  funext n
  simp

/-! ## Fixed and anti-fixed characterizations -/

theorem even_iff_waRefl_eq {r : ℕ} (a : WA r) :
    (∀ n : ℤ, a.toFun (-n) = a.toFun n) ↔ waRefl a = a := by
  constructor
  · intro h
    apply WA.ext
    funext n
    exact h n
  · intro h n
    exact congrArg (fun b : WA r => b.toFun n) h

theorem real_iff_waConj_eq {r : ℕ} (a : WA r) :
    (∀ n : ℤ, (a.toFun n).im = 0) ↔ waConj a = a := by
  constructor
  · intro h
    apply WA.ext
    funext n
    apply Complex.ext
    · simp
    · simp [h n]
  · intro h n
    have hn := congrArg (fun b : WA r => (b.toFun n).im) h
    simp only [waConj_coeff, Complex.star_def, Complex.conj_im] at hn
    linarith

theorem odd_iff_waRefl_eq_neg {r : ℕ} (a : WA r) :
    (∀ n : ℤ, a.toFun (-n) = -a.toFun n) ↔ waRefl a = -a := by
  constructor
  · intro h
    apply WA.ext
    funext n
    exact h n
  · intro h n
    exact congrArg (fun b : WA r => b.toFun n) h

theorem imag_iff_waConj_eq_neg {r : ℕ} (a : WA r) :
    (∀ n : ℤ, (a.toFun n).re = 0) ↔ waConj a = -a := by
  constructor
  · intro h
    apply WA.ext
    funext n
    apply Complex.ext
    · simp [h n]
    · simp
  · intro h n
    have hn := congrArg (fun b : WA r => (b.toFun n).re) h
    simp only [waConj_coeff, Complex.star_def, Complex.conj_re,
      WA.neg_toFun, Pi.neg_apply, Complex.neg_re] at hn
    linarith

theorem evenReal_iff_fixed {r : ℕ} (a : WA r) :
    a ∈ evenRealSubmodule r ↔ waRefl a = a ∧ waConj a = a := by
  rw [mem_evenRealSubmodule_iff, and_comm]
  exact and_congr (even_iff_waRefl_eq a) (real_iff_waConj_eq a)

theorem oddImag_iff_antifixed {r : ℕ} (a : WA r) :
    a ∈ oddImagSubmodule r ↔ waRefl a = -a ∧ waConj a = -a := by
  rw [mem_oddImagSubmodule_iff, and_comm]
  exact and_congr (odd_iff_waRefl_eq_neg a) (imag_iff_waConj_eq_neg a)

/-! ## Total ring inverse commutes with the involutions -/

theorem map_ringInverse_of_involutive
    {A : Type*} [CommRing A] (f : A →+* A)
    (hinv : ∀ x, f (f x) = x) (x : A) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  by_cases hx : IsUnit x
  · have hfx : IsUnit (f x) := hx.map f
    rw [← one_mul (Ring.inverse (f x))]
    apply (Ring.eq_mul_inverse_iff_mul_eq
      (f (Ring.inverse x)) 1 (f x) hfx).mpr
    rw [← f.map_mul, Ring.inverse_mul_cancel x hx, f.map_one]
  · have hfx : ¬IsUnit (f x) := by
      intro h
      have hmap : IsUnit (f (f x)) := h.map f
      rw [hinv x] at hmap
      exact hx hmap
    rw [Ring.inverse_non_unit x hx, f.map_zero,
      Ring.inverse_non_unit (f x) hfx]

theorem waRefl_ringInverse {r : ℕ} (a : WA r) :
    waRefl (Ring.inverse a) = Ring.inverse (waRefl a) :=
  map_ringInverse_of_involutive (waReflRH r) waRefl_involutive a

theorem waConj_ringInverse {r : ℕ} (a : WA r) :
    waConj (Ring.inverse a) = Ring.inverse (waConj a) :=
  map_ringInverse_of_involutive (waConjRH r) waConj_involutive a

theorem ringInverse_mem_evenReal {r : ℕ} (a : EvenRealWA r) :
    Ring.inverse a.1 ∈ evenRealSubmodule r := by
  rw [evenReal_iff_fixed]
  have ha := (evenReal_iff_fixed a.1).mp a.2
  constructor
  · rw [waRefl_ringInverse, ha.1]
  · rw [waConj_ringInverse, ha.2]

/-! ## Multiplication table -/

theorem mul_mem_evenReal {r : ℕ} (a b : EvenRealWA r) :
    a.1 * b.1 ∈ evenRealSubmodule r := by
  rw [evenReal_iff_fixed]
  have ha := (evenReal_iff_fixed a.1).mp a.2
  have hb := (evenReal_iff_fixed b.1).mp b.2
  constructor
  · rw [waRefl_mul, ha.1, hb.1]
  · rw [waConj_mul, ha.2, hb.2]

theorem mul_mem_oddImag {r : ℕ} (a : EvenRealWA r) (b : OddImagWA r) :
    a.1 * b.1 ∈ oddImagSubmodule r := by
  rw [oddImag_iff_antifixed]
  have ha := (evenReal_iff_fixed a.1).mp a.2
  have hb := (oddImag_iff_antifixed b.1).mp b.2
  constructor
  · rw [waRefl_mul, ha.1, hb.1, mul_neg]
  · rw [waConj_mul, ha.2, hb.2, mul_neg]

/-- Multiplication inside the even-real subspace. -/
def evenRealMul {r : ℕ} (a b : EvenRealWA r) : EvenRealWA r :=
  ⟨a.1 * b.1, mul_mem_evenReal a b⟩

/-- Multiplication of an even-real and an odd-imaginary profile. -/
def evenOddMul {r : ℕ} (a : EvenRealWA r) (b : OddImagWA r) : OddImagWA r :=
  ⟨a.1 * b.1, mul_mem_oddImag a b⟩

@[simp]
theorem evenRealMul_coe {r : ℕ} (a b : EvenRealWA r) :
    (evenRealMul a b : WA r) = a.1 * b.1 :=
  rfl

@[simp]
theorem evenOddMul_coe {r : ℕ} (a : EvenRealWA r) (b : OddImagWA r) :
    (evenOddMul a b : WA r) = a.1 * b.1 :=
  rfl

end ShenWork.M3Counterexample
