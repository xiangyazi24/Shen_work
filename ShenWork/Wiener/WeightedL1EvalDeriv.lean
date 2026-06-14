import ShenWork.Wiener.WeightedL1Eval

/-!
# Wiener brick — the eval/derivative commutation `evalC (∂ₓ a) = ∂ₓ (evalC a)`

This file proves that the weighted-Wiener-algebra Fourier-derivative operator
commutes with the synthesis homomorphism `evalC : WA 0 → C(AddCircle 2, ℂ)`.

Working with the **real lift** `x : ℝ ↦ evalC a (↑x : AddCircle 2)` (mirroring the
committed cosine version `cosineSeries_hasDerivAt_of_gradSummable`, which lives on
`ℝ`), the main theorem is

  `HasDerivAt (fun y => evalC (toZero a) ↑y) (evalC (toZero (wD a)) ↑x) x`,

i.e. the spatial derivative of the Wiener synthesis of `a : WA (r+1)` equals the
synthesis of the derivative-operator output `wD a : WA r`.  The proof is termwise
differentiation of the Fourier series via Mathlib's Weierstrass M-test
`hasDerivAt_tsum`:

* on `AddCircle 2`, `fourier n ↑x = exp ((iπn)·x)` (`fourier_coe_apply`, `T = 2`),
  so each mode `y ↦ aₙ · exp((iπn)·y)` has derivative `aₙ · (iπn) · exp((iπn)·y)`,
  and `(wD a)ₙ = iπn·aₙ` (the derivative multiplier) makes the derivative series
  the synthesis of `wD a`;
* the derivative majorant `‖aₙ‖·(π|n|)` is summable because `a ∈ WA (r+1)`
  (`memW_wDeriv`: the weight `(1+|n|)^{r+1}` dominates `π|n|·(1+|n|)^r ≥ π|n|`);
* the value series converges since `a ∈ WA (r+1) ⊆ WA 0`.

The function-level corollary `evalC_wD_eq_deriv` follows by `.deriv`.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace ShenWork.Wiener

namespace WA

/-! ### The WA-level Fourier derivative `wD : WA (r+1) → WA r`. -/

/-- The Fourier derivative `(a_n) ↦ (iπn·a_n)` bundled `WA (r+1) → WA r`
(membership closure `memW_wDeriv`). -/
def wD {r : ℕ} (a : WA (r + 1)) : WA r := ⟨wDeriv a.toFun, memW_wDeriv a.mem⟩

@[simp] theorem wD_toFun {r : ℕ} (a : WA (r + 1)) : (wD a).toFun = wDeriv a.toFun := rfl

/-- The inclusion `WA s → WA 0` (membership drops by `mem0`). -/
def toZero {s : ℕ} (a : WA s) : WA 0 := ⟨a.toFun, mem0 a⟩

@[simp] theorem toZero_toFun {s : ℕ} (a : WA s) : (toZero a).toFun = a.toFun := rfl

/-! ### The real-lift Fourier-mode and its derivative. -/

/-- On `AddCircle 2`, the synthesis term at a real point: `fourier n ↑x = exp((iπn)·x)`.
Here `T = 2`, so `2π·I·n·x / 2 = (I·π·n)·x`. -/
theorem fourier_two_coe (n : ℤ) (x : ℝ) :
    (fourier n (x : Circ) : ℂ) = Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The single inner linear map `y ↦ (iπn)·y` has derivative `iπn` at every real `x`. -/
theorem hasDerivAt_iPiN_mul (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Complex.I * Real.pi * (n : ℂ)) * (y : ℂ))
      (Complex.I * Real.pi * (n : ℂ)) x := by
  have hC : HasDerivAt (fun w : ℂ => (Complex.I * Real.pi * (n : ℂ)) * w)
      (Complex.I * Real.pi * (n : ℂ)) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul (Complex.I * Real.pi * (n : ℂ))
  simpa using hC.comp_ofReal

/-- **Per-mode derivative.**  `y ↦ a_n · exp((iπn)·y)` has derivative
`a_n · (iπn · exp((iπn)·y))` at every real `y`. -/
theorem evalMode_hasDerivAt (c : ℂ) (n : ℤ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => c * Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (z : ℂ)))
      (c * ((Complex.I * Real.pi * (n : ℂ)) *
        Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (y : ℂ)))) y := by
  have hexp := (hasDerivAt_iPiN_mul n y).cexp
  have h := hexp.const_mul c
  convert h using 1
  ring

/-! ### The real-lift synthesis as a tsum. -/

/-- The real-lift Wiener synthesis is the pointwise exponential series:
`evalC a ↑x = ∑' n, a_n · exp((iπn)·x)`. -/
theorem evalC_coe_eq_tsum (a : WA 0) (x : ℝ) :
    (evalC a (x : Circ) : ℂ)
      = ∑' n : ℤ, a.toFun n * Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (x : ℂ)) := by
  have hmap := (ContinuousMap.evalCLM ℂ (x : Circ)).map_tsum (summable_evalTerm a)
  rw [evalC_apply, evalLin_apply, evalFun]
  rw [show (∑' n : ℤ, evalTerm a n) (x : Circ)
      = (ContinuousMap.evalCLM ℂ (x : Circ)) (∑' n : ℤ, evalTerm a n) from rfl, hmap]
  refine tsum_congr (fun n => ?_)
  rw [ContinuousMap.evalCLM_apply, evalTerm, ContinuousMap.smul_apply, smul_eq_mul,
    fourier_two_coe]

/-! ### The derivative-series majorant. -/

/-- `‖wDeriv a n‖ = π·|n|·‖a n‖`. -/
theorem norm_wDeriv (a : ℤ → ℂ) (n : ℤ) :
    ‖wDeriv a n‖ = (Real.pi * |(n : ℝ)|) * ‖a n‖ := by
  rw [wDeriv, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg]
  rw [hpi, Complex.norm_intCast]

/-- **The derivative-series majorant is summable.**  For `a : WA (r+1)`, the
sequence `n ↦ ‖a_n‖·(π|n|)` is summable: it is the absolute (`MemW 0`) norm series
of the derivative `wD a`. -/
theorem summable_gradMajorant {r : ℕ} (a : WA (r + 1)) :
    Summable (fun n : ℤ => ‖a.toFun n‖ * (Real.pi * |(n : ℝ)|)) := by
  have hmem : MemW 0 (wDeriv a.toFun) := mem0 (wD a)
  rw [MemW] at hmem
  refine hmem.congr (fun n => ?_)
  rw [wWeight]; simp only [pow_zero, one_mul]
  rw [norm_wDeriv]; ring

/-! ### The main eval/derivative commutation. -/

/-- **The eval/derivative commutation (`HasDerivAt` form).**
The spatial derivative of the real-lift Wiener synthesis of `a : WA (r+1)` equals
the synthesis of the derivative-operator output `wD a : WA r`. -/
theorem evalC_hasDerivAt_wD {r : ℕ} (a : WA (r + 1)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (evalC (toZero a) (y : Circ) : ℂ))
      (evalC (toZero (wD a)) (x : Circ)) x := by
  set u : ℤ → ℝ := fun n => ‖a.toFun n‖ * (Real.pi * |(n : ℝ)|) with hu
  have hmaj : Summable u := summable_gradMajorant a
  -- value series at `y₀ = 0` is summable (`incl0 a ∈ WA 0`).
  have hval : Summable (fun n : ℤ =>
      a.toFun n * Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * ((0 : ℝ) : ℂ))) := by
    have h0 : MemW 0 (a.toFun) := mem0 a
    rw [MemW] at h0
    refine Summable.of_norm ?_
    refine h0.congr (fun n => ?_)
    rw [wWeight]; simp only [pow_zero, one_mul]
    rw [norm_mul]
    have : Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [this, norm_one, mul_one]
  -- the M-test.
  have hkey := hasDerivAt_tsum (𝕜 := ℝ) (F := ℂ) (u := u)
    (g := fun n z => a.toFun n * Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (z : ℂ)))
    (g' := fun n z => a.toFun n *
      ((Complex.I * Real.pi * (n : ℂ)) *
        Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (z : ℂ))))
    hmaj
    (fun n z => evalMode_hasDerivAt (a.toFun n) n z)
    (fun n z => by
      rw [hu]
      rw [norm_mul, norm_mul]
      have hexp : ‖Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (z : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        have : ((Complex.I * Real.pi * (n : ℂ)) * (z : ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.I_re, Complex.I_im]
        rw [this, Real.exp_zero]
      rw [hexp, mul_one]
      have hiPiN : ‖Complex.I * Real.pi * (n : ℂ)‖ = Real.pi * |(n : ℝ)| := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
          rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg]
        rw [hpi, Complex.norm_intCast]
      rw [hiPiN])
    hval x
  -- rewrite both sides into the synthesis form.
  have hfun : (fun y : ℝ => (evalC (toZero a) (y : Circ) : ℂ))
      = fun z : ℝ => ∑' n : ℤ,
          a.toFun n * Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (z : ℂ)) := by
    funext y
    rw [evalC_coe_eq_tsum (toZero a) y, toZero_toFun]
  rw [hfun]
  have hderiv : (evalC (toZero (wD a)) (x : Circ) : ℂ)
      = ∑' n : ℤ, a.toFun n *
          ((Complex.I * Real.pi * (n : ℂ)) *
            Complex.exp ((Complex.I * Real.pi * (n : ℂ)) * (x : ℂ))) := by
    rw [evalC_coe_eq_tsum (toZero (wD a)) x, toZero_toFun, wD_toFun]
    refine tsum_congr (fun n => ?_)
    rw [wDeriv]; ring
  rw [hderiv]
  exact hkey

/-- **The eval/derivative commutation (function form).**
`evalC (wD a) ↑x = ∂ₓ (evalC (toZero a) ↑·) x`. -/
theorem evalC_wD_eq_deriv {r : ℕ} (a : WA (r + 1)) (x : ℝ) :
    (evalC (toZero (wD a)) (x : Circ) : ℂ)
      = deriv (fun y : ℝ => (evalC (toZero a) (y : Circ) : ℂ)) x :=
  (evalC_hasDerivAt_wD a x).deriv.symm

end WA

end ShenWork.Wiener
