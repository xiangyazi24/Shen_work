import ShenWork.Paper3.StaticWAEvalBridge

/-!
# Algebraic rules for static Wiener evaluation

The regularity-forgetting map `WA r → WA 0` preserves the coefficient
sequence.  This file records the corresponding algebraic identities and their
pointwise consequences for the real synthesis of even-real profiles.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

@[simp]
theorem toZero_zero (r : ℕ) :
    WA.toZero (0 : WA r) = 0 := by
  apply WA.ext
  rfl

@[simp]
theorem toZero_one (r : ℕ) :
    WA.toZero (1 : WA r) = 1 := by
  apply WA.ext
  rfl

@[simp]
theorem toZero_add {r : ℕ} (a b : WA r) :
    WA.toZero (a + b) = WA.toZero a + WA.toZero b := by
  apply WA.ext
  rfl

@[simp]
theorem toZero_sub {r : ℕ} (a b : WA r) :
    WA.toZero (a - b) = WA.toZero a - WA.toZero b := by
  apply WA.ext
  rfl

@[simp]
theorem toZero_mul {r : ℕ} (a b : WA r) :
    WA.toZero (a * b) = WA.toZero a * WA.toZero b := by
  apply WA.ext
  rfl

@[simp]
theorem toZero_pow {r : ℕ} (a : WA r) (n : ℕ) :
    WA.toZero (a ^ n) = WA.toZero a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, toZero_mul, ih]

@[simp]
theorem toZero_real_smul {r : ℕ} (c : ℝ) (a : WA r) :
    WA.toZero (c • a) = (c : ℂ) • WA.toZero a := by
  apply WA.ext
  rfl

theorem evalC_toZero_add {r : ℕ} (a b : WA r) (x : ℝ) :
    WA.evalC (WA.toZero (a + b)) (x : WA.Circ) =
      WA.evalC (WA.toZero a) (x : WA.Circ) +
        WA.evalC (WA.toZero b) (x : WA.Circ) := by
  rw [toZero_add, map_add]
  rfl

theorem evalC_toZero_sub {r : ℕ} (a b : WA r) (x : ℝ) :
    WA.evalC (WA.toZero (a - b)) (x : WA.Circ) =
      WA.evalC (WA.toZero a) (x : WA.Circ) -
        WA.evalC (WA.toZero b) (x : WA.Circ) := by
  rw [toZero_sub, map_sub]
  rfl

theorem evalC_toZero_mul {r : ℕ} (a b : WA r) (x : ℝ) :
    WA.evalC (WA.toZero (a * b)) (x : WA.Circ) =
      WA.evalC (WA.toZero a) (x : WA.Circ) *
        WA.evalC (WA.toZero b) (x : WA.Circ) := by
  rw [toZero_mul, map_mul]
  rfl

theorem evalC_toZero_pow {r : ℕ} (a : WA r) (n : ℕ) (x : ℝ) :
    WA.evalC (WA.toZero (a ^ n)) (x : WA.Circ) =
      WA.evalC (WA.toZero a) (x : WA.Circ) ^ n := by
  rw [toZero_pow, map_pow]
  rfl

theorem evalC_toZero_real_smul {r : ℕ} (c : ℝ) (a : WA r) (x : ℝ) :
    WA.evalC (WA.toZero (c • a)) (x : WA.Circ) =
      (c : ℂ) * WA.evalC (WA.toZero a) (x : WA.Circ) := by
  rw [toZero_real_smul, map_smul]
  rfl

@[simp]
theorem staticEval_zero (r : ℕ) :
    staticEval (0 : WA r) = 0 := by
  funext x
  rw [staticEval, toZero_zero, map_zero]
  rfl

@[simp]
theorem staticEval_one (r : ℕ) :
    staticEval (1 : WA r) = 1 := by
  funext x
  rw [staticEval, toZero_one, map_one]
  rfl

theorem staticEval_add {r : ℕ} (a b : WA r) :
    staticEval (a + b) = staticEval a + staticEval b := by
  funext x
  rw [Pi.add_apply, staticEval, staticEval, staticEval,
    evalC_toZero_add]
  rfl

theorem staticEval_sub {r : ℕ} (a b : WA r) :
    staticEval (a - b) = staticEval a - staticEval b := by
  funext x
  rw [Pi.sub_apply, staticEval, staticEval, staticEval,
    evalC_toZero_sub]
  rfl

theorem staticEval_real_smul {r : ℕ} (c : ℝ) (a : WA r) :
    staticEval (c • a) = c • staticEval a := by
  funext x
  rw [Pi.smul_apply, staticEval, staticEval,
    evalC_toZero_real_smul]
  simp

theorem staticEval_mul_evenReal {r : ℕ}
    (a b : EvenRealWA r) :
    staticEval (a.1 * b.1) = staticEval a.1 * staticEval b.1 := by
  funext x
  rw [Pi.mul_apply, staticEval, evalC_toZero_mul,
    evalC_evenReal_eq_ofReal_staticEval,
    evalC_evenReal_eq_ofReal_staticEval]
  simp

theorem staticEval_pow_evenReal {r : ℕ}
    (a : EvenRealWA r) (n : ℕ) :
    staticEval (a.1 ^ n) = (staticEval a.1) ^ n := by
  funext x
  rw [Pi.pow_apply, staticEval, evalC_toZero_pow,
    evalC_evenReal_eq_ofReal_staticEval]
  norm_cast

end ShenWork.M3Counterexample
