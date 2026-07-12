import Mathlib

/-!
# Derivative parity: `deriv` of an even function is odd (about a point)

The weak-H² Neumann witness for the chemotaxis divergence source rests on the
parity chain `R even ⇒ ∂ₓR odd ⇒ flux Q odd ⇒ source ∂ₓQ even`.  The repo has the
resolver even-reflection (`intervalResolverLiftR_even`) and the coefficient-level
parity (`OpCoeffBridge`), but not the elementary **function-level** fact that the
derivative of a function even about a point is odd about that point.  These are
those base lemmas, self-contained on Mathlib, for both endpoints `0` and `1`.

`EvenAboutZero f := ∀ x, f (-x) = f x` (matching `IntervalSourceRepresentative`);
"even about `1`" is `∀ x, f (2 - x) = f x`.
-/

namespace ShenWork.Paper2.EvenDerivParity

/-- **The derivative of a function even about `0` is odd about `0`.**
If `f (-x) = f x` everywhere and `f` has derivative `f'`, then `f' (-x) = - f' x`. -/
theorem deriv_odd_of_evenAboutZero {f f' : ℝ → ℝ}
    (heven : ∀ x, f (-x) = f x)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    f' (-x) = - f' x := by
  -- x ↦ f (-x) has derivative -f'(-x) at x (chain rule with negation)
  have h1 : HasDerivAt (fun y => f (-y)) (-f' (-x)) x := by
    have hcomp := (hderiv (-x)).comp x (hasDerivAt_neg x)
    simpa using hcomp
  -- but f (-·) = f, so that derivative is also f' x
  have hfun : (fun y => f (-y)) = f := by funext y; exact heven y
  have h2 : HasDerivAt (fun y => f (-y)) (f' x) x := by rw [hfun]; exact hderiv x
  have := h1.unique h2
  linarith

/-- **The derivative of a function even about `1` is odd about `1`.**
If `f (2 - x) = f x` everywhere and `f` has derivative `f'`, then
`f' (2 - x) = - f' x` (antisymmetry of `f'` about `x = 1`). -/
theorem deriv_odd_of_evenAboutOne {f f' : ℝ → ℝ}
    (heven : ∀ x, f (2 - x) = f x)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    f' (2 - x) = - f' x := by
  -- x ↦ f (2 - x) has derivative -f'(2-x) at x
  have hlin : HasDerivAt (fun y : ℝ => 2 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 2
  have h1 : HasDerivAt (fun y => f (2 - y)) (-f' (2 - x)) x := by
    have hcomp := (hderiv (2 - x)).comp x hlin
    simpa using hcomp
  have hfun : (fun y => f (2 - y)) = f := by funext y; exact heven y
  have h2 : HasDerivAt (fun y => f (2 - y)) (f' x) x := by rw [hfun]; exact hderiv x
  have := h1.unique h2
  linarith

/-- Endpoint corollary at `0`: an odd-about-`0` derivative vanishes at `0`. -/
theorem deriv_zero_at_zero_of_evenAboutZero {f f' : ℝ → ℝ}
    (heven : ∀ x, f (-x) = f x)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    f' 0 = 0 := by
  have h := deriv_odd_of_evenAboutZero heven hderiv 0
  simp only [neg_zero] at h
  linarith

/-- Endpoint corollary at `1`: an odd-about-`1` derivative vanishes at `1`. -/
theorem deriv_zero_at_one_of_evenAboutOne {f f' : ℝ → ℝ}
    (heven : ∀ x, f (2 - x) = f x)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    f' 1 = 0 := by
  have h := deriv_odd_of_evenAboutOne heven hderiv 1
  norm_num at h
  linarith

end ShenWork.Paper2.EvenDerivParity
