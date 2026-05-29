/-
  ShenWork/PDE/IntervalFullSemigroupNeumann.lean

  **Two-endpoint Neumann property of the full Neumann semigroup.**

  The Path-A Duhamel framework was previously built on the zeroth-reflection
  semigroup `intervalSemigroupOperator` (kernel `(1/2)(heat(x-y)+heat(x+y))`),
  which reflects only about `0` and is therefore Neumann at the left endpoint
  `x = 0` only — making the `hGradEq` boundary identity FALSE at `x = 1`
  (ROUND-15 finding).

  The full Neumann kernel
  `intervalNeumannFullKernel t x y = ∑' k:ℤ, heat(x-y+2k) + heat(x+y+2k)`
  is the method-of-images periodised kernel: it is **even about `0`** and
  **period `2`** in `x`, hence also **even about `1`**.  Consequently the full
  semigroup `intervalFullSemigroupOperator t f` is even about `0` and `1`, so
  its spatial derivative vanishes at BOTH endpoints — the genuine homogeneous
  Neumann boundary condition.

  This file proves, with no `sorry`/`admit`/custom `axiom`:
  * `deriv_eq_zero_of_even_about` — a real-analysis helper: a function even
    about a point has zero derivative there.
  * `intervalNeumannFullKernel_even_zero`, `_period_two`, `_even_one` — the
    lattice-reindex symmetries of the full kernel.
  * `intervalFullSemigroupOperator_even_zero`, `_even_one` — inherited
    semigroup symmetries.
  * `intervalFullSemigroupOperator_deriv_at_zero_eq_zero`,
    `_deriv_at_one_eq_zero` — the two-endpoint Neumann condition.
-/
import ShenWork.PDE.IntervalNeumannFullKernel

open MeasureTheory
open scoped Topology

namespace ShenWork

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

/-- **A function even about a point has zero derivative there.**  If
`f (2c − x) = f x` for all `x` (reflection symmetry about `c`), then
`deriv f c = 0`: differentiating both sides via the chain rule gives
`deriv f c = − deriv f c`. -/
theorem deriv_eq_zero_of_even_about {f : ℝ → ℝ} {c : ℝ}
    (hsymm : ∀ x : ℝ, f (2 * c - x) = f x) : deriv f c = 0 := by
  by_cases hdiff : DifferentiableAt ℝ f c
  · have h1 : HasDerivAt f (deriv f c) c := hdiff.hasDerivAt
    have hinner : HasDerivAt (fun x : ℝ => 2 * c - x) (-1 : ℝ) c := by
      simpa using (hasDerivAt_const c (2 * c)).sub (hasDerivAt_id c)
    have h1' : HasDerivAt f (deriv f c) (2 * c - c) := by
      rw [show 2 * c - c = c by ring]; exact h1
    have hcomp : HasDerivAt (fun x : ℝ => f (2 * c - x)) (deriv f c * (-1)) c := by
      simpa [Function.comp] using h1'.comp c hinner
    have hcomp' : HasDerivAt f (deriv f c * (-1)) c := by
      have hfun : (fun x : ℝ => f (2 * c - x)) = f := funext hsymm
      rwa [hfun] at hcomp
    have heq := h1.unique hcomp'
    have hd : deriv f c * (-1 : ℝ) = - deriv f c := by ring
    rw [hd] at heq
    linarith
  · exact deriv_zero_of_not_differentiableAt hdiff

/-- The full Neumann kernel is **even about `0`** in the spatial variable:
`K t (−x) y = K t x y`, by reindexing the period-`2` lattice `k ↦ −k` and the
evenness of the Gaussian. -/
theorem intervalNeumannFullKernel_even_zero (t x y : ℝ) :
    intervalNeumannFullKernel t (-x) y = intervalNeumannFullKernel t x y := by
  unfold intervalNeumannFullKernel
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun k : ℤ => heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k))]
  refine tsum_congr (fun k => ?_)
  have e1 : heatKernel t (-x - y + 2 * (k : ℝ))
      = heatKernel t (x + y + 2 * ((Equiv.neg ℤ k : ℤ) : ℝ)) := by
    rw [← heatKernel_neg t (x + y + 2 * ((Equiv.neg ℤ k : ℤ) : ℝ))]
    congr 1
    simp only [Equiv.neg_apply]
    push_cast; ring
  have e2 : heatKernel t (-x + y + 2 * (k : ℝ))
      = heatKernel t (x - y + 2 * ((Equiv.neg ℤ k : ℤ) : ℝ)) := by
    rw [← heatKernel_neg t (x - y + 2 * ((Equiv.neg ℤ k : ℤ) : ℝ))]
    congr 1
    simp only [Equiv.neg_apply]
    push_cast; ring
  rw [e1, e2, add_comm]

/-- The full Neumann kernel is **period `2`** in the spatial variable:
`K t (x + 2) y = K t x y`, by reindexing the lattice `k ↦ k + 1`. -/
theorem intervalNeumannFullKernel_period_two (t x y : ℝ) :
    intervalNeumannFullKernel t (x + 2) y = intervalNeumannFullKernel t x y := by
  unfold intervalNeumannFullKernel
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k : ℤ => heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k))]
  refine tsum_congr (fun k => ?_)
  have e1 : heatKernel t (x + 2 - y + 2 * (k : ℝ))
      = heatKernel t (x - y + 2 * ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ)) := by
    congr 1
    simp only [Equiv.coe_addRight]
    push_cast; ring
  have e2 : heatKernel t (x + 2 + y + 2 * (k : ℝ))
      = heatKernel t (x + y + 2 * ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ)) := by
    congr 1
    simp only [Equiv.coe_addRight]
    push_cast; ring
  rw [e1, e2]

/-- The full Neumann kernel is **even about `1`**: `K t (2 − x) y = K t x y`,
combining period `2` with evenness about `0` (`2 − x = (−x) + 2`). -/
theorem intervalNeumannFullKernel_even_one (t x y : ℝ) :
    intervalNeumannFullKernel t (2 - x) y = intervalNeumannFullKernel t x y := by
  rw [show (2 - x : ℝ) = (-x) + 2 by ring,
    intervalNeumannFullKernel_period_two, intervalNeumannFullKernel_even_zero]

/-- The full Neumann semigroup is **even about `0`** in the spatial variable. -/
theorem intervalFullSemigroupOperator_even_zero (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f (-x) = intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  congr 1
  ext y
  rw [intervalNeumannFullKernel_even_zero]

/-- The full Neumann semigroup is **even about `1`** in the spatial variable. -/
theorem intervalFullSemigroupOperator_even_one (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f (2 - x) = intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  congr 1
  ext y
  rw [intervalNeumannFullKernel_even_one]

/-- **Left-endpoint Neumann for the full semigroup**: the spatial derivative of
`intervalFullSemigroupOperator t f` vanishes at `x = 0`. -/
theorem intervalFullSemigroupOperator_deriv_at_zero_eq_zero (t : ℝ) (f : ℝ → ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) 0 = 0 := by
  refine deriv_eq_zero_of_even_about (c := 0) (fun x => ?_)
  rw [show (2 * (0 : ℝ) - x) = -x by ring]
  exact intervalFullSemigroupOperator_even_zero t f x

/-- **Right-endpoint Neumann for the full semigroup**: the spatial derivative of
`intervalFullSemigroupOperator t f` vanishes at `x = 1`. -/
theorem intervalFullSemigroupOperator_deriv_at_one_eq_zero (t : ℝ) (f : ℝ → ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) 1 = 0 := by
  refine deriv_eq_zero_of_even_about (c := 1) (fun x => ?_)
  rw [show (2 * (1 : ℝ) - x) = 2 - x by ring]
  exact intervalFullSemigroupOperator_even_one t f x

/-- The Duhamel **source-integral term** `z ↦ ∫₀^τ S(τ−s)(g s) z ds` is even
about `0`: the integral of even functions is even. -/
theorem intervalFullSemigroup_integral_even_zero (τ : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s) (g s) (-z))
      = ∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s) (g s) z :=
  intervalIntegral.integral_congr
    (fun s _ => intervalFullSemigroupOperator_even_zero (τ - s) (g s) z)

/-- The Duhamel **source-integral term** is even about `1`. -/
theorem intervalFullSemigroup_integral_even_one (τ : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s) (g s) (2 - z))
      = ∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s) (g s) z :=
  intervalIntegral.integral_congr
    (fun s _ => intervalFullSemigroupOperator_even_one (τ - s) (g s) z)

/-- **Left-endpoint Neumann for the full-kernel Duhamel explicit field.**  The
spatial derivative of `z ↦ S(τ) h z + ∫₀^τ S(τ−s)(g s) z ds` vanishes at
`x = 0`: both the initial-data term and the source-integral term are even about
`0`. -/
theorem intervalFullDuhamelExplicit_deriv_at_zero_eq_zero
    (τ : ℝ) (h : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    deriv (fun z : ℝ =>
        intervalFullSemigroupOperator τ h z +
          ∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s) (g s) z) 0 = 0 := by
  refine deriv_eq_zero_of_even_about (c := 0) (fun z => ?_)
  rw [show (2 * (0 : ℝ) - z) = -z by ring,
    intervalFullSemigroupOperator_even_zero,
    intervalFullSemigroup_integral_even_zero]

/-- **Right-endpoint Neumann for the full-kernel Duhamel explicit field** at
`x = 1`. -/
theorem intervalFullDuhamelExplicit_deriv_at_one_eq_zero
    (τ : ℝ) (h : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    deriv (fun z : ℝ =>
        intervalFullSemigroupOperator τ h z +
          ∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s) (g s) z) 1 = 0 := by
  refine deriv_eq_zero_of_even_about (c := 1) (fun z => ?_)
  rw [show (2 * (1 : ℝ) - z) = 2 - z by ring,
    intervalFullSemigroupOperator_even_one,
    intervalFullSemigroup_integral_even_one]

end ShenWork
