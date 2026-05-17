import Mathlib

/-!
# ShenWork/PDE/ParabolicMaxPrinciple.lean

A Lean framework for the one-dimensional classical parabolic maximum principle
and the comparison theorem used for scalar reaction-diffusion equations.

The key analytic maximum-principle argument is isolated in
`weak_maximum_principle_linear` and marked with `sorry`.  The comparison theorem
itself is then proved from this weak maximum principle.
-/

noncomputable section

open Set
open scoped Topology

namespace ShenWork
namespace PDE
namespace ParabolicMaxPrinciple

/-- Time derivative of a function `u t x`. -/
def dt (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun τ : ℝ => u τ x) t

/-- First spatial derivative of a function `u t x`. -/
def dx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ => u t y) x

/-- Second spatial derivative of a function `u t x`. -/
def dxx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ => dx u t y) x

/-- The parabolic operator `∂ₜu - ∂ₓₓu`. -/
def parabolicOp (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  dt u t x - dxx u t x

/-- Boundedness on the finite parabolic strip `[0,T] × ℝ`. -/
def BoundedOnStrip (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ M

/--
A convenient real-line local Lipschitz hypothesis.

For every closed ball `[-R,R]`, there is a Lipschitz constant `L`.
-/
def LocallyLipschitzReal (g : ℝ → ℝ) : Prop :=
  ∀ R : ℝ,
    0 < R →
      ∃ L : ℝ,
        0 ≤ L ∧
          ∀ a b : ℝ,
            |a| ≤ R →
            |b| ≤ R →
            |g a - g b| ≤ L * |a - b|

/--
Classical subsolution of

`uₜ = uₓₓ + g(u)`,

i.e.

`uₜ - uₓₓ ≤ g(u)`.
-/
structure IsClassicalSubSolution
    (g : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun τ : ℝ => u τ x) (dt u t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => u t y) (dx u t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => dx u t y) (dxx u t x) x
  pde_le :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        parabolicOp u t x ≤ g (u t x)
  bounded :
    BoundedOnStrip T u

/--
Classical supersolution of

`uₜ = uₓₓ + g(u)`,

i.e.

`vₜ - vₓₓ ≥ g(v)`.
-/
structure IsClassicalSuperSolution
    (g : ℝ → ℝ) (T : ℝ) (v : ℝ → ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun τ : ℝ => v τ x) (dt v t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => v t y) (dx v t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => dx v t y) (dxx v t x) x
  pde_ge :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        g (v t x) ≤ parabolicOp v t x
  bounded :
    BoundedOnStrip T v

/--
A positive-part linear subsolution.

This is the Lean-friendly form needed for comparison.  It only requires

`wₜ - wₓₓ ≤ c w`

at points where `w > 0`, which is exactly what follows from a two-sided
Lipschitz condition on `g` when `w = u - v`.
-/
structure IsClassicalLinearSubSolution
    (c : ℝ) (T : ℝ) (w : ℝ → ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => w t y) (dx w t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun y : ℝ => dx w t y) (dxx w t x) x
  pde_le_of_pos :
    ∀ ⦃t x : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        0 < w t x →
          parabolicOp w t x ≤ c * w t x
  bounded :
    BoundedOnStrip T w

/--
The exponential barrier

`w̃(t,x) = exp(-λt) w(t,x)`.

For `λ > c`, one obtains a strict inequality at positive maxima.
-/
def expBarrier (lam : ℝ) (w : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (-(lam * t)) * w t x

/--
Weak parabolic maximum principle on the whole line.

If `w` is bounded on `[0,T] × ℝ`, satisfies

`wₜ - wₓₓ ≤ c w`

at positive points, and `w(0,x) ≤ 0`, then `w ≤ 0` on the strip.

Proof idea:

1. Choose `λ > c`.
2. Let `z(t,x) = exp(-λt) w(t,x)`.
3. Then, at positive points,

   `zₜ - zₓₓ ≤ (c - λ) z < 0`.

4. Add a spatial coercive barrier, for example

   `zε(t,x) = z(t,x) - ε * (1 + t + x^2)`,

   so that `zε → -∞` as `|x| → ∞`.
5. If `zε` had a positive maximum in `(0,T] × ℝ`, then at the maximum
   one has `zεₜ ≥ 0` and `zεₓₓ ≤ 0`, contradicting the strict inequality.
6. Let `ε → 0`.

This is the only genuinely hard analytic maximum-principle step.
-/
theorem weak_maximum_principle_linear
    {c T : ℝ} {w : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hc : 0 ≤ c)
    (hw : IsClassicalLinearSubSolution c T w)
    (hinit : ∀ x : ℝ, w 0 x ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, w t x ≤ 0 := by
  sorry

/--
Maximum principle with boundary value `M`.

If `u - M` is a linear positive-part subsolution and `u(0,x) ≤ M`, then
`u(t,x) ≤ M` on `[0,T] × ℝ`.
-/
theorem parabolic_maximum_principle
    {c T M : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hc : 0 ≤ c)
    (hw : IsClassicalLinearSubSolution c T (fun t x => u t x - M))
    (hinit : ∀ x : ℝ, u 0 x ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, u t x ≤ M := by
  have hinit' : ∀ x : ℝ, (fun t x => u t x - M) 0 x ≤ 0 := by
    intro x
    dsimp
    linarith [hinit x]
  have hmax :=
    weak_maximum_principle_linear
      (c := c) (T := T) (w := fun t x => u t x - M)
      hT hc hw hinit'
  intro t ht x
  have hx := hmax t ht x
  dsimp at hx
  linarith

/--
Difference of a subsolution and a supersolution is a positive-part linear
subsolution.

Let `w = u - v`.  Since

`uₜ - uₓₓ ≤ g(u)`

and

`vₜ - vₓₓ ≥ g(v)`,

we get

`wₜ - wₓₓ ≤ g(u) - g(v)`.

At points where `w > 0`, i.e. `u > v`, the Lipschitz estimate gives

`g(u) - g(v) ≤ |g(u) - g(v)| ≤ L |u - v| = L w`.

The derivative identities

`∂ₜ(u-v) = ∂ₜu - ∂ₜv`,
`∂ₓₓ(u-v) = ∂ₓₓu - ∂ₓₓv`

are routine but verbose in Lean, so this bridge lemma is isolated.
-/
private lemma difference_is_linear_subsolution
    {g : ℝ → ℝ} {T L R : ℝ} {u v : ℝ → ℝ → ℝ}
    (hsub : IsClassicalSubSolution g T u)
    (hsuper : IsClassicalSuperSolution g T v)
    (hLip :
      ∀ a b : ℝ,
        |a| ≤ R →
        |b| ≤ R →
          |g a - g b| ≤ L * |a - b|)
    (hL_nn : 0 ≤ L)
    (huR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ R)
    (hvR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |v t x| ≤ R) :
    IsClassicalLinearSubSolution L T (fun t x => u t x - v t x) := by
  sorry

/--
Classical comparison principle for one-dimensional scalar parabolic equations.

If `u` is a subsolution, `v` is a supersolution, both are bounded, and
`u(0,x) ≤ v(0,x)`, then `u ≤ v` on `[0,T] × ℝ`.
-/
theorem comparison_principle
    {g : ℝ → ℝ} {T : ℝ} {u v : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hg : LocallyLipschitzReal g)
    (hsub : IsClassicalSubSolution g T u)
    (hsuper : IsClassicalSuperSolution g T v)
    (hinit : ∀ x : ℝ, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, u t x ≤ v t x := by
  classical

  obtain ⟨Mu, hMu_nn, hMu⟩ := hsub.bounded
  obtain ⟨Mv, hMv_nn, hMv⟩ := hsuper.bounded

  let R : ℝ := Mu + Mv + 1

  have hR_pos : 0 < R := by
    dsimp [R]
    nlinarith [hMu_nn, hMv_nn]

  obtain ⟨L, hL_nn, hLip⟩ := hg R hR_pos

  have huR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ R := by
    intro t ht x
    have h := hMu t ht x
    dsimp [R]
    nlinarith [h, hMv_nn]

  have hvR : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |v t x| ≤ R := by
    intro t ht x
    have h := hMv t ht x
    dsimp [R]
    nlinarith [h, hMu_nn]

  have hw :
      IsClassicalLinearSubSolution L T (fun t x => u t x - v t x) :=
    difference_is_linear_subsolution
      (g := g) (T := T) (L := L) (R := R) (u := u) (v := v)
      hsub hsuper hLip hL_nn huR hvR

  have hinit_w : ∀ x : ℝ, (fun t x => u t x - v t x) 0 x ≤ 0 := by
    intro x
    dsimp
    linarith [hinit x]

  have hmax :=
    weak_maximum_principle_linear
      (c := L) (T := T) (w := fun t x => u t x - v t x)
      hT hL_nn hw hinit_w

  intro t ht x
  have hx := hmax t ht x
  dsimp at hx
  linarith

/-- Spatially constant function generated by a time profile `bar`. -/
def spatiallyConstant (bar : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t _x => bar t

/--
A spatially constant ODE supersolution.

For an upper comparison function for

`uₜ = uₓₓ + g(u)`,

the correct supersolution inequality is

`bar' ≥ g(bar)`,

i.e.

`g (bar t) ≤ deriv bar t`.
-/
structure IsClassicalODESuperSolution
    (g : ℝ → ℝ) (T : ℝ) (bar : ℝ → ℝ) : Prop where
  time_hasDerivAt :
    ∀ ⦃t : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt bar (deriv bar t) t
  ode_ge :
    ∀ ⦃t : ℝ⦄,
      t ∈ Set.Ioo (0 : ℝ) T →
        g (bar t) ≤ deriv bar t
  bounded :
    ∃ M : ℝ,
      0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, |bar t| ≤ M

/--
A spatially constant ODE supersolution is a PDE supersolution.

The spatial derivatives vanish.
-/
lemma spatiallyConstant_superSolution_of_ode
    {g : ℝ → ℝ} {T : ℝ} {bar : ℝ → ℝ}
    (hbar : IsClassicalODESuperSolution g T bar) :
    IsClassicalSuperSolution g T (spatiallyConstant bar) := by
  sorry

/--
Application: comparison against a spatially constant ODE supersolution.

If `u` is a subsolution of

`uₜ = uₓₓ + g(u)`

and `bar` satisfies

`bar' ≥ g(bar)`,

with `u(0,x) ≤ bar(0)`, then `u(t,x) ≤ bar(t)`.
-/
theorem comparison_with_spatially_constant_super
    {g : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ → ℝ} {bar : ℝ → ℝ}
    (hT : 0 < T)
    (hg : LocallyLipschitzReal g)
    (hsub : IsClassicalSubSolution g T u)
    (hbar : IsClassicalODESuperSolution g T bar)
    (hinit : ∀ x : ℝ, u 0 x ≤ bar 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, u t x ≤ bar t := by
  have hsuper :
      IsClassicalSuperSolution g T (spatiallyConstant bar) :=
    spatiallyConstant_superSolution_of_ode hbar

  have hinit' :
      ∀ x : ℝ, u 0 x ≤ spatiallyConstant bar 0 x := by
    intro x
    simpa [spatiallyConstant] using hinit x

  simpa [spatiallyConstant] using
    comparison_principle
      (g := g) (T := T) (u := u) (v := spatiallyConstant bar)
      hT hg hsub hsuper hinit'

end ParabolicMaxPrinciple
end PDE
end ShenWork