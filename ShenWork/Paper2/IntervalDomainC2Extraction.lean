/-
  B2 (MinPersistence): pointwise `HasDerivAt` extraction from interior `C²`.

  The classical-solution regularity conjuncts give `ContDiffOn ℝ 2 (lift) (Ioo 0 1)`
  for the `u`- and `v`-slices.  This file extracts the two pointwise facts the
  min-point machinery consumes at an interior `x*`:
    `HasDerivAt (lift) (deriv lift x*) x*`            (first derivative `v_x`),
    `HasDerivAt (deriv lift) (deriv (deriv lift) x*) x*`  (second derivative).
  via `ContDiffOn.deriv_of_isOpen` on the open interior.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **`C²`-to-`HasDerivAt` pair (interior).**  On an open set, a `C²` function
has the first two derivatives at every point as genuine `HasDerivAt` facts. -/
theorem contDiffOn_two_hasDerivAt_pair
    {f : ℝ → ℝ} {s : Set ℝ} (hopen : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt f (deriv f x) x ∧
      HasDerivAt (deriv f) (deriv (deriv f) x) x := by
  -- `f` is differentiable at `x`.
  have hf1 : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hx)
  -- `deriv f` is `C¹` on the open set, hence differentiable at `x`.
  have hderiv_c1 : ContDiffOn ℝ 1 (deriv f) s :=
    hf.deriv_of_isOpen hopen (by norm_num)
  have hf2 : DifferentiableAt ℝ (deriv f) x :=
    (hderiv_c1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hx)
  exact ⟨hf1.hasDerivAt, hf2.hasDerivAt⟩

end ShenWork.MinPersistenceAtoms
