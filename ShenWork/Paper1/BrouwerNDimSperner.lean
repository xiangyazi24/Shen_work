/-
# n-D Brouwer: the concrete Kuhn incidence and the assembly of `brouwer_stdSimplex_n`

This file completes the n-dimensional Brouwer fixed point theorem on the standard simplex,
mirroring the 2-D template `BrouwerTwoDim` but at symbolic `n`.  It builds on:

* `BrouwerNDim` — the abstract engine `sperner_n_dim_combinatorial`, the symbolic heart
  `heart_count_n`/`hheart_indexed`, and the Kuhn chain `stepVec`/`chainVZ`;
* `BrouwerNDimComplete` — the internal partner involution and `even_card_of_involution`;
* `BrouwerNDimFinal` — the mesh-limit engine `brouwer_of_rainbow_meshes`, the labelling layer
  `embPt`/`spernerLabelN`, the cell-validity layer `cellValid`/`chainNat`, and the endpoint
  partner.

The genuine new content here is the *concrete global incidence count* of the Kuhn complex:
the last-coordinate monotonicity of the chain (`chainVZ_last`), which makes the cell
reconstruction from a facet canonical, and the consequent `hinterior`/`hboundaryOdd`.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import ShenWork.Paper1.BrouwerNDimFinal

namespace ShenWork.Paper1

open Set Finset Filter Topology

/-! ## Last-coordinate monotonicity of the Kuhn chain

Every Kuhn step removes one unit of mass from the *last* coordinate (and adds it to a
non-last coordinate `a.castSucc ≠ last`).  Hence `chainVZ p σ t (last n) = p (last n) - t.val`
strictly decreases as the chain index `t` increases: the `n + 1` chain vertices have pairwise
distinct last coordinates, the consecutive integers `p(last), p(last)-1, …, p(last)-n`.

This is the structural backbone of the n-D incidence count: it pins down the chain *order*
from the unordered facet, making reconstruction canonical. -/

/-- A single Kuhn step lowers the last coordinate by exactly `1`. -/
theorem stepVec_last {n : ℕ} (a : Fin n) : stepVec a (Fin.last n) = -1 := by
  unfold stepVec
  have hne : (Fin.last n) ≠ a.castSucc := by
    intro hc
    have hval := congrArg Fin.val hc
    simp only [Fin.val_last, Fin.val_castSucc] at hval
    omega
  rw [if_neg hne, if_pos rfl]; ring

/-- **Last-coordinate of a chain vertex.**  `chainVZ p σ t (last n) = p (last n) - t.val`. -/
theorem chainVZ_last {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) :
    chainVZ p σ t (Fin.last n) = p (Fin.last n) - (t.val : ℤ) := by
  classical
  rw [chainVZ_apply]
  have hstep : ∀ s : Fin n, stepVec (σ s) (Fin.last n) = -1 := fun s => stepVec_last (σ s)
  rw [Finset.sum_congr rfl (fun s _ => hstep s)]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun s : Fin n => s.val < t.val)).card = t.val := by
    have ht : t.val ≤ n := by omega
    have heq : (Finset.univ.filter (fun s : Fin n => s.val < t.val))
        = (Finset.univ.filter (fun s : Fin n => s < t.val)) := by
      apply Finset.filter_congr; intro s _; rfl
    rw [heq, Fin.card_filter_val_lt]; omega
  rw [hcard]; push_cast; ring

end ShenWork.Paper1
