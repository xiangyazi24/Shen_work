/-
# Brouwer's fixed point theorem (layered construction)

Brouwer's fixed point theorem is absent from Mathlib v4.29.1 (see the stall report in
`ShenWork/Paper1/SchauderFixedPoint.lean`).  This file builds toward it in layers, on top
of the committed combinatorial Sperner engine (`ShenWork.Paper1.Sperner`:
`sperner_one_dim`, `sperner_two_dim_combinatorial`) and the committed one-dimensional
Schauder fixed point (`ShenWork.Paper1.schauder_fixedPoint_real`).

The target form (for the Schauder/traveling-wave construction) is a fixed point of a
continuous self-map of a nonempty compact convex set in `EuclideanSpace ℝ (Fin n)`:

```
theorem brouwer_fixedPoint {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_ne : K.Nonempty) (hK_conv : Convex ℝ K) (hK_cpt : IsCompact K)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousOn f K) (hmaps : Set.MapsTo f K K) : ∃ x ∈ K, f x = x
```

## Contents — what is fully proved here (axiom-clean)

### Layer A — dimension one (fully closed)
* `brouwer_dim_one_Icc` — a continuous self-map of `[0,1] ⊆ ℝ` has a fixed point
  (the `n = 1` Brouwer, directly from the IVT).
* `brouwer_fixedPoint_dim_one` — the **target statement, specialized to `n = 1`**: a
  continuous self-map of any nonempty compact convex `K ⊆ EuclideanSpace ℝ (Fin 1)` has a
  fixed point.  Obtained by transporting `schauder_fixedPoint_real` along the continuous
  linear equivalence `EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ`.

### Layer B — the analytic core of the 2-D (and n-D) Sperner route (fully closed)
The route to higher-dimensional Brouwer is: triangulate the standard simplex `Δⁿ`,
*label* each vertex `v` by `ℓ(v) = min{i | f(v)ᵢ ≤ vᵢ ∧ vᵢ > 0}`, apply
`sperner_two_dim_combinatorial` to get a rainbow simplex at every mesh, then extract a
convergent subsequence of barycenters whose limit `x*` satisfies `f(x*)ᵢ ≤ x*ᵢ` for all
`i`, forcing `f(x*) = x*`.  The two *analytic* bricks of this route are proved here,
independent of the (heavy) triangulation geometry:
* `sperner_label_nonempty` — the Sperner label set is nonempty (so `ℓ` is well-defined):
  for `v, f(v) ∈ Δⁿ` there is a coordinate `i` with `vᵢ > 0` and `f(v)ᵢ ≤ vᵢ`.  This is
  the pigeonhole forced by `∑ f(v) = ∑ v = 1` and is the Sperner boundary condition's
  engine.
* `eq_of_forall_le_on_stdSimplex` — the mesh→0 *closure* step: a point `x ∈ Δⁿ` with
  `f(x)ᵢ ≤ xᵢ` for **all** `i` is a fixed point.  This consumes the limit produced by
  Bolzano–Weierstrass (`IsCompact.tendsto_subseq`, present in Mathlib on the compact
  `stdSimplex`).

## Precise stall (next brick toward full 2-D / n-D Brouwer)
See the report at the bottom of the file: what remains is purely the *triangulation
incidence* needed to instantiate `sperner_two_dim_combinatorial` — a concrete Kuhn
subdivision of `Δ²` with its door/boundary incidence facts (`hheart`, `hinterior`,
`hboundaryOdd`, `hboundaryCount`).  The labeling and limit machinery above are exactly the
glue that connects that combinatorial output to the analytic fixed point.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import ShenWork.Paper1.Sperner
import ShenWork.Paper1.SchauderFixedPoint

namespace ShenWork.Paper1

open Set Finset

/-! ## Layer A — dimension one -/

/-- **Brouwer in dimension one, interval form.**
A continuous self-map of the unit interval `[0,1] ⊆ ℝ` has a fixed point.  This is the
`n = 1` Brouwer theorem, proved directly from the Intermediate Value Theorem applied to
`g x = f x − x`. -/
theorem brouwer_dim_one_Icc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hmaps : Set.MapsTo f (Icc 0 1) (Icc 0 1)) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = x := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨c, hc, hfix⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hf h01 hmaps
  exact ⟨c, hc, hfix⟩

/-- The continuous linear equivalence `EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ` used to transport
the one-dimensional fixed-point theorem into the target `EuclideanSpace` shape. -/
noncomputable def euclidOneEquiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- **Target statement, dimension one.**
A continuous self-map of a nonempty compact convex set `K ⊆ EuclideanSpace ℝ (Fin 1)` has a
fixed point.  This is `brouwer_fixedPoint` at `n = 1`, obtained by conjugating the committed
one-dimensional Schauder fixed point `schauder_fixedPoint_real` through
`euclidOneEquiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ`. -/
theorem brouwer_fixedPoint_dim_one {K : Set (EuclideanSpace ℝ (Fin 1))}
    (hK_ne : K.Nonempty) (hK_conv : Convex ℝ K) (hK_cpt : IsCompact K)
    {f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (hf : ContinuousOn f K) (hmaps : Set.MapsTo f K K) : ∃ x ∈ K, f x = x := by
  set e := euclidOneEquiv with he
  set K'' : Set ℝ := Set.image (⇑e) K with hK''
  have hne'' : K''.Nonempty := hK_ne.image e
  have hcpt'' : IsCompact K'' := hK_cpt.image e.continuous
  have hconv'' : Convex ℝ K'' := hK_conv.linear_image e.toLinearMap
  -- conjugated map `g = e ∘ f ∘ e.symm`, a continuous self-map of `K''`.
  set g : ℝ → ℝ := fun y => e (f (e.symm y)) with hg
  have hg_cont : ContinuousOn g K'' := by
    apply e.continuous.comp_continuousOn
    apply hf.comp (e.symm.continuous.continuousOn)
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy]; simpa using hx
  have hg_maps : Set.MapsTo g K'' K'' := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨f x, hmaps hx, ?_⟩
    rw [hg, ← hxy]; simp
  obtain ⟨U, hU, hfix⟩ :=
    schauder_fixedPoint_real hne'' hconv'' hcpt'' hg_cont hg_maps
  refine ⟨e.symm U, ?_, ?_⟩
  · obtain ⟨x, hx, hxU⟩ := hU; rw [← hxU]; simpa using hx
  · have hex : e (f (e.symm U)) = U := hfix
    exact e.injective (by rw [hex, e.apply_symm_apply])

/-! ## Layer B — the analytic core of the Sperner route to higher-dimensional Brouwer -/

/-- **Sperner label set is nonempty (the boundary-condition engine).**
For `v` and `f(v)` in the standard simplex `Δⁿ`, there is a coordinate `i` with `vᵢ > 0`
and `f(v)ᵢ ≤ vᵢ`.  Hence the Sperner label `ℓ(v) = min{i | f(v)ᵢ ≤ vᵢ, vᵢ > 0}` is
well-defined at every vertex.  Pigeonhole: were `vᵢ < f(v)ᵢ` at every coordinate with
`vᵢ > 0`, then `∑ v < ∑ f(v)`, contradicting `∑ v = ∑ f(v) = 1`. -/
theorem sperner_label_nonempty {n : ℕ} (v fv : Fin (n + 1) → ℝ)
    (hv : v ∈ stdSimplex ℝ (Fin (n + 1))) (hfv : fv ∈ stdSimplex ℝ (Fin (n + 1))) :
    ∃ i, v i > 0 ∧ fv i ≤ v i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hv0, hvsum⟩ := hv
  obtain ⟨hfv0, hfvsum⟩ := hfv
  -- componentwise `v i ≤ fv i`, strict wherever `v i > 0`.
  have hle : ∀ i, v i ≤ fv i := by
    intro i
    rcases lt_or_eq_of_le (hv0 i) with h | h
    · exact le_of_lt (hcon i h)
    · rw [← h]; exact hfv0 i
  -- some coordinate is positive, since `∑ v = 1 ≠ 0`.
  have hex : ∃ i, 0 < v i := by
    by_contra h2; push Not at h2
    have hz : ∀ i, v i = 0 := fun i => le_antisymm (h2 i) (hv0 i)
    rw [Finset.sum_congr rfl (fun i _ => hz i)] at hvsum
    simp at hvsum
  obtain ⟨j, hj⟩ := hex
  have hstrict : ∑ i, v i < ∑ i, fv i :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hcon j hj⟩
  rw [hvsum, hfvsum] at hstrict
  exact lt_irrefl 1 hstrict

/-- **Mesh→0 closure step.**
A point `x ∈ Δⁿ` whose image satisfies `f(x)ᵢ ≤ xᵢ` for **every** coordinate `i` is a
fixed point: `f(x) = x`.  This is the analytic payoff of the Sperner route — the limit
`x*` of rainbow barycenters satisfies exactly this hypothesis (all labels appear, so every
coordinate weakly decreases), and `∑ f(x) = ∑ x = 1` upgrades the inequalities to
equalities. -/
theorem eq_of_forall_le_on_stdSimplex {n : ℕ} (x fx : Fin (n + 1) → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin (n + 1))) (hfx : fx ∈ stdSimplex ℝ (Fin (n + 1)))
    (hle : ∀ i, fx i ≤ x i) : fx = x := by
  obtain ⟨_, hxsum⟩ := hx
  obtain ⟨_, hfxsum⟩ := hfx
  funext i
  by_contra hne
  have hlt : fx i < x i := lt_of_le_of_ne (hle i) hne
  have hstrict : ∑ j, fx j < ∑ j, x j :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
  rw [hxsum, hfxsum] at hstrict
  exact lt_irrefl 1 hstrict

/-! ## Precise stall report — next brick toward full 2-D / n-D Brouwer

**What is closed.**  Layer A gives Brouwer in dimension one in both the interval form and
the target `EuclideanSpace ℝ (Fin 1)` form.  Layer B gives the two analytic bricks of the
Sperner route on `Δⁿ`, in full generality over `n`: the label set is nonempty
(`sperner_label_nonempty`, the Sperner boundary engine) and the all-coordinates-decrease
limit point is a fixed point (`eq_of_forall_le_on_stdSimplex`, the mesh→0 closure).  These
are the *glue* lemmas: they connect the combinatorial output of
`sperner_two_dim_combinatorial` to an analytic fixed point.

**What remains (the single missing brick).**  To assemble 2-D Brouwer one must *instantiate*
the abstract `sperner_two_dim_combinatorial` with a concrete triangulation of `Δ²` at mesh
`1/k` and discharge its four geometric hypotheses.  Concretely, the next brick is the

  TRIANGULATION-INCIDENCE LEMMA (Kuhn / order subdivision of `Δ²` at mesh `1/k`):
  Let the vertices be the lattice points `p/k` with `p : Fin 3 → ℕ`, `∑ p = k`, and let the
  cells be the `order-chain` 2-simplices (Kuhn simplices) `{p, p + e_{σ1}, p + e_{σ1} + e_{σ2}}`.
  Provide `Δ := cells`, `ε := edges`, `bounds`, `isDoor` (= the colour pair on the edge is
  `{0,1}` under the Sperner labeling `ℓ` above), `isBoundary` (= the edge lies on the bottom
  face `{x : x₂ = 0}`), `isRainbow := isRainbowTri ∘ (labels)`, and prove:
    (i)   `hheart`  : reduces *definitionally* to `doorCount_odd_iff_rainbow` (already proved),
          once `bounds`/`isDoor`/`isRainbow` are wired to the three vertex colours of a cell;
    (ii)  `hinterior` : every interior door edge bounds exactly two cells  (the core planar
          incidence count — this is the heavy combinatorial geometry);
    (iii) `hboundaryOdd` : every boundary door edge bounds exactly one cell;
    (iv)  `hboundaryCount` : an odd number of boundary doors — this is **already available**
          as `sperner_one_dim` applied to the bottom edge's restricted 2-labeling.
  Mathlib has no API for this subdivision; (ii) is the genuine missing geometry.  With it,
  `sperner_two_dim_combinatorial` yields a rainbow cell at every `k`; `sperner_label_nonempty`
  guarantees the labeling is well-defined; the barycenters live in the compact `stdSimplex`
  so `IsCompact.tendsto_subseq` extracts a convergent subsequence; uniform continuity of `f`
  on the compact simplex pushes the per-coordinate label inequalities to the limit, giving
  `∀ i, f(x*)ᵢ ≤ x*ᵢ`; and `eq_of_forall_le_on_stdSimplex` closes `f(x*) = x*`.

**n-D induction.**  The same shape lifts verbatim once `sperner_two_dim_combinatorial` is
generalized to `sperner_n_dim_combinatorial` (an `(n−1)`-face boundary induction); the
analytic bricks here are already dimension-agnostic (`Fin (n+1)`).
-/

end ShenWork.Paper1
