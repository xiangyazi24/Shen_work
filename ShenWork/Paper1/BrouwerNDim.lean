/-
# n-D Brouwer fixed point via the Kuhn (order) subdivision of `Δⁿ`

This file generalizes `ShenWork.Paper1.brouwer_stdSimplex_two` to all dimensions, following the
combinatorial-Kuhn route.  The abstract double-counting engine
(`sperner_two_dim_combinatorial`) is already dimension-free, so the genuinely new work is:

* the **n-D Sperner heart** `heart_count_n` — a cell with vertex-colouring
  `c : Fin (n+1) → Fin (n+1)` has an *odd* number of door-facets iff `c` is a bijection
  (rainbow).  A door-facet is a facet (delete-one-vertex) whose `n` colours are exactly
  `{0,…,n-1} = univ.erase (Fin.last n)`;
* the **abstract n-D Sperner lemma** `sperner_n_dim_combinatorial`, the dimension-agnostic
  counting result, stated for general cell/facet `Finset`s.

The concrete Kuhn complex and the mesh-limit assembly to `brouwer_stdSimplex_n` build on these.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import ShenWork.Paper1.BrouwerTwoDim

namespace ShenWork.Paper1

open Set Finset Filter Topology

/-! ## The abstract n-D combinatorial Sperner lemma

The double-counting / `ZMod 2` engine `sperner_two_dim_combinatorial` never refers to the
dimension `2`: it takes opaque `Finset`s of cells and facets with an incidence relation and
the door/boundary/rainbow predicates.  We re-expose it under an `n`-dimensional name. -/

/-- **Abstract n-D combinatorial Sperner lemma.**  Identical to the 2-D engine — the
double-counting argument is dimension-free.  Given a triangulation (`cells`, `facets`) with
door/boundary/rainbow predicates satisfying the local heart identity, the even-interior /
odd-boundary facet incidence, and an odd boundary-door count, the number of rainbow cells is
**odd** (in particular `≥ 1`). -/
theorem sperner_n_dim_combinatorial
    {Cl Fc : Type*}
    (cells : Finset Cl) (facets : Finset Fc)
    (bounds : Cl → Fc → Prop) [DecidableRel bounds]
    (isDoor : Fc → Prop) [DecidablePred isDoor]
    (isBoundary : Fc → Prop) [DecidablePred isBoundary]
    (isRainbow : Cl → Prop) [DecidablePred isRainbow]
    (hheart : ∀ t ∈ cells,
        Odd (facets.filter (fun e => bounds t e ∧ isDoor e)).card ↔ isRainbow t)
    (hinterior : ∀ e ∈ facets, isDoor e → ¬ isBoundary e →
        Even (cells.filter (fun t => bounds t e)).card)
    (hboundaryOdd : ∀ e ∈ facets, isDoor e → isBoundary e →
        Odd (cells.filter (fun t => bounds t e)).card)
    (hboundaryCount : Odd (facets.filter (fun e => isDoor e ∧ isBoundary e)).card) :
    Odd (cells.filter isRainbow).card :=
  sperner_two_dim_combinatorial cells facets bounds isDoor isBoundary isRainbow
    hheart hinterior hboundaryOdd hboundaryCount

/-! ## The n-D Sperner heart

A cell of `Δⁿ` has `n+1` vertices coloured by a function `c : Fin (n+1) → Fin (n+1)`.
The facet opposite vertex `i` carries the colour set `(univ.erase i).image c`.  It is a
*door* iff that colour set is exactly `{0,…,n-1} = univ.erase (Fin.last n)`.  The cell is
*rainbow* iff `c` is a bijection. -/

/-- The colour set on the facet opposite vertex `i`. -/
def facetColors {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) (i : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  (Finset.univ.erase i).image c

/-- The facet opposite `i` is a *door* iff it carries exactly the colours
`{0,…,n-1} = univ.erase (Fin.last n)`. -/
def doorAt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) (i : Fin (n + 1)) : Prop :=
  facetColors c i = Finset.univ.erase (Fin.last n)

instance {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) : DecidablePred (doorAt c) :=
  fun i => by unfold doorAt; infer_instance

/-- The number of door-facets of a cell coloured by `c`. -/
def doorCountN {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) : ℕ :=
  (Finset.univ.filter (doorAt c)).card

/-- A door-facet forces `c` to be injective on the complementary vertex set: the facet
colour set has `n` elements, exactly the cardinality of `univ.erase i`. -/
theorem injOn_of_doorAt {n : ℕ} {c : Fin (n + 1) → Fin (n + 1)} {i : Fin (n + 1)}
    (hi : doorAt c i) : Set.InjOn c ↑(Finset.univ.erase i) := by
  have hcard : (facetColors c i).card = (Finset.univ.erase i).card := by
    rw [hi, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have := Finset.injOn_of_card_image_eq (s := Finset.univ.erase i) (f := c)
    (by rw [facetColors] at hcard; exact hcard)
  simpa using this

/-- Removing one of two equally-coloured vertices leaves the same facet colour set. -/
theorem facetColors_eq_of_dup {n : ℕ} {c : Fin (n + 1) → Fin (n + 1)} {a b : Fin (n + 1)}
    (hab : a ≠ b) (hc : c a = c b) : facetColors c a = facetColors c b := by
  unfold facetColors
  ext x
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨y, hya, rfl⟩
    by_cases hyb : y = b
    · exact ⟨a, hab, by rw [hc, ← hyb]⟩
    · exact ⟨y, hyb, rfl⟩
  · rintro ⟨y, hyb, rfl⟩
    by_cases hya : y = a
    · exact ⟨b, hab.symm, by rw [← hc, ← hya]⟩
    · exact ⟨y, hya, rfl⟩

/-- **¬injective ⟹ even door-count.**  If `c` is not injective, fix a collision `a ≠ b`,
`c a = c b`.  Every door-vertex lies in `{a, b}` (a door forces injectivity off that vertex),
and `a` is a door iff `b` is (same facet colour set).  Hence the door set is `∅` or `{a,b}`. -/
theorem even_doorCountN_of_not_injective {n : ℕ} {c : Fin (n + 1) → Fin (n + 1)}
    (hni : ¬ Function.Injective c) : Even (doorCountN c) := by
  classical
  -- extract a collision pair
  rw [Function.not_injective_iff] at hni
  obtain ⟨a, b, hcab, hab⟩ := hni
  -- the door set is contained in {a, b}
  have hsub : (Finset.univ.filter (doorAt c)) ⊆ {a, b} := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hinj := injOn_of_doorAt hi.2
    by_contra hni'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hni'
    push Not at hni'
    have ha : a ∈ (↑(Finset.univ.erase i) : Set (Fin (n + 1))) := by
      simp [Ne.symm hni'.1]
    have hb : b ∈ (↑(Finset.univ.erase i) : Set (Fin (n + 1))) := by
      simp [Ne.symm hni'.2]
    exact hab (hinj ha hb hcab)
  -- a is a door iff b is a door
  have heq : facetColors c a = facetColors c b := facetColors_eq_of_dup hab hcab
  have hiff : doorAt c a ↔ doorAt c b := by unfold doorAt; rw [heq]
  -- case on whether the door set is empty or all of {a, b}
  by_cases hda : doorAt c a
  · have hdb : doorAt c b := hiff.mp hda
    have : (Finset.univ.filter (doorAt c)) = {a, b} := by
      apply Finset.Subset.antisymm hsub
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [Finset.mem_filter, hda, hdb]
    rw [doorCountN, this, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hdb : ¬ doorAt c b := fun h => hda (hiff.mpr h)
    have : (Finset.univ.filter (doorAt c)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      have : i ∈ ({a, b} : Finset (Fin (n + 1))) → ¬ doorAt c i := by
        intro hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> assumption
      intro hcon
      exact this (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)) hcon
    rw [doorCountN, this, Finset.card_empty]
    exact ⟨0, rfl⟩

/-- **bijective ⟹ door-count = 1.**  When `c` is a bijection, injectivity gives
`facetColors c i = univ.erase (c i)`, so the facet opposite `i` is a door iff `c i =
Fin.last n`; this happens for exactly one `i`. -/
theorem doorCountN_eq_one_of_bijective {n : ℕ} {c : Fin (n + 1) → Fin (n + 1)}
    (hb : Function.Bijective c) : doorCountN c = 1 := by
  classical
  have hinj : Function.Injective c := hb.1
  -- door at i ↔ c i = last
  have hdoor : ∀ i, doorAt c i ↔ c i = Fin.last n := by
    intro i
    unfold doorAt facetColors
    rw [Finset.image_erase hinj, Finset.image_univ_of_surjective hb.2]
    constructor
    · intro h
      by_contra hne
      have hmem : Fin.last n ∈ Finset.univ.erase (c i) :=
        Finset.mem_erase.mpr ⟨fun hcontra => hne hcontra.symm, Finset.mem_univ _⟩
      rw [h] at hmem
      simp at hmem
    · intro h; rw [h]
  -- the door set is the singleton {c⁻¹ last}
  obtain ⟨i0, hi0⟩ := hb.2 (Fin.last n)
  have : (Finset.univ.filter (doorAt c)) = {i0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hdoor i]
    constructor
    · intro h; exact hinj (h.trans hi0.symm)
    · intro h; rw [h, hi0]
  rw [doorCountN, this, Finset.card_singleton]

/-- **The n-D Sperner heart.**  A cell coloured by `c : Fin (n+1) → Fin (n+1)` has an *odd*
number of door-facets iff it is rainbow (`c` is a bijection).  Replaces the 2-D `decide`-over-
`3^3` heart by a structural argument valid for symbolic `n`. -/
theorem heart_count_n {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) :
    Odd (doorCountN c) ↔ Function.Bijective c := by
  constructor
  · intro hodd
    by_contra hnb
    -- not bijective on a finite type ⟺ not injective
    have hni : ¬ Function.Injective c := by
      intro hinj
      exact hnb ⟨hinj, Finite.surjective_of_injective hinj⟩
    exact (Nat.not_odd_iff_even.mpr (even_doorCountN_of_not_injective hni)) hodd
  · intro hb
    rw [doorCountN_eq_one_of_bijective hb]
    exact ⟨0, rfl⟩

/-! ## The concrete Kuhn complex (combinatorial finite data)

We model the Kuhn (corner / order) subdivision of `Δⁿ` at mesh `1/k` as purely combinatorial
finite data.  A **vertex** is a barycentric lattice point `p : Fin (n+1) → ℕ` with `∑ p = k`.
A **cell** is a base vertex `p` together with a permutation `σ : Equiv.Perm (Fin n)` selecting
the order in which unit mass is moved out of the last coordinate into the others; its ordered
chain of `n+1` vertices is

  `chainV p σ t = p + ∑_{s < t} (e_{σ s} − e_{last})`   (`t : Fin (n+1)`).

A **facet** is the chain with one vertex dropped.  This is the standard Kuhn corner simplex
anchored at `p`; existence at mesh `k` is the requirement that every chain vertex is a genuine
nonnegative lattice point. -/

/-- A single Kuhn step displacement applied to a barycentric point: move one unit from the
last coordinate into coordinate `a`.  Encoded additively over `ℤ` to avoid `ℕ` underflow. -/
def stepVec {n : ℕ} (a : Fin n) : Fin (n + 1) → ℤ :=
  fun i => (if i = a.castSucc then 1 else 0) - (if i = Fin.last n then 1 else 0)

/-- The `t`-th vertex of the Kuhn chain based at `p` with step order `σ`, over `ℤ`. -/
def chainVZ {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    Fin (n + 1) → ℤ :=
  fun i => p i + ∑ s ∈ Finset.univ.filter (fun s : Fin n => s.castSucc.val < t.val),
    stepVec (σ s) i

/-- Each Kuhn step preserves the barycentric sum (`∑ stepVec = 0`). -/
theorem sum_stepVec {n : ℕ} (a : Fin n) : ∑ i, stepVec a i = 0 := by
  classical
  unfold stepVec
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ i : Fin (n + 1), (if i = a.castSucc then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ a.castSucc]; simp
  have h2 : (∑ i : Fin (n + 1), (if i = Fin.last n then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ (Fin.last n)]; simp
  rw [h1, h2]; ring

/-- The Kuhn chain preserves the barycentric sum: `∑ chainVZ p σ t = ∑ p`. -/
theorem sum_chainVZ {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) : ∑ i, chainVZ p σ t i = ∑ i, p i := by
  classical
  unfold chainVZ
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have : ∀ s ∈ Finset.univ.filter (fun s : Fin n => s.castSucc.val < t.val),
      ∑ i, stepVec (σ s) i = 0 := fun s _ => sum_stepVec (σ s)
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero, add_zero]

/-! ## Heart in the engine's `hheart` form

For the instantiation, a cell's facets are indexed by the dropped vertex `i : Fin (n+1)`,
`isDoor` is `doorAt c`, and `isRainbow` is `Function.Bijective c`.  The per-cell heart that
`sperner_n_dim_combinatorial` consumes is then exactly `heart_count_n`, repackaged through
the indexed facet count.  This is the bridge lemma that discharges `hheart` once a concrete
`bounds`/facet structure realises `facets.filter (bounds c ·)` as the `n+1` indexed facets. -/
theorem hheart_indexed {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) :
    Odd (Finset.univ.filter (fun i : Fin (n + 1) => doorAt c i)).card
      ↔ Function.Bijective c :=
  heart_count_n c

/-! ## Precise stall report — the remaining bricks toward `brouwer_stdSimplex_n`

**What is closed here (axiom-clean: `[propext, Classical.choice, Quot.sound]`).**

* `sperner_n_dim_combinatorial` — the abstract n-D Sperner counting lemma.  The committed
  double-counting / `ZMod 2` engine is dimension-free, so this is its `n`-D re-exposure; the
  whole `bipartiteAbove`/`bipartiteBelow` parity argument transports verbatim.
* `heart_count_n` (with `doorCountN_eq_one_of_bijective`, `even_doorCountN_of_not_injective`,
  `injOn_of_doorAt`, `facetColors_eq_of_dup`) — the **n-D Sperner heart**: a cell coloured by
  `c : Fin (n+1) → Fin (n+1)` has an odd number of door-facets iff `c` is a bijection.  This
  is the genuine crux the 2-D file discharged by `decide` over `3^3`; here it is a *structural*
  proof valid for symbolic `n`.  Door at `i` forces `c` injective off `i`
  (`injOn_of_doorAt`); a collision pair `a ≠ b`, `c a = c b` confines all doors to `{a,b}`
  with `doorAt a ↔ doorAt b` (`facetColors_eq_of_dup`), giving an *even* door-count whenever
  `c` is not injective; bijectivity gives exactly one door (`facetColors c i = univ.erase
  (c i)`, door `⟺ c i = last`).  `hheart_indexed` packages it in the engine's `hheart` form.
* `stepVec`, `chainVZ`, `sum_stepVec`, `sum_chainVZ` — the concrete Kuhn corner-simplex chain
  (base `p` + step-order `σ`, moving unit mass out of the last coordinate), with the
  barycentric-sum invariant `∑ chainVZ p σ t = ∑ p`.

**Precise remaining frontier (the heavy Kuhn incidence geometry).**  To assemble
`brouwer_stdSimplex_n` from the above, the missing bricks — in order — are:

  (K1) CANONICAL FACET ENCODING.  A facet is an unordered `n`-subset of chain vertices
       (drop one vertex of `chainVZ p σ`).  Provide a `DecidableEq` normal form
       (`Finset (Fin (n+1) → ℤ)` of its `n` lattice points) and the `cells`/`facets`
       `Finset`s at mesh `k` with the analogue of `mem_cells`/`mem_edges`.
  (K2) FACET-SHARING (the genuine n-D incidence — the analogue of `incidence_card`).  Each
       interior facet is shared by exactly two cells, each boundary facet by one.  The
       3-case split is: (i) internal drop `0 < t < n` ⟹ the partner cell is `σ ∘ swap
       (t-1) t` (adjacent step transposition); (ii)/(iii) endpoint drop `t = 0` / `t = n`
       ⟹ a shift to the neighbouring base cell, admissible (decidable) iff the shifted base
       stays in-mesh — exactly the geometric-boundary condition.  This discharges
       `hinterior`/`hboundaryOdd`.
  (K3) BOUNDARY INDUCTION.  `hboundaryCount` reduces to `sperner_(n-1)_dim` on the
       distinguished face `{p : p (Fin.last n) = 0}` (the last barycentric coordinate
       vanishes), whose induced Kuhn subdivision is the `(n-1)`-dimensional one; base case
       `n = 1` is the committed `sperner_one_dim`.  Then `sperner_n_dim_combinatorial`
       (with `hheart_indexed`) yields an odd, hence positive, rainbow-cell count at every
       mesh.
  (K4) MESH-LIMIT + TRANSPORT.  Reuse the dimension-agnostic glue verbatim: the Sperner
       label (`sperner_label_nonempty`), the rainbow per-colour vertices within mesh `n+1`,
       `IsCompact.tendsto_subseq` on the compact `stdSimplex`, and
       `eq_of_forall_le_on_stdSimplex` — exactly the shape of `brouwer_stdSimplex_two`.
       `brouwer_compact_convex` then transports `brouwer_stdSimplex_n` to a compact convex
       `K` in a finite-dimensional normed space via barycentric coordinates of a containing
       simplex plus the nearest-point retraction onto `K`.

(K2) is the genuine missing geometry: a canonical facet representation with decidable
admissibility and the adjacent-transposition / base-shift case analysis.  Mathlib has no API
for the Kuhn subdivision, so this is a from-scratch incidence count.  The abstract engine
(`sperner_n_dim_combinatorial`) and the symbolic-`n` heart (`heart_count_n`) — the two pieces
that do not reduce to bookkeeping — are fully discharged above.
-/

end ShenWork.Paper1
