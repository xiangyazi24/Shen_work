/-
# 2-D Brouwer fixed point via the Kuhn (order) subdivision of `Δ²`

This file instantiates the abstract combinatorial Sperner lemma
(`ShenWork.Paper1.sperner_two_dim_combinatorial`) with a *concrete* triangular-grid
("Kuhn" / order) subdivision of the standard 2-simplex `Δ²` at mesh `1/k`, discharges its
four geometric hypotheses, and assembles 2-D Brouwer's fixed point theorem.

## Coordinate model

A lattice vertex is a pair `(i, j) : ℕ × ℕ` with `i + j ≤ k`, embedded into `Δ²` by
`vertexPt k (i,j) = (i/k, j/k, (k-i-j)/k)`.  Cells (2-simplices) come in two orientations:

* `Up i j`    — vertices `(i,j), (i+1,j), (i,j+1)`            (exists iff `i+j+1 ≤ k`);
* `Down i j`  — vertices `(i+1,j), (i,j+1), (i+1,j+1)`        (exists iff `i+j+2 ≤ k`).

Edges come in three orientations:

* `Horiz i j` — `(i,j)–(i+1,j)`     (exists iff `i+j+1 ≤ k`);
* `Vert  i j` — `(i,j)–(i,j+1)`     (exists iff `i+j+1 ≤ k`);
* `Diag  i j` — `(i+1,j)–(i,j+1)`   (exists iff `i+j+1 ≤ k`).

The uniform incidence fact (proved below) is: **each edge bounds `Up i j` together with at
most one neighbouring `Down`, and the `Down` is present exactly when the edge is interior.**
This drives `hinterior` (interior ⇒ 2 cells) and `hboundaryOdd` (boundary ⇒ 1 cell).
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import ShenWork.Paper1.Brouwer

namespace ShenWork.Paper1

open Set Finset Filter Topology

/-! ## The combinatorial cell / edge types -/

/-- A 2-cell of the order subdivision: an `Up` or `Down` triangle anchored at `(i, j)`. -/
inductive Cell : Type
  | up (i j : ℕ) : Cell
  | down (i j : ℕ) : Cell
  deriving DecidableEq, Repr

/-- An edge of the order subdivision: horizontal, vertical or diagonal, anchored at
`(i, j)`. -/
inductive Edg : Type
  | horiz (i j : ℕ) : Edg
  | vert (i j : ℕ) : Edg
  | diag (i j : ℕ) : Edg
  deriving DecidableEq, Repr

/-! ## Incidence: which edges bound which cells -/

/-- The incidence relation `bounds c e`: the edge `e` is one of the three edges of cell `c`.

* `Up i j` is bounded by `Horiz i j`, `Vert i j`, `Diag i j`.
* `Down i j` is bounded by `Diag i j`, `Horiz i (j+1)`, `Vert (i+1) j`. -/
def bounds : Cell → Edg → Bool
  | Cell.up i j, Edg.horiz a b => i = a ∧ j = b
  | Cell.up i j, Edg.vert a b => i = a ∧ j = b
  | Cell.up i j, Edg.diag a b => i = a ∧ j = b
  | Cell.down i j, Edg.diag a b => i = a ∧ j = b
  | Cell.down i j, Edg.horiz a b => a = i ∧ b = j + 1
  | Cell.down i j, Edg.vert a b => a = i + 1 ∧ b = j

/-! ## Existence (membership) at mesh `k` -/

/-- A cell exists at mesh `k` iff all its vertices lie in the lattice `Δ²ₖ`:
`Up i j` needs `i+j+1 ≤ k`, `Down i j` needs `i+j+2 ≤ k`. -/
def cellMem (k : ℕ) : Cell → Prop
  | Cell.up i j => i + j + 1 ≤ k
  | Cell.down i j => i + j + 2 ≤ k

instance (k : ℕ) : DecidablePred (cellMem k) := by
  intro c; cases c <;> · unfold cellMem; infer_instance

/-- An edge exists at mesh `k` iff both its endpoints lie in the lattice `Δ²ₖ`.  All three
orientations need `i+j+1 ≤ k`. -/
def edgeMem (k : ℕ) : Edg → Prop
  | Edg.horiz i j => i + j + 1 ≤ k
  | Edg.vert i j => i + j + 1 ≤ k
  | Edg.diag i j => i + j + 1 ≤ k

instance (k : ℕ) : DecidablePred (edgeMem k) := by
  intro e; cases e <;> · unfold edgeMem; infer_instance

/-- Decidable incidence (`bounds` is `Bool`-valued). -/
instance : DecidableRel (fun c e => bounds c e = true) := fun _ _ => inferInstance

/-! ## The triangulation Finsets at mesh `k` -/

/-- All anchor pairs `(i, j)` with `i + j + 1 ≤ k`; a superset of the indices that occur. -/
def anchors (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => p.1 + p.2 + 1 ≤ k)

/-- The set of cells (`Up` and `Down` triangles) present at mesh `k`. -/
def cells (k : ℕ) : Finset Cell :=
  ((anchors k).image (fun p => Cell.up p.1 p.2)) ∪
    ((anchors k).image (fun p => Cell.down p.1 p.2)).filter (cellMem k)

/-- The set of edges present at mesh `k`. -/
def edges (k : ℕ) : Finset Edg :=
  ((anchors k).image (fun p => Edg.horiz p.1 p.2)) ∪
    ((anchors k).image (fun p => Edg.vert p.1 p.2)) ∪
    ((anchors k).image (fun p => Edg.diag p.1 p.2))

/-- `(i, j)` is an anchor at mesh `k` iff `i + j + 1 ≤ k`. -/
@[simp] theorem mem_anchors {k i j : ℕ} : (i, j) ∈ anchors k ↔ i + j + 1 ≤ k := by
  simp only [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨⟨by omega, by omega⟩, h⟩

/-- Cell membership in `cells k` is exactly `cellMem k`. -/
@[simp] theorem mem_cells {k : ℕ} {c : Cell} : c ∈ cells k ↔ cellMem k c := by
  cases c with
  | up i j =>
    simp only [cells, Finset.mem_union, Finset.mem_filter, Finset.mem_image, cellMem]
    constructor
    · rintro (⟨p, hp, hpe⟩ | ⟨⟨p, _, hpe⟩, _⟩)
      · obtain ⟨rfl, rfl⟩ : p.1 = i ∧ p.2 = j := by simpa using hpe
        exact (mem_anchors.mp hp)
      · exact absurd hpe (by simp)
    · intro h; exact Or.inl ⟨(i, j), mem_anchors.mpr h, rfl⟩
  | down i j =>
    simp only [cells, Finset.mem_union, Finset.mem_filter, Finset.mem_image, cellMem]
    constructor
    · rintro (⟨p, _, hpe⟩ | ⟨⟨p, hp, hpe⟩, hm⟩)
      · exact absurd hpe (by simp)
      · obtain ⟨rfl, rfl⟩ : p.1 = i ∧ p.2 = j := by simpa using hpe
        exact hm
    · intro h
      exact Or.inr ⟨⟨(i, j), mem_anchors.mpr (by omega), rfl⟩, by simpa [cellMem] using h⟩

/-- Edge membership in `edges k` is exactly `edgeMem k`. -/
@[simp] theorem mem_edges {k : ℕ} {e : Edg} : e ∈ edges k ↔ edgeMem k e := by
  cases e with
  | horiz i j =>
    simp only [edges, Finset.mem_union, Finset.mem_image, edgeMem]
    constructor
    · rintro ((⟨p, hp, hpe⟩ | ⟨p, _, hpe⟩) | ⟨p, _, hpe⟩)
      · obtain ⟨rfl, rfl⟩ : p.1 = i ∧ p.2 = j := by simpa using hpe
        exact mem_anchors.mp hp
      · exact absurd hpe (by simp)
      · exact absurd hpe (by simp)
    · intro h; exact Or.inl (Or.inl ⟨(i, j), mem_anchors.mpr h, rfl⟩)
  | vert i j =>
    simp only [edges, Finset.mem_union, Finset.mem_image, edgeMem]
    constructor
    · rintro ((⟨p, _, hpe⟩ | ⟨p, hp, hpe⟩) | ⟨p, _, hpe⟩)
      · exact absurd hpe (by simp)
      · obtain ⟨rfl, rfl⟩ : p.1 = i ∧ p.2 = j := by simpa using hpe
        exact mem_anchors.mp hp
      · exact absurd hpe (by simp)
    · intro h; exact Or.inl (Or.inr ⟨(i, j), mem_anchors.mpr h, rfl⟩)
  | diag i j =>
    simp only [edges, Finset.mem_union, Finset.mem_image, edgeMem]
    constructor
    · rintro ((⟨p, _, hpe⟩ | ⟨p, _, hpe⟩) | ⟨p, hp, hpe⟩)
      · exact absurd hpe (by simp)
      · exact absurd hpe (by simp)
      · obtain ⟨rfl, rfl⟩ : p.1 = i ∧ p.2 = j := by simpa using hpe
        exact mem_anchors.mp hp
    · intro h; exact Or.inr ⟨(i, j), mem_anchors.mpr h, rfl⟩

/-! ## Incidence counts: cells bounding a given edge

For every edge there are at most two cells in the whole type `Cell` that bound it — an `Up`
and a `Down` — and each edge orientation pins them down explicitly.  The "boundary"/interior
distinction is exactly whether the `Down` neighbour is present at mesh `k`. -/

/-- The `Up`-neighbour of an edge: the (unique) up-triangle bounding it. -/
def upNbr : Edg → Cell
  | Edg.horiz i j => Cell.up i j
  | Edg.vert i j => Cell.up i j
  | Edg.diag i j => Cell.up i j

/-- The `Down`-neighbour of an edge: the (unique) down-triangle bounding it, when present. -/
def downNbr : Edg → Cell
  | Edg.horiz i j => Cell.down i (j - 1)
  | Edg.vert i j => Cell.down (i - 1) j
  | Edg.diag i j => Cell.down i j

/-- Whether the `Down`-neighbour actually bounds the edge (it fails to exist for the very
first row/column): `j ≥ 1` for `Horiz`, `i ≥ 1` for `Vert`, always for `Diag`. -/
def downBoundsEdge : Edg → Prop
  | Edg.horiz _ j => 1 ≤ j
  | Edg.vert i _ => 1 ≤ i
  | Edg.diag _ _ => True

instance : DecidablePred downBoundsEdge := by
  intro e; cases e <;> · unfold downBoundsEdge; infer_instance

/-- A cell bounds an edge iff it is the `Up`-neighbour, or the `Down`-neighbour with that
neighbour genuinely present. -/
theorem bounds_iff (c : Cell) (e : Edg) :
    bounds c e = true ↔ (c = upNbr e ∨ (c = downNbr e ∧ downBoundsEdge e)) := by
  cases e <;> cases c <;>
    simp only [bounds, upNbr, downNbr, downBoundsEdge, Cell.up.injEq, Cell.down.injEq,
      decide_eq_true_eq, reduceCtorEq, false_or, or_false, false_and, and_true] <;>
    constructor <;> intro h <;> omega

/-- The `Up`- and `Down`-neighbours of any edge are different cells. -/
theorem upNbr_ne_downNbr (e : Edg) : upNbr e ≠ downNbr e := by
  cases e <;> simp [upNbr, downNbr]

/-- For a present edge, its `Up`-neighbour is a present cell. -/
theorem upNbr_mem {k : ℕ} {e : Edg} (he : edgeMem k e) : upNbr e ∈ cells k := by
  cases e <;>
    · simp only [upNbr, mem_cells, cellMem]; simpa [edgeMem] using he

/-- An edge is *interior* (in the triangulation) iff its `Down`-neighbour is present and
genuinely bounds it.  Otherwise it is on the geometric boundary. -/
def isInterior (k : ℕ) (e : Edg) : Prop := downNbr e ∈ cells k ∧ downBoundsEdge e

instance (k : ℕ) : DecidablePred (isInterior k) := fun e => by unfold isInterior; infer_instance

/-- **Edge–cell incidence count.**  A present edge `e` is bounded by exactly `1` cell if it
is on the boundary, and by exactly `2` cells if it is interior. -/
theorem incidence_card {k : ℕ} {e : Edg} (he : edgeMem k e) :
    ((cells k).filter (fun c => bounds c e)).card = if isInterior k e then 2 else 1 := by
  classical
  have hAmem : upNbr e ∈ cells k := upNbr_mem he
  have hne := upNbr_ne_downNbr e
  -- rewrite the predicate through `bounds_iff`
  have hfilt : (cells k).filter (fun c => bounds c e)
      = (cells k).filter (fun c => c = upNbr e ∨ (c = downNbr e ∧ downBoundsEdge e)) := by
    apply Finset.filter_congr; intro c _; simp [bounds_iff c e]
  rw [hfilt]
  by_cases hI : isInterior k e
  · obtain ⟨hBmem, hBb⟩ := id hI
    have : (cells k).filter (fun c => c = upNbr e ∨ (c = downNbr e ∧ downBoundsEdge e))
        = {upNbr e, downNbr e} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h | ⟨h, _⟩⟩ <;> tauto
      · rintro (rfl | rfl)
        · exact ⟨hAmem, Or.inl rfl⟩
        · exact ⟨hBmem, Or.inr ⟨rfl, hBb⟩⟩
    rw [this, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton,
      if_pos hI]
  · have : (cells k).filter (fun c => c = upNbr e ∨ (c = downNbr e ∧ downBoundsEdge e))
        = {upNbr e} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hc, h | ⟨rfl, hb⟩⟩
        · exact h
        · exact absurd ⟨hc, hb⟩ hI
      · rintro rfl; exact ⟨hAmem, Or.inl rfl⟩
    rw [this, Finset.card_singleton, if_neg hI]

/-! ## The Sperner labelling layer

Fix a vertex 3-colouring `L : ℕ × ℕ → Fin 3`.  An edge is a *door* iff its two endpoints
carry the colours `0` and `1`; a cell is *rainbow* iff its three vertices carry all of
`0, 1, 2`. -/

/-- Symmetric "is the colour pair `{a,b} = {0,1}`" predicate. -/
def doorPair (a b : Fin 3) : Bool := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)

/-- The two endpoints of an edge (as lattice points). -/
def edgeVerts : Edg → (ℕ × ℕ) × (ℕ × ℕ)
  | Edg.horiz i j => ((i, j), (i + 1, j))
  | Edg.vert i j => ((i, j), (i, j + 1))
  | Edg.diag i j => ((i + 1, j), (i, j + 1))

/-- The three vertices of a cell (as lattice points). -/
def cellVerts : Cell → (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)
  | Cell.up i j => ((i, j), (i + 1, j), (i, j + 1))
  | Cell.down i j => ((i + 1, j), (i, j + 1), (i + 1, j + 1))

/-- An edge is a *door* under labelling `L`. -/
def isDoor (L : ℕ × ℕ → Fin 3) (e : Edg) : Bool :=
  doorPair (L (edgeVerts e).1) (L (edgeVerts e).2)

instance (L : ℕ × ℕ → Fin 3) : DecidablePred (fun e => isDoor L e = true) :=
  fun e => inferInstance

/-- A cell is *rainbow* under labelling `L`. -/
def isRainbow (L : ℕ × ℕ → Fin 3) (c : Cell) : Bool :=
  ({L (cellVerts c).1, L (cellVerts c).2.1, L (cellVerts c).2.2} : Finset (Fin 3)) = {0, 1, 2}

instance (L : ℕ × ℕ → Fin 3) : DecidablePred (fun c => isRainbow L c = true) :=
  fun c => inferInstance

/-- **Self-contained combinatorial heart** (re-proved here for the local `doorPair` /
rainbow definitions, by exhausting the `3^3` colourings of a triple).  A triple has an odd
number of `{0,1}`-pairs among its three edges iff its colours are exactly `{0,1,2}`. -/
theorem heart_count (c0 c1 c2 : Fin 3) :
    Odd ((if doorPair c0 c1 then 1 else 0) + (if doorPair c0 c2 then 1 else 0)
        + (if doorPair c1 c2 then 1 else 0))
      ↔ (({c0, c1, c2} : Finset (Fin 3)) = {0, 1, 2}) := by
  revert c0 c1 c2; decide

/-- The three edges of a cell. -/
def cellEdges : Cell → Edg × Edg × Edg
  | Cell.up i j => (Edg.horiz i j, Edg.vert i j, Edg.diag i j)
  | Cell.down i j => (Edg.diag i j, Edg.horiz i (j + 1), Edg.vert (i + 1) j)

/-- The three edges of a cell are pairwise distinct. -/
theorem cellEdges_nodup (c : Cell) :
    (cellEdges c).1 ≠ (cellEdges c).2.1 ∧ (cellEdges c).1 ≠ (cellEdges c).2.2 ∧
      (cellEdges c).2.1 ≠ (cellEdges c).2.2 := by
  cases c <;> simp [cellEdges]

/-- A cell bounds exactly its three edges. -/
theorem bounds_eq_cellEdges (c : Cell) (e : Edg) :
    bounds c e = true ↔
      (e = (cellEdges c).1 ∨ e = (cellEdges c).2.1 ∨ e = (cellEdges c).2.2) := by
  cases c <;> cases e <;>
    simp only [bounds, cellEdges, Edg.horiz.injEq, Edg.vert.injEq, Edg.diag.injEq,
      decide_eq_true_eq, reduceCtorEq, false_or, or_false] <;>
    constructor <;> intro h <;> omega

/-- For a present cell, its three edges are present at mesh `k`. -/
theorem cellEdges_mem {k : ℕ} {c : Cell} (hc : cellMem k c) :
    (cellEdges c).1 ∈ edges k ∧ (cellEdges c).2.1 ∈ edges k ∧
      (cellEdges c).2.2 ∈ edges k := by
  cases c with
  | up i j =>
    simp only [cellEdges, mem_edges, edgeMem]; simp only [cellMem] at hc; omega
  | down i j =>
    simp only [cellEdges, mem_edges, edgeMem]; simp only [cellMem] at hc
    refine ⟨by omega, by omega, by omega⟩

/-- The door-edges bounding a present cell, as a Finset filtered from its three edges. -/
theorem door_filter_eq {k : ℕ} {L : ℕ × ℕ → Fin 3} {c : Cell} (hc : cellMem k c) :
    (edges k).filter (fun e => bounds c e = true ∧ isDoor L e = true)
      = ({(cellEdges c).1, (cellEdges c).2.1, (cellEdges c).2.2} : Finset Edg).filter
          (fun e => isDoor L e = true) := by
  obtain ⟨h1, h2, h3⟩ := cellEdges_mem hc
  ext e
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hb, hd⟩
    exact ⟨(bounds_eq_cellEdges c e).mp hb, hd⟩
  · rintro ⟨he, hd⟩
    refine ⟨?_, (bounds_eq_cellEdges c e).mpr he, hd⟩
    rcases he with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

/-- **`hheart` for cell `c`.**  The number of door-edges bounding a present cell `c` is odd
iff `c` is rainbow.  This is the local Sperner heart, transported from `heart_count` through
the explicit three-edge / three-vertex alignment of the order subdivision. -/
theorem hheart_cell {k : ℕ} {L : ℕ × ℕ → Fin 3} {c : Cell} (hc : cellMem k c) :
    Odd ((edges k).filter (fun e => bounds c e = true ∧ isDoor L e = true)).card
      ↔ isRainbow L c = true := by
  rw [door_filter_eq hc]
  obtain ⟨hne1, hne2, hne3⟩ := cellEdges_nodup c
  -- card of the filtered 3-element set = sum of the three door indicators
  have hcard : (({(cellEdges c).1, (cellEdges c).2.1, (cellEdges c).2.2} : Finset Edg).filter
        (fun e => isDoor L e = true)).card
      = (if isDoor L (cellEdges c).1 then 1 else 0) + (if isDoor L (cellEdges c).2.1 then 1 else 0)
          + (if isDoor L (cellEdges c).2.2 then 1 else 0) := by
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    by_cases d1 : isDoor L (cellEdges c).1 = true <;>
    by_cases d2 : isDoor L (cellEdges c).2.1 = true <;>
    by_cases d3 : isDoor L (cellEdges c).2.2 = true <;>
      simp_all [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton] <;> omega
  rw [hcard]
  -- align edge-door with vertex-pair-door, then apply heart_count
  cases c with
  | up i j =>
    simp only [isRainbow, cellVerts, isDoor, cellEdges, edgeVerts, decide_eq_true_eq]
    exact heart_count _ _ _
  | down i j =>
    simp only [isRainbow, cellVerts, isDoor, cellEdges, edgeVerts, decide_eq_true_eq]
    rw [← heart_count (L (i + 1, j)) (L (i, j + 1)) (L (i + 1, j + 1))]
    have hsum : ((if doorPair (L (i + 1, j)) (L (i, j + 1)) = true then 1 else 0)
          + (if doorPair (L (i, j + 1)) (L (i + 1, j + 1)) = true then 1 else 0)
          + (if doorPair (L (i + 1, j)) (L (i + 1, j + 1)) = true then 1 else 0))
        = ((if doorPair (L (i + 1, j)) (L (i, j + 1)) = true then 1 else 0)
          + (if doorPair (L (i + 1, j)) (L (i + 1, j + 1)) = true then 1 else 0)
          + (if doorPair (L (i, j + 1)) (L (i + 1, j + 1)) = true then 1 else 0)) := by ring
    exact hsum ▸ Iff.rfl

/-! ## The interior / boundary incidence hypotheses

The geometric "boundary" of the triangulated region is exactly the set of edges with no
`Down`-neighbour cell — `isBoundary := ¬ isInterior`.  The interior/boundary incidence
hypotheses of `sperner_two_dim_combinatorial` are then immediate from `incidence_card`. -/

/-- An edge is on the boundary iff it is not interior. -/
def isBoundary (k : ℕ) (e : Edg) : Prop := ¬ isInterior k e

instance (k : ℕ) : DecidablePred (isBoundary k) := fun e => by unfold isBoundary; infer_instance

/-- **`hinterior`.**  A non-boundary (interior) edge bounds an even number (= 2) of cells. -/
theorem hinterior_cell {k : ℕ} {e : Edg} (he : e ∈ edges k) (hb : ¬ isBoundary k e) :
    Even ((cells k).filter (fun c => bounds c e = true)).card := by
  have hI : isInterior k e := not_not.mp hb
  rw [incidence_card (mem_edges.mp he), if_pos hI]
  exact ⟨1, rfl⟩

/-- **`hboundaryOdd`.**  A boundary edge bounds an odd number (= 1) of cells. -/
theorem hboundaryOdd_cell {k : ℕ} {e : Edg} (he : e ∈ edges k) (hb : isBoundary k e) :
    Odd ((cells k).filter (fun c => bounds c e = true)).card := by
  rw [incidence_card (mem_edges.mp he), if_neg hb]
  exact ⟨0, rfl⟩

/-! ## The simplex embedding and the Sperner labelling -/

/-- The lattice point `(i, j)` mapped into `Δ²` at mesh `k`:
`vertexPt k (i,j) = (i/k, j/k, (k-i-j)/k)`. -/
noncomputable def vertexPt (k : ℕ) (p : ℕ × ℕ) : Fin 3 → ℝ :=
  ![(p.1 : ℝ) / k, (p.2 : ℝ) / k, ((k : ℝ) - p.1 - p.2) / k]

/-- For `0 < k` and a lattice point `(i,j)` with `i + j ≤ k`, `vertexPt k (i,j) ∈ Δ²`. -/
theorem vertexPt_mem_stdSimplex {k i j : ℕ} (hk : 0 < k) (hij : i + j ≤ k) :
    vertexPt k (i, j) ∈ stdSimplex ℝ (Fin 3) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hile : (i : ℝ) ≤ k := by exact_mod_cast (le_trans (Nat.le_add_right i j) hij)
  have hjle : (j : ℝ) ≤ k := by exact_mod_cast (le_trans (Nat.le_add_left j i) hij)
  have hsum : (i : ℝ) + j ≤ k := by exact_mod_cast hij
  constructor
  · intro t
    fin_cases t <;> simp only [vertexPt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
      apply div_nonneg <;> first | positivity | linarith
  · simp only [vertexPt, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    field_simp
    ring

open scoped Classical in
/-- The Sperner colour-set of a point `v` with image `fv`: the coordinates `t` with
`v t > 0` and `fv t ≤ v t`.  Nonempty on `Δ²` by `sperner_label_nonempty`. -/
noncomputable def labelSet (v fv : Fin 3 → ℝ) : Finset (Fin 3) :=
  Finset.univ.filter (fun t => v t > 0 ∧ fv t ≤ v t)

/-- The Sperner label of a lattice point under `f` at mesh `k`: the least coordinate `t`
with `(vertexPt) t > 0` and `(f ∘ vertexPt) t ≤ (vertexPt) t`.  Defaults to `0` off the
simplex (never used there). -/
noncomputable def spernerLabel (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (k : ℕ)
    (p : ℕ × ℕ) : Fin 3 :=
  if h : (labelSet (vertexPt k p) (f (vertexPt k p))).Nonempty then
    (labelSet (vertexPt k p) (f (vertexPt k p))).min' h else 0

/-- The label set is genuinely nonempty for an in-simplex vertex mapped by a self-map. -/
theorem labelSet_nonempty {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} {p : ℕ × ℕ}
    (hv : vertexPt k p ∈ stdSimplex ℝ (Fin 3))
    (hfv : f (vertexPt k p) ∈ stdSimplex ℝ (Fin 3)) :
    (labelSet (vertexPt k p) (f (vertexPt k p))).Nonempty := by
  obtain ⟨t, ht⟩ := sperner_label_nonempty (vertexPt k p) (f (vertexPt k p)) hv hfv
  exact ⟨t, by simp only [labelSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht⟩

/-- The Sperner label lies in its own colour-set: the labelled coordinate is positive and
weakly decreasing. -/
theorem spernerLabel_spec {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} {p : ℕ × ℕ}
    (hv : vertexPt k p ∈ stdSimplex ℝ (Fin 3))
    (hfv : f (vertexPt k p) ∈ stdSimplex ℝ (Fin 3)) :
    vertexPt k p (spernerLabel f k p) > 0 ∧
      f (vertexPt k p) (spernerLabel f k p) ≤ vertexPt k p (spernerLabel f k p) := by
  have hne := labelSet_nonempty hv hfv
  unfold spernerLabel
  rw [dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  simpa only [labelSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- The label avoids any coordinate where the vertex is zero. -/
theorem spernerLabel_ne_of_zero {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} {p : ℕ × ℕ}
    (hv : vertexPt k p ∈ stdSimplex ℝ (Fin 3))
    (hfv : f (vertexPt k p) ∈ stdSimplex ℝ (Fin 3)) {t : Fin 3} (ht : vertexPt k p t = 0) :
    spernerLabel f k p ≠ t := by
  intro heq
  have hpos := (spernerLabel_spec hv hfv).1
  rw [heq, ht] at hpos
  exact lt_irrefl 0 hpos

/-- On the bottom face (`j = 0`) the second coordinate vanishes, so the label is never `1`. -/
theorem label_ne_one_bottom {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k i : ℕ} (hk : 0 < k)
    (hi : i ≤ k) (hfv : f (vertexPt k (i, 0)) ∈ stdSimplex ℝ (Fin 3)) :
    spernerLabel f k (i, 0) ≠ 1 := by
  have hv := vertexPt_mem_stdSimplex (i := i) (j := 0) hk (by omega)
  refine spernerLabel_ne_of_zero hv hfv ?_
  simp [vertexPt]

/-- On the left face (`i = 0`) the first coordinate vanishes, so the label is never `0`. -/
theorem label_ne_zero_left {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k j : ℕ} (hk : 0 < k)
    (hj : j ≤ k) (hfv : f (vertexPt k (0, j)) ∈ stdSimplex ℝ (Fin 3)) :
    spernerLabel f k (0, j) ≠ 0 := by
  have hv := vertexPt_mem_stdSimplex (i := 0) (j := j) hk (by omega)
  refine spernerLabel_ne_of_zero hv hfv ?_
  simp [vertexPt]

/-- On the hypotenuse (`i + j = k`) the third coordinate vanishes, so the label is never
`2`. -/
theorem label_ne_two_hyp {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k i j : ℕ} (hk : 0 < k)
    (hij : i + j = k) (hfv : f (vertexPt k (i, j)) ∈ stdSimplex ℝ (Fin 3)) :
    spernerLabel f k (i, j) ≠ 2 := by
  have hv := vertexPt_mem_stdSimplex (i := i) (j := j) hk (by omega)
  refine spernerLabel_ne_of_zero hv hfv ?_
  have : ((k : ℝ) - i - j) = 0 := by
    have : (i : ℝ) + j = k := by exact_mod_cast hij
    linarith
  simp [vertexPt, this]

/-! ## `hboundaryCount` via 1-D Sperner on the hypotenuse

The door-bearing boundary face is the hypotenuse `i + j = k`.  Its `k + 1` lattice points
`(k-m, m)` (`m : Fin (k+1)`) carry labels in `{0, 1}` (the label is never `2` there), with
ends `0` (corner `(k,0)`) and `1` (corner `(0,k)`).  The 1-D Sperner lemma gives an odd
number of label-changing segments, which are exactly the boundary doors. -/

/-- The hypotenuse 1-D labelling: the Sperner label on point `(k-m, m)`, collapsed to
`Fin 2` (it is `0` or `1`, never `2`). -/
noncomputable def hypLabel (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (k : ℕ) (m : Fin (k + 1)) :
    Fin 2 :=
  if spernerLabel f k (k - m.val, m.val) = 0 then 0 else 1

/-- The bottom-right corner `(k, 0)` carries label `0`, so `hypLabel … 0 = 0`. -/
theorem hypLabel_zero {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} (hk : 0 < k)
    (hfv : f (vertexPt k (k, 0)) ∈ stdSimplex ℝ (Fin 3)) : hypLabel f k 0 = 0 := by
  have h2 : spernerLabel f k (k, 0) ≠ 2 := label_ne_two_hyp hk (by omega) hfv
  have h1 : spernerLabel f k (k, 0) ≠ 1 := label_ne_one_bottom hk (le_refl k) hfv
  have h0 : spernerLabel f k (k, 0) = 0 := by
    have := (spernerLabel f k (k, 0)); fin_cases this <;> simp_all <;> omega
  simp only [hypLabel, Fin.val_zero, Nat.sub_zero]
  rw [if_pos h0]

/-- The top corner `(0, k)` carries label `1`, so `hypLabel … (last k) = 1`. -/
theorem hypLabel_last {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} (hk : 0 < k)
    (hfv : f (vertexPt k (0, k)) ∈ stdSimplex ℝ (Fin 3)) : hypLabel f k (Fin.last k) = 1 := by
  have h2 : spernerLabel f k (0, k) ≠ 2 := label_ne_two_hyp hk (by omega) hfv
  have h0 : spernerLabel f k (0, k) ≠ 0 := label_ne_zero_left hk (le_refl k) hfv
  simp only [hypLabel, Fin.val_last, Nat.sub_self]
  rw [if_neg h0]

/-- Arithmetic description of `isInterior` on a horizontal edge. -/
theorem isInterior_horiz {k i j : ℕ} :
    isInterior k (Edg.horiz i j) ↔ (1 ≤ j ∧ i + j + 1 ≤ k) := by
  simp only [isInterior, downNbr, downBoundsEdge, mem_cells, cellMem]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

/-- Arithmetic description of `isInterior` on a vertical edge. -/
theorem isInterior_vert {k i j : ℕ} :
    isInterior k (Edg.vert i j) ↔ (1 ≤ i ∧ i + j + 1 ≤ k) := by
  simp only [isInterior, downNbr, downBoundsEdge, mem_cells, cellMem]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

/-- Arithmetic description of `isInterior` on a diagonal edge. -/
theorem isInterior_diag {k i j : ℕ} :
    isInterior k (Edg.diag i j) ↔ i + j + 2 ≤ k := by
  simp only [isInterior, downNbr, downBoundsEdge, mem_cells, cellMem, and_true]

/-- A bottom-face horizontal edge is never a door (its endpoints have second coordinate `0`,
so neither carries label `1`). -/
theorem bottom_not_door {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k i : ℕ} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3)))
    (he : Edg.horiz i 0 ∈ edges k) : isDoor (spernerLabel f k) (Edg.horiz i 0) = false := by
  have hik : i + 1 ≤ k := by have := mem_edges.mp he; simpa [edgeMem] using this
  have hf1 : f (vertexPt k (i, 0)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := i) (j := 0) hk (by omega))
  have hf2 : f (vertexPt k (i + 1, 0)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := i + 1) (j := 0) hk (by omega))
  have l1 : spernerLabel f k (i, 0) ≠ 1 := label_ne_one_bottom hk (by omega) hf1
  have l2 : spernerLabel f k (i + 1, 0) ≠ 1 := label_ne_one_bottom hk (by omega) hf2
  simp only [isDoor, edgeVerts, doorPair, decide_eq_false_iff_not, not_or, not_and]
  exact ⟨fun _ h => l2 h, fun h => absurd h l1⟩

/-- A left-face vertical edge is never a door (first coordinate `0`, so no label `0`). -/
theorem left_not_door {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k j : ℕ} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3)))
    (he : Edg.vert 0 j ∈ edges k) : isDoor (spernerLabel f k) (Edg.vert 0 j) = false := by
  have hjk : j + 1 ≤ k := by have := mem_edges.mp he; simpa [edgeMem] using this
  have hf1 : f (vertexPt k (0, j)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := 0) (j := j) hk (by omega))
  have hf2 : f (vertexPt k (0, j + 1)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := 0) (j := j + 1) hk (by omega))
  have l1 : spernerLabel f k (0, j) ≠ 0 := label_ne_zero_left hk (by omega) hf1
  have l2 : spernerLabel f k (0, j + 1) ≠ 0 := label_ne_zero_left hk (by omega) hf2
  simp only [isDoor, edgeVerts, doorPair, decide_eq_false_iff_not, not_or, not_and]
  exact ⟨fun h _ => l1 h, fun _ h => l2 h⟩

/-- For colours avoiding `2`, the `{0,1}`-door condition is exactly an inequality of the
collapsed `Fin 2` labels. -/
theorem doorPair_iff_collapse (a b : Fin 3) (ha : a ≠ 2) (hb : b ≠ 2) :
    doorPair a b = true ↔
      ((if a = 0 then (0 : Fin 2) else 1) ≠ (if b = 0 then (0 : Fin 2) else 1)) := by
  revert ha hb; revert a b; decide

/-- On a hypotenuse segment, "is a door" matches "the 1-D label changes".  Both endpoint
labels avoid `2`, so the `{0,1}`-door condition is exactly an inequality of collapsed
labels. -/
theorem hyp_isDoor_iff {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3))) (m : Fin k) :
    isDoor (spernerLabel f k) (Edg.diag (k - 1 - m.val) m.val) = true
      ↔ hypLabel f k m.castSucc ≠ hypLabel f k m.succ := by
  have hm : m.val < k := m.isLt
  have e1 : k - 1 - m.val + 1 = k - m.val := by omega
  have hP1 : f (vertexPt k (k - m.val, m.val)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := k - m.val) (j := m.val) hk (by omega))
  have hP2 : f (vertexPt k (k - 1 - m.val, m.val + 1)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := k - 1 - m.val) (j := m.val + 1) hk (by omega))
  have n1 : spernerLabel f k (k - m.val, m.val) ≠ 2 := label_ne_two_hyp hk (by omega) hP1
  have n2 : spernerLabel f k (k - 1 - m.val, m.val + 1) ≠ 2 := label_ne_two_hyp hk (by omega) hP2
  have e2 : k - (m.val + 1) = k - 1 - m.val := by omega
  simp only [isDoor, edgeVerts, e1, hypLabel, Fin.coe_castSucc, Fin.val_succ, e2]
  exact doorPair_iff_collapse _ _ n1 n2

/-- A boundary door is a hypotenuse diagonal `diag (k-1-b) b` for some `b < k`. -/
theorem boundary_door_form {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3))) {e : Edg}
    (he : e ∈ edges k) (hd : isDoor (spernerLabel f k) e = true) (hb : isBoundary k e) :
    ∃ b, b < k ∧ e = Edg.diag (k - 1 - b) b := by
  have hem := mem_edges.mp he
  cases e with
  | horiz i j =>
    -- horizontal boundary edge ⇒ j = 0 ⇒ not a door, contradiction
    rw [isBoundary, isInterior_horiz] at hb
    have hj0 : j = 0 := by simp only [edgeMem] at hem; omega
    subst hj0
    rw [bottom_not_door hk hmaps he] at hd; exact absurd hd (by simp)
  | vert i j =>
    rw [isBoundary, isInterior_vert] at hb
    have hi0 : i = 0 := by simp only [edgeMem] at hem; omega
    subst hi0
    rw [left_not_door hk hmaps he] at hd; exact absurd hd (by simp)
  | diag i j =>
    rw [isBoundary, isInterior_diag] at hb
    simp only [edgeMem] at hem
    have hij : i + j + 1 = k := by omega
    exact ⟨j, by omega, by congr 1; omega⟩

/-- Second (anchor) index of an edge — used as the inverse of the hypotenuse bijection. -/
def edgB : Edg → ℕ
  | Edg.horiz _ j => j
  | Edg.vert _ j => j
  | Edg.diag _ j => j

/-- **`hboundaryCount`.**  The number of boundary doors is odd: it equals the number of
label-changing segments along the hypotenuse 1-D path, which is odd by `sperner_one_dim`
(the path runs from the corner labelled `0` to the corner labelled `1`). -/
theorem hboundaryCount {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3))) :
    Odd ((edges k).filter
      (fun e => isDoor (spernerLabel f k) e = true ∧ isBoundary k e)).card := by
  classical
  set L := spernerLabel f k
  -- 1-D rainbow count along the hypotenuse is odd
  have hfv0 : f (vertexPt k (k, 0)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := k) (j := 0) hk (by omega))
  have hfvk : f (vertexPt k (0, k)) ∈ stdSimplex ℝ (Fin 3) :=
    hmaps (vertexPt_mem_stdSimplex (i := 0) (j := k) hk (by omega))
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1d := sperner_one_dim (hypLabel f (n + 1)) (hypLabel_zero hk hfv0) (hypLabel_last hk hfvk)
  set s := univ.filter (fun m : Fin (n + 1) =>
      hypLabel f (n + 1) m.castSucc ≠ hypLabel f (n + 1) m.succ) with hs
  set t := (edges (n + 1)).filter (fun e => isDoor L e = true ∧ isBoundary (n + 1) e) with ht
  suffices hcard : s.card = t.card by rw [← hcard]; exact h1d
  -- the bijection `m ↦ diag (n - m) m`, inverse extracts the second index
  have key : ∀ b (hbk : b < n + 1),
      (Edg.diag (n - b) b ∈ t ↔
        (⟨b, hbk⟩ : Fin (n + 1)) ∈ s) := by
    intro b hbk
    have hiff := hyp_isDoor_iff hk hmaps (⟨b, hbk⟩ : Fin (n + 1))
    simp only [show n + 1 - 1 - b = n - b by omega] at hiff
    rw [ht, hs, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hd, _⟩; exact ⟨Finset.mem_univ _, hiff.mp hd⟩
    · rintro ⟨_, hL⟩
      have hd : isDoor L (Edg.diag (n - b) b) = true := hiff.mpr hL
      refine ⟨?_, hd, ?_⟩
      · rw [mem_edges]; simp only [edgeMem]; omega
      · rw [isBoundary, isInterior_diag]; omega
  refine Finset.card_nbij' (fun m => Edg.diag (n - m.val) m.val)
    (fun e => (⟨edgB e % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1))) ?_ ?_ ?_ ?_
  · intro m hm
    have : (⟨m.val, m.isLt⟩ : Fin (n + 1)) ∈ s := by simpa [Fin.eta] using hm
    exact (key m.val m.isLt).mpr this
  · intro e he
    have he' : e ∈ t := he
    obtain ⟨b, hbk, rfl⟩ := boundary_door_form hk hmaps
      (Finset.mem_filter.mp he').1 (Finset.mem_filter.mp he').2.1 (Finset.mem_filter.mp he').2.2
    have : edgB (Edg.diag (n + 1 - 1 - b) b) = b := rfl
    simp only [this, Nat.mod_eq_of_lt hbk]
    have hin : Edg.diag (n - b) b ∈ t := by
      simpa [show n + 1 - 1 - b = n - b by omega] using he'
    exact (key b hbk).mp hin
  · intro m hm
    simp [Fin.ext_iff, edgB, Nat.mod_eq_of_lt m.isLt]
  · intro e he
    have he' : e ∈ t := he
    obtain ⟨b, hbk, rfl⟩ := boundary_door_form hk hmaps
      (Finset.mem_filter.mp he').1 (Finset.mem_filter.mp he').2.1 (Finset.mem_filter.mp he').2.2
    have : edgB (Edg.diag (n + 1 - 1 - b) b) = b := rfl
    simp only [this, Nat.mod_eq_of_lt hbk]
    rw [show n + 1 - 1 - b = n - b by omega]

/-! ## Rainbow cell at every mesh -/

/-- **Sperner output: a rainbow cell exists at every mesh `k ≥ 1`.**  All four hypotheses of
`sperner_two_dim_combinatorial` are discharged for the order subdivision and the Sperner
labelling, giving an odd (hence positive) number of rainbow cells. -/
theorem exists_rainbow_cell {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {k : ℕ} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3))) :
    ∃ c ∈ cells k, isRainbow (spernerLabel f k) c = true := by
  classical
  set L := spernerLabel f k with hL
  have hodd : Odd ((cells k).filter (fun c => isRainbow L c = true)).card :=
    sperner_two_dim_combinatorial (cells k) (edges k)
      (fun c e => bounds c e = true) (fun e => isDoor L e = true)
      (isBoundary k) (fun c => isRainbow L c = true)
      (fun t ht => hheart_cell (mem_cells.mp ht))
      (fun e he hd hb => hinterior_cell he hb)
      (fun e he hd hb => hboundaryOdd_cell he hb)
      (hboundaryCount hk hmaps)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hodd.pos
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.1, hc.2⟩

/-! ## From a rainbow cell to per-colour vertices

A rainbow cell yields, for each colour `t : Fin 3`, a lattice vertex `pₜ` with
`spernerLabel f k pₜ = t`, all three vertices being vertices of one cell (hence pairwise
within mesh distance).  The label property gives `f(vertexPt pₜ)ₜ ≤ (vertexPt pₜ)ₜ`. -/

/-- The three lattice vertices of a cell, as a function `Fin 3 → ℕ × ℕ`. -/
def cellVertex (c : Cell) (t : Fin 3) : ℕ × ℕ :=
  ![(cellVerts c).1, (cellVerts c).2.1, (cellVerts c).2.2] t

/-- A cell is rainbow iff every colour is realised by one of its three vertices under `L`. -/
theorem isRainbow_iff_surjective {L : ℕ × ℕ → Fin 3} {c : Cell} :
    isRainbow L c = true ↔ ∀ t : Fin 3, ∃ s : Fin 3, L (cellVertex c s) = t := by
  simp only [isRainbow, cellVertex, decide_eq_true_eq]
  constructor
  · intro h t
    have ht : t ∈ ({0, 1, 2} : Finset (Fin 3)) := by fin_cases t <;> simp
    rw [← h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h0 | h1 | h2
    · exact ⟨0, by simp [Matrix.cons_val_zero, h0.symm]⟩
    · exact ⟨1, by simp [h1.symm]⟩
    · exact ⟨2, by simp [Matrix.cons_val_two, h2.symm]⟩
  · intro h
    have huniv : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
    rw [huniv, Finset.eq_univ_iff_forall]
    intro x
    obtain ⟨s, hs⟩ := h x
    fin_cases s <;>
      simp_all only [cellVertex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Finset.mem_insert, Finset.mem_singleton] <;>
      subst hs <;> tauto

/-- Every vertex of a present cell lies in the lattice `i + j ≤ k`. -/
theorem cellVertex_le {k : ℕ} {c : Cell} (hc : cellMem k c) (t : Fin 3) :
    (cellVertex c t).1 + (cellVertex c t).2 ≤ k := by
  cases c <;> simp only [cellMem] at hc <;> fin_cases t <;>
    simp only [cellVertex, cellVerts] <;> simp <;> omega

/-- Two vertices of one present cell differ by at most `1` in each lattice coordinate. -/
theorem cellVertex_close (c : Cell) (s t : Fin 3) :
    ((cellVertex c s).1 : ℤ) - (cellVertex c t).1 ∈ Set.Icc (-1 : ℤ) 1 ∧
      ((cellVertex c s).2 : ℤ) - (cellVertex c t).2 ∈ Set.Icc (-1 : ℤ) 1 := by
  cases c <;> fin_cases s <;> fin_cases t <;>
    simp only [cellVertex, cellVerts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Set.mem_Icc] <;>
    constructor <;> push_cast <;> omega

/-! ## Mesh-limit assembly: 2-D Brouwer -/

/-- Coordinatewise bound on the gap between two cell vertices' simplex points: each
coordinate differs by at most `2 / k`. -/
theorem vertexPt_dist_le {k : ℕ} (hk : 0 < k) (c : Cell) (s t : Fin 3) (r : Fin 3) :
    |vertexPt k (cellVertex c s) r - vertexPt k (cellVertex c t) r| ≤ 2 / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨h1, h2⟩ := cellVertex_close c s t
  simp only [Set.mem_Icc] at h1 h2
  have hb1 : |((cellVertex c s).1 : ℝ) - (cellVertex c t).1| ≤ 1 := by
    rw [abs_le]; exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
  have hb2 : |((cellVertex c s).2 : ℝ) - (cellVertex c t).2| ≤ 1 := by
    rw [abs_le]; exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
  have hred : ∀ (p : ℕ × ℕ), vertexPt k p 0 = (p.1 : ℝ) / k ∧
      vertexPt k p 1 = (p.2 : ℝ) / k ∧
      vertexPt k p 2 = ((k : ℝ) - p.1 - p.2) / k := fun p => by
    refine ⟨?_, ?_, ?_⟩ <;> simp [vertexPt]
  fin_cases r <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one]
  · rw [(hred _).1, (hred _).1, div_sub_div_same, abs_div, abs_of_pos hkR,
      div_le_div_iff_of_pos_right hkR]; nlinarith [hb1]
  · rw [(hred _).2.1, (hred _).2.1, div_sub_div_same, abs_div, abs_of_pos hkR,
      div_le_div_iff_of_pos_right hkR]; nlinarith [hb2]
  · rw [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl, (hred _).2.2, (hred _).2.2,
      div_sub_div_same, abs_div, abs_of_pos hkR]
    rw [div_le_div_iff_of_pos_right hkR, abs_le]
    rw [abs_le] at hb1 hb2
    constructor <;> nlinarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-- **Rainbow approximation at mesh `n+1`.**  For each `n`, there is a cell `c` of `Δ²` at
mesh `n+1` whose vertices realise all three colours; writing `P t := vertexPt (n+1)
(cellVertex c t)`, each `P t ∈ Δ²` satisfies `f(P t)ₜ ≤ (P t)ₜ`, and the three points are
within `2/(n+1)` of each other coordinatewise. -/
theorem rainbow_approx {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (n : ℕ)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3))) :
    ∃ P : Fin 3 → (Fin 3 → ℝ),
      (∀ t, P t ∈ stdSimplex ℝ (Fin 3)) ∧
      (∀ t, f (P t) t ≤ P t t) ∧
      (∀ s t r, |P s r - P t r| ≤ 2 / (n + 1)) := by
  obtain ⟨c, hcmem, hrain⟩ := exists_rainbow_cell (k := n + 1) (by omega) hmaps
  have hcM : cellMem (n + 1) c := mem_cells.mp hcmem
  -- per-colour vertex realising each label
  have hsurj := (isRainbow_iff_surjective).mp hrain
  choose g hg using hsurj
  refine ⟨fun t => vertexPt (n + 1) (cellVertex c (g t)), ?_, ?_, ?_⟩
  · intro t
    exact vertexPt_mem_stdSimplex (by omega) (cellVertex_le hcM (g t))
  · intro t
    have hv : vertexPt (n + 1) (cellVertex c (g t)) ∈ stdSimplex ℝ (Fin 3) :=
      vertexPt_mem_stdSimplex (by omega) (cellVertex_le hcM (g t))
    have hfv : f (vertexPt (n + 1) (cellVertex c (g t))) ∈ stdSimplex ℝ (Fin 3) := hmaps hv
    have hspec := spernerLabel_spec hv hfv
    rw [hg t] at hspec
    exact hspec.2
  · intro s t r
    have : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact vertexPt_dist_le (by omega) c (g s) (g t) r

/-- **2-D Brouwer fixed point theorem on the standard 2-simplex.**
A continuous self-map of `Δ² = stdSimplex ℝ (Fin 3)` has a fixed point.  Assembled from the
Sperner output (`exists_rainbow_cell`) via the mesh-`1/(n+1)` triangulation: rainbow cells
give per-colour vertices that converge (along a subsequence extracted by compactness) to a
point `x*` with `f(x*)ᵢ ≤ x*ᵢ` for all `i`, which `eq_of_forall_le_on_stdSimplex` upgrades to
`f x* = x*`. -/
theorem brouwer_stdSimplex_two {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hf : ContinuousOn f (stdSimplex ℝ (Fin 3)))
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 3)) (stdSimplex ℝ (Fin 3))) :
    ∃ x ∈ stdSimplex ℝ (Fin 3), f x = x := by
  classical
  -- per-mesh rainbow data
  choose P hPmem hPle hPclose using fun n => rainbow_approx n hmaps
  -- the centre sequence lives in the compact simplex
  have hbmem : ∀ n, P n 0 ∈ stdSimplex ℝ (Fin 3) := fun n => hPmem n 0
  obtain ⟨x, hx, φ, hφ, htend⟩ :=
    (isCompact_stdSimplex (𝕜 := ℝ) (Fin 3)).tendsto_subseq hbmem
  refine ⟨x, hx, ?_⟩
  -- key: the rainbow gap tends to 0 along the subsequence
  have hgap0 : Tendsto (fun j => (2 : ℝ) / (φ j + 1)) atTop (𝓝 0) := by
    have hmono : Tendsto (fun j => (φ j : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    simpa using hmono.inv_tendsto_atTop.const_mul (2 : ℝ)
  -- each colour's vertex also converges to x along the subsequence
  have hPtend : ∀ t : Fin 3, Tendsto (fun j => P (φ j) t) atTop (𝓝 x) := by
    intro t
    rw [tendsto_pi_nhds]
    intro r
    have hb_r : Tendsto (fun j => P (φ j) 0 r) atTop (𝓝 (x r)) :=
      ((continuous_apply r).continuousAt.tendsto).comp htend
    have hdiff0 : Tendsto (fun j => P (φ j) t r - P (φ j) 0 r) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun j => (2 : ℝ) / (φ j + 1)) ?_ hgap0
      intro j
      simpa [Real.norm_eq_abs] using hPclose (φ j) t 0 r
    have := hdiff0.add hb_r
    simpa using this
  -- continuity passes the per-colour label inequality to the limit
  have hfx_le : ∀ t : Fin 3, f x t ≤ x t := by
    intro t
    -- f (P (φ j) t) → f x  (continuity within the simplex)
    have hfcont : Tendsto (fun j => f (P (φ j) t)) atTop (𝓝 (f x)) := by
      apply (hf.continuousWithinAt hx).tendsto.comp
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hPtend t) (Eventually.of_forall (fun j => hPmem (φ j) t))
    have hfx_t : Tendsto (fun j => f (P (φ j) t) t) atTop (𝓝 (f x t)) :=
      ((continuous_apply t).continuousAt.tendsto).comp hfcont
    have hxt : Tendsto (fun j => P (φ j) t t) atTop (𝓝 (x t)) :=
      (tendsto_pi_nhds.mp (hPtend t)) t
    exact le_of_tendsto_of_tendsto hfx_t hxt (Eventually.of_forall (fun j => hPle (φ j) t))
  -- all coordinates weakly decrease ⇒ fixed point
  exact eq_of_forall_le_on_stdSimplex x (f x) hx (hmaps hx) hfx_le

end ShenWork.Paper1
