/-
# Sperner's Lemma (combinatorial foundation of Brouwer's fixed point theorem)

Mathlib v4.29.1 has only the *antichain* Sperner theorem (`IsAntichain.sperner`,
`Mathlib/Combinatorics/SetFamily/LYM.lean`); it does **not** have the topological /
combinatorial Sperner lemma that underlies Brouwer.  This file builds it from scratch.

## Contents

* `ShenWork.Paper1.sperner_one_dim` — the 1-D Sperner lemma (= discrete IVT):
  for a 2-labeling `ℓ : Fin (n+1) → Fin 2` of a path with `ℓ 0 = 0`, `ℓ last = 1`,
  the number of "rainbow" edges `{i, i+1}` with `ℓ i ≠ ℓ (i+1)` is **odd**
  (so in particular `≥ 1`).  Proved by a parity-telescoping argument in `ZMod 2`.

* `ShenWork.Paper1.sperner_one_dim_exists` — the existential corollary (a rainbow
  edge exists), the form directly consumed by the 1-D Brouwer / IVT argument.

The 2-D / n-D combinatorial Sperner lemma is the genuine Brouwer foundation; see the
report accompanying this file for the precise next brick (an abstract simplicial
complex with a coloring + the boundary "door"-counting parity argument).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace ShenWork.Paper1

open Finset

/-! ## 1-D Sperner lemma -/

/-- The `ZMod 2` value of a `Fin 2` label. -/
private def lab2 (a : Fin 2) : ZMod 2 := (a.val : ZMod 2)

private lemma lab2_eq_iff (a b : Fin 2) : lab2 a = lab2 b ↔ a = b := by
  unfold lab2
  constructor
  · intro h
    have ha : a.val < 2 := a.isLt
    have hb : b.val < 2 := b.isLt
    have hval : (a.val : ZMod 2).val = (b.val : ZMod 2).val := by rw [h]
    rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hval
    exact Fin.ext hval
  · intro h; rw [h]

/-- For two `Fin 2` labels, the difference in `ZMod 2` is `1` iff the labels differ. -/
private lemma lab2_sub_eq_one_iff (a b : Fin 2) :
    lab2 b - lab2 a = 1 ↔ a ≠ b := by
  constructor
  · intro h hab
    rw [hab, sub_self] at h
    exact (by decide : (0 : ZMod 2) ≠ 1) h
  · intro hab
    -- in `ZMod 2`, two distinct elements differ by `1`
    fin_cases a <;> fin_cases b <;> simp_all [lab2]

/-- The "vertex labels" packaged as a function `ℕ → ZMod 2`, total via `Fin.last`-clamping
is unnecessary: we only index `i ≤ n`, and `range n`/`range (n+1)` stay in bounds. -/
private def gLab {n : ℕ} (ℓ : Fin (n + 1) → Fin 2) (i : ℕ) : ZMod 2 :=
  if h : i < n + 1 then lab2 (ℓ ⟨i, h⟩) else 0

/-- The number of rainbow edges, cast into `ZMod 2`, equals the telescoping
sum `gLab n - gLab 0 = lab2 (ℓ last) - lab2 (ℓ 0)`. -/
private lemma rainbow_card_cast {n : ℕ} (ℓ : Fin (n + 1) → Fin 2) :
    ((univ.filter (fun i : Fin n => ℓ i.castSucc ≠ ℓ i.succ)).card : ZMod 2)
      = lab2 (ℓ (Fin.last n)) - lab2 (ℓ 0) := by
  -- Step 1: card → sum of `ZMod 2` indicators over `Fin n`.
  rw [natCast_card_filter]
  -- Step 2: reindex `Fin n` to `range n`.
  have hreindex :
      (∑ i : Fin n, (if ℓ i.castSucc ≠ ℓ i.succ then (1 : ZMod 2) else 0))
        = ∑ i ∈ range n, (gLab ℓ (i + 1) - gLab ℓ i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => gLab ℓ (i + 1) - gLab ℓ i) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- Identify the indicator at `i` with the label-difference `gLab (i+1) - gLab i`.
    have hi : (i : ℕ) < n + 1 := Nat.lt_succ_of_lt i.isLt
    have hi1 : (i : ℕ) + 1 < n + 1 := Nat.succ_lt_succ i.isLt
    have egi : gLab ℓ (i : ℕ) = lab2 (ℓ i.castSucc) := by
      have : (⟨(i : ℕ), hi⟩ : Fin (n + 1)) = i.castSucc := by ext; simp
      unfold gLab; rw [dif_pos hi, this]
    have egi1 : gLab ℓ ((i : ℕ) + 1) = lab2 (ℓ i.succ) := by
      have : (⟨(i : ℕ) + 1, hi1⟩ : Fin (n + 1)) = i.succ := by ext; simp [Fin.val_succ]
      unfold gLab; rw [dif_pos hi1, this]
    rw [egi, egi1]
    by_cases h : ℓ i.castSucc = ℓ i.succ
    · simp only [h, ne_eq, not_true_eq_false, if_false, sub_self]
    · simp only [h, ne_eq, not_false_eq_true, if_true]
      exact ((lab2_sub_eq_one_iff (ℓ i.castSucc) (ℓ i.succ)).mpr h).symm
  rw [hreindex, Finset.sum_range_sub (gLab ℓ) n]
  -- Step 3: evaluate the endpoints.
  have e0 : gLab ℓ 0 = lab2 (ℓ 0) := by
    have : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := by ext; simp
    unfold gLab; rw [dif_pos (Nat.succ_pos n), this]
  have en : gLab ℓ n = lab2 (ℓ (Fin.last n)) := by
    have : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by ext; simp [Fin.last]
    unfold gLab; rw [dif_pos (Nat.lt_succ_self n), this]
  rw [e0, en]

/-- **1-D Sperner lemma** (the discrete intermediate value theorem).

Given a 2-labeling `ℓ` of the `n + 1` vertices of a path with the two ends labeled
`0` and `1`, the number of edges whose endpoints carry different labels is **odd**. -/
theorem sperner_one_dim {n : ℕ} (ℓ : Fin (n + 1) → Fin 2)
    (h0 : ℓ 0 = 0) (hn : ℓ (Fin.last n) = 1) :
    Odd (univ.filter (fun i : Fin n => ℓ i.castSucc ≠ ℓ i.succ)).card := by
  have hcast := rainbow_card_cast ℓ
  rw [h0, hn] at hcast
  have hone : lab2 (1 : Fin 2) - lab2 (0 : Fin 2) = (1 : ZMod 2) := by decide
  rw [hone] at hcast
  -- `(card : ZMod 2) = 1` ↔ card is odd.
  exact ZMod.natCast_eq_one_iff_odd.mp hcast

/-- The existential corollary: a rainbow edge exists (discrete IVT). -/
theorem sperner_one_dim_exists {n : ℕ} (ℓ : Fin (n + 1) → Fin 2)
    (h0 : ℓ 0 = 0) (hn : ℓ (Fin.last n) = 1) :
    ∃ i : Fin n, ℓ i.castSucc ≠ ℓ i.succ := by
  have hodd := sperner_one_dim ℓ h0 hn
  by_contra hcon
  push Not at hcon
  have hempty : (univ.filter (fun i : Fin n => ℓ i.castSucc ≠ ℓ i.succ)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _; exact not_not.mpr (hcon i)
  rw [hempty, Finset.card_empty] at hodd
  simp at hodd

/-! ## 2-D combinatorial Sperner lemma

We give the *combinatorial* 2-D Sperner lemma — the form Brouwer's fixed point theorem
actually consumes.  A triangulation of a triangle is modelled abstractly as a finite set
of "triangles" `T` together with a finite set of "edges" `E`, an incidence relation
`bounds : Δ → ε → Prop` (which edges bound a triangle), a 3-colouring captured by the
*door* predicate `isDoor : ε → Prop` (an edge whose two endpoints carry colours `0` and
`1`), and a *rainbow* predicate `isRainbow : Δ → Prop` (a triangle carrying all three
colours).  The geometry enters through three hypotheses, each of which is a *local*,
checkable fact about a triangulation:

* `hheart` — for each triangle, its number of door-edges is odd **iff** it is rainbow.
  (This is the genuine combinatorial heart; see `doorCount_odd_iff_rainbow`, proved by
  exhausting the `3^3` colourings of a triple.)
* `hinterior` / `hboundary` — each door bounds an even number of triangles unless it is a
  *boundary* door, and there are an odd number of boundary doors (the latter is exactly
  the 1-D Sperner lemma applied to the bottom edge — `sperner_one_dim`).

The conclusion is that the number of **rainbow triangles is odd**, hence `≥ 1`. -/

/-- Whether an unordered colour pair `{a, b}` equals `{0, 1}` — i.e. the edge is a *door*. -/
private def isDoorPair (a b : Fin 3) : Bool := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)

/-- Number of *door* edges among the three edges `{01}, {02}, {12}` of a triangle whose
vertices carry colours `c0, c1, c2 : Fin 3`. -/
private def doorCount (c0 c1 c2 : Fin 3) : ℕ :=
  (if isDoorPair c0 c1 then 1 else 0) + (if isDoorPair c0 c2 then 1 else 0)
    + (if isDoorPair c1 c2 then 1 else 0)

/-- A triangle is *rainbow* iff its three vertex colours are exactly `{0, 1, 2}`. -/
private def isRainbowTri (c0 c1 c2 : Fin 3) : Bool := ({c0, c1, c2} : Finset (Fin 3)) = {0, 1, 2}

/-- **Combinatorial heart of 2-D Sperner.**  A triangle has an *odd* number of door-edges
iff it is rainbow.  Proved by exhausting the `3 ^ 3` colourings of a triple. -/
theorem doorCount_odd_iff_rainbow (c0 c1 c2 : Fin 3) :
    Odd (doorCount c0 c1 c2) ↔ isRainbowTri c0 c1 c2 = true := by
  revert c0 c1 c2; decide

/-- **Abstract 2-D combinatorial Sperner lemma.**  Given a triangulation (`T` triangles,
`E` edges) with a door predicate and a rainbow predicate satisfying the local heart
identity, the even-interior / odd-boundary door incidence, and an odd boundary-door count,
the number of rainbow triangles is **odd** (in particular there is a rainbow triangle). -/
theorem sperner_two_dim_combinatorial
    {Δ ε : Type*}
    (T : Finset Δ) (E : Finset ε)
    (bounds : Δ → ε → Prop) [DecidableRel bounds]
    (isDoor : ε → Prop) [DecidablePred isDoor]
    (isBoundary : ε → Prop) [DecidablePred isBoundary]
    (isRainbow : Δ → Prop) [DecidablePred isRainbow]
    -- heart: a triangle's door-edge count is odd iff it is rainbow
    (hheart : ∀ t ∈ T, Odd (E.filter (fun e => bounds t e ∧ isDoor e)).card ↔ isRainbow t)
    -- each non-boundary door bounds an even number of triangles
    (hinterior : ∀ e ∈ E, isDoor e → ¬ isBoundary e →
        Even (T.filter (fun t => bounds t e)).card)
    -- each boundary door bounds an odd number of triangles
    (hboundaryOdd : ∀ e ∈ E, isDoor e → isBoundary e →
        Odd (T.filter (fun t => bounds t e)).card)
    -- the number of boundary doors is odd (= 1-D Sperner on the bottom edge)
    (hboundaryCount : Odd (E.filter (fun e => isDoor e ∧ isBoundary e)).card) :
    Odd (T.filter isRainbow).card := by
  classical
  -- Restrict the incidence relation to door-edges.
  set r : Δ → ε → Prop := fun t e => bounds t e ∧ isDoor e with hr
  -- Double-count incidences `(t, e)` with `t ∈ T`, `e ∈ E`, `e` a door bounding `t`.
  have hswap :
      ∑ t ∈ T, (E.filter (r t)).card = ∑ e ∈ E, (T.filter (fun t => r t e)).card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := r) (s := T) (t := E)
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using this
  -- Work modulo 2 (in `ZMod 2`): a `card` is odd iff its cast is `1`.
  -- LHS parity: number of triangles with an odd door-count = number of rainbow triangles.
  have hLHS : (∑ t ∈ T, (E.filter (r t)).card : ZMod 2)
      = ((T.filter isRainbow).card : ZMod 2) := by
    rw [natCast_card_filter isRainbow T]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    -- (E.filter (r t)).card mod 2 = indicator of rainbow t
    have hiff : Odd (E.filter (r t)).card ↔ isRainbow t := hheart t ht
    by_cases hR : isRainbow t
    · simp only [hR, if_true]
      have : Odd (E.filter (r t)).card := hiff.mpr hR
      exact ZMod.natCast_eq_one_iff_odd.mpr this
    · simp only [hR, if_false]
      have hEven : ¬ Odd (E.filter (r t)).card := fun h => hR (hiff.mp h)
      rw [Nat.not_odd_iff_even] at hEven
      exact ZMod.natCast_eq_zero_iff_even.mpr hEven
  -- RHS parity: each door bounds (interior: even, boundary: odd) triangles; non-doors give 0.
  have hRHS : (∑ e ∈ E, (T.filter (fun t => r t e)).card : ZMod 2)
      = ((E.filter (fun e => isDoor e ∧ isBoundary e)).card : ZMod 2) := by
    rw [natCast_card_filter (fun e => isDoor e ∧ isBoundary e) E]
    refine Finset.sum_congr rfl (fun e he => ?_)
    by_cases hd : isDoor e
    · by_cases hb : isBoundary e
      · -- boundary door: odd count, indicator 1
        simp only [hd, hb, and_true, if_true]
        have : Odd (T.filter (fun t => r t e)).card := by
          have : (T.filter (fun t => r t e)) = (T.filter (fun t => bounds t e)) := by
            apply Finset.filter_congr; intro t _; simp [hr, hd]
          rw [this]; exact hboundaryOdd e he hd hb
        exact ZMod.natCast_eq_one_iff_odd.mpr this
      · -- interior door: even count, indicator 0
        simp only [hd, hb, and_false, if_false]
        have hEven : Even (T.filter (fun t => r t e)).card := by
          have : (T.filter (fun t => r t e)) = (T.filter (fun t => bounds t e)) := by
            apply Finset.filter_congr; intro t _; simp [hr, hd]
          rw [this]; exact hinterior e he hd hb
        exact ZMod.natCast_eq_zero_iff_even.mpr hEven
    · -- non-door: r t e false, count 0, indicator 0
      simp only [hd, false_and, if_false]
      have hzero : (T.filter (fun t => r t e)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro t _; simp [hr, hd]
      rw [hzero, Finset.card_empty, Nat.cast_zero]
  -- Cast the double-count identity into `ZMod 2`.
  have hswapZ : (∑ t ∈ T, (E.filter (r t)).card : ZMod 2)
      = (∑ e ∈ E, (T.filter (fun t => r t e)).card : ZMod 2) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, hswap]
  -- Combine: rainbow count ≡ boundary-door count ≡ 1 (mod 2).
  have key : ((T.filter isRainbow).card : ZMod 2)
      = ((E.filter (fun e => isDoor e ∧ isBoundary e)).card : ZMod 2) := by
    rw [← hLHS, hswapZ, hRHS]
  have hbd : ((E.filter (fun e => isDoor e ∧ isBoundary e)).card : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hboundaryCount
  rw [hbd] at key
  exact ZMod.natCast_eq_one_iff_odd.mp key

end ShenWork.Paper1
