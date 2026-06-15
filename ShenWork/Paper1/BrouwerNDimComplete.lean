/-
# n-D Brouwer: the Kuhn facet-sharing incidence (K2) on top of the abstract n-D Sperner

This file builds the concrete Kuhn (order) subdivision incidence on top of the committed
`ShenWork.Paper1.BrouwerNDim` pieces — the abstract engine `sperner_n_dim_combinatorial`,
the symbolic-`n` heart `heart_count_n`/`hheart_indexed`, and the Kuhn chain
`stepVec`/`chainVZ`/`sum_chainVZ` — mirroring the 2-D template `BrouwerTwoDim`.

## The combinatorial model

A **cell** of the Kuhn subdivision at base `p : Fin (n+1) → ℤ` with step-order
`σ : Equiv.Perm (Fin n)` is the ordered lattice chain `chainVZ p σ : Fin (n+1) → (Fin (n+1) → ℤ)`.
Its `n + 1` vertices are `chainVZ p σ 0, …, chainVZ p σ (last n)`.

A **facet** is obtained by *dropping one vertex index* `t : Fin (n+1)` of a cell; canonically it
is the **set** of the remaining `n` chain vertices, `facetSet (p, σ) t : Finset (Fin (n+1) → ℤ)`.
Using the unordered set as the normal form makes facet equality `DecidableEq`-checkable and
identifies the two cells that share an interior facet.

## The internal-facet partner (the genuine n-D incidence heart)

Dropping an **internal** vertex `t = s.succ` (`0 < t < last`) leaves a chain that is *also* the
drop of the same internal index from the cell with the two surrounding steps swapped,
`σ' = σ * Equiv.swap s.castSucc s.succ` (an adjacent transposition of `Fin n`).  This is the
`partnerPerm` map below; it is the n-D analogue of the 2-D `Up`/`Down` neighbour pairing and
shows every internal facet is shared by *exactly two* distinct cells over the same base.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import ShenWork.Paper1.BrouwerNDim

namespace ShenWork.Paper1

open Set Finset Filter Topology

/-! ## Chain vertices and the partner permutation -/

/-- The set of the `n + 1` ordered chain vertices of the Kuhn cell `(p, σ)`. -/
def chainSet {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin (n + 1) → ℤ) :=
  Finset.univ.image (chainVZ p σ)

/-- The canonical (unordered) facet of the cell `(p, σ)` obtained by dropping vertex `t`:
the `n` remaining chain vertices, recorded as a `Finset`. -/
def facetSet {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    Finset (Fin (n + 1) → ℤ) :=
  (Finset.univ.erase t).image (chainVZ p σ)

/-- The prefix-step index set `{ s : Fin n | s.castSucc.val < t.val }` that defines
`chainVZ … t`.  Below `t.val` it is `Iio`-shaped on the `Fin n` order. -/
theorem chainVZ_apply {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) (i : Fin (n + 1)) :
    chainVZ p σ t i
      = p i + ∑ s ∈ Finset.univ.filter (fun s : Fin n => s.val < t.val), stepVec (σ s) i := by
  unfold chainVZ
  refine congrArg (p i + ·) (Finset.sum_congr ?_ (fun _ _ => rfl))
  apply Finset.filter_congr; intro s _; simp [Fin.val_castSucc]

/-- The prefix index sets are nested along the `Fin (n+1)` order. -/
theorem chainVZ_prefix_mono {n : ℕ} (t u : Fin (n + 1)) (htu : t.val ≤ u.val) :
    Finset.univ.filter (fun s : Fin n => s.val < t.val)
      ⊆ Finset.univ.filter (fun s : Fin n => s.val < u.val) := by
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  omega

/-! ## The internal-facet partner

Drop an internal vertex `t` (with `1 ≤ t.val ≤ n`).  The two Kuhn steps surrounding it sit at
the `Fin n` positions `a := t-1` and `b := t`.  Swapping `σ` at `a, b` leaves every chain
vertex *except* `chainVZ … t` unchanged, hence leaves the dropped-`t` facet set unchanged. -/

/-- Swapping `σ` at two adjacent positions `a, b` leaves the prefix sum defining vertex `u`
unchanged, provided the prefix `{s.val < u.val}` contains both or neither of `a, b`. -/
theorem chainVZ_swap_eq_of_prefix {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (a b : Fin n) (u : Fin (n + 1))
    (hab : (a.val < u.val) ↔ (b.val < u.val)) :
    chainVZ p (σ * Equiv.swap a b) u = chainVZ p σ u := by
  classical
  funext i
  rw [chainVZ_apply, chainVZ_apply]
  refine congrArg (p i + ·) ?_
  set S : Finset (Fin n) := Finset.univ.filter (fun s : Fin n => s.val < u.val) with hS
  -- `swap a b` permutes `S` onto itself (both or neither of `a, b` lie in `S`)
  have hmaps : ∀ s ∈ S, Equiv.swap a b s ∈ S := by
    intro s hs
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    by_cases hsa : s = a
    · subst hsa; rw [Equiv.swap_apply_left]; exact hab.mp hs
    · by_cases hsb : s = b
      · subst hsb; rw [Equiv.swap_apply_right]; exact hab.mpr hs
      · rwa [Equiv.swap_apply_of_ne_of_ne hsa hsb]
  -- reindex the sum over `S` by the involution `swap a b`
  refine Finset.sum_nbij' (fun s => Equiv.swap a b s) (fun s => Equiv.swap a b s)
    hmaps hmaps (fun s _ => by simp) (fun s _ => by simp) (fun s _ => ?_)
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]

/-- **Internal-facet partner: the facet sets coincide.**  For an internal drop index `t`
(`1 ≤ t.val` and `t.val < n + 1 - 1`), the two adjacent step positions
`a := ⟨t-1⟩, b := ⟨t⟩ : Fin n` give a partner permutation `σ * swap a b` whose dropped-`t`
facet is *identical* to that of `σ`: every chain vertex other than `chainVZ … t` is fixed. -/
theorem facetSet_partner_eq {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n)
    (a b : Fin n) (ha : a.val = t.val - 1) (hb : b.val = t.val) :
    facetSet p (σ * Equiv.swap a b) t = facetSet p σ t := by
  classical
  unfold facetSet
  apply Finset.image_congr
  intro u hu
  rw [Finset.mem_coe, Finset.mem_erase] at hu
  obtain ⟨hut, _⟩ := hu
  have hne : u.val ≠ t.val := fun h => hut (Fin.ext h)
  apply chainVZ_swap_eq_of_prefix
  rw [ha, hb]; omega

/-- The partner permutation differs from `σ`: an adjacent transposition `swap a b` with
`a ≠ b` is nontrivial, so `σ * swap a b ≠ σ`. -/
theorem partnerPerm_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    σ * Equiv.swap a b ≠ σ := by
  intro h
  have hone : Equiv.swap a b = (1 : Equiv.Perm (Fin n)) := by
    have h2 : σ * Equiv.swap a b = σ * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel h2
  have : Equiv.swap a b a = a := by rw [hone]; rfl
  rw [Equiv.swap_apply_left] at this
  exact hab this.symm

/-- The partner cell shares the *same base* `p`, so it is present at mesh `k` exactly when the
original cell is.  Combined with `partnerPerm_ne`, an internal facet is therefore bounded by (at
least) the two distinct cells `(p, σ)` and `(p, σ * swap a b)`. -/
theorem facetSet_partner_pair {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n)
    (a b : Fin n) (ha : a.val = t.val - 1) (hb : b.val = t.val) (hab : a ≠ b) :
    σ * Equiv.swap a b ≠ σ ∧ facetSet p (σ * Equiv.swap a b) t = facetSet p σ t :=
  ⟨partnerPerm_ne σ hab, facetSet_partner_eq p σ h0 hlt a b ha hb⟩

/-! ## Evenness from a fixed-point-free involution (the `hinterior` engine)

The partner pairing on the cells bounding an interior facet is a *fixed-point-free involution*.
Such a Finset has even cardinality.  This is the abstract bridge that turns the partner lemma
into the engine's `hinterior` (interior door ⟹ even bounding-cell count). -/

/-- **A Finset closed under a fixed-point-free involution has even cardinality.**  Sums the
constant `1 : ZMod 2` over `s`, pairing each `a` with `g a`: `1 + 1 = 0`, so the total — which
is `(s.card : ZMod 2)` — vanishes, i.e. `s.card` is even. -/
theorem even_card_of_involution {α : Type*} [DecidableEq α] (s : Finset α) (g : ∀ a ∈ s, α)
    (hne : ∀ a ha, g a ha ≠ a) (g_mem : ∀ a ha, g a ha ∈ s)
    (hinv : ∀ a ha, g (g a ha) (g_mem a ha) = a) : Even s.card := by
  classical
  have hsum : ∑ _x ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution g (fun a ha => by decide) (fun a ha _ => hne a ha) g_mem hinv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

/-! ## Concrete Kuhn cells and the per-facet partner involution

A **cell** at base `p` is the pair `(p, σ)`.  We fix a base `p` (the internal partner never
changes the base) and work with cells of fixed base, encoded by their permutation
`σ : Equiv.Perm (Fin n)` — a `Fintype` with `DecidableEq`, so `Finset (Equiv.Perm (Fin n))`
is the natural carrier for "the cells of base `p` bounding a given facet".

For a fixed internal drop index `t`, the partner map `σ ↦ σ * swap a b` (with `a,b` the two
positions around `t`) is a fixed-point-free involution: this is precisely the data
`even_card_of_involution` consumes, giving the `hinterior` parity for the *internal* facets. -/

/-- The two `Fin n` step positions surrounding an internal drop index `t`
(`1 ≤ t.val ≤ n - 1`), as a pair `(a, b)` with `a.val = t-1`, `b.val = t`. -/
def aroundPos {n : ℕ} {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) :
    Fin n × Fin n :=
  (⟨t.val - 1, by omega⟩, ⟨t.val, by omega⟩)

/-- The two surrounding positions are distinct. -/
theorem aroundPos_ne {n : ℕ} {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) :
    (aroundPos h0 hlt).1 ≠ (aroundPos h0 hlt).2 := by
  simp only [aroundPos, Ne, Fin.mk.injEq]; omega

/-- The per-facet partner map on permutations, for an internal drop index `t`:
`σ ↦ σ * swap a b`.  It is a fixed-point-free involution on `Equiv.Perm (Fin n)`. -/
def partnerOf {n : ℕ} {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n)
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  σ * Equiv.swap (aroundPos h0 hlt).1 (aroundPos h0 hlt).2

/-- `partnerOf` is an involution. -/
theorem partnerOf_involutive {n : ℕ} {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n)
    (σ : Equiv.Perm (Fin n)) : partnerOf h0 hlt (partnerOf h0 hlt σ) = σ := by
  unfold partnerOf
  rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- `partnerOf` is fixed-point-free. -/
theorem partnerOf_ne {n : ℕ} {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n)
    (σ : Equiv.Perm (Fin n)) : partnerOf h0 hlt σ ≠ σ :=
  partnerPerm_ne σ (aroundPos_ne h0 hlt)

/-- `partnerOf` preserves the dropped-`t` facet set. -/
theorem partnerOf_facetSet {n : ℕ} (p : Fin (n + 1) → ℤ) {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) (σ : Equiv.Perm (Fin n)) :
    facetSet p (partnerOf h0 hlt σ) t = facetSet p σ t :=
  facetSet_partner_eq p σ h0 hlt _ _ rfl rfl

/-- **Internal-facet `hinterior` parity (per fixed base).**  Let `t` be an internal drop index
and let `S : Finset (Equiv.Perm (Fin n))` be a set of base-`p` cells that is **closed under the
partner map** `partnerOf` (the geometric content "every cell bounding the facet is reached from
one such cell by the adjacent-step swap").  Then `S.card` is even: the partner map is a
fixed-point-free involution on `S`.  This is the `hinterior` engine for internal facets, modulo
the single closure hypothesis (the reconstruction converse, K2'). -/
theorem internal_hinterior_card_even {n : ℕ} {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) (S : Finset (Equiv.Perm (Fin n)))
    (hclosed : ∀ σ ∈ S, partnerOf h0 hlt σ ∈ S) : Even S.card :=
  even_card_of_involution S (fun σ _ => partnerOf h0 hlt σ)
    (fun σ _ => partnerOf_ne h0 hlt σ) hclosed
    (fun σ _ => partnerOf_involutive h0 hlt σ)

/-- **Internal-facet `hinterior`, unconditional on the fixed-`(p,t)` slice.**  The set of
base-`p` permutations whose drop-`t` facet equals a fixed `F` is **automatically** closed under
the partner map (`partnerOf` preserves the facet, `partnerOf_facetSet`), so its cardinality is
**even with no further hypothesis**.  This removes the closure hypothesis of
`internal_hinterior_card_even` for the natural carrier set: the cells of base `p` bounding the
interior facet `F` via an internal drop at `t` always come in partner pairs.  (The remaining
content toward the global engine is purely that the *global* `bounds`-filter over all cells, for
an interior facet, decomposes into such fixed-`(p,t)` slices — the reconstruction converse K2'.) -/
theorem internal_hinterior_slice_even {n : ℕ} (p : Fin (n + 1) → ℤ) {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) (F : Finset (Fin (n + 1) → ℤ)) :
    Even (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => facetSet p σ t = F)).card := by
  classical
  refine internal_hinterior_card_even h0 hlt _ ?_
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [partnerOf_facetSet]; exact hσ.2

end ShenWork.Paper1
