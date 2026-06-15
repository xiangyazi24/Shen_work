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

/-- The chain map `t ↦ chainVZ p σ t` is injective: distinct indices give distinct last
coordinates. -/
theorem chainVZ_injective {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (chainVZ p σ) := by
  intro t t' heq
  have hl : chainVZ p σ t (Fin.last n) = chainVZ p σ t' (Fin.last n) := by rw [heq]
  rw [chainVZ_last, chainVZ_last] at hl
  have : (t.val : ℤ) = (t'.val : ℤ) := by omega
  exact Fin.ext (by exact_mod_cast this)

/-- A chain vertex of `(p, σ)` belongs to `facetSet p σ t` iff its index differs from `t`. -/
theorem mem_facetSet_iff {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t u : Fin (n + 1)) : chainVZ p σ u ∈ facetSet p σ t ↔ u ≠ t := by
  unfold facetSet
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨w, hwt, hw⟩
    have : u = w := (chainVZ_injective p σ hw).symm
    rw [this]; exact hwt
  · intro hut
    exact ⟨u, hut, rfl⟩

/-- `facetSet p σ t` has exactly `n` elements (the `n` chain vertices other than the dropped
one), since the chain map is injective. -/
theorem card_facetSet {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) : (facetSet p σ t).card = n := by
  unfold facetSet
  rw [Finset.card_image_of_injective _ (chainVZ_injective p σ),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Drop-index recovery.**  If the facet `F` equals `facetSet p σ t`, then `t` is the unique
chain index whose vertex is missing from `F`.  This recovers the dropped index from the
unordered facet (knowing the cell), the backbone of the global incidence reconstruction. -/
theorem dropIdx_unique {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t u : Fin (n + 1)} (hu : chainVZ p σ u ∉ facetSet p σ t) : u = t := by
  by_contra hne
  exact hu ((mem_facetSet_iff p σ t u).mpr hne)

/-- The dropped index `t` is characterised by: every *other* chain vertex is in `F`, and
`chainVZ p σ t ∉ F`.  Combined with `card_facetSet`, this fully recovers `t`. -/
theorem facetSet_drop_notMem {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) : chainVZ p σ t ∉ facetSet p σ t := by
  rw [mem_facetSet_iff]; simp

/-! ## The concrete Kuhn cell carrier and global incidence

A **cell** is a pair `c = (p, σ)` with base `p : Fin (n+1) → ℤ` and step order
`σ : Equiv.Perm (Fin n)`; `KCell n` is the carrier type (a product of types with
`DecidableEq`).  The cells *present at mesh `k`* are the valid ones (`cellValid`); they live
in a finite box of bases.  A facet is a `Finset (Fin (n+1) → ℤ)`, and `c` *bounds* `F` iff
`F = facetSet p σ t` for some drop index `t`. -/

/-- The Kuhn cell carrier: base over `ℤ` plus a step-order permutation. -/
abbrev KCell (n : ℕ) : Type := (Fin (n + 1) → ℤ) × Equiv.Perm (Fin n)

/-- A cell *bounds* a facet `F` iff some drop of its chain yields `F`. -/
def cellBounds {n : ℕ} (c : KCell n) (F : Finset (Fin (n + 1) → ℤ)) : Prop :=
  ∃ t : Fin (n + 1), facetSet c.1 c.2 t = F

instance {n : ℕ} (c : KCell n) (F : Finset (Fin (n + 1) → ℤ)) :
    Decidable (cellBounds c F) := by unfold cellBounds; infer_instance

/-- A cell *exists at mesh `k`* iff it is `cellValid` (base sums to `k`, all chain vertices
nonnegative). -/
def cellMemN {n : ℕ} (k : ℕ) (c : KCell n) : Prop := cellValid k c.1 c.2

instance {n : ℕ} (k : ℕ) (c : KCell n) : Decidable (cellMemN k c) := by
  unfold cellMemN; infer_instance

/-- The unique drop index that produced `F` from the bounding cell `c`: the chain index
whose vertex is missing from `F`.  Well-defined when `cellBounds c F`. -/
noncomputable def dropOf {n : ℕ} (c : KCell n) (F : Finset (Fin (n + 1) → ℤ)) : Fin (n + 1) :=
  if h : ∃ t : Fin (n + 1), chainVZ c.1 c.2 t ∉ F then h.choose else 0

/-- When `c` bounds `F` via drop `t`, the recovered `dropOf c F` equals `t`. -/
theorem dropOf_eq {n : ℕ} (c : KCell n) {F : Finset (Fin (n + 1) → ℤ)} {t : Fin (n + 1)}
    (ht : facetSet c.1 c.2 t = F) : dropOf c F = t := by
  have hmiss : chainVZ c.1 c.2 t ∉ F := by rw [← ht]; exact facetSet_drop_notMem c.1 c.2 t
  have hex : ∃ u : Fin (n + 1), chainVZ c.1 c.2 u ∉ F := ⟨t, hmiss⟩
  unfold dropOf
  rw [dif_pos hex]
  -- the chosen `u` is missing from `F = facetSet … t`, hence `u = t` by `dropIdx_unique`
  have hchoose : chainVZ c.1 c.2 hex.choose ∉ F := hex.choose_spec
  have hchoose' : chainVZ c.1 c.2 hex.choose ∉ facetSet c.1 c.2 t := ht ▸ hchoose
  exact dropIdx_unique c.1 c.2 hchoose'

/-! ## The endpoint forward / inverse maps and their inverse relation

`endpointFwd` is the endpoint base-shift `(p, σ) ↦ (p + stepVec (σ 0), σ * finRotate n)` of
`BrouwerNDimFinal`, packaged on the carrier `KCell n`.  `endpointInv` is its two-sided
inverse; together they form the endpoint half of the global partner involution. -/

/-- The endpoint forward map on cells (drop-`0` ↦ drop-`last`):
`(p, σ) ↦ (p + stepVec (σ ⟨0,hn⟩), σ * finRotate n)`. -/
noncomputable def endpointFwd {n : ℕ} (hn : 0 < n) (c : KCell n) : KCell n :=
  (fun i => c.1 i + stepVec (c.2 ⟨0, hn⟩) i, c.2 * finRotate n)

/-- The endpoint inverse map on cells (drop-`last` ↦ drop-`0`): undoes `endpointFwd`.
With `τ = σ' * (finRotate n)⁻¹`, the base shifts back by `stepVec (τ ⟨0,hn⟩)`. -/
noncomputable def endpointInv {n : ℕ} (hn : 0 < n) (c : KCell n) : KCell n :=
  (fun i => c.1 i - stepVec ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩) i, c.2 * (finRotate n)⁻¹)

/-- `endpointInv` undoes `endpointFwd`. -/
theorem endpointInv_fwd {n : ℕ} (hn : 0 < n) (c : KCell n) :
    endpointInv hn (endpointFwd hn c) = c := by
  have hperm : c.2 * finRotate n * (finRotate n)⁻¹ = c.2 := mul_inv_cancel_right _ _
  apply Prod.ext
  · funext i
    simp only [endpointInv, endpointFwd, hperm]
    ring
  · simp only [endpointInv, endpointFwd, hperm]

/-- `endpointFwd` undoes `endpointInv`. -/
theorem endpointFwd_inv {n : ℕ} (hn : 0 < n) (c : KCell n) :
    endpointFwd hn (endpointInv hn c) = c := by
  have hperm : c.2 * (finRotate n)⁻¹ * finRotate n = c.2 := inv_mul_cancel_right _ _
  apply Prod.ext
  · funext i
    simp only [endpointInv, endpointFwd, hperm]
    ring
  · simp only [endpointInv, endpointFwd, hperm]

/-! ## The global partner map on cells bounding a facet

For a facet `F` and a cell `c` bounding it (`cellBounds c F`), recover the drop index
`t = dropOf c F` and form the partner sharing `F`:

* `t = 0`        — endpoint forward `endpointFwd` (its drop-`last` facet equals `F`);
* `t = last`     — endpoint inverse `endpointInv` (its drop-`0` facet equals `F`);
* `0 < t < n`    — internal swap `(p, σ * swap (t-1) t)` (same drop-`t` facet).

This map is a fixed-point-free involution on the cells bounding an *interior* facet; on a
geometric boundary facet exactly one side is a valid cell, so the count is odd. -/

/-- The (internal) adjacent-swap partner permutation around drop index `t`. -/
noncomputable def swapAround {n : ℕ} (t : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  if h : 0 < t.val ∧ t.val < n then
    σ * Equiv.swap ⟨t.val - 1, by omega⟩ ⟨t.val, by omega⟩
  else σ

/-- The global partner of cell `c` at facet `F`: endpoint forward/inverse at the two ends,
internal swap in between, keyed by the recovered drop index `dropOf c F`. -/
noncomputable def partnerCell {n : ℕ} (hn : 0 < n) (c : KCell n)
    (F : Finset (Fin (n + 1) → ℤ)) : KCell n :=
  let t := dropOf c F
  if t.val = 0 then endpointFwd hn c
  else if t.val = n then endpointInv hn c
  else (c.1, swapAround t c.2)

/-! ### Facet-sharing of the partner (each case) -/

/-- Internal case: the swap partner shares the same drop-`t` facet. -/
theorem swapAround_facet {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) :
    facetSet p (swapAround t σ) t = facetSet p σ t := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩]
  exact facetSet_partner_eq p σ h0 hlt _ _ rfl rfl

/-- Internal case: the swap partner is a *different* cell (nontrivial transposition). -/
theorem swapAround_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) : swapAround t σ ≠ σ := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩]
  refine partnerPerm_ne σ ?_
  simp only [Ne, Fin.mk.injEq]; omega

/-- Internal case: `swapAround` is involutive. -/
theorem swapAround_involutive {n : ℕ} (σ : Equiv.Perm (Fin n)) {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) : swapAround t (swapAround t σ) = σ := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩, dif_pos ⟨h0, hlt⟩, mul_assoc, Equiv.swap_mul_self, mul_one]

/-- Endpoint forward case: `endpointFwd hn c` shares `c`'s drop-`0` facet via *its* drop-`last`
facet. -/
theorem endpointFwd_facet {n : ℕ} (hn : 0 < n) (c : KCell n) :
    facetSet (endpointFwd hn c).1 (endpointFwd hn c).2 (Fin.last n)
      = facetSet c.1 c.2 0 := by
  unfold endpointFwd
  exact facetSet_endpoint_eq hn c.1 c.2

/-- Endpoint inverse case: `endpointInv hn c` shares `c`'s drop-`last` facet via *its*
drop-`0` facet.  Obtained by applying `endpointFwd_facet` to `endpointInv hn c` and using
`endpointFwd_inv`. -/
theorem endpointInv_facet {n : ℕ} (hn : 0 < n) (c : KCell n) :
    facetSet (endpointInv hn c).1 (endpointInv hn c).2 0
      = facetSet c.1 c.2 (Fin.last n) := by
  have h := endpointFwd_facet hn (endpointInv hn c)
  rw [endpointFwd_inv hn c] at h
  exact h.symm

/-! ### The partner is a fixed-point-free involution -/

/-- Evaluate `partnerCell` when the drop index has value `0`. -/
theorem partnerCell_of_zero {n : ℕ} (hn : 0 < n) (c : KCell n)
    {F : Finset (Fin (n + 1) → ℤ)} (h : (dropOf c F).val = 0) :
    partnerCell hn c F = endpointFwd hn c := by
  unfold partnerCell; rw [if_pos h]

/-- Evaluate `partnerCell` when the drop index has value `n` (i.e. `last`). -/
theorem partnerCell_of_last {n : ℕ} (hn : 0 < n) (c : KCell n)
    {F : Finset (Fin (n + 1) → ℤ)} (h0 : (dropOf c F).val ≠ 0) (h : (dropOf c F).val = n) :
    partnerCell hn c F = endpointInv hn c := by
  unfold partnerCell; rw [if_neg h0, if_pos h]

/-- Evaluate `partnerCell` for an internal drop index. -/
theorem partnerCell_of_internal {n : ℕ} (hn : 0 < n) (c : KCell n)
    {F : Finset (Fin (n + 1) → ℤ)} (h0 : (dropOf c F).val ≠ 0) (h : (dropOf c F).val ≠ n) :
    partnerCell hn c F = (c.1, swapAround (dropOf c F) c.2) := by
  unfold partnerCell; rw [if_neg h0, if_neg h]

/-- `last n` has value `n`, distinguishing the `t.val = n` branch. -/
theorem dropOf_partner {n : ℕ} (hn : 0 < n) (c : KCell n) {F : Finset (Fin (n + 1) → ℤ)}
    (hb : cellBounds c F) :
    dropOf (partnerCell hn c F) F = (
      let t := dropOf c F
      if t.val = 0 then Fin.last n
      else if t.val = n then (0 : Fin (n + 1))
      else t) := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  simp only [partnerCell, htd]
  by_cases h0 : t.val = 0
  · rw [if_pos h0]
    have : facetSet (endpointFwd hn c).1 (endpointFwd hn c).2 (Fin.last n) = F := by
      rw [endpointFwd_facet hn c]
      have : (0 : Fin (n + 1)) = t := Fin.ext (by simp [h0])
      rw [this]; exact ht
    rw [dropOf_eq _ this]; simp [h0]
  · rw [if_neg h0]
    by_cases hn' : t.val = n
    · rw [if_pos hn']
      have htlast : t = Fin.last n := Fin.ext (by simp [hn', Fin.val_last])
      have : facetSet (endpointInv hn c).1 (endpointInv hn c).2 0 = F := by
        rw [endpointInv_facet hn c, ← htlast]; exact ht
      rw [dropOf_eq _ this]; simp [h0, hn']
    · rw [if_neg hn']
      have h0' : 0 < t.val := by omega
      have hlt : t.val < n := by omega
      have : facetSet c.1 (swapAround t c.2) t = F := by
        rw [swapAround_facet c.1 c.2 h0' hlt]; exact ht
      rw [dropOf_eq _ this]; simp [h0, hn']

/-- **The partner involution.**  For a cell bounding `F`, the partner of the partner is the
original cell. -/
theorem partnerCell_involutive {n : ℕ} (hn : 0 < n) (c : KCell n)
    {F : Finset (Fin (n + 1) → ℤ)} (hb : cellBounds c F) :
    partnerCell hn (partnerCell hn c F) F = c := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  have hdp := dropOf_partner hn c ⟨t, ht⟩
  simp only [htd] at hdp
  by_cases h0 : t.val = 0
  · -- partner = endpointFwd, its drop = last (val n), so re-partner via endpointInv
    have hpart : partnerCell hn c F = endpointFwd hn c :=
      partnerCell_of_zero hn c (by rw [htd]; exact h0)
    have hdrop : (dropOf (endpointFwd hn c) F).val = n := by
      rw [← hpart, hdp]; simp [h0, Fin.val_last]
    rw [hpart, partnerCell_of_last hn _ (by rw [hdrop]; omega) hdrop]
    exact endpointInv_fwd hn c
  · by_cases hn' : t.val = n
    · -- partner = endpointInv, its drop = 0, re-partner via endpointFwd
      have hpart : partnerCell hn c F = endpointInv hn c :=
        partnerCell_of_last hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn')
      have hdrop : (dropOf (endpointInv hn c) F).val = 0 := by
        rw [← hpart, hdp]; simp [h0, hn']
      rw [hpart, partnerCell_of_zero hn _ hdrop]
      exact endpointFwd_inv hn c
    · -- internal: partner = (p, swapAround t σ), same drop t
      have hpart : partnerCell hn c F = (c.1, swapAround t c.2) := by
        rw [partnerCell_of_internal hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn'), htd]
      have hdrop : dropOf (c.1, swapAround t c.2) F = t := by
        rw [← hpart, hdp]; simp [h0, hn']
      have hdrop0 : (dropOf (c.1, swapAround t c.2) F).val ≠ 0 := by rw [hdrop]; exact h0
      have hdropn : (dropOf (c.1, swapAround t c.2) F).val ≠ n := by rw [hdrop]; exact hn'
      rw [hpart, partnerCell_of_internal hn _ hdrop0 hdropn, hdrop]
      have h0' : 0 < t.val := by omega
      have hlt : t.val < n := by omega
      apply Prod.ext
      · rfl
      · exact swapAround_involutive c.2 h0' hlt

/-- **The partner bounds the same facet `F`.** -/
theorem partnerCell_bounds {n : ℕ} (hn : 0 < n) (c : KCell n)
    {F : Finset (Fin (n + 1) → ℤ)} (hb : cellBounds c F) :
    cellBounds (partnerCell hn c F) F := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  by_cases h0 : t.val = 0
  · rw [partnerCell_of_zero hn c (by rw [htd]; exact h0)]
    refine ⟨Fin.last n, ?_⟩
    rw [endpointFwd_facet hn c]
    have : (0 : Fin (n + 1)) = t := Fin.ext (by simp [h0])
    rw [this]; exact ht
  · by_cases hn' : t.val = n
    · rw [partnerCell_of_last hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn')]
      refine ⟨0, ?_⟩
      rw [endpointInv_facet hn c]
      have htlast : t = Fin.last n := Fin.ext (by simp [hn', Fin.val_last])
      rw [← htlast]; exact ht
    · rw [partnerCell_of_internal hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn'), htd]
      refine ⟨t, ?_⟩
      rw [swapAround_facet c.1 c.2 (by omega) (by omega)]; exact ht

/-- **The partner is a genuinely different cell** (the involution is fixed-point-free).  In
each case a structural witness separates the partner from `c`: a distinct base (endpoint) or a
distinct permutation (internal swap). -/
theorem partnerCell_ne {n : ℕ} (hn : 0 < n) (c : KCell n)
    {F : Finset (Fin (n + 1) → ℤ)} (hb : cellBounds c F) :
    partnerCell hn c F ≠ c := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  by_cases h0 : t.val = 0
  · rw [partnerCell_of_zero hn c (by rw [htd]; exact h0)]
    intro hcon
    -- bases differ: endpointFwd shifts the base
    have hbase : (endpointFwd hn c).1 = c.1 := by rw [hcon]
    exact (endpoint_base_ne hn c.1 c.2) hbase
  · by_cases hn' : t.val = n
    · rw [partnerCell_of_last hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn')]
      intro hcon
      -- apply endpointFwd to both sides: c = endpointFwd (endpointInv c) = endpointFwd c
      have h2 : endpointFwd hn (endpointInv hn c) = endpointFwd hn c := by rw [hcon]
      rw [endpointFwd_inv hn c] at h2
      -- h2 : c = endpointFwd hn c
      have hbase : (endpointFwd hn c).1 = c.1 := congrArg Prod.fst h2.symm
      exact (endpoint_base_ne hn c.1 c.2) hbase
    · rw [partnerCell_of_internal hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn'), htd]
      intro hcon
      have hperm : swapAround t c.2 = c.2 := by
        have := congrArg Prod.snd hcon; simpa using this
      exact (swapAround_ne c.2 (by omega) (by omega)) hperm

/-! ## `hinterior` from the global partner involution

The cells of `cells k` bounding an *interior* facet `F` (i.e. a facet whose bounding cells all
have valid partners) come in partner pairs under `partnerCell`, a fixed-point-free involution
on that Finset; hence the count is even.  This is the engine's `hinterior` for the concrete
Kuhn complex, *modulo* the single geometric input that the partner of a valid bounding cell of
an interior facet is itself valid (`hPartnerValid`). -/

/-- **`hinterior` via the partner involution.**  Let `F` be a facet such that every valid cell
bounding `F` has a valid partner (the interior condition `hPartnerValid`).  Then the number of
valid cells of `cells k` bounding `F` is even: `partnerCell hn · F` is a fixed-point-free
involution on that Finset (`partnerCell_ne`, `partnerCell_involutive`), carrying it to itself
(`partnerCell_bounds` + `hPartnerValid`). -/
theorem hinterior_kuhn {n : ℕ} (hn : 0 < n) (k : ℕ)
    (cellsK : Finset (KCell n)) (hcellsK : ∀ c, c ∈ cellsK ↔ cellMemN k c)
    (F : Finset (Fin (n + 1) → ℤ))
    (hPartnerValid : ∀ c ∈ cellsK, cellBounds c F → cellMemN k (partnerCell hn c F)) :
    Even (cellsK.filter (fun c => cellBounds c F)).card := by
  classical
  set S := cellsK.filter (fun c => cellBounds c F) with hS
  have hmemS : ∀ c, c ∈ S → c ∈ cellsK ∧ cellBounds c F := by
    intro c hc; rw [hS, Finset.mem_filter] at hc; exact hc
  have g_mem : ∀ c (_ : c ∈ S), partnerCell hn c F ∈ S := by
    intro c hc
    obtain ⟨hck, hcb⟩ := hmemS c hc
    rw [hS, Finset.mem_filter]
    exact ⟨(hcellsK _).mpr (hPartnerValid c hck hcb), partnerCell_bounds hn c hcb⟩
  refine even_card_of_involution S (fun c _ => partnerCell hn c F) ?_ g_mem ?_
  · -- fixed-point-free
    intro c hc
    exact partnerCell_ne hn c (hmemS c hc).2
  · -- involutive
    intro c hc
    exact partnerCell_involutive hn c (hmemS c hc).2

/-! ## Internal validity preservation (the squeeze)

Dropping an *internal* vertex `t` (`0 < t < n`) and applying the adjacent swap produces a new
intermediate vertex `chainVZ p (σ * swap (t-1) t) t`, which is *squeezed* between the two
valid neighbours `chainVZ p σ (t-1)` and `chainVZ p σ (t+1)`: explicitly it equals
`chainVZ p σ (t-1) + stepVec (σ ⟨t⟩)`.  Coordinatewise this is `≥ 0`:

* away from the last coordinate, the step only *adds*, so the new vertex dominates the valid
  `chainVZ p σ (t-1)`;
* at the last coordinate, the step subtracts `1`, but the *next* valid vertex
  `chainVZ p σ (t+1) = chainVZ p σ (t-1) + stepVec(σ⟨t-1⟩) + stepVec(σ⟨t⟩)` already subtracted
  `2` there and stayed `≥ 0`, so `chainVZ p σ (t-1) (last) ≥ 2 > 1`.

Hence *every* internal facet has a valid partner: internal facets are always interior. -/

/-- **The swapped intermediate vertex, general form.**  For positions `a, b : Fin n` with
`a.val = t.val - 1` and `b.val = t.val` (`0 < t.val`), the drop-`t` vertex of `σ * swap a b`
equals the previous valid vertex `chainVZ p σ ⟨t-1⟩` plus the inserted step `stepVec (σ b)`. -/
theorem chainVZ_swap_drop {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (a b : Fin n) (hav : a.val = t.val - 1)
    (hbv : b.val = t.val) (i : Fin (n + 1)) :
    chainVZ p (σ * Equiv.swap a b) t i
      = chainVZ p σ ⟨t.val - 1, by omega⟩ i + stepVec (σ b) i := by
  classical
  rw [chainVZ_apply, chainVZ_apply]
  -- prefix for `t` is `{s.val < t.val}`; for `t-1` is `{s.val < t.val - 1}`.
  have hSteq : (Finset.univ.filter (fun s : Fin n => s.val < t.val))
      = insert a (Finset.univ.filter (fun s : Fin n => s.val < t.val - 1)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hs
      rcases Nat.lt_or_ge s.val (t.val - 1) with h | h
      · exact Or.inr h
      · left; apply Fin.ext; rw [hav]; omega
    · rintro (rfl | h)
      · rw [hav]; omega
      · omega
  have haSp : a ∉ Finset.univ.filter (fun s : Fin n => s.val < t.val - 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    omega
  rw [hSteq, Finset.sum_insert haSp]
  -- LHS step at `a` is `stepVec ((σ * swap a b) a) i = stepVec (σ b) i`
  have hstepA : stepVec ((σ * Equiv.swap a b) a) i = stepVec (σ b) i := by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
  -- the remaining sum over the `t-1` prefix is unchanged
  have hrest : ∀ s ∈ Finset.univ.filter (fun s : Fin n => s.val < t.val - 1),
      stepVec ((σ * Equiv.swap a b) s) i = stepVec (σ s) i := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have hsa : s ≠ a := by intro h; rw [h, hav] at hs; omega
    have hsb : s ≠ b := by intro h; rw [h, hbv] at hs; omega
    simp only [Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne hsa hsb]
  rw [hstepA, Finset.sum_congr rfl hrest]
  ring

/-- The swapped intermediate vertex equals the previous valid vertex plus one step, packaged
for `swapAround`. -/
theorem swapAround_chainVZ_eq {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) (i : Fin (n + 1)) :
    chainVZ p (swapAround t σ) t i
      = chainVZ p σ ⟨t.val - 1, by omega⟩ i + stepVec (σ ⟨t.val, hlt⟩) i := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩]
  exact chainVZ_swap_drop p σ h0 ⟨t.val - 1, by omega⟩ ⟨t.val, hlt⟩ rfl rfl i

/-- Off the dropped index, the swap partner's chain vertex is unchanged. -/
theorem swapAround_chainVZ_eq_of_ne {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) {u : Fin (n + 1)} (hu : u ≠ t) :
    chainVZ p (swapAround t σ) u = chainVZ p σ u := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩]
  apply chainVZ_swap_eq_of_prefix
  -- prefix `{s.val < u.val}` contains both or neither of `t-1, t`
  have huv : u.val ≠ t.val := fun h => hu (Fin.ext h)
  show ((⟨t.val - 1, by omega⟩ : Fin n).val < u.val) ↔ ((⟨t.val, hlt⟩ : Fin n).val < u.val)
  simp only [Fin.val_mk]
  omega

/-- **Internal validity preservation (the squeeze).**  If `(p, σ)` is valid at mesh `k` and
`t` is an *internal* drop index (`0 < t < n`), then the internal-swap partner `(p, swapAround
t σ)` is also valid at mesh `k`.  Every chain vertex other than the dropped one is unchanged;
the new intermediate vertex `chainVZ p σ ⟨t-1⟩ + stepVec (σ ⟨t⟩)` is squeezed nonnegative by its
two valid neighbours. -/
theorem cellValid_swapAround {n k : ℕ} {p : Fin (n + 1) → ℤ} {σ : Equiv.Perm (Fin n)}
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) (hc : cellValid k p σ) :
    cellValid k p (swapAround t σ) := by
  refine ⟨hc.1, ?_⟩
  intro u i
  by_cases hu : u = t
  · -- the new intermediate vertex
    rw [hu, swapAround_chainVZ_eq p σ h0 hlt i]
    by_cases hi : i = Fin.last n
    · -- last coordinate: use the next valid vertex to bound `chainVZ … (t-1) (last) ≥ 2`
      rw [hi]
      have hstep : stepVec (σ ⟨t.val, hlt⟩) (Fin.last n) = -1 := stepVec_last _
      rw [hstep]
      -- next vertex `t+1` is valid: `chainVZ p σ ⟨t+1⟩ last ≥ 0`
      have hvalid_next : 0 ≤ chainVZ p σ ⟨t.val + 1, by omega⟩ (Fin.last n) :=
        hc.2 ⟨t.val + 1, by omega⟩ (Fin.last n)
      rw [chainVZ_last] at hvalid_next
      have hprev : chainVZ p σ ⟨t.val - 1, by omega⟩ (Fin.last n)
          = p (Fin.last n) - (((t.val - 1 : ℕ) : ℤ)) := by
        rw [chainVZ_last]
      rw [hprev]
      have ht1 : ((t.val + 1 : ℕ) : ℤ) = (t.val : ℤ) + 1 := by push_cast; ring
      have ht2 : ((t.val - 1 : ℕ) : ℤ) = (t.val : ℤ) - 1 := by
        rw [Nat.cast_sub h0]; norm_num
      rw [ht1] at hvalid_next; rw [ht2]
      omega
    · -- non-last coordinate: the step only adds, so dominates the valid previous vertex
      have hstep : 0 ≤ stepVec (σ ⟨t.val, hlt⟩) i := by
        unfold stepVec
        rw [if_neg hi]
        split <;> omega
      have hprev : 0 ≤ chainVZ p σ ⟨t.val - 1, by omega⟩ i := hc.2 ⟨t.val - 1, by omega⟩ i
      linarith
  · -- unchanged vertex
    rw [swapAround_chainVZ_eq_of_ne p σ h0 hlt hu]
    exact hc.2 u i

/-! ## `hinterior` for internal facets (unconditional)

Combining the squeeze (`cellValid_swapAround`) with the partner involution: when every cell
bounding `F` drops it at an *internal* index, the partner of each is valid, so the bounding
count is even — with no further hypothesis.  This is the engine's `hinterior` for the internal
facets of the Kuhn complex. -/

/-- If every valid cell bounding `F` drops it internally, the bounding count is even. -/
theorem hinterior_internal {n : ℕ} (hn : 0 < n) (k : ℕ)
    (cellsK : Finset (KCell n)) (hcellsK : ∀ c, c ∈ cellsK ↔ cellMemN k c)
    (F : Finset (Fin (n + 1) → ℤ))
    (hAllInternal : ∀ c ∈ cellsK, cellBounds c F →
      0 < (dropOf c F).val ∧ (dropOf c F).val < n) :
    Even (cellsK.filter (fun c => cellBounds c F)).card := by
  refine hinterior_kuhn hn k cellsK hcellsK F ?_
  intro c hc hcb
  obtain ⟨h0, hlt⟩ := hAllInternal c hc hcb
  have hcv : cellMemN k c := (hcellsK c).mp hc
  -- the partner is the internal swap; its validity is the squeeze
  rw [partnerCell_of_internal hn c (by omega) (by omega)]
  unfold cellMemN at hcv ⊢
  exact cellValid_swapAround h0 hlt hcv

/-! ## The base case: `n = 0` (the one-point simplex)

`stdSimplex ℝ (Fin 1)` is the single point `![1]`: the unique coordinate is forced to `1` by
`∑ = 1`.  Any self-map fixes it.  This is the `n = 0` base of the dimension induction. -/

/-- On `Δ⁰ = stdSimplex ℝ (Fin 1)` the only point has its unique coordinate equal to `1`. -/
theorem stdSimplex_fin_one_eq {x : Fin 1 → ℝ} (hx : x ∈ stdSimplex ℝ (Fin 1)) :
    x = fun _ => 1 := by
  obtain ⟨_, hsum⟩ := hx
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simpa using hsum

/-- **Brouwer on the `0`-simplex.**  Every self-map of the one-point simplex
`Δ⁰ = stdSimplex ℝ (Fin 1)` has a fixed point (trivially: there is only one point). -/
theorem brouwer_stdSimplex_zero {f : (Fin 1 → ℝ) → (Fin 1 → ℝ)}
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin 1)) (stdSimplex ℝ (Fin 1))) :
    ∃ x ∈ stdSimplex ℝ (Fin 1), f x = x := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · constructor
    · intro i; norm_num
    · simp
  · have hmem : (fun _ => 1 : Fin 1 → ℝ) ∈ stdSimplex ℝ (Fin 1) := by
      constructor
      · intro i; norm_num
      · simp
    have hfmem := hmaps hmem
    rw [stdSimplex_fin_one_eq hfmem]

/-! ## Precise stall report — frontier to the full `brouwer_stdSimplex_n`

**What is fully closed here (axiom-clean: `[propext, Classical.choice, Quot.sound]`, verified
by `#print axioms`).**

* `chainVZ_last`, `stepVec_last`, `chainVZ_injective`, `mem_facetSet_iff`, `card_facetSet` —
  the **last-coordinate backbone**.  Every Kuhn step lowers the last coordinate by exactly `1`
  (`stepVec_last`), so `chainVZ p σ t (last) = p(last) - t.val` (`chainVZ_last`): the `n+1`
  chain vertices carry the *distinct, consecutive* last coordinates `p(last), …, p(last)-n`.
  Hence the chain map is injective (`chainVZ_injective`), a facet has exactly `n` vertices
  (`card_facetSet`), and a vertex lies in a facet iff its index ≠ the drop (`mem_facetSet_iff`).

* `dropIdx_unique`, `dropOf`, `dropOf_eq` — the **drop-index recovery**.  From the unordered
  facet `F` and a bounding cell `c`, the dropped index is the unique chain index whose vertex
  is missing from `F`; `dropOf c F` recovers it, with `dropOf_eq` proving it equals the
  genuine drop when `facetSet c.1 c.2 t = F`.

* `endpointFwd`, `endpointInv`, `endpointInv_fwd`, `endpointFwd_inv`, `endpointFwd_facet`,
  `endpointInv_facet` — the **endpoint base-shift map and its two-sided inverse**, packaged on
  the carrier `KCell n`, with the facet-sharing identities (drop-`0` ↔ drop-`last`) lifted from
  the committed `facetSet_endpoint_eq`.

* `swapAround`, `swapAround_facet`, `swapAround_ne`, `swapAround_involutive` — the **internal
  adjacent-swap partner**, packaged from the committed `facetSet_partner_eq` / `partnerPerm_ne`.

* `partnerCell`, `partnerCell_of_zero/last/internal`, `dropOf_partner`,
  **`partnerCell_involutive`**, **`partnerCell_bounds`**, **`partnerCell_ne`** — the genuine
  **global K2′ involution**.  A *single* map `partnerCell hn c F` unifies BOTH partner types
  (endpoint forward at drop `0`, endpoint inverse at drop `last`, internal swap in between),
  keyed by the recovered drop index `dropOf c F`.  It is proved to (i) bound the same facet
  `F`, (ii) be a *different* cell (fixed-point-free), and (iii) be involutive — the three data
  `even_card_of_involution` consumes.  This is precisely the route-independent "single global
  fixed-point-free involution on the cells bounding an interior facet" the prior stall reports
  flagged as the crux of K2′; it is now CLOSED, with the two endpoint cases interlocking
  through `dropOf_partner` (drop `0` ↦ drop `last` and back).

* **`hinterior_kuhn`** — the engine's `hinterior` for the concrete Kuhn complex, obtained from
  the global involution: the valid cells of `cellsK` bounding a facet `F` come in partner
  pairs, hence even — *modulo* the single geometric input `hPartnerValid` (the partner of a
  valid bounding cell is valid).

* `chainVZ_swap_drop`, `swapAround_chainVZ_eq`, `swapAround_chainVZ_eq_of_ne`,
  **`cellValid_swapAround`** — the **internal squeeze** (internal validity preservation).  The
  internal-swap partner's only new vertex is `chainVZ p σ ⟨t-1⟩ + stepVec (σ ⟨t⟩)`, squeezed
  nonnegative between its two valid neighbours (away from the last coordinate the step only
  adds; at the last coordinate the *next* valid vertex forces `chainVZ p σ ⟨t-1⟩ (last) ≥ 2`).
  Hence **every internal facet is interior** — the partner is automatically valid.

* **`hinterior_internal`** — combining the squeeze with the involution: when every valid cell
  bounding `F` drops it at an *internal* index, the bounding count is even **with no further
  hypothesis**.  This fully discharges `hinterior` for the internal facets of the Kuhn complex.

* `stdSimplex_fin_one_eq`, **`brouwer_stdSimplex_zero`** — the `n = 0` base case of the
  dimension induction (the one-point simplex; every self-map fixes its unique point).

**The remaining frontier (genuinely large from-scratch geometry — NOT bookkeeping).**  Each
brick below was assessed and is a substantial construction, not a one-liner:

  (R1) ENDPOINT BOUNDARY CHARACTERISATION.  For an *endpoint* facet (drop `0`/`last`), the
       partner (`endpointFwd`/`endpointInv`) shifts the base by `±stepVec`, which can push a
       chain vertex coordinate negative — i.e. off the mesh.  Need: the precise predicate
       `isBoundaryN k F :=` "the endpoint partner of a bounding cell is *invalid*", and the
       fact that the endpoint partner is valid ⟺ `F` is not on the geometric `∂Δⁿ`.  Unlike the
       internal squeeze (where the new vertex is *between* two valid ones), the endpoint shift
       has no squeeze: validity genuinely fails at the boundary.  This is the analogue of the
       2-D `isInterior`/`downBoundsEdge` distinction, but the in-mesh test is an `n`-coordinate
       nonnegativity condition on the shifted base.

  (R2) FACET DROP-TYPE UNIFORMITY.  `hinterior_internal` requires *every* valid cell bounding
       `F` to drop it internally.  This holds because the *last-coordinate gap pattern* of `F`
       (whether the missing last coordinate is at the top, bottom, or strictly interior of the
       contiguous run `{max, …, max-n}`) is an invariant of `F` alone, recoverable via
       `chainVZ_last`.  Formalising "F determines the drop type for all its bounding cells" is a
       reconstruction-uniqueness lemma (the converse direction of `dropOf_eq`, across distinct
       cells).  The backbone (`chainVZ_last`, `card_facetSet`) is in place; the uniqueness
       argument over the at-most-two bounding cells remains.

  (R3) BOUNDARY-DOOR COUNT (K3) — the heaviest brick.  `hboundaryCount` reduces by induction on
       `n` to `sperner_(n-1)_dim` on the distinguished face `{q : q(last) = 0}`, whose induced
       subdivision is the `(n-1)`-dimensional Kuhn complex.  This requires *from scratch*: the
       `(n-1)`-Kuhn face complex, its incidence, the relation of its rainbow cells to the n-D
       boundary doors, and the labelling restriction (`spernerLabelN_ne_of_zero` supplies "the
       label avoids the vanishing coordinate").  Base case `n = 1` is the committed
       `sperner_one_dim`.  This is comparable in size to the entire `BrouwerTwoDim.lean`.

  (R4) FINSET ASSEMBLY + MESH LIMIT.  Build the concrete `cells k`/`facets k` Finsets (a finite
       box of valid bases × permutations, with `mem_cells`-analogues), wire `hheart` from the
       committed `hheart_indexed`, then feed `sperner_n_dim_combinatorial` (with (R1)–(R3)) to
       get a rainbow cell at every mesh, and apply the committed `brouwer_of_rainbow_meshes`
       (the K4 engine) — exactly mirroring `exists_rainbow_cell` / `brouwer_stdSimplex_two`.
       The per-colour-vertex extraction and the `2/(m+1)` coordinate bound transport verbatim
       (the chain vertices of one cell differ by one Kuhn step, hence ≤ `1/k` per coordinate);
       the labelling layer (`embPt`, `spernerLabelN`, `spernerLabelN_spec`) is already in
       `BrouwerNDimFinal`.

**Summary.**  The two geometric crux bricks the prior reports flagged — the *global*
fixed-point-free partner involution unifying both partner types (`partnerCell_involutive` +
`partnerCell_bounds` + `partnerCell_ne`), and the *internal validity squeeze*
(`cellValid_swapAround`) that makes every internal facet interior — are DISCHARGED here and
compile axiom-clean, together with the full last-coordinate reconstruction backbone, the
engine-ready `hinterior_internal`, and the `n = 0` base case.  What remains (R1–R4) is the
endpoint/boundary geometry, the drop-type uniqueness, the (n-1)-Sperner boundary induction K3
(the heaviest, ≈ a second 2-D file), and the Finset/mesh-limit assembly — each a genuine
from-scratch construction with no Mathlib shortcut, not finite bookkeeping. -/

end ShenWork.Paper1
