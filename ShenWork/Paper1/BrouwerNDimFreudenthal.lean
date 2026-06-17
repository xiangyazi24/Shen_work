/-
# Boundary-compatible Freudenthal cells

This file builds a parallel, boundary-compatible Freudenthal/type-A cell model.  It is
deliberately independent of the older fixed-donor `chainVZ` model: a `d`-cell is a monotone
Freudenthal simplex in `Fin d` coordinates, indexed by a base point and a permutation of the
`d` coordinate increments.  If the last coordinate increment is last in the permutation, the
drop of the final vertex is a literal bottom-face `(d-1)` Freudenthal cell.

The file closes the model-level facts needed by the R3 rebuild:

* the bottom facet lies in `{last = 0}`;
* projecting that bottom facet by dropping the last coordinate gives exactly the lower
  Freudenthal chain set;
* the upper door condition is equivalent to the lower rainbow-cell condition for the
  projected labelling.

No proof placeholders or extra assumptions.
-/
import ShenWork.Paper1.BrouwerNDimR3

namespace ShenWork.Paper1

open Finset

namespace Freudenthal

/-! ## The monotone Freudenthal chain -/

/-- The unit increment in coordinate `a`. -/
def unitVec {n : ℕ} (a : Fin n) : Fin n → ℤ :=
  fun i => if i = a then 1 else 0

/-- The Freudenthal chain based at `p`, adding coordinate increments in order `σ`. -/
def chainVZ {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    Fin n → ℤ :=
  fun i => p i + if (σ.symm i).val < t.val then 1 else 0

/-- The set of all vertices of a Freudenthal cell. -/
def chainSet {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n → ℤ) :=
  Finset.univ.image (chainVZ p σ)

/-- The facet obtained by dropping vertex `t`. -/
def facetSet {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    Finset (Fin n → ℤ) :=
  (Finset.univ.erase t).image (chainVZ p σ)

/-- A Freudenthal cell carrier: base point plus coordinate-increment order. -/
abbrev Cell (n : ℕ) : Type :=
  (Fin n → ℤ) × Equiv.Perm (Fin n)

/-- Valid cube-mesh cells: every base coordinate lies in `{0, ..., k-1}`. -/
def cellValid {n : ℕ} (k : ℕ) (c : Cell n) : Prop :=
  ∀ i, 0 ≤ c.1 i ∧ c.1 i < (k : ℤ)

instance {n k : ℕ} (c : Cell n) : Decidable (cellValid k c) := by
  unfold cellValid
  infer_instance

/-- Finite set of valid Freudenthal cells at mesh `k`. -/
noncomputable def cells (n k : ℕ) : Finset (Cell n) :=
  (Finset.univ.image
      (fun (pσ : (Fin n → Fin k) × Equiv.Perm (Fin n)) =>
        ((fun i => (pσ.1 i : ℤ)), pσ.2) : _ → Cell n)).filter
    (cellValid k)

/-- Membership in `cells` is exactly `cellValid`. -/
theorem mem_cells {n k : ℕ} {c : Cell n} : c ∈ cells n k ↔ cellValid k c := by
  classical
  unfold cells
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hc
    refine ⟨?_, hc⟩
    rw [Finset.mem_image]
    refine ⟨(fun i => ⟨(c.1 i).toNat, ?_⟩, c.2), Finset.mem_univ _, ?_⟩
    · have hi := hc i
      omega
    · apply Prod.ext
      · funext i
        have hi := hc i
        simp only [Int.toNat_of_nonneg hi.1]
      · rfl

/-- Drop the last coordinate. -/
def dropLast {n : ℕ} (v : Fin (n + 1) → ℤ) : Fin n → ℤ :=
  Fin.init v

@[simp] theorem dropLast_apply {n : ℕ} (v : Fin (n + 1) → ℤ) (i : Fin n) :
    dropLast v i = v i.castSucc := rfl

/-- Append a zero last coordinate. -/
def appendZero {n : ℕ} (v : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.snoc v 0

@[simp] theorem appendZero_last {n : ℕ} (v : Fin n → ℤ) :
    appendZero v (Fin.last n) = 0 := by
  simp [appendZero]

@[simp] theorem appendZero_castSucc {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    appendZero v i.castSucc = v i := by
  simp [appendZero, Fin.snoc_castSucc]

@[simp] theorem dropLast_appendZero {n : ℕ} (v : Fin n → ℤ) :
    dropLast (appendZero v) = v := by
  funext i
  simp [dropLast, appendZero, Fin.init, Fin.snoc_castSucc]

theorem unitVec_dropLast {n : ℕ} {a : Fin (n + 1)} (ha : a ≠ Fin.last n)
    (j : Fin n) : dropLast (unitVec a) j = unitVec (a.castPred ha) j := by
  unfold dropLast unitVec
  change (if j.castSucc = a then (1 : ℤ) else 0)
    = if j = a.castPred ha then (1 : ℤ) else 0
  by_cases h : j.castSucc = a
  · have hpred : a.castPred ha = j := by
      rw [Fin.castPred_eq_iff_eq_castSucc]
      exact h.symm
    rw [if_pos h, if_pos hpred.symm]
  · have hpred : j ≠ a.castPred ha := by
      intro hj
      apply h
      rw [← Fin.castSucc_castPred a ha, hj]
    rw [if_neg h, if_neg hpred]

/-! ## Restricting a permutation fixing the last coordinate -/

/-- Restrict a permutation of `Fin (n+1)` that fixes `last` to the first `n` coordinates. -/
noncomputable def restrictLast {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) : Equiv.Perm (Fin n) :=
  let f : Fin n → Fin n := fun i =>
    (σ i.castSucc).castPred (by
      intro hlast
      have hpre : i.castSucc = Fin.last n := by
        apply σ.injective
        rw [hlast, hσ]
      exact Fin.castSucc_ne_last i hpre)
  Equiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro i j hij
      apply Fin.castSucc_injective
      apply σ.injective
      have hcast := (Fin.castPred_inj).mp hij
      simpa [f] using hcast
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

@[simp] theorem restrictLast_apply {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) (i : Fin n) :
    restrictLast σ hσ i =
      (σ i.castSucc).castPred (by
        intro hlast
        have hpre : i.castSucc = Fin.last n := by
          apply σ.injective
          rw [hlast, hσ]
        exact Fin.castSucc_ne_last i hpre) := by
  simp [restrictLast]

theorem castSucc_restrictLast_apply {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) (i : Fin n) :
    (restrictLast σ hσ i).castSucc = σ i.castSucc := by
  rw [restrictLast_apply]
  exact Fin.castSucc_castPred _ _

theorem castSucc_restrictLast_symm_apply {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) (i : Fin n) :
    ((restrictLast σ hσ).symm i).castSucc = σ.symm i.castSucc := by
  apply σ.injective
  have hleft : σ (((restrictLast σ hσ).symm i).castSucc) = i.castSucc := by
    have h := castSucc_restrictLast_apply σ hσ ((restrictLast σ hσ).symm i)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [hleft, Equiv.apply_symm_apply]

/-- Extend a permutation by fixing the last coordinate. -/
noncomputable def extendLast {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  let f : Fin (n + 1) → Fin (n + 1) := fun i =>
    if h : i = Fin.last n then Fin.last n else (τ (i.castPred h)).castSucc
  Equiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro i j hij
      by_cases hi : i = Fin.last n
      · subst hi
        by_cases hj : j = Fin.last n
        · subst hj
          rfl
        · exfalso
          have hval := congrArg Fin.val hij
          simp [f, hj] at hval
          have hlt := (τ (j.castPred hj)).isLt
          omega
      · by_cases hj : j = Fin.last n
        · subst hj
          exfalso
          have hval := congrArg Fin.val hij
          simp [f, hi] at hval
          have hlt := (τ (i.castPred hi)).isLt
          omega
        · have hcast : (τ (i.castPred hi)).castSucc
              = (τ (j.castPred hj)).castSucc := by
            simpa [f, hi, hj] using hij
          have hτ : τ (i.castPred hi) = τ (j.castPred hj) :=
            Fin.castSucc_injective _ hcast
          have hpred : i.castPred hi = j.castPred hj := τ.injective hτ
          exact (Fin.castPred_inj.mp hpred)
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

@[simp] theorem extendLast_apply_last {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    extendLast τ (Fin.last n) = Fin.last n := by
  simp [extendLast]

@[simp] theorem extendLast_apply_castSucc {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLast τ i.castSucc = (τ i).castSucc := by
  have hne : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
  simp [extendLast, hne]

@[simp] theorem restrictLast_extendLast {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    restrictLast (extendLast τ) (extendLast_apply_last τ) = τ := by
  apply Equiv.ext
  intro i
  apply Fin.castSucc_injective
  rw [castSucc_restrictLast_apply, extendLast_apply_castSucc]

@[simp] theorem extendLast_restrictLast {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) :
    extendLast (restrictLast σ hσ) = σ := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ ?_ i
  · rw [extendLast_apply_last, hσ]
  · intro j
    rw [extendLast_apply_castSucc, castSucc_restrictLast_apply]

/-- The projected cell obtained by dropping the last coordinate. -/
noncomputable def restrictCell {n : ℕ} (c : Cell (n + 1))
    (hσ : c.2 (Fin.last n) = Fin.last n) : Cell n :=
  (dropLast c.1, restrictLast c.2 hσ)

/-- Extend a lower-dimensional cell into the bottom face. -/
noncomputable def extendCell {n : ℕ} (c : Cell n) : Cell (n + 1) :=
  (appendZero c.1, extendLast c.2)

@[simp] theorem restrictCell_extendCell {n : ℕ} (c : Cell n) :
    restrictCell (extendCell c) (extendLast_apply_last c.2) = c := by
  apply Prod.ext
  · exact dropLast_appendZero c.1
  · exact restrictLast_extendLast c.2

/-- Validity is preserved by dropping a fixed last coordinate. -/
theorem restrictCell_valid {n k : ℕ} {c : Cell (n + 1)}
    (hσ : c.2 (Fin.last n) = Fin.last n) (hc : cellValid k c) :
    cellValid k (restrictCell c hσ) := by
  intro i
  exact hc i.castSucc

/-- Extending into the bottom face preserves validity for positive mesh size. -/
theorem extendCell_valid {n k : ℕ} (hk : 0 < k) {c : Cell n}
    (hc : cellValid k c) : cellValid k (extendCell c) := by
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp [extendCell, hk]
  · intro j
    simpa [extendCell] using hc j

theorem extendCell_injective {n : ℕ} : Function.Injective (extendCell (n := n)) := by
  intro c d hcd
  apply Prod.ext
  · funext i
    have hp := congrArg Prod.fst hcd
    have hcoord := congrFun hp i.castSucc
    simpa [extendCell] using hcoord
  · apply Equiv.ext
    intro i
    apply Fin.castSucc_injective
    have hσ := congrArg Prod.snd hcd
    have hcoord := congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e i.castSucc) hσ
    simpa [extendCell] using hcoord

/-- A bottom-face cell has zero last base coordinate and fixes the last increment last. -/
def isBottomCell {n : ℕ} (c : Cell (n + 1)) : Prop :=
  c.1 (Fin.last n) = 0 ∧ c.2 (Fin.last n) = Fin.last n

instance {n : ℕ} (c : Cell (n + 1)) : Decidable (isBottomCell c) := by
  unfold isBottomCell
  infer_instance

/-- Valid Freudenthal cells whose final facet lies on the bottom face. -/
noncomputable def bottomCells (n k : ℕ) : Finset (Cell (n + 1)) :=
  (cells (n + 1) k).filter isBottomCell

theorem extendCell_mem_bottomCells {n k : ℕ} (hk : 0 < k) {c : Cell n}
    (hc : c ∈ cells n k) : extendCell c ∈ bottomCells n k := by
  rw [bottomCells, Finset.mem_filter]
  refine ⟨mem_cells.mpr (extendCell_valid hk (mem_cells.mp hc)), ?_⟩
  exact ⟨appendZero_last c.1, extendLast_apply_last c.2⟩

theorem restrictCell_mem_cells_of_bottom {n k : ℕ} {c : Cell (n + 1)}
    (hc : c ∈ bottomCells n k) {hσ : c.2 (Fin.last n) = Fin.last n} :
    restrictCell c hσ ∈ cells n k := by
  have hcb := hc
  rw [bottomCells, Finset.mem_filter] at hcb
  exact mem_cells.mpr (restrictCell_valid hσ (mem_cells.mp hcb.1))

theorem extendCell_restrictCell {n : ℕ} {c : Cell (n + 1)}
    (hp : c.1 (Fin.last n) = 0) (hσ : c.2 (Fin.last n) = Fin.last n) :
    extendCell (restrictCell c hσ) = c := by
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simpa [extendCell, restrictCell] using hp.symm
    · intro j
      simp [extendCell, restrictCell]
  · simp [extendCell, restrictCell]

theorem bottomCells_eq_image_extend {n k : ℕ} (hk : 0 < k) :
    bottomCells n k = (cells n k).image (extendCell (n := n)) := by
  classical
  ext c
  constructor
  · intro hc
    have hcb := hc
    rw [bottomCells, Finset.mem_filter] at hcb
    obtain ⟨hp, hσ⟩ := hcb.2
    refine Finset.mem_image.mpr ?_
    refine ⟨restrictCell c hσ, restrictCell_mem_cells_of_bottom hc, ?_⟩
    exact extendCell_restrictCell hp hσ
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact extendCell_mem_bottomCells hk hd

theorem card_bottomCells {n k : ℕ} (hk : 0 < k) :
    (bottomCells n k).card = (cells n k).card := by
  rw [bottomCells_eq_image_extend hk]
  exact Finset.card_image_of_injective _ extendCell_injective

theorem dropLast_chain_castSucc {n : ℕ} (p : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ (Fin.last n) = Fin.last n)
    (t : Fin (n + 1)) :
    dropLast (chainVZ p σ t.castSucc) = chainVZ (dropLast p) (restrictLast σ hσ) t := by
  funext j
  change p j.castSucc + (if (σ.symm j.castSucc).val < t.val then (1 : ℤ) else 0)
    = dropLast p j + if (((restrictLast σ hσ).symm j).val : ℕ) < t.val then 1 else 0
  have hval : (((restrictLast σ hσ).symm j).val : ℕ)
      = (σ.symm j.castSucc).val := by
    have h := congrArg Fin.val (castSucc_restrictLast_symm_apply σ hσ j)
    simpa only [Fin.val_castSucc] using h
  rw [dropLast_apply, hval]

/-! ## The bottom facet is the lower Freudenthal complex -/

theorem symm_last_of_apply_last {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    (hσ : σ (Fin.last n) = Fin.last n) :
    σ.symm (Fin.last n) = Fin.last n := by
  apply σ.injective
  rw [Equiv.apply_symm_apply, hσ]

/-- If the last coordinate increment is last, all non-final vertices stay on the bottom face. -/
theorem chain_last_eq_zero_of_ne_final {n : ℕ} {p : Fin (n + 1) → ℤ}
    {σ : Equiv.Perm (Fin (n + 1))} (hp : p (Fin.last n) = 0)
    (hσ : σ (Fin.last n) = Fin.last n) {t : Fin (n + 2)}
    (ht : t ≠ Fin.last (n + 1)) :
    chainVZ p σ t (Fin.last n) = 0 := by
  unfold chainVZ
  have hsymm := symm_last_of_apply_last hσ
  have htval : t.val ≤ n := by
    have : t.val ≠ n + 1 := by
      intro h
      exact ht (Fin.ext (by simpa [Fin.val_last] using h))
    omega
  rw [hp, hsymm]
  have hnot : ¬ (Fin.last n).val < t.val := by
    simp only [Fin.val_last]
    omega
  rw [if_neg hnot]
  norm_num

/-- Every vertex of the bottom facet lies in the literal bottom face `{last = 0}`. -/
theorem bottomFacet_last_zero {n : ℕ} {p : Fin (n + 1) → ℤ}
    {σ : Equiv.Perm (Fin (n + 1))} (hp : p (Fin.last n) = 0)
    (hσ : σ (Fin.last n) = Fin.last n) {v : Fin (n + 1) → ℤ}
    (hv : v ∈ facetSet p σ (Fin.last (n + 1))) :
    v (Fin.last n) = 0 := by
  unfold facetSet at hv
  rw [Finset.mem_image] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  rw [Finset.mem_erase] at ht
  exact chain_last_eq_zero_of_ne_final hp hσ ht.1

/-- Projecting the bottom facet gives exactly the lower-dimensional Freudenthal chain set. -/
theorem image_dropLast_bottomFacet {n : ℕ} (p : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ (Fin.last n) = Fin.last n) :
    (facetSet p σ (Fin.last (n + 1))).image dropLast
      = chainSet (dropLast p) (restrictLast σ hσ) := by
  classical
  ext v
  constructor
  · intro hv
    rw [Finset.mem_image] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    unfold facetSet at hx
    rw [Finset.mem_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [Finset.mem_erase] at ht
    refine Finset.mem_image.mpr ?_
    refine ⟨t.castPred ht.1, Finset.mem_univ _, ?_⟩
    rw [← dropLast_chain_castSucc p σ hσ]
    rw [Fin.castSucc_castPred t ht.1]
  · intro hv
    unfold chainSet at hv
    rw [Finset.mem_image] at hv
    obtain ⟨t, _ht, rfl⟩ := hv
    refine Finset.mem_image.mpr ?_
    refine ⟨chainVZ p σ t.castSucc, ?_, ?_⟩
    · unfold facetSet
      rw [Finset.mem_image]
      refine ⟨t.castSucc, ?_, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨Fin.castSucc_ne_last t, Finset.mem_univ _⟩
    · exact dropLast_chain_castSucc p σ hσ t

/-- Packaged bottom-face restriction for valid Freudenthal cells. -/
theorem valid_bottomFacet_projects {n k : ℕ} {c : Cell (n + 1)}
    (hc : cellValid k c) (hp : c.1 (Fin.last n) = 0)
    (hσ : c.2 (Fin.last n) = Fin.last n) :
    cellValid k (restrictCell c hσ) ∧
      (∀ v ∈ facetSet c.1 c.2 (Fin.last (n + 1)), v (Fin.last n) = 0) ∧
      (facetSet c.1 c.2 (Fin.last (n + 1))).image dropLast
        = chainSet (restrictCell c hσ).1 (restrictCell c hσ).2 := by
  refine ⟨restrictCell_valid hσ hc, ?_, ?_⟩
  · intro v hv
    exact bottomFacet_last_zero hp hσ hv
  · exact image_dropLast_bottomFacet c.1 c.2 hσ

/-- Extending a lower cell embeds its lower chain as the non-final upper chain. -/
theorem chain_extend_castSucc {n : ℕ} (c : Cell n) (t : Fin (n + 1)) :
    chainVZ (extendCell c).1 (extendCell c).2 t.castSucc
      = appendZero (chainVZ c.1 c.2 t) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [appendZero_last]
    exact chain_last_eq_zero_of_ne_final (appendZero_last c.1)
      (extendLast_apply_last c.2) (Fin.castSucc_ne_last t)
  · intro j
    have h := congrFun
      (dropLast_chain_castSucc (extendCell c).1 (extendCell c).2
        (extendLast_apply_last c.2) t) j
    simpa [extendCell] using h

/-- The bottom facet of an extended cell projects to the original lower chain set. -/
theorem image_dropLast_extendCell_bottomFacet {n : ℕ} (c : Cell n) :
    (facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1))).image dropLast
      = chainSet c.1 c.2 := by
  simpa [extendCell] using
    image_dropLast_bottomFacet (appendZero c.1) (extendLast c.2)
      (extendLast_apply_last c.2)

/-! ## Door on the upper bottom facet equals rainbow on the lower cell -/

/-- The lower colour carried by a bottom-facet vertex whose upper colour avoids `last`. -/
noncomputable def bottomFaceColor {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2)) (p : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (havoid : ∀ t : Fin (n + 1), L (chainVZ p σ t.castSucc) ≠ Fin.last (n + 1)) :
    Fin (n + 1) → Fin (n + 1) :=
  fun t => (L (chainVZ p σ t.castSucc)).castPred (havoid t)

/-- Cell colours induced by a labelling of Freudenthal vertices. -/
noncomputable def cellColor {n : ℕ} (L : (Fin n → ℤ) → Fin (n + 1)) (c : Cell n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun t => L (chainVZ c.1 c.2 t)

/-- The labelling induced on the bottom face by deleting the forbidden top colour. -/
noncomputable def bottomLabel {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1)) :
    (Fin n → ℤ) → Fin (n + 1) :=
  fun v => (L (appendZero v)).castPred (havoid v)

theorem bottomLabel_castSucc {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (v : Fin n → ℤ) :
    (bottomLabel L havoid v).castSucc = L (appendZero v) := by
  unfold bottomLabel
  exact Fin.castSucc_castPred _ _

/-- On an extended bottom cell, the upper bottom-face colour is the induced lower colour. -/
theorem bottomFaceColor_extend_eq {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (c : Cell n)
    (hchain : ∀ t : Fin (n + 1),
      L (chainVZ (extendCell c).1 (extendCell c).2 t.castSucc) ≠ Fin.last (n + 1)) :
    bottomFaceColor L (extendCell c).1 (extendCell c).2 hchain
      = cellColor (bottomLabel L havoid) c := by
  funext t
  apply Fin.castSucc_injective
  unfold bottomFaceColor cellColor
  rw [Fin.castSucc_castPred, bottomLabel_castSucc, chain_extend_castSucc]

theorem bottomFaceColor_surjective_of_door {n : ℕ}
    {L : (Fin (n + 1) → ℤ) → Fin (n + 2)} {p : Fin (n + 1) → ℤ}
    {σ : Equiv.Perm (Fin (n + 1))}
    (havoid : ∀ t : Fin (n + 1), L (chainVZ p σ t.castSucc) ≠ Fin.last (n + 1))
    (hdoor :
      (facetSet p σ (Fin.last (n + 1))).image L =
        Finset.univ.erase (Fin.last (n + 1))) :
    Function.Surjective (bottomFaceColor L p σ havoid) := by
  intro c
  have hc : c.castSucc ∈ Finset.univ.erase (Fin.last (n + 1)) := by
    rw [Finset.mem_erase]
    exact ⟨Fin.castSucc_ne_last c, Finset.mem_univ _⟩
  rw [← hdoor] at hc
  rw [Finset.mem_image] at hc
  obtain ⟨v, hvF, hvL⟩ := hc
  unfold facetSet at hvF
  rw [Finset.mem_image] at hvF
  obtain ⟨t, ht, htchain⟩ := hvF
  rw [Finset.mem_erase] at ht
  refine ⟨t.castPred ht.1, ?_⟩
  unfold bottomFaceColor
  have htcast : (t.castPred ht.1).castSucc = t := Fin.castSucc_castPred t ht.1
  change (L (chainVZ p σ (t.castPred ht.1).castSucc)).castPred _ = c
  rw [Fin.castPred_eq_iff_eq_castSucc]
  rw [htcast, htchain, hvL]

theorem bottomFaceColor_bijective_of_door {n : ℕ}
    {L : (Fin (n + 1) → ℤ) → Fin (n + 2)} {p : Fin (n + 1) → ℤ}
    {σ : Equiv.Perm (Fin (n + 1))}
    (havoid : ∀ t : Fin (n + 1), L (chainVZ p σ t.castSucc) ≠ Fin.last (n + 1))
    (hdoor :
      (facetSet p σ (Fin.last (n + 1))).image L =
        Finset.univ.erase (Fin.last (n + 1))) :
    Function.Bijective (bottomFaceColor L p σ havoid) := by
  have hsurj := bottomFaceColor_surjective_of_door (L := L) (p := p) (σ := σ) havoid hdoor
  exact ⟨Function.Surjective.injective_of_finite (Equiv.refl _) hsurj, hsurj⟩

theorem door_of_bottomFaceColor_surjective {n : ℕ}
    {L : (Fin (n + 1) → ℤ) → Fin (n + 2)} {p : Fin (n + 1) → ℤ}
    {σ : Equiv.Perm (Fin (n + 1))}
    (havoid : ∀ t : Fin (n + 1), L (chainVZ p σ t.castSucc) ≠ Fin.last (n + 1))
    (hsurj : Function.Surjective (bottomFaceColor L p σ havoid)) :
    (facetSet p σ (Fin.last (n + 1))).image L =
      Finset.univ.erase (Fin.last (n + 1)) := by
  classical
  ext c
  constructor
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨v, hvF, hvL⟩ := hc
    unfold facetSet at hvF
    rw [Finset.mem_image] at hvF
    obtain ⟨t, ht, htchain⟩ := hvF
    rw [Finset.mem_erase] at ht
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [← hvL, ← htchain]
    have htcast : (t.castPred ht.1).castSucc = t := Fin.castSucc_castPred t ht.1
    rw [← htcast]
    exact havoid (t.castPred ht.1)
  · intro hc
    rw [Finset.mem_erase] at hc
    obtain ⟨hne, _⟩ := hc
    obtain ⟨t, ht⟩ := hsurj (c.castPred hne)
    refine Finset.mem_image.mpr ?_
    refine ⟨chainVZ p σ t.castSucc, ?_, ?_⟩
    · unfold facetSet
      rw [Finset.mem_image]
      refine ⟨t.castSucc, ?_, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨Fin.castSucc_ne_last t, Finset.mem_univ _⟩
    · unfold bottomFaceColor at ht
      have hcast : (L (chainVZ p σ t.castSucc)).castPred (havoid t) = c.castPred hne := ht
      exact Fin.castPred_inj.mp hcast

/-- A bottom-facet door is equivalent to a rainbow lower Freudenthal cell. -/
theorem door_iff_bottomFaceColor_bijective {n : ℕ}
    {L : (Fin (n + 1) → ℤ) → Fin (n + 2)} {p : Fin (n + 1) → ℤ}
    {σ : Equiv.Perm (Fin (n + 1))}
    (havoid : ∀ t : Fin (n + 1), L (chainVZ p σ t.castSucc) ≠ Fin.last (n + 1)) :
    (facetSet p σ (Fin.last (n + 1))).image L =
        Finset.univ.erase (Fin.last (n + 1))
      ↔ Function.Bijective (bottomFaceColor L p σ havoid) := by
  constructor
  · exact bottomFaceColor_bijective_of_door havoid
  · intro hbij
    exact door_of_bottomFaceColor_surjective havoid hbij.2

/-- Door condition on an extended bottom facet equals rainbow in the induced lower labelling. -/
theorem door_iff_extendCell_rainbow {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (c : Cell n) :
    (facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1))).image L =
        Finset.univ.erase (Fin.last (n + 1))
      ↔ Function.Bijective (cellColor (bottomLabel L havoid) c) := by
  let hchain : ∀ t : Fin (n + 1),
      L (chainVZ (extendCell c).1 (extendCell c).2 t.castSucc) ≠ Fin.last (n + 1) := by
    intro t
    rw [chain_extend_castSucc]
    exact havoid (chainVZ c.1 c.2 t)
  rw [door_iff_bottomFaceColor_bijective hchain]
  rw [bottomFaceColor_extend_eq L havoid c hchain]

/-- A bottom-compatible upper cell has a door on its final facet. -/
def isBottomDoor {n : ℕ} (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (c : Cell (n + 1)) : Prop :=
  (facetSet c.1 c.2 (Fin.last (n + 1))).image L =
    Finset.univ.erase (Fin.last (n + 1))

instance {n : ℕ} (L : (Fin (n + 1) → ℤ) → Fin (n + 2)) (c : Cell (n + 1)) :
    Decidable (isBottomDoor L c) := by
  unfold isBottomDoor
  infer_instance

/-- A lower Freudenthal cell is rainbow under `L`. -/
def isRainbow {n : ℕ} (L : (Fin n → ℤ) → Fin (n + 1)) (c : Cell n) : Prop :=
  Function.Bijective (cellColor L c)

noncomputable instance {n : ℕ} (L : (Fin n → ℤ) → Fin (n + 1)) (c : Cell n) :
    Decidable (isRainbow L c) :=
  Classical.propDecidable _

/-- Bottom-door count equals lower rainbow-cell count under the induced bottom labelling. -/
theorem card_bottomDoors_eq_rainbow {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1)) :
    ((bottomCells n k).filter (fun c => isBottomDoor L c)).card =
      ((cells n k).filter (fun c => isRainbow (bottomLabel L havoid) c)).card := by
  classical
  rw [bottomCells_eq_image_extend hk]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ extendCell_injective]
  congr 1
  apply Finset.filter_congr
  intro c _hc
  unfold isBottomDoor isRainbow
  exact door_iff_extendCell_rainbow L havoid c

/-! ## Global facets and partner cells -/

theorem chainVZ_injective {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (chainVZ p σ) := by
  intro t u htu
  by_contra hne
  have hval : t.val ≠ u.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · have htn : t.val < n := by
      have := u.isLt
      omega
    let a : Fin n := ⟨t.val, htn⟩
    have htcoord : chainVZ p σ t (σ a) = p (σ a) := by
      unfold chainVZ
      have hnot : ¬ (σ.symm (σ a)).val < t.val := by
        rw [Equiv.symm_apply_apply]
        change ¬ t.val < t.val
        omega
      rw [if_neg hnot]
      ring
    have hucoord : chainVZ p σ u (σ a) = p (σ a) + 1 := by
      unfold chainVZ
      have hyes : (σ.symm (σ a)).val < u.val := by
        rw [Equiv.symm_apply_apply]
        exact hlt
      rw [if_pos hyes]
    have hcoord := congrFun htu (σ a)
    rw [htcoord, hucoord] at hcoord
    omega
  · have hun : u.val < n := by
      have := t.isLt
      omega
    let a : Fin n := ⟨u.val, hun⟩
    have hucoord : chainVZ p σ u (σ a) = p (σ a) := by
      unfold chainVZ
      have hnot : ¬ (σ.symm (σ a)).val < u.val := by
        rw [Equiv.symm_apply_apply]
        change ¬ u.val < u.val
        omega
      rw [if_neg hnot]
      ring
    have htcoord : chainVZ p σ t (σ a) = p (σ a) + 1 := by
      unfold chainVZ
      have hyes : (σ.symm (σ a)).val < t.val := by
        rw [Equiv.symm_apply_apply]
        exact hgt
      rw [if_pos hyes]
    have hcoord := congrFun htu (σ a)
    rw [htcoord, hucoord] at hcoord
    omega

theorem mem_facetSet_iff {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (t u : Fin (n + 1)) : chainVZ p σ u ∈ facetSet p σ t ↔ u ≠ t := by
  unfold facetSet
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨w, hwt, hw⟩
    have : u = w := (chainVZ_injective p σ hw).symm
    rw [this]
    exact hwt
  · intro hut
    exact ⟨u, hut, rfl⟩

theorem facetSet_drop_notMem {n : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    chainVZ p σ t ∉ facetSet p σ t := by
  rw [mem_facetSet_iff]
  simp

theorem facetSet_injective {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (facetSet p σ) := by
  intro t u htu
  by_contra hne
  have htmem : chainVZ p σ t ∈ facetSet p σ u :=
    (mem_facetSet_iff p σ u t).mpr hne
  rw [← htu] at htmem
  exact facetSet_drop_notMem p σ t htmem

theorem card_facetSet {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) : (facetSet p σ t).card = n := by
  unfold facetSet
  rw [Finset.card_image_of_injective _ (chainVZ_injective p σ),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

@[simp] theorem chainVZ_zero {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    chainVZ p σ 0 = p := by
  funext i
  unfold chainVZ
  have hnot : ¬ (σ.symm i).val < (0 : Fin (n + 1)).val := by simp
  rw [if_neg hnot]
  ring

theorem base_le_chainVZ {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) (i : Fin n) :
    p i ≤ chainVZ p σ t i := by
  unfold chainVZ
  by_cases h : (σ.symm i).val < t.val
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

theorem chain_indicator_iff_of_eq {n : ℕ} {p : Fin n → ℤ}
    {σ τ : Equiv.Perm (Fin n)} {t : Fin (n + 1)}
    (h : chainVZ p σ t = chainVZ p τ t) (i : Fin n) :
    (σ.symm i).val < t.val ↔ (τ.symm i).val < t.val := by
  have hi := congrFun h i
  unfold chainVZ at hi
  constructor
  · intro hs
    rw [if_pos hs] at hi
    by_contra ht
    rw [if_neg ht] at hi
    omega
  · intro ht
    rw [if_pos ht] at hi
    by_contra hs
    rw [if_neg hs] at hi
    omega

theorem sum_chainVZ {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) :
    (∑ i, chainVZ p σ t i) = (∑ i, p i) + (t.val : ℤ) := by
  classical
  unfold chainVZ
  rw [Finset.sum_add_distrib]
  congr 1
  have htarget :
      (Finset.univ.filter (fun i : Fin n => (σ.symm i).val < t.val))
        = (Finset.univ.filter (fun s : Fin n => s.val < t.val)).image σ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨σ.symm i, hi, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
  have hprefix : (Finset.univ.filter (fun s : Fin n => s.val < t.val)).card = t.val := by
    have ht : t.val ≤ n := by omega
    have heq : (Finset.univ.filter (fun s : Fin n => s.val < t.val))
        = (Finset.univ.filter (fun s : Fin n => s < t.val)) := by
      apply Finset.filter_congr
      intro s _
      rfl
    rw [heq, Fin.card_filter_val_lt]
    omega
  have hcard : (Finset.univ.filter
      (fun i : Fin n => (σ.symm i).val < t.val)).card = t.val := by
    rw [htarget, Finset.card_image_of_injective _ σ.injective, hprefix]
  calc
    (∑ i : Fin n, if (σ.symm i).val < t.val then (1 : ℤ) else 0)
        = ((Finset.univ.filter
            (fun i : Fin n => (σ.symm i).val < t.val)).card : ℤ) := by
          rw [Finset.sum_boole]
    _ = (t.val : ℤ) := by rw [hcard]

theorem base_eq_of_chainSet_eq {n : ℕ} {p q : Fin n → ℤ}
    {σ τ : Equiv.Perm (Fin n)} (h : chainSet p σ = chainSet q τ) : p = q := by
  classical
  have hp_mem : p ∈ chainSet p σ := by
    unfold chainSet
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, by simp⟩
  have hq_mem : q ∈ chainSet q τ := by
    unfold chainSet
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, by simp⟩
  have hp_in_q : p ∈ chainSet q τ := by simpa [h] using hp_mem
  have hq_in_p : q ∈ chainSet p σ := by simpa [h] using hq_mem
  unfold chainSet at hp_in_q hq_in_p
  rw [Finset.mem_image] at hp_in_q hq_in_p
  obtain ⟨t, _ht, ht⟩ := hp_in_q
  obtain ⟨u, _hu, hu⟩ := hq_in_p
  funext i
  have hqle : q i ≤ p i := by
    rw [← ht]
    exact base_le_chainVZ q τ t i
  have hple : p i ≤ q i := by
    rw [← hu]
    exact base_le_chainVZ p σ u i
  omega

theorem chainSet_injective {n : ℕ} :
    Function.Injective (fun c : Cell n => chainSet c.1 c.2) := by
  classical
  intro c d hcd
  rcases c with ⟨p, σ⟩
  rcases d with ⟨q, τ⟩
  have hpq : p = q := base_eq_of_chainSet_eq hcd
  subst q
  have hvertex : ∀ t : Fin (n + 1), chainVZ p σ t = chainVZ p τ t := by
    intro t
    have hmem : chainVZ p σ t ∈ chainSet p τ := by
      have : chainVZ p σ t ∈ chainSet p σ := by
        unfold chainSet
        rw [Finset.mem_image]
        exact ⟨t, Finset.mem_univ _, rfl⟩
      simpa [hcd] using this
    unfold chainSet at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨u, _hu, hu⟩ := hmem
    have hsum := congrArg (fun v : Fin n → ℤ => ∑ i, v i) hu
    change (∑ i, chainVZ p τ u i) = (∑ i, chainVZ p σ t i) at hsum
    rw [sum_chainVZ, sum_chainVZ] at hsum
    have huv : u = t := Fin.ext (by omega)
    rw [huv] at hu
    exact hu.symm
  have hperm : σ = τ := by
    apply Equiv.ext
    intro a
    have h0 : chainVZ p σ ⟨a.val, by omega⟩ =
        chainVZ p τ ⟨a.val, by omega⟩ := hvertex ⟨a.val, by omega⟩
    have h1 : chainVZ p σ ⟨a.val + 1, by omega⟩ =
        chainVZ p τ ⟨a.val + 1, by omega⟩ := hvertex ⟨a.val + 1, by omega⟩
    have hlt1 : (τ.symm (σ a)).val < a.val + 1 := by
      have hiff := chain_indicator_iff_of_eq h1 (σ a)
      have hs : (σ.symm (σ a)).val < (⟨a.val + 1, by omega⟩ : Fin (n + 1)).val := by
        rw [Equiv.symm_apply_apply]
        simp
      exact hiff.mp hs
    have hnlt0 : ¬ (τ.symm (σ a)).val < a.val := by
      have hiff := chain_indicator_iff_of_eq h0 (σ a)
      have hs : ¬ (σ.symm (σ a)).val < (⟨a.val, by omega⟩ : Fin (n + 1)).val := by
        rw [Equiv.symm_apply_apply]
        simp
      intro ht
      exact hs (hiff.mpr ht)
    have hpre : τ.symm (σ a) = a := Fin.ext (by omega)
    have happ := congrArg τ hpre
    simpa using happ
  subst τ
  rfl

/-- A cell bounds a facet if one of its dropped-vertex facets is that facet. -/
def cellBounds {n : ℕ} (c : Cell n) (F : Finset (Fin n → ℤ)) : Prop :=
  ∃ t : Fin (n + 1), facetSet c.1 c.2 t = F

instance {n : ℕ} (c : Cell n) (F : Finset (Fin n → ℤ)) :
    Decidable (cellBounds c F) := by
  unfold cellBounds
  infer_instance

/-- All facets appearing in valid Freudenthal cells at mesh `k`. -/
noncomputable def facets (n k : ℕ) : Finset (Finset (Fin n → ℤ)) :=
  ((cells n k).product Finset.univ).image
    (fun ct : Cell n × Fin (n + 1) => facetSet ct.1.1 ct.1.2 ct.2)

theorem mem_facets_of_bounds {n k : ℕ} {c : Cell n} {F : Finset (Fin n → ℤ)}
    (hc : c ∈ cells n k) (hb : cellBounds c F) : F ∈ facets n k := by
  classical
  obtain ⟨t, rfl⟩ := hb
  unfold facets
  rw [Finset.mem_image]
  exact ⟨(c, t), Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩, rfl⟩

theorem mem_facets_iff {n k : ℕ} {F : Finset (Fin n → ℤ)} :
    F ∈ facets n k ↔ ∃ c ∈ cells n k, cellBounds c F := by
  classical
  constructor
  · intro hF
    unfold facets at hF
    rw [Finset.mem_image] at hF
    obtain ⟨ct, hct, hF⟩ := hF
    have hctp := Finset.mem_product.mp hct
    refine ⟨ct.1, hctp.1, ct.2, hF⟩
  · rintro ⟨c, hc, hb⟩
    exact mem_facets_of_bounds hc hb

/-- The colour set on a fixed cell facet is the corresponding indexed facet colour set. -/
theorem image_facetSet_eq {n : ℕ} (L : (Fin n → ℤ) → Fin (n + 1))
    (c : Cell n) (t : Fin (n + 1)) :
    (facetSet c.1 c.2 t).image L = facetColors (cellColor L c) t := by
  classical
  unfold facetSet facetColors cellColor
  rw [Finset.image_image]
  rfl

theorem facetSet_isDoor_iff {n : ℕ} (L : (Fin n → ℤ) → Fin (n + 1))
    (c : Cell n) (t : Fin (n + 1)) :
    (facetSet c.1 c.2 t).image L = Finset.univ.erase (Fin.last n)
      ↔ doorAt (cellColor L c) t := by
  rw [image_facetSet_eq]
  rfl

/-- The drop facets of a fixed Freudenthal cell. -/
noncomputable def cellFacets {n : ℕ} (c : Cell n) :
    Finset (Finset (Fin n → ℤ)) :=
  (Finset.univ : Finset (Fin (n + 1))).image (facetSet c.1 c.2)

theorem mem_cellFacets_iff {n : ℕ} (c : Cell n) (F : Finset (Fin n → ℤ)) :
    F ∈ cellFacets c ↔ cellBounds c F := by
  unfold cellFacets cellBounds
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Finset.mem_univ _, ht⟩

theorem doorFacets_filter_eq {n k : ℕ} {L : (Fin n → ℤ) → Fin (n + 1)}
    {c : Cell n} (hc : c ∈ cells n k) :
    (facets n k).filter
        (fun F => cellBounds c F ∧ F.image L = Finset.univ.erase (Fin.last n))
      = (cellFacets c).filter (fun F => F.image L = Finset.univ.erase (Fin.last n)) := by
  classical
  ext F
  simp only [Finset.mem_filter, mem_cellFacets_iff]
  constructor
  · rintro ⟨_, hb, hd⟩
    exact ⟨hb, hd⟩
  · rintro ⟨hb, hd⟩
    exact ⟨mem_facets_of_bounds hc hb, hb, hd⟩

theorem hheart {n k : ℕ} {L : (Fin n → ℤ) → Fin (n + 1)} {c : Cell n}
    (hc : c ∈ cells n k) :
    Odd ((facets n k).filter
        (fun F => cellBounds c F ∧ F.image L = Finset.univ.erase (Fin.last n))).card
      ↔ isRainbow L c := by
  classical
  unfold isRainbow
  rw [doorFacets_filter_eq hc, ← hheart_indexed (cellColor L c)]
  have hcard : ((cellFacets c).filter
        (fun F => F.image L = Finset.univ.erase (Fin.last n))).card
      = (Finset.univ.filter (fun t : Fin (n + 1) => doorAt (cellColor L c) t)).card := by
    unfold cellFacets
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ (facetSet_injective c.1 c.2)]
    congr 1
    apply Finset.filter_congr
    intro t _
    rw [facetSet_isDoor_iff]
  rw [hcard]

/-- The unique dropped index recovered from a bounding cell and a facet. -/
noncomputable def dropOf {n : ℕ} (c : Cell n) (F : Finset (Fin n → ℤ)) :
    Fin (n + 1) :=
  if h : ∃ t : Fin (n + 1), chainVZ c.1 c.2 t ∉ F then h.choose else 0

theorem dropIdx_unique {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    {t u : Fin (n + 1)} (hu : chainVZ p σ u ∉ facetSet p σ t) : u = t := by
  by_contra hne
  exact hu ((mem_facetSet_iff p σ t u).mpr hne)

theorem dropOf_eq {n : ℕ} (c : Cell n) {F : Finset (Fin n → ℤ)}
    {t : Fin (n + 1)} (ht : facetSet c.1 c.2 t = F) : dropOf c F = t := by
  have hmiss : chainVZ c.1 c.2 t ∉ F := by
    rw [← ht]
    exact facetSet_drop_notMem c.1 c.2 t
  have hex : ∃ u : Fin (n + 1), chainVZ c.1 c.2 u ∉ F := ⟨t, hmiss⟩
  unfold dropOf
  rw [dif_pos hex]
  have hchoose : chainVZ c.1 c.2 hex.choose ∉ F := hex.choose_spec
  have hchoose' : chainVZ c.1 c.2 hex.choose ∉ facetSet c.1 c.2 t := by
    rw [ht]
    exact hchoose
  exact dropIdx_unique c.1 c.2 hchoose'

theorem chainVZ_swap_eq_of_prefix {n : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (a b : Fin n) (u : Fin (n + 1))
    (hab : (a.val < u.val) ↔ (b.val < u.val)) :
    chainVZ p (σ * Equiv.swap a b) u = chainVZ p σ u := by
  funext i
  unfold chainVZ
  have hsymm : (σ * Equiv.swap a b).symm i = Equiv.swap a b (σ.symm i) := by
    apply (σ * Equiv.swap a b).injective
    rw [Equiv.apply_symm_apply]
    simp [Equiv.Perm.coe_mul]
  rw [hsymm]
  by_cases ha : σ.symm i = a
  · rw [ha, Equiv.swap_apply_left]
    by_cases hb_lt : b.val < u.val
    · rw [if_pos hb_lt, if_pos (hab.mpr hb_lt)]
    · rw [if_neg hb_lt, if_neg (fun h => hb_lt (hab.mp h))]
  · by_cases hb : σ.symm i = b
    · rw [hb, Equiv.swap_apply_right]
      by_cases ha_lt : a.val < u.val
      · rw [if_pos ha_lt, if_pos (hab.mp ha_lt)]
      · rw [if_neg ha_lt, if_neg (fun h => ha_lt (hab.mpr h))]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem facetSet_swap_eq {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) :
    facetSet p (σ * Equiv.swap ⟨t.val - 1, by omega⟩ ⟨t.val, hlt⟩) t =
      facetSet p σ t := by
  classical
  unfold facetSet
  apply Finset.image_congr
  intro u hu
  rw [Finset.mem_coe, Finset.mem_erase] at hu
  obtain ⟨hut, _⟩ := hu
  have hne : u.val ≠ t.val := fun h => hut (Fin.ext h)
  apply chainVZ_swap_eq_of_prefix
  change (t.val - 1 < u.val) ↔ (t.val < u.val)
  omega

noncomputable def swapAround {n : ℕ} (t : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  if h : 0 < t.val ∧ t.val < n then
    σ * Equiv.swap ⟨t.val - 1, by omega⟩ ⟨t.val, by omega⟩
  else σ

theorem swapAround_facet {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) :
    facetSet p (swapAround t σ) t = facetSet p σ t := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩]
  exact facetSet_swap_eq p σ h0 hlt

theorem swapAround_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) : swapAround t σ ≠ σ := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩]
  refine partnerPerm_ne σ ?_
  simp only [Ne, Fin.mk.injEq]
  omega

theorem swapAround_involutive {n : ℕ} (σ : Equiv.Perm (Fin n))
    {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n) :
    swapAround t (swapAround t σ) = σ := by
  unfold swapAround
  rw [dif_pos ⟨h0, hlt⟩, dif_pos ⟨h0, hlt⟩, mul_assoc,
    Equiv.swap_mul_self, mul_one]

theorem finRotate_symm_val_of_pos {n : ℕ} {s : Fin n} (hs : 0 < s.val) :
    ((finRotate n).symm s).val = s.val - 1 := by
  have hsub : s.val - 1 < n := by omega
  have hrw : (finRotate n ⟨s.val - 1, hsub⟩).val = (s.val - 1) + 1 :=
    finRotate_val_of_lt (s := ⟨s.val - 1, hsub⟩) (by
      show (s.val - 1) + 1 < n
      omega)
  have hpred : (finRotate n).symm s = ⟨s.val - 1, hsub⟩ := by
    apply (finRotate n).injective
    rw [Equiv.apply_symm_apply]
    ext
    rw [hrw]
    exact (Nat.sub_add_cancel hs).symm
  rw [hpred]

theorem not_finRotate_symm_lt_of_zero {n : ℕ} {s : Fin n} (hs : s.val = 0)
    {m : ℕ} (hm : m < n) : ¬ ((finRotate n).symm s).val < m := by
  intro hlt
  have hval : s.val = ((finRotate n).symm s).val + 1 := by
    have hrot := finRotate_val_of_lt (s := (finRotate n).symm s) (by omega)
    simpa [Equiv.apply_symm_apply] using hrot
  omega

noncomputable def endpointFwd {n : ℕ} (hn : 0 < n) (c : Cell n) : Cell n :=
  (fun i => c.1 i + unitVec (c.2 ⟨0, hn⟩) i, c.2 * finRotate n)

noncomputable def endpointInv {n : ℕ} (hn : 0 < n) (c : Cell n) : Cell n :=
  (fun i => c.1 i - unitVec ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩) i,
    c.2 * (finRotate n)⁻¹)

theorem endpointInv_fwd {n : ℕ} (hn : 0 < n) (c : Cell n) :
    endpointInv hn (endpointFwd hn c) = c := by
  have hperm : c.2 * finRotate n * (finRotate n)⁻¹ = c.2 := mul_inv_cancel_right _ _
  apply Prod.ext
  · funext i
    simp only [endpointInv, endpointFwd, hperm]
    ring
  · simp only [endpointInv, endpointFwd, hperm]

theorem endpointFwd_inv {n : ℕ} (hn : 0 < n) (c : Cell n) :
    endpointFwd hn (endpointInv hn c) = c := by
  have hperm : c.2 * (finRotate n)⁻¹ * finRotate n = c.2 := inv_mul_cancel_right _ _
  apply Prod.ext
  · funext i
    simp only [endpointInv, endpointFwd, hperm]
    ring
  · simp only [endpointInv, endpointFwd, hperm]

theorem chainVZ_endpoint_shift {n : ℕ} (hn : 0 < n) (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) {u : Fin (n + 1)} (hu : u.val < n) :
    chainVZ (fun i => p i + unitVec (σ ⟨0, hn⟩) i) (σ * finRotate n) u =
      chainVZ p σ ⟨u.val + 1, by omega⟩ := by
  funext i
  unfold chainVZ
  have hsymm : (σ * finRotate n).symm i = (finRotate n).symm (σ.symm i) := by
    apply (σ * finRotate n).injective
    rw [Equiv.apply_symm_apply]
    simp [Equiv.Perm.coe_mul]
  rw [hsymm]
  change p i + unitVec (σ ⟨0, hn⟩) i +
      (if ((finRotate n).symm (σ.symm i)).val < u.val then (1 : ℤ) else 0) =
    p i + if (σ.symm i).val < u.val + 1 then (1 : ℤ) else 0
  by_cases hzero : (σ.symm i).val = 0
  · have hidx : σ.symm i = ⟨0, hn⟩ := Fin.ext (by simpa using hzero)
    have hi : i = σ ⟨0, hn⟩ := by
      rw [← Equiv.apply_symm_apply σ i, hidx]
    have hunit : unitVec (σ ⟨0, hn⟩) i = 1 := by
      unfold unitVec
      rw [if_pos hi]
    have hnot : ¬ ((finRotate n).symm (σ.symm i)).val < u.val :=
      not_finRotate_symm_lt_of_zero hzero hu
    have hyes : (σ.symm i).val < u.val + 1 := by omega
    rw [hunit, if_neg hnot, if_pos hyes]
    ring
  · have hpos : 0 < (σ.symm i).val := Nat.pos_of_ne_zero hzero
    have hidx : σ.symm i ≠ ⟨0, hn⟩ := fun h => hzero (by simp [h])
    have hi : i ≠ σ ⟨0, hn⟩ := by
      intro h
      apply hidx
      rw [h, Equiv.symm_apply_apply]
    have hunit : unitVec (σ ⟨0, hn⟩) i = 0 := by
      unfold unitVec
      rw [if_neg hi]
    have hrot := finRotate_symm_val_of_pos hpos
    have hiff : (((finRotate n).symm (σ.symm i)).val < u.val) ↔
        (σ.symm i).val < u.val + 1 := by
      rw [hrot]
      omega
    by_cases hlt : ((finRotate n).symm (σ.symm i)).val < u.val
    · rw [hunit, if_pos hlt, if_pos (hiff.mp hlt)]
      ring
    · rw [hunit, if_neg hlt, if_neg (fun h => hlt (hiff.mpr h))]
      ring

theorem facetSet_endpoint_eq {n : ℕ} (hn : 0 < n) (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    facetSet (fun i => p i + unitVec (σ ⟨0, hn⟩) i) (σ * finRotate n) (Fin.last n) =
      facetSet p σ 0 := by
  classical
  unfold facetSet
  ext v
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨u, hune, rfl⟩
    have hult : u.val < n := by
      have hne : u.val ≠ n := fun h => hune (Fin.ext (by simpa [Fin.val_last] using h))
      omega
    refine ⟨⟨u.val + 1, by omega⟩, ?_, (chainVZ_endpoint_shift hn p σ hult).symm⟩
    intro hcon
    have hv0 : (⟨u.val + 1, by omega⟩ : Fin (n + 1)).val =
        (0 : Fin (n + 1)).val := by
      rw [hcon]
    simp at hv0
  · rintro ⟨w, hwne, rfl⟩
    have hwpos : 0 < w.val := by
      rcases Nat.eq_zero_or_pos w.val with h | h
      · exact absurd (Fin.ext (by simpa using h)) hwne
      · exact h
    have hwlt : w.val - 1 < n := by omega
    have hwlt1 : w.val - 1 < n + 1 := by omega
    refine ⟨⟨w.val - 1, hwlt1⟩, ?_, ?_⟩
    · intro hcon
      have hvl : (⟨w.val - 1, hwlt1⟩ : Fin (n + 1)).val = (Fin.last n).val := by
        rw [hcon]
      simp only [Fin.val_last] at hvl
      omega
    · have hkey := chainVZ_endpoint_shift hn p σ
        (u := ⟨w.val - 1, hwlt1⟩) (by simpa using hwlt)
      rw [hkey]
      congr 1
      apply Fin.ext
      show w.val - 1 + 1 = w.val
      omega

theorem endpoint_base_ne {n : ℕ} (hn : 0 < n) (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    (fun i => p i + unitVec (σ ⟨0, hn⟩) i) ≠ p := by
  intro hcon
  have hcoord := congrFun hcon (σ ⟨0, hn⟩)
  unfold unitVec at hcoord
  rw [if_pos rfl] at hcoord
  omega

theorem endpointFwd_facet {n : ℕ} (hn : 0 < n) (c : Cell n) :
    facetSet (endpointFwd hn c).1 (endpointFwd hn c).2 (Fin.last n) =
      facetSet c.1 c.2 0 := by
  unfold endpointFwd
  exact facetSet_endpoint_eq hn c.1 c.2

theorem endpointInv_facet {n : ℕ} (hn : 0 < n) (c : Cell n) :
    facetSet (endpointInv hn c).1 (endpointInv hn c).2 0 =
      facetSet c.1 c.2 (Fin.last n) := by
  have h := endpointFwd_facet hn (endpointInv hn c)
  rw [endpointFwd_inv hn c] at h
  exact h.symm

theorem endpointFwd_ne {n : ℕ} (hn : 0 < n) (c : Cell n) :
    endpointFwd hn c ≠ c := by
  intro hcon
  exact endpoint_base_ne hn c.1 c.2 (congrArg Prod.fst hcon)

theorem endpointInv_ne {n : ℕ} (hn : 0 < n) (c : Cell n) :
    endpointInv hn c ≠ c := by
  intro hcon
  have h2 : endpointFwd hn (endpointInv hn c) = endpointFwd hn c := by
    rw [hcon]
  rw [endpointFwd_inv hn c] at h2
  exact endpointFwd_ne hn c h2.symm

/-- The global cell on the other side of a facet, keyed by the recovered drop index. -/
noncomputable def partnerCell {n : ℕ} (hn : 0 < n) (c : Cell n)
    (F : Finset (Fin n → ℤ)) : Cell n :=
  let t := dropOf c F
  if t.val = 0 then endpointFwd hn c
  else if t.val = n then endpointInv hn c
  else (c.1, swapAround t c.2)

theorem partnerCell_of_zero {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (h : (dropOf c F).val = 0) :
    partnerCell hn c F = endpointFwd hn c := by
  unfold partnerCell
  rw [if_pos h]

theorem partnerCell_of_last {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (h0 : (dropOf c F).val ≠ 0)
    (h : (dropOf c F).val = n) :
    partnerCell hn c F = endpointInv hn c := by
  unfold partnerCell
  rw [if_neg h0, if_pos h]

theorem partnerCell_of_internal {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (h0 : (dropOf c F).val ≠ 0)
    (h : (dropOf c F).val ≠ n) :
    partnerCell hn c F = (c.1, swapAround (dropOf c F) c.2) := by
  unfold partnerCell
  rw [if_neg h0, if_neg h]

theorem dropOf_partner {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (hb : cellBounds c F) :
    dropOf (partnerCell hn c F) F =
      (let t := dropOf c F
       if t.val = 0 then Fin.last n else if t.val = n then (0 : Fin (n + 1)) else t) := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  simp only [partnerCell, htd]
  by_cases h0 : t.val = 0
  · rw [if_pos h0]
    have : facetSet (endpointFwd hn c).1 (endpointFwd hn c).2 (Fin.last n) = F := by
      rw [endpointFwd_facet hn c]
      have : (0 : Fin (n + 1)) = t := Fin.ext (by simp [h0])
      rw [this]
      exact ht
    rw [dropOf_eq _ this]
    simp [h0]
  · rw [if_neg h0]
    by_cases hn' : t.val = n
    · rw [if_pos hn']
      have htlast : t = Fin.last n := Fin.ext (by simp [hn', Fin.val_last])
      have : facetSet (endpointInv hn c).1 (endpointInv hn c).2 0 = F := by
        rw [endpointInv_facet hn c, ← htlast]
        exact ht
      rw [dropOf_eq _ this]
      simp [hn']
    · rw [if_neg hn']
      have h0' : 0 < t.val := by omega
      have hlt : t.val < n := by omega
      have : facetSet c.1 (swapAround t c.2) t = F := by
        rw [swapAround_facet c.1 c.2 h0' hlt]
        exact ht
      rw [dropOf_eq _ this]
      simp [h0, hn']

theorem partnerCell_involutive {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (hb : cellBounds c F) :
    partnerCell hn (partnerCell hn c F) F = c := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  have hdp := dropOf_partner hn c ⟨t, ht⟩
  simp only [htd] at hdp
  by_cases h0 : t.val = 0
  · have hpart : partnerCell hn c F = endpointFwd hn c :=
      partnerCell_of_zero hn c (by rw [htd]; exact h0)
    have hdrop : (dropOf (endpointFwd hn c) F).val = n := by
      rw [← hpart, hdp]
      simp [h0, Fin.val_last]
    rw [hpart, partnerCell_of_last hn _ (by rw [hdrop]; omega) hdrop]
    exact endpointInv_fwd hn c
  · by_cases hn' : t.val = n
    · have hpart : partnerCell hn c F = endpointInv hn c :=
        partnerCell_of_last hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn')
      have hdrop : (dropOf (endpointInv hn c) F).val = 0 := by
        rw [← hpart, hdp]
        simp [hn']
      rw [hpart, partnerCell_of_zero hn _ hdrop]
      exact endpointFwd_inv hn c
    · have hpart : partnerCell hn c F = (c.1, swapAround t c.2) := by
        rw [partnerCell_of_internal hn c (by rw [htd]; exact h0)
          (by rw [htd]; exact hn'), htd]
      have hdrop : dropOf (c.1, swapAround t c.2) F = t := by
        rw [← hpart, hdp]
        simp [h0, hn']
      have hdrop0 : (dropOf (c.1, swapAround t c.2) F).val ≠ 0 := by
        rw [hdrop]
        exact h0
      have hdropn : (dropOf (c.1, swapAround t c.2) F).val ≠ n := by
        rw [hdrop]
        exact hn'
      rw [hpart, partnerCell_of_internal hn _ hdrop0 hdropn, hdrop]
      have h0' : 0 < t.val := by omega
      have hlt : t.val < n := by omega
      apply Prod.ext
      · rfl
      · exact swapAround_involutive c.2 h0' hlt

theorem partnerCell_bounds {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (hb : cellBounds c F) :
    cellBounds (partnerCell hn c F) F := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  by_cases h0 : t.val = 0
  · rw [partnerCell_of_zero hn c (by rw [htd]; exact h0)]
    refine ⟨Fin.last n, ?_⟩
    rw [endpointFwd_facet hn c]
    have : (0 : Fin (n + 1)) = t := Fin.ext (by simp [h0])
    rw [this]
    exact ht
  · by_cases hn' : t.val = n
    · rw [partnerCell_of_last hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn')]
      refine ⟨0, ?_⟩
      rw [endpointInv_facet hn c]
      have htlast : t = Fin.last n := Fin.ext (by simp [hn', Fin.val_last])
      rw [← htlast]
      exact ht
    · rw [partnerCell_of_internal hn c (by rw [htd]; exact h0)
        (by rw [htd]; exact hn'), htd]
      refine ⟨t, ?_⟩
      rw [swapAround_facet c.1 c.2 (by omega) (by omega)]
      exact ht

theorem partnerCell_ne {n : ℕ} (hn : 0 < n) (c : Cell n)
    {F : Finset (Fin n → ℤ)} (hb : cellBounds c F) :
    partnerCell hn c F ≠ c := by
  obtain ⟨t, ht⟩ := hb
  have htd : dropOf c F = t := dropOf_eq c ht
  by_cases h0 : t.val = 0
  · rw [partnerCell_of_zero hn c (by rw [htd]; exact h0)]
    exact endpointFwd_ne hn c
  · by_cases hn' : t.val = n
    · rw [partnerCell_of_last hn c (by rw [htd]; exact h0) (by rw [htd]; exact hn')]
      exact endpointInv_ne hn c
    · rw [partnerCell_of_internal hn c (by rw [htd]; exact h0)
        (by rw [htd]; exact hn'), htd]
      intro hcon
      have hperm : swapAround t c.2 = c.2 := by
        have := congrArg Prod.snd hcon
        simpa using this
      exact (swapAround_ne c.2 (by omega) (by omega)) hperm

/-- A facet is on the mesh boundary iff some valid bounding cell has an invalid partner. -/
def isBoundary {n : ℕ} (hn : 0 < n) (k : ℕ) (F : Finset (Fin n → ℤ)) : Prop :=
  ∃ c ∈ cells n k, cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F)

noncomputable instance {n k : ℕ} (hn : 0 < n) (F : Finset (Fin n → ℤ)) :
    Decidable (isBoundary hn k F) :=
  Classical.propDecidable _

theorem partner_valid_of_not_boundary {n k : ℕ} (hn : 0 < n)
    {F : Finset (Fin n → ℤ)} (hnb : ¬ isBoundary hn k F)
    {c : Cell n} (hc : c ∈ cells n k) (hb : cellBounds c F) :
    cellValid k (partnerCell hn c F) := by
  by_contra hbad
  exact hnb ⟨c, hc, hb, hbad⟩

theorem hinterior_of_not_boundary {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) (hnb : ¬ isBoundary hn k F) :
    Even ((cells n k).filter (fun c => cellBounds c F)).card := by
  classical
  set S := (cells n k).filter (fun c => cellBounds c F) with hS
  have hmemS : ∀ c, c ∈ S → c ∈ cells n k ∧ cellBounds c F := by
    intro c hc
    rw [hS, Finset.mem_filter] at hc
    exact hc
  have g_mem : ∀ c (_ : c ∈ S), partnerCell hn c F ∈ S := by
    intro c hc
    obtain ⟨hcell, hb⟩ := hmemS c hc
    rw [hS, Finset.mem_filter]
    exact ⟨mem_cells.mpr (partner_valid_of_not_boundary hn hnb hcell hb),
      partnerCell_bounds hn c hb⟩
  refine even_card_of_involution S (fun c _ => partnerCell hn c F) ?_ g_mem ?_
  · intro c hc
    exact partnerCell_ne hn c (hmemS c hc).2
  · intro c hc
    exact partnerCell_involutive hn c (hmemS c hc).2

theorem even_validPartner_card {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    Even ((cells n k).filter
      (fun c => cellBounds c F ∧ cellValid k (partnerCell hn c F))).card := by
  classical
  set S := (cells n k).filter
    (fun c => cellBounds c F ∧ cellValid k (partnerCell hn c F)) with hS
  have hmemS : ∀ c, c ∈ S →
      c ∈ cells n k ∧ cellBounds c F ∧ cellValid k (partnerCell hn c F) := by
    intro c hc
    rw [hS, Finset.mem_filter] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2⟩
  have g_mem : ∀ c (_ : c ∈ S), partnerCell hn c F ∈ S := by
    intro c hc
    obtain ⟨hcell, hb, hpvalid⟩ := hmemS c hc
    rw [hS, Finset.mem_filter]
    refine ⟨mem_cells.mpr hpvalid, partnerCell_bounds hn c hb, ?_⟩
    rw [partnerCell_involutive hn c hb]
    exact mem_cells.mp hcell
  refine even_card_of_involution S (fun c _ => partnerCell hn c F) ?_ g_mem ?_
  · intro c hc
    exact partnerCell_ne hn c (hmemS c hc).2.1
  · intro c hc
    exact partnerCell_involutive hn c (hmemS c hc).2.1

theorem bounds_card_odd_iff_invalid {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    Odd ((cells n k).filter (fun c => cellBounds c F)).card
      ↔ Odd ((cells n k).filter
          (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))).card := by
  classical
  have hdisj : Disjoint
      ((cells n k).filter
        (fun c => cellBounds c F ∧ cellValid k (partnerCell hn c F)))
      ((cells n k).filter
        (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))) := by
    rw [Finset.disjoint_left]
    intro c hcv hci
    rw [Finset.mem_filter] at hcv hci
    exact hci.2.2 hcv.2.2
  have hunion : (cells n k).filter (fun c => cellBounds c F)
      = ((cells n k).filter
          (fun c => cellBounds c F ∧ cellValid k (partnerCell hn c F)))
        ∪ ((cells n k).filter
          (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro c _
    constructor
    · intro hb
      by_cases hp : cellValid k (partnerCell hn c F)
      · exact Or.inl ⟨hb, hp⟩
      · exact Or.inr ⟨hb, hp⟩
    · rintro (⟨hb, _⟩ | ⟨hb, _⟩) <;> exact hb
  have hcard : ((cells n k).filter (fun c => cellBounds c F)).card
      = ((cells n k).filter
          (fun c => cellBounds c F ∧ cellValid k (partnerCell hn c F))).card
        + ((cells n k).filter
          (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))).card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  obtain ⟨m, hm⟩ := even_validPartner_card hn F
  rw [hcard, hm]
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

theorem hboundaryOdd_of_singleton {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ))
    (hsingle : ((cells n k).filter
      (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))).card = 1) :
    Odd ((cells n k).filter (fun c => cellBounds c F)).card := by
  rw [bounds_card_odd_iff_invalid hn F, hsingle]
  exact ⟨0, rfl⟩

/-- Freudenthal Sperner output with the singleton boundary-partner input supplied. -/
theorem exists_rainbow_cellF_R2 {n : ℕ} (hn : 0 < n) (k : ℕ)
    (L : (Fin n → ℤ) → Fin (n + 1))
    (hR2 : ∀ F ∈ facets n k,
      (F.image L = Finset.univ.erase (Fin.last n)) → isBoundary hn k F →
        ((cells n k).filter
          (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))).card = 1)
    (hR3 : Odd ((facets n k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last n)) ∧ isBoundary hn k F)).card) :
    Odd ((cells n k).filter (fun c => isRainbow L c)).card := by
  classical
  refine sperner_n_dim_combinatorial (cells n k) (facets n k)
    (fun c F => cellBounds c F)
    (fun F => F.image L = Finset.univ.erase (Fin.last n))
    (isBoundary hn k)
    (isRainbow L)
    ?_ ?_ ?_ hR3
  · intro c hc
    exact hheart hc
  · intro F _ _ hb
    exact hinterior_of_not_boundary hn F hb
  · intro F hF hd hb
    exact hboundaryOdd_of_singleton hn F (hR2 F hF hd hb)

theorem rainbow_count_zero_odd (k : ℕ) (L : (Fin 0 → ℤ) → Fin 1) :
    Odd ((cells 0 k).filter (fun c => isRainbow L c)).card := by
  classical
  have hrain : ∀ c : Cell 0, isRainbow L c := by
    intro c
    unfold isRainbow
    constructor
    · intro a b _
      apply Fin.ext
      omega
    · intro y
      refine ⟨0, ?_⟩
      apply Fin.ext
      omega
  have hfilter : (cells 0 k).filter (fun c => isRainbow L c) = cells 0 k := by
    rw [Finset.filter_eq_self]
    intro c _hc
    exact hrain c
  have hcells : cells 0 k = (Finset.univ : Finset (Cell 0)) := by
    ext c
    rw [mem_cells]
    unfold cellValid
    simp
  rw [hfilter, hcells, Finset.card_univ]
  haveI : Subsingleton (Cell 0) := inferInstance
  have hcard : Fintype.card (Cell 0) = 1 :=
    Fintype.card_ofSubsingleton ((fun i => Fin.elim0 i, 1) : Cell 0)
  rw [hcard]
  exact ⟨0, rfl⟩

theorem finalFacet_extendCell_injective {n : ℕ} :
    Function.Injective
      (fun c : Cell n =>
        facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1))) := by
  intro c d hcd
  apply chainSet_injective
  have himg := congrArg (fun F : Finset (Fin (n + 1) → ℤ) => F.image dropLast) hcd
  change (facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1))).image dropLast =
    (facetSet (extendCell d).1 (extendCell d).2 (Fin.last (n + 1))).image dropLast at himg
  rw [image_dropLast_extendCell_bottomFacet,
    image_dropLast_extendCell_bottomFacet] at himg
  exact himg

/-- Door facets on the bottom face, represented as global facet sets. -/
noncomputable def bottomDoorFacets {n : ℕ} (k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2)) :
    Finset (Finset (Fin (n + 1) → ℤ)) :=
  ((cells n k).filter (fun c => isBottomDoor L (extendCell c))).image
    (fun c => facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1)))

theorem card_bottomDoorFacets_eq_rainbow {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1)) :
    (bottomDoorFacets k L).card =
      ((cells n k).filter (fun c => isRainbow (bottomLabel L havoid) c)).card := by
  classical
  unfold bottomDoorFacets
  rw [Finset.card_image_of_injective _ finalFacet_extendCell_injective]
  congr 1
  apply Finset.filter_congr
  intro c _hc
  unfold isBottomDoor isRainbow
  exact door_iff_extendCell_rainbow L havoid c

theorem bottomDoorFacets_odd_of_lower_rainbow_odd {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hodd : Odd ((cells n k).filter
      (fun c => isRainbow (bottomLabel L havoid) c)).card) :
    Odd (bottomDoorFacets k L).card := by
  rw [card_bottomDoorFacets_eq_rainbow L havoid]
  exact hodd

theorem finRotate_symm_zero {n : ℕ} :
    (finRotate (n + 1)).symm (0 : Fin (n + 1)) = Fin.last n := by
  apply (finRotate (n + 1)).injective
  rw [Equiv.apply_symm_apply]
  rw [finRotate_succ_apply]
  ext
  simp [Fin.add_def, Fin.val_last]

theorem endpointInv_extendCell_invalid {n k : ℕ} (c : Cell n) :
    ¬ cellValid k (endpointInv (Nat.succ_pos n) (extendCell c)) := by
  intro hv
  have hidx :
      ((extendCell c).2 * (finRotate (n + 1))⁻¹) (0 : Fin (n + 1)) = Fin.last n := by
    change extendLast c.2 ((finRotate (n + 1)).symm (0 : Fin (n + 1))) =
      Fin.last n
    rw [finRotate_symm_zero, extendLast_apply_last]
  have hcoord : (endpointInv (Nat.succ_pos n) (extendCell c)).1 (Fin.last n) = -1 := by
    unfold endpointInv
    change (extendCell c).1 (Fin.last n) -
        unitVec (((extendCell c).2 * (finRotate (n + 1))⁻¹) (0 : Fin (n + 1)))
          (Fin.last n) = -1
    rw [hidx]
    simp [extendCell, unitVec]
  have hnonneg := (hv (Fin.last n)).1
  rw [hcoord] at hnonneg
  omega

theorem bottom_geometry_of_facet_last_zero {n k : ℕ} {c : Cell (n + 1)}
    (hc : c ∈ cells (n + 1) k) {t : Fin (n + 2)}
    (hzero : ∀ v ∈ facetSet c.1 c.2 t, v (Fin.last n) = 0) :
    c.1 (Fin.last n) = 0 ∧ c.2 (Fin.last n) = Fin.last n ∧
      t = Fin.last (n + 1) := by
  classical
  let s : Fin (n + 1) := c.2.symm (Fin.last n)
  have hvalid := mem_cells.mp hc
  have hp_nonneg : 0 ≤ c.1 (Fin.last n) := (hvalid (Fin.last n)).1
  have hs_le : s.val ≤ n := by
    have := s.isLt
    omega
  have hnot_step : ∀ u : Fin (n + 2), u ≠ t → ¬ s.val < u.val := by
    intro u hut hlt
    have hv : chainVZ c.1 c.2 u ∈ facetSet c.1 c.2 t :=
      (mem_facetSet_iff c.1 c.2 t u).mpr hut
    have hz := hzero (chainVZ c.1 c.2 u) hv
    unfold chainVZ at hz
    have hscoord : c.2.symm (Fin.last n) = s := rfl
    rw [hscoord, if_pos hlt] at hz
    omega
  have hp_zero_of_nonstep : ∀ u : Fin (n + 2), u ≠ t →
      ¬ s.val < u.val → c.1 (Fin.last n) = 0 := by
    intro u hut hnlt
    have hv : chainVZ c.1 c.2 u ∈ facetSet c.1 c.2 t :=
      (mem_facetSet_iff c.1 c.2 t u).mpr hut
    have hz := hzero (chainVZ c.1 c.2 u) hv
    unfold chainVZ at hz
    have hscoord : c.2.symm (Fin.last n) = s := rfl
    rw [hscoord, if_neg hnlt] at hz
    omega
  have ht_last : t = Fin.last (n + 1) := by
    by_contra ht
    have hlt : s.val < (Fin.last (n + 1) : Fin (n + 2)).val := by
      simp only [Fin.val_last]
      omega
    exact hnot_step (Fin.last (n + 1)) (by simpa [eq_comm] using ht) hlt
  have hs_last : s = Fin.last n := by
    by_contra hs
    have hslt : s.val < n := by
      have hsne : s.val ≠ n := by
        intro h
        exact hs (Fin.ext (by simpa [Fin.val_last] using h))
      omega
    let u : Fin (n + 2) := ⟨s.val + 1, by omega⟩
    have hut : u ≠ t := by
      rw [ht_last]
      intro h
      have hval := congrArg Fin.val h
      simp only [u, Fin.val_last] at hval
      omega
    have hlt : s.val < u.val := by
      simp [u]
    exact hnot_step u hut hlt
  have hp_zero : c.1 (Fin.last n) = 0 := by
    let u : Fin (n + 2) := 0
    by_cases htu : u = t
    · let u' : Fin (n + 2) := 1
      have hu't : u' ≠ t := by
        rw [← htu]
        intro h
        have hval := congrArg Fin.val h
        simp [u, u'] at hval
      exact hp_zero_of_nonstep u' hu't (hnot_step u' hu't)
    · exact hp_zero_of_nonstep u htu (hnot_step u htu)
  have hσ : c.2 (Fin.last n) = Fin.last n := by
    have happ := congrArg c.2 hs_last
    have hraw : Fin.last n = c.2 (Fin.last n) := by
      simpa [s] using happ
    exact hraw.symm
  exact ⟨hp_zero, hσ, ht_last⟩

theorem extendCell_finalFacet_boundary {n k : ℕ} (hk : 0 < k) {c : Cell n}
    (hc : c ∈ cells n k) :
    isBoundary (Nat.succ_pos n) k
      (facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1))) := by
  let F := facetSet (extendCell c).1 (extendCell c).2 (Fin.last (n + 1))
  have hcell : extendCell c ∈ cells (n + 1) k :=
    mem_cells.mpr (extendCell_valid hk (mem_cells.mp hc))
  have hb : cellBounds (extendCell c) F := ⟨Fin.last (n + 1), rfl⟩
  refine ⟨extendCell c, hcell, hb, ?_⟩
  have hdrop : dropOf (extendCell c) F = Fin.last (n + 1) :=
    dropOf_eq (extendCell c) rfl
  have h0 : (dropOf (extendCell c) F).val ≠ 0 := by
    rw [hdrop]
    simp [Fin.val_last]
  have hlast : (dropOf (extendCell c) F).val = n + 1 := by
    rw [hdrop]
    simp [Fin.val_last]
  rw [partnerCell_of_last (Nat.succ_pos n) (extendCell c) h0 hlast]
  exact endpointInv_extendCell_invalid c

theorem bottomDoorFacets_subset_boundaryDoors {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2)) :
    bottomDoorFacets k L ⊆
      (facets (n + 1) k).filter
        (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
          isBoundary (Nat.succ_pos n) k F) := by
  classical
  intro F hF
  unfold bottomDoorFacets at hF
  rw [Finset.mem_image] at hF
  obtain ⟨c, hc, rfl⟩ := hF
  rw [Finset.mem_filter] at hc
  rw [Finset.mem_filter]
  let upper : Cell (n + 1) := extendCell c
  have hupper : upper ∈ cells (n + 1) k :=
    mem_cells.mpr (extendCell_valid hk (mem_cells.mp hc.1))
  have hb : cellBounds upper
      (facetSet upper.1 upper.2 (Fin.last (n + 1))) := ⟨Fin.last (n + 1), rfl⟩
  refine ⟨mem_facets_of_bounds hupper hb, hc.2, ?_⟩
  exact extendCell_finalFacet_boundary hk hc.1

theorem boundaryDoors_subset_bottomDoorFacets_of_vertices_bottom {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (hbottom : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ∀ v ∈ F, v (Fin.last n) = 0) :
    (facets (n + 1) k).filter
        (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
          isBoundary (Nat.succ_pos n) k F) ⊆
      bottomDoorFacets k L := by
  classical
  intro F hF
  rw [Finset.mem_filter] at hF
  obtain ⟨hFmem, hdoor, hboundary⟩ := hF
  obtain ⟨c, hc, t, htF⟩ := mem_facets_iff.mp hFmem
  have hzero : ∀ v ∈ facetSet c.1 c.2 t, v (Fin.last n) = 0 := by
    intro v hv
    exact hbottom F hFmem hdoor hboundary v (by simpa [← htF] using hv)
  obtain ⟨hp, hσ, htlast⟩ := bottom_geometry_of_facet_last_zero hc hzero
  have hrestrict : restrictCell c hσ ∈ cells n k :=
    restrictCell_mem_cells_of_bottom (by
      rw [bottomCells, Finset.mem_filter]
      exact ⟨hc, hp, hσ⟩)
  have hceq : extendCell (restrictCell c hσ) = c :=
    extendCell_restrictCell hp hσ
  unfold bottomDoorFacets
  rw [Finset.mem_image]
  refine ⟨restrictCell c hσ, ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨hrestrict, ?_⟩
    unfold isBottomDoor
    rw [hceq]
    have hdoor' : (facetSet c.1 c.2 (Fin.last (n + 1))).image L =
        Finset.univ.erase (Fin.last (n + 1)) := by
      rw [← htF] at hdoor
      rwa [htlast] at hdoor
    exact hdoor'
  · rw [hceq]
    rw [← htF, htlast]

theorem boundaryDoors_eq_bottomDoorFacets_of_vertices_bottom {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (hbottom : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ∀ v ∈ F, v (Fin.last n) = 0) :
    (facets (n + 1) k).filter
        (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
          isBoundary (Nat.succ_pos n) k F) = bottomDoorFacets k L := by
  apply Finset.Subset.antisymm
  · exact boundaryDoors_subset_bottomDoorFacets_of_vertices_bottom L hbottom
  · exact bottomDoorFacets_subset_boundaryDoors hk L

theorem hR3_of_boundaryDoors_eq_bottomDoorFacets {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hboundary :
      (facets (n + 1) k).filter
        (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
          isBoundary (Nat.succ_pos n) k F) = bottomDoorFacets k L)
    (hodd : Odd ((cells n k).filter
      (fun c => isRainbow (bottomLabel L havoid) c)).card) :
    Odd ((facets (n + 1) k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
        isBoundary (Nat.succ_pos n) k F)).card := by
  rw [hboundary]
  exact bottomDoorFacets_odd_of_lower_rainbow_odd L havoid hodd

theorem hR3_of_boundary_door_vertices_bottom {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hbottom : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ∀ v ∈ F, v (Fin.last n) = 0)
    (hodd : Odd ((cells n k).filter
      (fun c => isRainbow (bottomLabel L havoid) c)).card) :
    Odd ((facets (n + 1) k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
        isBoundary (Nat.succ_pos n) k F)).card := by
  exact hR3_of_boundaryDoors_eq_bottomDoorFacets L havoid
    (boundaryDoors_eq_bottomDoorFacets_of_vertices_bottom hk L hbottom) hodd

theorem rainbow_count_succ_odd_of_boundary_data {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hR2 : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ((cells (n + 1) k).filter
            (fun c => cellBounds c F ∧
              ¬ cellValid k (partnerCell (Nat.succ_pos n) c F))).card = 1)
    (hboundary :
      (facets (n + 1) k).filter
        (fun F => (F.image L = Finset.univ.erase (Fin.last (n + 1))) ∧
          isBoundary (Nat.succ_pos n) k F) = bottomDoorFacets k L)
    (hlower : Odd ((cells n k).filter
      (fun c => isRainbow (bottomLabel L havoid) c)).card) :
    Odd ((cells (n + 1) k).filter (fun c => isRainbow L c)).card := by
  have hR3 := hR3_of_boundaryDoors_eq_bottomDoorFacets L havoid hboundary hlower
  exact exists_rainbow_cellF_R2 (Nat.succ_pos n) k L hR2 hR3

theorem rainbow_count_succ_odd_of_boundary_vertices_bottom {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hR2 : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ((cells (n + 1) k).filter
            (fun c => cellBounds c F ∧
              ¬ cellValid k (partnerCell (Nat.succ_pos n) c F))).card = 1)
    (hbottom : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ∀ v ∈ F, v (Fin.last n) = 0)
    (hlower : Odd ((cells n k).filter
      (fun c => isRainbow (bottomLabel L havoid) c)).card) :
    Odd ((cells (n + 1) k).filter (fun c => isRainbow L c)).card := by
  exact rainbow_count_succ_odd_of_boundary_data L havoid hR2
    (boundaryDoors_eq_bottomDoorFacets_of_vertices_bottom hk L hbottom) hlower

/-- Labellings for the `n`-dimensional Freudenthal model. -/
abbrev Label (n : ℕ) : Type :=
  (Fin n → ℤ) → Fin (n + 1)

/-- Recursive boundary data sufficient for the Freudenthal parity induction. -/
def BoundaryData : (n k : ℕ) → Label n → Prop
  | 0, _k, _L => True
  | n + 1, k, L =>
      ∃ havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1),
        (∀ F ∈ facets (n + 1) k,
          (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
            isBoundary (Nat.succ_pos n) k F →
              ((cells (n + 1) k).filter
                (fun c => cellBounds c F ∧
                  ¬ cellValid k (partnerCell (Nat.succ_pos n) c F))).card = 1) ∧
        (∀ F ∈ facets (n + 1) k,
          (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
            isBoundary (Nat.succ_pos n) k F →
              ∀ v ∈ F, v (Fin.last n) = 0) ∧
        BoundaryData n k (bottomLabel L havoid)

theorem rainbow_count_odd_of_boundaryData {n k : ℕ} (hk : 0 < k)
    (L : Label n) (hdata : BoundaryData n k L) :
    Odd ((cells n k).filter (fun c => isRainbow L c)).card := by
  induction n with
  | zero =>
      exact rainbow_count_zero_odd k L
  | succ n ih =>
      rcases hdata with ⟨havoid, hR2, hbottom, hlower⟩
      exact rainbow_count_succ_odd_of_boundary_vertices_bottom hk L havoid hR2
        hbottom (ih (bottomLabel L havoid) hlower)

theorem exists_rainbow_cellF_of_boundaryData {n k : ℕ} (hk : 0 < k)
    (L : Label n) (hdata : BoundaryData n k L) :
    ∃ c ∈ cells n k, isRainbow L c := by
  classical
  have hodd := rainbow_count_odd_of_boundaryData hk L hdata
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hodd.pos
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.1, hc.2⟩

/-!
Status for the full R3/G1 propagation:

This file now has the boundary-compatible Freudenthal/type-A finite carrier, global facets,
drop recovery, per-cell non-overlap (`chainSet_injective`), the partner-cell involution,
the boundary predicate, the interior/boundary parity reduction, and the Freudenthal
`exists_rainbow_cellF_R2` assembly.  It also turns bottom-face doors into lower-dimensional
rainbow cells as global facet sets (`card_bottomDoorFacets_eq_rainbow`) and proves those
bottom facets are genuine boundary facets.

Closed here, with explicit boundary data:
* if every boundary door has all vertices on `{last = 0}`, then it is geometrically the
  final facet of an extended bottom cell (`bottom_geometry_of_facet_last_zero`), hence
  the global boundary-door set equals `bottomDoorFacets`
  (`boundaryDoors_eq_bottomDoorFacets_of_vertices_bottom`);
* `BoundaryData` recursively packages the bottom-colour exclusion, the singleton invalid
  partner input, and the bottom-only boundary-door exclusion in every dimension, and
  `rainbow_count_odd_of_boundaryData` supplies the lower-dimensional odd count by induction.

Still not closed here:
* proving the `BoundaryData` fields for the concrete Sperner labelling used by
  `BrouwerNDimFinal` (in particular the bottom-only boundary-door exclusion and the R2
  singleton input in this Freudenthal carrier);
* the mesh-limit/transport replacement from this cube/type-A model to the existing n-D
  Brouwer/G1/wave statements.
-/

#print axioms image_dropLast_bottomFacet
#print axioms valid_bottomFacet_projects
#print axioms chain_extend_castSucc
#print axioms restrictCell_extendCell
#print axioms bottomCells_eq_image_extend
#print axioms card_bottomCells
#print axioms door_iff_bottomFaceColor_bijective
#print axioms door_iff_extendCell_rainbow
#print axioms card_bottomDoors_eq_rainbow
#print axioms chainSet_injective
#print axioms hheart
#print axioms partnerCell_involutive
#print axioms partnerCell_bounds
#print axioms hinterior_of_not_boundary
#print axioms bounds_card_odd_iff_invalid
#print axioms hboundaryOdd_of_singleton
#print axioms exists_rainbow_cellF_R2
#print axioms rainbow_count_zero_odd
#print axioms finalFacet_extendCell_injective
#print axioms card_bottomDoorFacets_eq_rainbow
#print axioms bottomDoorFacets_odd_of_lower_rainbow_odd
#print axioms bottom_geometry_of_facet_last_zero
#print axioms extendCell_finalFacet_boundary
#print axioms bottomDoorFacets_subset_boundaryDoors
#print axioms boundaryDoors_subset_bottomDoorFacets_of_vertices_bottom
#print axioms boundaryDoors_eq_bottomDoorFacets_of_vertices_bottom
#print axioms hR3_of_boundaryDoors_eq_bottomDoorFacets
#print axioms hR3_of_boundary_door_vertices_bottom
#print axioms rainbow_count_succ_odd_of_boundary_data
#print axioms rainbow_count_succ_odd_of_boundary_vertices_bottom
#print axioms rainbow_count_odd_of_boundaryData
#print axioms exists_rainbow_cellF_of_boundaryData

end Freudenthal

end ShenWork.Paper1
