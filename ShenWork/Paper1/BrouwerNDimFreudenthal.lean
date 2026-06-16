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

/-!
Remaining gap for the full R3/G1 propagation:

The file above gives the boundary-compatible Freudenthal/type-A local model and the literal
bottom-face door-to-rainbow equivalence.  What is not yet wired is the replacement of the old
global `cellsN`/`facetsN` engine by this model: the finite valid-cell carrier, cover/non-overlap
bookkeeping, global interior partner involution, and the induction that feeds the lower
Freudenthal rainbow count back into `exists_rainbow_cellN_R2`.
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

end Freudenthal

end ShenWork.Paper1
