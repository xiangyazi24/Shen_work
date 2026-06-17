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

/-! ## A boundary-compatible type-A simplex carrier

The old barycentric carrier fixes the donor coordinate to `last`.  A type-A cell instead lets
the donor be the last entry of a full coordinate order `τ`; each step is a root
`e_{τ s} - e_{τ last}`.  If the global bottom coordinate is the final increment, the final
facet is literally contained in the bottom face.
-/

/-- The type-A root step `e_a - e_d`. -/
def rootStep {n : ℕ} (a d : Fin (n + 1)) : Fin (n + 1) → ℤ :=
  fun i => (if i = a then 1 else 0) - if i = d then 1 else 0

/-- Type-A simplex chain with full coordinate order `τ`; `τ last` is the donor. -/
def typeAChain {n : ℕ} (p : Fin (n + 1) → ℤ)
    (τ : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1)) :
    Fin (n + 1) → ℤ :=
  fun i => p i + ∑ s ∈ Finset.univ.filter (fun s : Fin n => s.val < t.val),
    rootStep (τ s.castSucc) (τ (Fin.last n)) i

/-- The facet obtained by dropping one vertex from a type-A chain. -/
def typeAFacetSet {n : ℕ} (p : Fin (n + 1) → ℤ)
    (τ : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1)) :
    Finset (Fin (n + 1) → ℤ) :=
  (Finset.univ.erase t).image (typeAChain p τ)

/-- Type-A cell carrier. -/
abbrev TypeACell (n : ℕ) : Type :=
  (Fin (n + 1) → ℤ) × Equiv.Perm (Fin (n + 1))

@[simp] theorem typeAChain_zero {n : ℕ} (p : Fin (n + 1) → ℤ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    typeAChain p τ 0 = p := by
  funext i
  unfold typeAChain
  simp

/-- Valid type-A cells in the mesh simplex: all chain vertices are nonnegative and the base
has total mass `k`. -/
def typeACellValid {n k : ℕ} (c : TypeACell n) : Prop :=
  (∑ i, c.1 i = (k : ℤ)) ∧
    ∀ t : Fin (n + 1), ∀ i : Fin (n + 1), 0 ≤ typeAChain c.1 c.2 t i

instance {n k : ℕ} (c : TypeACell n) : Decidable (typeACellValid (k := k) c) := by
  unfold typeACellValid
  infer_instance

theorem typeACellValid_base_nonneg {n k : ℕ} {c : TypeACell n}
    (hc : typeACellValid (k := k) c) (i : Fin (n + 1)) :
    0 ≤ c.1 i := by
  simpa using hc.2 0 i

theorem typeACellValid_base_le {n k : ℕ} {c : TypeACell n}
    (hc : typeACellValid (k := k) c) (i : Fin (n + 1)) :
    c.1 i ≤ (k : ℤ) := by
  have hle : c.1 i ≤ ∑ j : Fin (n + 1), c.1 j := by
    exact Finset.single_le_sum
      (fun j _hj => typeACellValid_base_nonneg hc j) (Finset.mem_univ i)
  rw [hc.1] at hle
  exact hle

/-- Finite set of valid type-A cells at mesh `k`. -/
noncomputable def typeACells (n k : ℕ) : Finset (TypeACell n) :=
  (Finset.univ.image
      (fun (pτ : (Fin (n + 1) → Fin (k + 1)) × Equiv.Perm (Fin (n + 1))) =>
        ((fun i => (pτ.1 i : ℤ)), pτ.2) : _ → TypeACell n)).filter
    (typeACellValid (k := k))

theorem mem_typeACells {n k : ℕ} {c : TypeACell n} :
    c ∈ typeACells n k ↔ typeACellValid (k := k) c := by
  classical
  unfold typeACells
  rw [Finset.mem_filter]
  constructor
  · intro h
    exact h.2
  · intro hc
    refine ⟨?_, hc⟩
    rw [Finset.mem_image]
    refine ⟨(fun i => ⟨(c.1 i).toNat, ?_⟩, c.2), Finset.mem_univ _, ?_⟩
    · have hle := typeACellValid_base_le hc i
      have hnn := typeACellValid_base_nonneg hc i
      omega
    · apply Prod.ext
      · funext i
        have hnn := typeACellValid_base_nonneg hc i
        simp only [Int.toNat_of_nonneg hnn]
      · rfl

/-- A type-A cell bounds a facet if one of its drop-one-vertex facets is that facet. -/
def typeACellBounds {n : ℕ} (c : TypeACell n)
    (F : Finset (Fin (n + 1) → ℤ)) : Prop :=
  ∃ t : Fin (n + 1), typeAFacetSet c.1 c.2 t = F

instance {n : ℕ} (c : TypeACell n) (F : Finset (Fin (n + 1) → ℤ)) :
    Decidable (typeACellBounds c F) := by
  unfold typeACellBounds
  infer_instance

/-- All facets appearing in valid type-A cells at mesh `k`. -/
noncomputable def typeAFacets (n k : ℕ) :
    Finset (Finset (Fin (n + 1) → ℤ)) :=
  ((typeACells n k).product Finset.univ).image
    (fun ct : TypeACell n × Fin (n + 1) => typeAFacetSet ct.1.1 ct.1.2 ct.2)

theorem mem_typeAFacets_of_bounds {n k : ℕ} {c : TypeACell n}
    {F : Finset (Fin (n + 1) → ℤ)}
    (hc : c ∈ typeACells n k) (hb : typeACellBounds c F) :
    F ∈ typeAFacets n k := by
  classical
  obtain ⟨t, ht⟩ := hb
  unfold typeAFacets
  rw [Finset.mem_image]
  exact ⟨(c, t), Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩, ht⟩

theorem mem_typeAFacets_iff {n k : ℕ} {F : Finset (Fin (n + 1) → ℤ)} :
    F ∈ typeAFacets n k ↔ ∃ c ∈ typeACells n k, typeACellBounds c F := by
  classical
  constructor
  · intro hF
    unfold typeAFacets at hF
    rw [Finset.mem_image] at hF
    obtain ⟨ct, hct, hF⟩ := hF
    have hctp := Finset.mem_product.mp hct
    exact ⟨ct.1, hctp.1, ct.2, hF⟩
  · rintro ⟨c, hc, hb⟩
    exact mem_typeAFacets_of_bounds hc hb

/-- The colour of a type-A cell's vertices under a lattice labelling. -/
noncomputable def typeACellColor {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : TypeACell n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun t => L (typeAChain c.1 c.2 t)

/-- A type-A cell is rainbow when its vertex-colour map is bijective. -/
def typeAIsRainbow {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : TypeACell n) : Prop :=
  Function.Bijective (typeACellColor L c)

noncomputable instance {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : TypeACell n) :
    Decidable (typeAIsRainbow L c) :=
  Classical.propDecidable _

theorem typeAChain_bottom_last_zero {m : ℕ} {p : Fin (m + 2) → ℤ}
    {τ : Equiv.Perm (Fin (m + 2))}
    (hp : p (Fin.last (m + 1)) = 0)
    (hτ : τ (Fin.castSucc (Fin.last m)) = Fin.last (m + 1))
    {u : Fin (m + 2)} (hu : u.val ≤ m) :
    typeAChain p τ u (Fin.last (m + 1)) = 0 := by
  classical
  unfold typeAChain
  rw [hp]
  have hdonor : Fin.last (m + 1) ≠ τ (Fin.last (m + 1)) := by
    intro h
    have heq : τ (Fin.castSucc (Fin.last m)) = τ (Fin.last (m + 1)) := by
      exact hτ.trans h
    have hpre := τ.injective heq
    have hval := congrArg Fin.val hpre
    simp [Fin.val_last] at hval
  have hstep : ∀ s ∈ Finset.univ.filter (fun s : Fin (m + 1) => s.val < u.val),
      rootStep (τ s.castSucc) (τ (Fin.last (m + 1))) (Fin.last (m + 1)) = 0 := by
    intro s hs
    have hslt : s.val < u.val := (Finset.mem_filter.mp hs).2
    have hinc : Fin.last (m + 1) ≠ τ s.castSucc := by
      intro h
      have heq : τ s.castSucc = τ (Fin.castSucc (Fin.last m)) := by
        exact h.symm.trans hτ.symm
      have hpre := τ.injective heq
      have hval := congrArg Fin.val hpre
      simp [Fin.val_last] at hval
      omega
    unfold rootStep
    rw [if_neg hinc, if_neg hdonor]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_const_zero, add_zero]

/-- If the bottom coordinate is the last increment, the final type-A facet lies in the
literal bottom face. -/
theorem typeAFinalFacet_bottom_last_zero {m : ℕ} {p : Fin (m + 2) → ℤ}
    {τ : Equiv.Perm (Fin (m + 2))}
    (hp : p (Fin.last (m + 1)) = 0)
    (hτ : τ (Fin.castSucc (Fin.last m)) = Fin.last (m + 1))
    {v : Fin (m + 2) → ℤ}
    (hv : v ∈ typeAFacetSet p τ (Fin.last (m + 1))) :
    v (Fin.last (m + 1)) = 0 := by
  unfold typeAFacetSet at hv
  rw [Finset.mem_image] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [Finset.mem_erase] at hu
  have huval : u.val ≤ m := by
    have hne : u.val ≠ m + 1 := by
      intro h
      exact hu.1 (Fin.ext (by simpa [Fin.val_last] using h))
    omega
  exact typeAChain_bottom_last_zero hp hτ huval

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

/-- Bottom cells whose final facet is a door.  This is the boundary-compatible
bottom-door carrier; it is intentionally not the legacy `zeroDoorCellsN` carrier. -/
noncomputable def bottomDoors (n k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2)) : Finset (Cell (n + 1)) :=
  (bottomCells n k).filter (fun c => isBottomDoor L c)

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
    (bottomDoors n k L).card =
      ((cells n k).filter (fun c => isRainbow (bottomLabel L havoid) c)).card := by
  classical
  unfold bottomDoors
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

theorem unitVec_injective {n : ℕ} : Function.Injective (unitVec (n := n)) := by
  intro a b hab
  have hcoord := congrFun hab a
  unfold unitVec at hcoord
  rw [if_pos rfl] at hcoord
  by_cases hba : b = a
  · exact hba.symm
  · have hab' : a ≠ b := fun h => hba h.symm
    rw [if_neg hab'] at hcoord
    omega

theorem chainVZ_step {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (s : Fin n) :
    chainVZ p σ s.succ = fun i => chainVZ p σ s.castSucc i + unitVec (σ s) i := by
  funext i
  unfold chainVZ unitVec
  by_cases hi : i = σ s
  · subst i
    rw [Equiv.symm_apply_apply]
    have hsucc : s.val < (s.succ : Fin (n + 1)).val := by simp
    have hcast : ¬ s.val < (s.castSucc : Fin (n + 1)).val := by simp
    rw [if_pos hsucc, if_neg hcast, if_pos rfl]
    ring
  · have hne : σ.symm i ≠ s := by
      intro h
      apply hi
      rw [← h, Equiv.apply_symm_apply]
    have hneval : (σ.symm i).val ≠ s.val := fun h => hne (Fin.ext h)
    have hiff :
        (σ.symm i).val < (s.succ : Fin (n + 1)).val ↔
          (σ.symm i).val < (s.castSucc : Fin (n + 1)).val := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      constructor <;> intro h <;> omega
    rw [if_neg hi]
    by_cases hlt : (σ.symm i).val < (s.castSucc : Fin (n + 1)).val
    · rw [if_pos (hiff.mpr hlt), if_pos hlt]
      ring
    · rw [if_neg (fun h => hlt (hiff.mp h)), if_neg hlt]
      ring

theorem mem_facetSet_exists {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) {v : Fin n → ℤ} (hv : v ∈ facetSet p σ t) :
    ∃ u : Fin (n + 1), u ≠ t ∧ chainVZ p σ u = v := by
  unfold facetSet at hv
  rw [Finset.mem_image] at hv
  obtain ⟨u, hu, huv⟩ := hv
  rw [Finset.mem_erase] at hu
  exact ⟨u, hu.1, huv⟩

theorem sum_total_facetSet {n : ℕ} (p : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) :
    ∑ v ∈ facetSet p σ t, ∑ i, v i =
      (n : ℤ) * (∑ i, p i) +
        ∑ u ∈ (Finset.univ.erase t), (u.val : ℤ) := by
  classical
  unfold facetSet
  rw [Finset.sum_image (by
    intro a _ b _ hab
    exact chainVZ_injective p σ hab)]
  calc
    ∑ u ∈ Finset.univ.erase t, ∑ i, chainVZ p σ u i
        = ∑ u ∈ Finset.univ.erase t, ((∑ i, p i) + (u.val : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro u _hu
          exact sum_chainVZ p σ u
    _ = ∑ u ∈ Finset.univ.erase t, (∑ i, p i) +
          ∑ u ∈ Finset.univ.erase t, (u.val : ℤ) := by
          rw [Finset.sum_add_distrib]
    _ = (n : ℤ) * (∑ i, p i) +
          ∑ u ∈ Finset.univ.erase t, (u.val : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
            Fintype.card_fin]
          have hcard : (n + 1 - 1 : ℕ) = n := by omega
          rw [hcard]

theorem chainVZ_match_off {n : ℕ} (hn : 0 < n) {p p' : Fin n → ℤ}
    {σ σ' : Equiv.Perm (Fin n)} {t : Fin (n + 1)}
    (hF : facetSet p σ t = facetSet p' σ' t) :
    ∀ u : Fin (n + 1), u ≠ t → chainVZ p σ u = chainVZ p' σ' u := by
  classical
  have hsum := congrArg (fun F : Finset (Fin n → ℤ) => ∑ v ∈ F, ∑ i, v i) hF
  change (∑ v ∈ facetSet p σ t, ∑ i, v i) =
    (∑ v ∈ facetSet p' σ' t, ∑ i, v i) at hsum
  rw [sum_total_facetSet p σ t, sum_total_facetSet p' σ' t] at hsum
  have hbase : ∑ i, p i = ∑ i, p' i := by
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    nlinarith
  intro u hu
  have hmem : chainVZ p σ u ∈ facetSet p' σ' t := by
    rw [← hF]
    exact (mem_facetSet_iff p σ t u).mpr hu
  obtain ⟨u', _hu't, hu'eq⟩ := mem_facetSet_exists p' σ' t hmem
  have hsumv := congrArg (fun v : Fin n → ℤ => ∑ i, v i) hu'eq
  change (∑ i, chainVZ p' σ' u' i) = (∑ i, chainVZ p σ u i) at hsumv
  rw [sum_chainVZ, sum_chainVZ, hbase] at hsumv
  have huu' : u = u' := Fin.ext (by exact_mod_cast (by omega : (u.val : ℤ) = u'.val))
  simpa [huu'.symm] using hu'eq.symm

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

theorem facetSet_dropOf {n : ℕ} {c : Cell n} {F : Finset (Fin n → ℤ)}
    (hb : cellBounds c F) : facetSet c.1 c.2 (dropOf c F) = F := by
  obtain ⟨t, ht⟩ := hb
  rw [dropOf_eq c ht]
  exact ht

theorem dropOf_eq_zero {n : ℕ} {c : Cell n} {F : Finset (Fin n → ℤ)}
    (h : (dropOf c F).val = 0) : dropOf c F = 0 :=
  Fin.ext (by simpa using h)

theorem dropOf_eq_last {n : ℕ} {c : Cell n} {F : Finset (Fin n → ℤ)}
    (h : (dropOf c F).val = n) : dropOf c F = Fin.last n :=
  Fin.ext (by simpa [Fin.val_last] using h)

theorem cell_eq_of_facetSet_eq_zero {n : ℕ} (hn : 0 < n) {p p' : Fin n → ℤ}
    {σ σ' : Equiv.Perm (Fin n)} (hF : facetSet p σ 0 = facetSet p' σ' 0) :
    p = p' ∧ σ = σ' := by
  have hmatch := chainVZ_match_off hn hF
  have hstep : ∀ s : Fin n, s ≠ ⟨0, hn⟩ → σ s = σ' s := by
    intro s hs
    have hsc0 : s.castSucc ≠ (0 : Fin (n + 1)) := by
      intro h
      apply hs
      exact Fin.ext (by simpa using congrArg Fin.val h)
    have hss0 : s.succ ≠ (0 : Fin (n + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    have h1 := hmatch s.castSucc hsc0
    have h2 := hmatch s.succ hss0
    have hstepeq : unitVec (σ s) = unitVec (σ' s) := by
      have e1 := chainVZ_step p σ s
      have e2 := chainVZ_step p' σ' s
      funext i
      have := congrFun (e1 ▸ h2 :
        (fun i => chainVZ p σ s.castSucc i + unitVec (σ s) i) =
          chainVZ p' σ' s.succ) i
      rw [e2, h1] at this
      simp only at this ⊢
      linarith
    exact unitVec_injective hstepeq
  have hσ : σ = σ' := ShenWork.Paper1.perm_eq_of_eq_off_point hstep
  refine ⟨?_, hσ⟩
  have h1ne : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (0 : Fin (n + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hm := hmatch ⟨1, by omega⟩ h1ne
  funext i
  have hc := congrFun hm i
  let z : Fin n := ⟨0, hn⟩
  have hone : (⟨1, by omega⟩ : Fin (n + 1)) = z.succ := by
    apply Fin.ext
    simp [z]
  rw [hone, chainVZ_step p σ z, chainVZ_step p' σ' z, hσ] at hc
  simp [z, chainVZ_zero] at hc
  linarith

theorem cell_eq_of_facetSet_eq_last {n : ℕ} (hn : 0 < n) {p p' : Fin n → ℤ}
    {σ σ' : Equiv.Perm (Fin n)}
    (hF : facetSet p σ (Fin.last n) = facetSet p' σ' (Fin.last n)) :
    p = p' ∧ σ = σ' := by
  have hmatch := chainVZ_match_off hn hF
  have h0ne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_last] at this
    omega
  have hp : p = p' := by
    have hm := hmatch 0 h0ne
    simpa using hm
  refine ⟨hp, ?_⟩
  have hstep : ∀ s : Fin n, s ≠ ⟨n - 1, by omega⟩ → σ s = σ' s := by
    intro s hs
    have hsc : s.castSucc ≠ Fin.last n := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_last] at hv
      have := s.isLt
      omega
    have hss : s.succ ≠ Fin.last n := by
      intro h
      apply hs
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_last] at hv
      apply Fin.ext
      show s.val = n - 1
      omega
    have h1 := hmatch s.castSucc hsc
    have h2 := hmatch s.succ hss
    have hstepeq : unitVec (σ s) = unitVec (σ' s) := by
      have e1 := chainVZ_step p σ s
      have e2 := chainVZ_step p' σ' s
      funext i
      have := congrFun (e1 ▸ h2 :
        (fun i => chainVZ p σ s.castSucc i + unitVec (σ s) i) =
          chainVZ p' σ' s.succ) i
      rw [e2, h1] at this
      simp only at this ⊢
      linarith
    exact unitVec_injective hstepeq
  exact ShenWork.Paper1.perm_eq_of_eq_off_point hstep

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

theorem bounds_endpoint_dichotomy {n : ℕ} (hn : 0 < n) {c c' : Cell n}
    {F : Finset (Fin n → ℤ)} (hcb : cellBounds c F) (hcb' : cellBounds c' F)
    (he : (dropOf c F).val = 0 ∨ (dropOf c F).val = n)
    (he' : (dropOf c' F).val = 0 ∨ (dropOf c' F).val = n) :
    c' = c ∨ c' = partnerCell hn c F := by
  have hfc : facetSet c.1 c.2 (dropOf c F) = F := facetSet_dropOf hcb
  have hfc' : facetSet c'.1 c'.2 (dropOf c' F) = F := facetSet_dropOf hcb'
  rcases he with h0 | hl
  · rw [dropOf_eq_zero h0] at hfc
    rcases he' with h0' | hl'
    · rw [dropOf_eq_zero h0'] at hfc'
      have heq := cell_eq_of_facetSet_eq_zero hn (hfc.trans hfc'.symm)
      exact Or.inl (Prod.ext heq.1.symm heq.2.symm)
    · rw [dropOf_eq_last hl'] at hfc'
      have hfwd : facetSet (endpointFwd hn c).1 (endpointFwd hn c).2 (Fin.last n) = F := by
        rw [endpointFwd_facet hn c]
        exact hfc
      have heq := cell_eq_of_facetSet_eq_last hn (hfc'.trans hfwd.symm)
      right
      rw [partnerCell_of_zero hn c h0]
      exact Prod.ext heq.1 heq.2
  · rw [dropOf_eq_last hl] at hfc
    rcases he' with h0' | hl'
    · rw [dropOf_eq_zero h0'] at hfc'
      have hinv : facetSet (endpointInv hn c).1 (endpointInv hn c).2 0 = F := by
        rw [endpointInv_facet hn c]
        exact hfc
      have heq := cell_eq_of_facetSet_eq_zero hn (hfc'.trans hinv.symm)
      right
      rw [partnerCell_of_last hn c (by rw [hl]; omega) hl]
      exact Prod.ext heq.1 heq.2
    · rw [dropOf_eq_last hl'] at hfc'
      have heq := cell_eq_of_facetSet_eq_last hn (hfc.trans hfc'.symm)
      exact Or.inl (Prod.ext heq.1.symm heq.2.symm)

/-- A facet is on the mesh boundary iff some valid bounding cell has an invalid partner. -/
def isBoundary {n : ℕ} (hn : 0 < n) (k : ℕ) (F : Finset (Fin n → ℤ)) : Prop :=
  ∃ c ∈ cells n k, cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F)

noncomputable instance {n k : ℕ} (hn : 0 < n) (F : Finset (Fin n → ℤ)) :
    Decidable (isBoundary hn k F) :=
  Classical.propDecidable _

theorem isBoundary_endpoint {n k : ℕ} (hn : 0 < n) {F : Finset (Fin n → ℤ)}
    (hb : isBoundary hn k F) :
    ∃ c, c ∈ cells n k ∧ cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F) ∧
      ((dropOf c F).val = 0 ∨ (dropOf c F).val = n) := by
  obtain ⟨c, hc, hcb, hpinv⟩ := hb
  refine ⟨c, hc, hcb, hpinv, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hn'⟩ := hcon
  have hlt : (dropOf c F).val < n := by
    have := (dropOf c F).isLt
    omega
  apply hpinv
  rw [partnerCell_of_internal hn c h0 hn']
  simpa [cellValid] using mem_cells.mp hc

theorem boundary_singleton_invalid {n k : ℕ} (hn : 0 < n)
    {F : Finset (Fin n → ℤ)} (hb : isBoundary hn k F) :
    ((cells n k).filter
        (fun c => cellBounds c F ∧ ¬ cellValid k (partnerCell hn c F))).card = 1 := by
  classical
  obtain ⟨c₀, hc₀k, hc₀b, hc₀inv, hc₀end⟩ := isBoundary_endpoint hn hb
  rw [Finset.card_eq_one]
  refine ⟨c₀, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hc₀k, hc₀b, hc₀inv⟩
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hck, hcb, hcinv⟩ := hc
    have hcend : (dropOf c F).val = 0 ∨ (dropOf c F).val = n := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h0, hn'⟩ := hcon
      apply hcinv
      rw [partnerCell_of_internal hn c h0 hn']
      simpa [cellValid] using mem_cells.mp hck
    rcases bounds_endpoint_dichotomy hn hc₀b hcb hc₀end hcend with h | h
    · exact h
    · exfalso
      apply hc₀inv
      rw [← h]
      exact mem_cells.mp hck

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

theorem rainbow_count_succ_odd_of_boundary_vertices_bottom_R2 {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hbottom : ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ∀ v ∈ F, v (Fin.last n) = 0)
    (hlower : Odd ((cells n k).filter
      (fun c => isRainbow (bottomLabel L havoid) c)).card) :
    Odd ((cells (n + 1) k).filter (fun c => isRainbow L c)).card := by
  exact rainbow_count_succ_odd_of_boundary_vertices_bottom hk L havoid
    (fun _F _hF _hdoor hb => boundary_singleton_invalid (Nat.succ_pos n) hb)
    hbottom hlower

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

/-- Recursive boundary data after the Freudenthal R2 singleton has been proved internally. -/
def BoundaryBottomData : (n k : ℕ) → Label n → Prop
  | 0, _k, _L => True
  | n + 1, k, L =>
      ∃ havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1),
        (∀ F ∈ facets (n + 1) k,
          (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
            isBoundary (Nat.succ_pos n) k F →
              ∀ v ∈ F, v (Fin.last n) = 0) ∧
        BoundaryBottomData n k (bottomLabel L havoid)

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

/-- Recursive rainbow parity using the Freudenthal R2 singleton internally. -/
theorem rainbow_count_odd_of_boundaryBottomData {n k : ℕ} (hk : 0 < k)
    (L : Label n) (hdata : BoundaryBottomData n k L) :
    Odd ((cells n k).filter (fun c => isRainbow L c)).card := by
  induction n with
  | zero =>
      exact rainbow_count_zero_odd k L
  | succ n ih =>
      rcases hdata with ⟨havoid, hbottom, hlower⟩
      exact rainbow_count_succ_odd_of_boundary_vertices_bottom_R2 hk L havoid
        hbottom (ih (bottomLabel L havoid) hlower)

/-- Recursive parity for the boundary-compatible box bottom doors. -/
theorem bottomDoors_odd_of_boundaryData {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hdata : BoundaryData n k (bottomLabel L havoid)) :
    Odd (bottomDoors n k L).card := by
  rw [card_bottomDoors_eq_rainbow hk L havoid]
  exact rainbow_count_odd_of_boundaryData hk (bottomLabel L havoid) hdata

theorem bottomDoors_odd_of_boundaryBottomData {n k : ℕ} (hk : 0 < k)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 2))
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1))
    (hdata : BoundaryBottomData n k (bottomLabel L havoid)) :
    Odd (bottomDoors n k L).card := by
  rw [card_bottomDoors_eq_rainbow hk L havoid]
  exact rainbow_count_odd_of_boundaryBottomData hk (bottomLabel L havoid) hdata

theorem exists_rainbow_cellF_of_boundaryData {n k : ℕ} (hk : 0 < k)
    (L : Label n) (hdata : BoundaryData n k L) :
    ∃ c ∈ cells n k, isRainbow L c := by
  classical
  have hodd := rainbow_count_odd_of_boundaryData hk L hdata
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hodd.pos
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem exists_rainbow_cellF_of_boundaryBottomData {n k : ℕ} (hk : 0 < k)
    (L : Label n) (hdata : BoundaryBottomData n k L) :
    ∃ c ∈ cells n k, isRainbow L c := by
  classical
  have hodd := rainbow_count_odd_of_boundaryBottomData hk L hdata
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hodd.pos
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.1, hc.2⟩

/-! ## Transport to the barycentric Kuhn carrier

The finite-dimensional Brouwer layer uses barycentric Kuhn cells
`KCell n = (Fin (n+1) → ℤ) × Perm (Fin n)`: one coordinate is the slack
coordinate removed by `dropLast`.  A Freudenthal `Cell n` represents the first
`n` barycentric coordinates; the missing coordinate is `k - ∑ i, p i`.
-/

/-- Add the barycentric slack coordinate to a Freudenthal base. -/
def appendSlack {n : ℕ} (k : ℕ) (p : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.snoc p ((k : ℤ) - ∑ i, p i)

@[simp] theorem appendSlack_castSucc {n k : ℕ} (p : Fin n → ℤ) (i : Fin n) :
    appendSlack k p i.castSucc = p i := by
  simp [appendSlack]

@[simp] theorem appendSlack_last {n k : ℕ} (p : Fin n → ℤ) :
    appendSlack k p (Fin.last n) = (k : ℤ) - ∑ i, p i := by
  simp [appendSlack]

theorem sum_appendSlack {n k : ℕ} (p : Fin n → ℤ) :
    ∑ i : Fin (n + 1), appendSlack k p i = (k : ℤ) := by
  rw [Fin.sum_univ_castSucc]
  simp [appendSlack]

/-! ### The old zero-door base projection

For an old barycentric zero-door cell in dimension `m + 1`, the first upper step becomes
the slack coordinate of the lower Freudenthal chart.  The remaining tail steps, after the
coordinate rotation `faceCoordPerm`, form a literal `m`-dimensional Freudenthal chain.
-/

/-- The lower Freudenthal base obtained from an old zero-door cell by deleting the first
face step (the future slack coordinate) and the old last barycentric coordinate. -/
def oldZeroDoorLowerBase {m : ℕ} (c : ShenWork.Paper1.KCell (m + 1)) :
    Fin m → ℤ :=
  fun i => c.1 ((c.2 i.succ).castSucc)

/-- The lower Freudenthal cell underlying an old zero-door cell, in the rotated chart. -/
def oldZeroDoorLowerCell {m : ℕ} (c : ShenWork.Paper1.KCell (m + 1)) :
    Cell m :=
  (oldZeroDoorLowerBase c, 1)

/-- The post-projection colour set on an old drop-`0` door facet.

Each old drop-`0` vertex first transfers its last-coordinate mass to the first face step, then
is relabelled on the literal face `{last = 0}`.  This is the boundary label needed for the
dimension-drop parity, unlike the legacy pre-transition door below. -/
noncomputable def zeroDoorPostLabels {n : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : ShenWork.Paper1.KCell n) :
    Finset (Fin (n + 1)) :=
  (Finset.univ : Finset (Fin n)).image
    (fun u => L (appendZero (ShenWork.Paper1.zeroDoorFaceVertex c u)))

/-- After transferring the old last-coordinate mass to the first face step and rotating
coordinates, every non-slack coordinate is exactly the lower Freudenthal chain vertex. -/
theorem zeroDoorFaceVertex_pull_castSucc {m : ℕ}
    (c : ShenWork.Paper1.KCell (m + 1)) (u : Fin (m + 1)) (i : Fin m) :
    ShenWork.Paper1.pullCoord (ShenWork.Paper1.faceCoordPerm c.2)
      (ShenWork.Paper1.zeroDoorFaceVertex c u) i.castSucc =
      chainVZ (oldZeroDoorLowerCell c).1 (oldZeroDoorLowerCell c).2 u i := by
  classical
  unfold ShenWork.Paper1.pullCoord ShenWork.Paper1.zeroDoorFaceVertex
  rw [ShenWork.Paper1.faceCoordPerm_castSucc]
  unfold ShenWork.Paper1.transferLastMass
  have hneDonor : c.2 i.succ ≠ c.2 (ShenWork.Paper1.finZeroOf u) := by
    intro h
    have hpre := c.2.injective h
    have hval := congrArg Fin.val hpre
    simp [ShenWork.Paper1.finZeroOf_val, Fin.val_succ] at hval
  rw [ShenWork.Paper1.faceUnitVec_apply_ne hneDonor]
  simp only [mul_zero, add_zero]
  rw [ShenWork.Paper1.dropLast_chainVZ_count]
  unfold oldZeroDoorLowerCell oldZeroDoorLowerBase chainVZ
  change c.1 ((c.2 i.succ).castSucc) +
      (if ((c.2.symm (c.2 i.succ)).val : ℕ) < u.succ.val then (1 : ℤ) else 0) =
    c.1 ((c.2 i.succ).castSucc) + if (i.val : ℕ) < u.val then 1 else 0
  rw [Equiv.symm_apply_apply]
  have hiff : ((i.succ).val < u.succ.val) ↔ (i.val < u.val) := by
    change i.val + 1 < u.val + 1 ↔ i.val < u.val
    omega
  by_cases h : i.val < u.val
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hlt => h (hiff.mp hlt)), if_neg h]

/-- Coordinate pullback by a permutation preserves the coordinate sum. -/
theorem sum_pullCoord {n : ℕ} (ρ : Equiv.Perm (Fin n)) (v : Fin n → ℤ) :
    ∑ i : Fin n, ShenWork.Paper1.pullCoord ρ v i = ∑ i : Fin n, v i := by
  unfold ShenWork.Paper1.pullCoord
  exact Equiv.sum_comp ρ v

/-- Undo `pullCoord ρ`; equivalently compose with `ρ.symm`. -/
def unpullCoord {n : ℕ} (ρ : Equiv.Perm (Fin n)) (v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => v (ρ.symm i)

theorem pullCoord_unpullCoord {n : ℕ} (ρ : Equiv.Perm (Fin n)) (v : Fin n → ℤ) :
    ShenWork.Paper1.pullCoord ρ (unpullCoord ρ v) = v := by
  funext i
  unfold ShenWork.Paper1.pullCoord unpullCoord
  rw [Equiv.symm_apply_apply]

theorem unpullCoord_pullCoord {n : ℕ} (ρ : Equiv.Perm (Fin n)) (v : Fin n → ℤ) :
    unpullCoord ρ (ShenWork.Paper1.pullCoord ρ v) = v := by
  funext i
  change v (ρ (ρ.symm i)) = v i
  rw [Equiv.apply_symm_apply]

/-- The lower face label obtained by rotating a face point back to the original upper
coordinates and appending a zero last coordinate.  If the upper label accidentally returns the
forbidden top colour, this total label defaults to `0`; on valid Sperner face vertices the
forbidden case is proved impossible before this label is used. -/
noncomputable def postProjectedLowerLabel {m : ℕ} (k : ℕ)
    (L : (Fin (m + 2) → ℤ) → Fin (m + 2))
    (ρ : Equiv.Perm (Fin (m + 1))) : Label m :=
  fun v =>
    if h : L (appendZero (unpullCoord ρ (appendSlack k v))) ≠ Fin.last (m + 1) then
      (L (appendZero (unpullCoord ρ (appendSlack k v)))).castPred h
    else 0

theorem postProjectedLowerLabel_castSucc_of_ne {m k : ℕ}
    (L : (Fin (m + 2) → ℤ) → Fin (m + 2))
    (ρ : Equiv.Perm (Fin (m + 1))) {v : Fin m → ℤ}
    (h : L (appendZero (unpullCoord ρ (appendSlack k v))) ≠ Fin.last (m + 1)) :
    (postProjectedLowerLabel k L ρ v).castSucc =
      L (appendZero (unpullCoord ρ (appendSlack k v))) := by
  unfold postProjectedLowerLabel
  rw [dif_pos h, Fin.castSucc_castPred]

/-- The full post-projected zero-door vertex is the lower Freudenthal vertex plus slack,
after rotating face coordinates by `faceCoordPerm`. -/
theorem zeroDoorFaceVertex_pull_eq_appendSlack {m k : ℕ}
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c) (u : Fin (m + 1)) :
    ShenWork.Paper1.pullCoord (ShenWork.Paper1.faceCoordPerm c.2)
        (ShenWork.Paper1.zeroDoorFaceVertex c u) =
      appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
        (oldZeroDoorLowerCell c).2 u) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · have hsumL :
        ∑ i : Fin (m + 1),
            ShenWork.Paper1.pullCoord (ShenWork.Paper1.faceCoordPerm c.2)
              (ShenWork.Paper1.zeroDoorFaceVertex c u) i = (k : ℤ) := by
      rw [sum_pullCoord]
      exact ShenWork.Paper1.zeroDoorFaceVertex_sum hc u
    have hsumR :
        ∑ i : Fin (m + 1),
            appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
              (oldZeroDoorLowerCell c).2 u) i = (k : ℤ) := by
      exact sum_appendSlack _
    have hcast : ∀ i : Fin m,
        ShenWork.Paper1.pullCoord (ShenWork.Paper1.faceCoordPerm c.2)
            (ShenWork.Paper1.zeroDoorFaceVertex c u) i.castSucc =
          appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
            (oldZeroDoorLowerCell c).2 u) i.castSucc := by
      intro i
      rw [zeroDoorFaceVertex_pull_castSucc, appendSlack_castSucc]
    rw [Fin.sum_univ_castSucc] at hsumL
    rw [Fin.sum_univ_castSucc] at hsumR
    have hprefix :
        (∑ i : Fin m,
            ShenWork.Paper1.pullCoord (ShenWork.Paper1.faceCoordPerm c.2)
              (ShenWork.Paper1.zeroDoorFaceVertex c u) i.castSucc)
          =
        (∑ i : Fin m,
            appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
              (oldZeroDoorLowerCell c).2 u) i.castSucc) := by
      exact Finset.sum_congr rfl (fun i _hi => hcast i)
    rw [hprefix] at hsumL
    linarith
  · intro i
    rw [appendSlack_castSucc]
    exact zeroDoorFaceVertex_pull_castSucc c u i

theorem postProjectedLowerLabel_cellColor_castSucc {m k : ℕ}
    (L : (Fin (m + 2) → ℤ) → Fin (m + 2))
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c) (u : Fin (m + 1))
    (havoid :
      L (appendZero
        (unpullCoord (ShenWork.Paper1.faceCoordPerm c.2)
          (appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
            (oldZeroDoorLowerCell c).2 u)))) ≠ Fin.last (m + 1)) :
    (cellColor
        (postProjectedLowerLabel k L (ShenWork.Paper1.faceCoordPerm c.2))
        (oldZeroDoorLowerCell c) u).castSucc =
      L (appendZero (ShenWork.Paper1.zeroDoorFaceVertex c u)) := by
  unfold cellColor
  rw [postProjectedLowerLabel_castSucc_of_ne L _ havoid]
  have hproj := zeroDoorFaceVertex_pull_eq_appendSlack (c := c) hc u
  have hunpull := congrArg (unpullCoord (ShenWork.Paper1.faceCoordPerm c.2)) hproj
  rw [unpullCoord_pullCoord] at hunpull
  rw [← hunpull]

theorem image_castSucc_eq_erase_last_iff_bijective {n : ℕ}
    (g : Fin n → Fin n) :
    ((Finset.univ : Finset (Fin n)).image (fun u => (g u).castSucc) =
        Finset.univ.erase (Fin.last n))
      ↔ Function.Bijective g := by
  classical
  constructor
  · intro h
    have hsurj : Function.Surjective g := by
      intro y
      have hy : y.castSucc ∈ Finset.univ.erase (Fin.last n) := by
        rw [Finset.mem_erase]
        exact ⟨Fin.castSucc_ne_last y, Finset.mem_univ _⟩
      rw [← h] at hy
      rw [Finset.mem_image] at hy
      obtain ⟨u, _hu, hgu⟩ := hy
      exact ⟨u, Fin.castSucc_injective _ hgu⟩
    exact ⟨Function.Surjective.injective_of_finite (Equiv.refl _) hsurj, hsurj⟩
  · intro hbij
    ext y
    constructor
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨u, _hu, rfl⟩ := hy
      rw [Finset.mem_erase]
      exact ⟨Fin.castSucc_ne_last (g u), Finset.mem_univ _⟩
    · intro hy
      rw [Finset.mem_erase] at hy
      obtain ⟨hnelast, _⟩ := hy
      obtain ⟨u, hu⟩ := hbij.2 (y.castPred hnelast)
      rw [Finset.mem_image]
      refine ⟨u, Finset.mem_univ _, ?_⟩
      rw [hu, Fin.castSucc_castPred]

theorem zeroDoorPostLabels_eq_lower_cellColor_image {m k : ℕ}
    (L : (Fin (m + 2) → ℤ) → Fin (m + 2))
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c)
    (havoid : ∀ u : Fin (m + 1),
      L (appendZero
        (unpullCoord (ShenWork.Paper1.faceCoordPerm c.2)
          (appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
            (oldZeroDoorLowerCell c).2 u)))) ≠ Fin.last (m + 1)) :
    zeroDoorPostLabels L c =
      (Finset.univ : Finset (Fin (m + 1))).image
        (fun u =>
          (cellColor
            (postProjectedLowerLabel k L (ShenWork.Paper1.faceCoordPerm c.2))
            (oldZeroDoorLowerCell c) u).castSucc) := by
  unfold zeroDoorPostLabels
  apply Finset.image_congr
  intro u _hu
  exact (postProjectedLowerLabel_cellColor_castSucc L hc u (havoid u)).symm

theorem zeroDoorPostLabels_door_iff_lower_rainbow {m k : ℕ}
    (L : (Fin (m + 2) → ℤ) → Fin (m + 2))
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c)
    (havoid : ∀ u : Fin (m + 1),
      L (appendZero
        (unpullCoord (ShenWork.Paper1.faceCoordPerm c.2)
          (appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
            (oldZeroDoorLowerCell c).2 u)))) ≠ Fin.last (m + 1)) :
    zeroDoorPostLabels L c = Finset.univ.erase (Fin.last (m + 1))
      ↔ isRainbow
        (postProjectedLowerLabel k L (ShenWork.Paper1.faceCoordPerm c.2))
        (oldZeroDoorLowerCell c) := by
  rw [zeroDoorPostLabels_eq_lower_cellColor_image L hc havoid]
  unfold isRainbow
  exact image_castSucc_eq_erase_last_iff_bijective
    (cellColor
      (postProjectedLowerLabel k L (ShenWork.Paper1.faceCoordPerm c.2))
      (oldZeroDoorLowerCell c))

theorem appendZero_toNat_sum_of_nonneg {n k : ℕ} {v : Fin n → ℤ}
    (hnn : ∀ i, 0 ≤ v i) (hsum : ∑ i : Fin n, v i = (k : ℤ)) :
    ∑ i : Fin (n + 1), (appendZero v i).toNat = k := by
  rw [Fin.sum_univ_castSucc]
  simp only [appendZero_castSucc, appendZero_last, Int.toNat_zero, add_zero]
  have hcast : ∑ i : Fin n, ((v i).toNat : ℤ) = ∑ i : Fin n, v i := by
    exact Finset.sum_congr rfl (fun i _hi => Int.toNat_of_nonneg (hnn i))
  have hNat : ((∑ i : Fin n, (v i).toNat : ℕ) : ℤ) = (k : ℤ) := by
    rw [Nat.cast_sum, hcast, hsum]
  exact_mod_cast hNat

theorem postProjectedLowerLabel_labelN_avoid {m k : ℕ}
    {f : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (m + 2)))
      (stdSimplex ℝ (Fin (m + 2))))
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c) (u : Fin (m + 1)) :
    ShenWork.Paper1.labelN f k
        (appendZero
          (unpullCoord (ShenWork.Paper1.faceCoordPerm c.2)
            (appendSlack k (chainVZ (oldZeroDoorLowerCell c).1
              (oldZeroDoorLowerCell c).2 u)))) ≠ Fin.last (m + 1) := by
  have hproj := zeroDoorFaceVertex_pull_eq_appendSlack (c := c) hc u
  have hunpull := congrArg (unpullCoord (ShenWork.Paper1.faceCoordPerm c.2)) hproj
  rw [unpullCoord_pullCoord] at hunpull
  rw [← hunpull]
  let z : Fin (m + 1) → ℤ := ShenWork.Paper1.zeroDoorFaceVertex c u
  have hsum : ∑ i : Fin (m + 2), (appendZero z i).toNat = k := by
    exact appendZero_toNat_sum_of_nonneg
      (fun i => ShenWork.Paper1.zeroDoorFaceVertex_nonneg hc u i)
      (ShenWork.Paper1.zeroDoorFaceVertex_sum hc u)
  have hzero : appendZero z (Fin.last (m + 1)) = 0 := by
    simp [z]
  exact ShenWork.Paper1.label_avoids_forbidden_coord_on_face
    (n := m + 1) hk hmaps hsum hzero

theorem zeroDoorPostLabels_labelN_door_iff_lower_rainbow {m k : ℕ}
    {f : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (m + 2)))
      (stdSimplex ℝ (Fin (m + 2))))
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c) :
    zeroDoorPostLabels (ShenWork.Paper1.labelN f k) c =
        Finset.univ.erase (Fin.last (m + 1))
      ↔ isRainbow
        (postProjectedLowerLabel k (ShenWork.Paper1.labelN f k)
          (ShenWork.Paper1.faceCoordPerm c.2))
        (oldZeroDoorLowerCell c) := by
  exact zeroDoorPostLabels_door_iff_lower_rainbow
    (ShenWork.Paper1.labelN f k) hc
    (postProjectedLowerLabel_labelN_avoid hk hmaps hc)

/-- Freudenthal cells lying in the standard simplex alcove at mesh `k`. -/
def simplexCellValid {n k : ℕ} (c : Cell n) : Prop :=
  cellValid k c ∧ (∑ i, c.1 i) + (n : ℤ) ≤ (k : ℤ)

instance {n k : ℕ} (c : Cell n) : Decidable (simplexCellValid (k := k) c) := by
  unfold simplexCellValid
  infer_instance

theorem chainVZ_nonneg_of_cellValid {n k : ℕ} {c : Cell n}
    (hc : cellValid k c) (t : Fin (n + 1)) (i : Fin n) :
    0 ≤ chainVZ c.1 c.2 t i := by
  unfold chainVZ
  by_cases h : (c.2.symm i).val < t.val
  · rw [if_pos h]
    have hi := (hc i).1
    omega
  · rw [if_neg h]
    simpa using (hc i).1

theorem old_stepVec_castSucc {n : ℕ} (a j : Fin n) :
    ShenWork.Paper1.stepVec a j.castSucc = unitVec a j := by
  unfold ShenWork.Paper1.stepVec unitVec
  have hlast : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
  by_cases hja : j = a
  · subst hja
    rw [if_pos rfl, if_pos rfl, if_neg hlast]
    ring
  · have hcast : j.castSucc ≠ a.castSucc := fun h => hja (Fin.castSucc_injective _ h)
    rw [if_neg hcast, if_neg hja, if_neg hlast]
    ring

/-- Dropping the slack coordinate from the old barycentric Kuhn chain gives the
Freudenthal chain on the first `n` coordinates. -/
theorem dropLast_old_chainVZ_appendSlack {n k : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    dropLast (ShenWork.Paper1.chainVZ (appendSlack k p) σ t) = chainVZ p σ t := by
  classical
  funext j
  change ShenWork.Paper1.chainVZ (appendSlack k p) σ t j.castSucc = chainVZ p σ t j
  unfold ShenWork.Paper1.chainVZ chainVZ
  rw [appendSlack_castSucc]
  congr 1
  have hfilter :
      (Finset.univ.filter (fun s : Fin n => s.castSucc.val < t.val))
        = (Finset.univ.filter (fun s : Fin n => s.val < t.val)) := by
    apply Finset.filter_congr
    intro s _
    rfl
  rw [hfilter]
  rw [Finset.sum_congr rfl (fun s _hs => old_stepVec_castSucc (σ s) j)]
  by_cases hin : (σ.symm j).val < t.val
  · rw [if_pos hin]
    rw [Finset.sum_eq_single (σ.symm j)]
    · rw [Equiv.apply_symm_apply]
      unfold unitVec
      rw [if_pos rfl]
    · intro s _hs hs
      unfold unitVec
      have hne : j ≠ σ s := by
        intro h
        have hsymm : σ.symm j = s := by
          rw [h, Equiv.symm_apply_apply]
        exact hs hsymm.symm
      rw [if_neg hne]
    · intro hnot
      exact absurd
        (Finset.mem_filter.mpr ⟨Finset.mem_univ (σ.symm j), hin⟩) hnot
  · rw [if_neg hin]
    rw [Finset.sum_eq_zero]
    intro s hs
    unfold unitVec
    have hne : j ≠ σ s := by
      intro h
      apply hin
      have hsymm : σ.symm j = s := by
        rw [h, Equiv.symm_apply_apply]
      rw [hsymm]
      exact (Finset.mem_filter.mp hs).2
    rw [if_neg hne]

theorem old_chainVZ_last_appendSlack {n k : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    ShenWork.Paper1.chainVZ (appendSlack k p) σ t (Fin.last n)
      = (k : ℤ) - ∑ i, p i - (t.val : ℤ) := by
  rw [ShenWork.Paper1.chainVZ_last, appendSlack_last]

/-- A Freudenthal simplex-alcove cell gives a valid old barycentric Kuhn cell. -/
theorem old_cellValid_of_simplexCellValid {n k : ℕ} {c : Cell n}
    (hc : simplexCellValid (k := k) c) :
    ShenWork.Paper1.cellValid k (appendSlack k c.1) c.2 := by
  constructor
  · exact sum_appendSlack c.1
  · intro t i
    refine Fin.lastCases ?_ ?_ i
    · rw [old_chainVZ_last_appendSlack]
      have ht : (t.val : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast (Nat.le_of_lt_succ t.isLt)
      linarith [hc.2, ht]
    · intro j
      have hdrop := congrFun (dropLast_old_chainVZ_appendSlack (k := k) c.1 c.2 t) j
      rw [dropLast_apply] at hdrop
      rw [hdrop]
      exact chainVZ_nonneg_of_cellValid hc.1 t j

theorem simplexCellValid_of_old_cellValid {n k : ℕ} (hn : 0 < n)
    {p : Fin (n + 1) → ℤ} {σ : Equiv.Perm (Fin n)}
    (hc : ShenWork.Paper1.cellValid k p σ) :
    simplexCellValid (k := k) (dropLast p, σ) := by
  constructor
  · intro i
    have hbox := ShenWork.Paper1.cellValid_base_mem_box hc i.castSucc
    refine ⟨hbox.1, ?_⟩
    have hlast_ge := ShenWork.Paper1.cellValid_last_ge hc
    have hsum :
        (∑ j : Fin n, p j.castSucc) + p (Fin.last n) = (k : ℤ) := by
      simpa [Fin.sum_univ_castSucc] using hc.1
    have hpi_le : p i.castSucc ≤ (k : ℤ) - (n : ℤ) := by
      have hle_first : p i.castSucc ≤ ∑ j : Fin n, p j.castSucc := by
        refine Finset.single_le_sum (f := fun j : Fin n => p j.castSucc) ?_
          (Finset.mem_univ i)
        intro j _hj
        exact (ShenWork.Paper1.cellValid_base_mem_box hc j.castSucc).1
      linarith
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    simpa [dropLast] using (lt_of_le_of_lt hpi_le (by linarith))
  · have hsum_drop :
        (∑ i : Fin n, dropLast p i) + p (Fin.last n) = (k : ℤ) := by
      have hsum :
          (∑ i : Fin n, p i.castSucc) + p (Fin.last n) = (k : ℤ) := by
        simpa [Fin.sum_univ_castSucc] using hc.1
      simpa [dropLast] using hsum
    have hlast_ge := ShenWork.Paper1.cellValid_last_ge hc
    linarith

/-- The lower tail cell extracted from an old zero-door cell is a valid Freudenthal box cell. -/
theorem oldZeroDoorLowerCell_cellValid {m k : ℕ}
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c) :
    cellValid k (oldZeroDoorLowerCell c) := by
  have hsimple : simplexCellValid (k := k) (dropLast c.1, c.2) :=
    simplexCellValid_of_old_cellValid (Nat.succ_pos m)
      (by simpa [ShenWork.Paper1.cellMemN] using hc)
  intro i
  have hi := hsimple.1 (c.2 i.succ)
  simpa [oldZeroDoorLowerCell, oldZeroDoorLowerBase, dropLast] using hi

/-- Membership form of `oldZeroDoorLowerCell_cellValid`. -/
theorem oldZeroDoorLowerCell_mem_cells {m k : ℕ}
    {c : ShenWork.Paper1.KCell (m + 1)}
    (hc : ShenWork.Paper1.cellMemN k c) :
    oldZeroDoorLowerCell c ∈ cells m k :=
  mem_cells.mpr (oldZeroDoorLowerCell_cellValid hc)

/-- Valid Freudenthal cells in the simplex alcove, as a finite set. -/
noncomputable def simplexCells (n k : ℕ) : Finset (Cell n) :=
  (cells n k).filter (fun c => (∑ i, c.1 i) + (n : ℤ) ≤ (k : ℤ))

theorem mem_simplexCells {n k : ℕ} {c : Cell n} :
    c ∈ simplexCells n k ↔ simplexCellValid (k := k) c := by
  rw [simplexCells, Finset.mem_filter, mem_cells]
  rfl

/-- The old barycentric carrier associated to a Freudenthal simplex cell. -/
def toKCell {n : ℕ} (k : ℕ) (c : Cell n) : ShenWork.Paper1.KCell n :=
  (appendSlack k c.1, c.2)

theorem appendSlack_dropLast_of_sum {n k : ℕ} {p : Fin (n + 1) → ℤ}
    (hsum : ∑ i, p i = (k : ℤ)) : appendSlack k (dropLast p) = p := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hsum' :
        (∑ j : Fin n, p j.castSucc) + p (Fin.last n) = (k : ℤ) := by
      simpa [Fin.sum_univ_castSucc] using hsum
    rw [appendSlack_last]
    change (k : ℤ) - ∑ x : Fin n, p x.castSucc = p (Fin.last n)
    linarith
  · intro j
    rw [appendSlack_castSucc, dropLast_apply]

theorem image_simplexCells_toKCell_eq_cellsN {n k : ℕ} (hn : 0 < n) :
    (simplexCells n k).image (toKCell k) = ShenWork.Paper1.cellsN n k := by
  classical
  ext c
  constructor
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    rw [ShenWork.Paper1.mem_cellsN]
    exact old_cellValid_of_simplexCellValid (mem_simplexCells.mp hd)
  · intro hc
    have hcvalid := ShenWork.Paper1.mem_cellsN.mp hc
    let d : Cell n := (dropLast c.1, c.2)
    have hdvalid : simplexCellValid (k := k) d :=
      simplexCellValid_of_old_cellValid hn hcvalid
    rw [Finset.mem_image]
    refine ⟨d, mem_simplexCells.mpr hdvalid, ?_⟩
    unfold toKCell d
    apply Prod.ext
    · exact appendSlack_dropLast_of_sum hcvalid.1
    · rfl

theorem old_chainVZ_appendSlack_eq {n k : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    ShenWork.Paper1.chainVZ (appendSlack k p) σ t = appendSlack k (chainVZ p σ t) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [old_chainVZ_last_appendSlack, appendSlack_last, sum_chainVZ]
    ring
  · intro j
    have hdrop := congrFun (dropLast_old_chainVZ_appendSlack (k := k) p σ t) j
    rw [dropLast_apply] at hdrop
    simpa [appendSlack] using hdrop

theorem old_facetSet_appendSlack_eq {n k : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    ShenWork.Paper1.facetSet (appendSlack k p) σ t =
      (facetSet p σ t).image (appendSlack k) := by
  classical
  unfold ShenWork.Paper1.facetSet facetSet
  rw [Finset.image_image]
  apply Finset.image_congr
  intro u _hu
  exact old_chainVZ_appendSlack_eq p σ u

/-! ### Slack-face audit for the current simplex-alcove carrier

The current `simplexCells` carrier is the first-coordinate chart transported to the older
barycentric Kuhn cells.  Its codimension-one facets are not literal facets of the slack face
`appendSlack k v (Fin.last n) = 0` once `2 ≤ n`: the vertices of a Freudenthal facet have
different coordinate sums.  The real simplex slack-face recursion therefore needs a different
boundary-compatible type-A carrier, not just the `simplexCells` filter below.
-/

theorem appendSlack_chainVZ_last {n k : ℕ} (p : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) (t : Fin (n + 1)) :
    appendSlack k (chainVZ p σ t) (Fin.last n) =
      (k : ℤ) - ∑ i, p i - (t.val : ℤ) := by
  rw [appendSlack_last, sum_chainVZ]
  ring

theorem no_simplexFacet_all_slack_zero_of_two_le {n k : ℕ} (hn : 2 ≤ n)
    (c : Cell n) (t : Fin (n + 1)) :
    ¬ (∀ v ∈ facetSet c.1 c.2 t, appendSlack k v (Fin.last n) = 0) := by
  classical
  intro hslack
  let z : Fin (n + 1) := ⟨0, by omega⟩
  let o : Fin (n + 1) := ⟨1, by omega⟩
  let tw : Fin (n + 1) := ⟨2, by omega⟩
  have hzo : z.val ≠ o.val := by simp [z, o]
  have hzt : z.val ≠ tw.val := by simp [z, tw]
  have hot : o.val ≠ tw.val := by simp [o, tw]
  have vertex_slack_eq :
      ∀ u : Fin (n + 1), u ≠ t →
        (k : ℤ) - ∑ i, c.1 i - (u.val : ℤ) = 0 := by
    intro u hut
    have hu : chainVZ c.1 c.2 u ∈ facetSet c.1 c.2 t :=
      (mem_facetSet_iff c.1 c.2 t u).mpr hut
    have hs := hslack (chainVZ c.1 c.2 u) hu
    rw [appendSlack_chainVZ_last] at hs
    exact hs
  have pair_equal :
      ∀ u v : Fin (n + 1), u ≠ t → v ≠ t → (u.val : ℤ) = (v.val : ℤ) := by
    intro u v hut hvt
    have hu := vertex_slack_eq u hut
    have hv := vertex_slack_eq v hvt
    linarith
  by_cases ht0 : t.val = 0
  · have ho_ne : o ≠ t := fun h => by
      have hv := congrArg Fin.val h
      simp [o] at hv
      omega
    have htw_ne : tw ≠ t := fun h => by
      have hv := congrArg Fin.val h
      simp [tw] at hv
      omega
    have hvals := pair_equal o tw ho_ne htw_ne
    have hNat : o.val = tw.val := by exact_mod_cast hvals
    exact hot hNat
  · by_cases ht1 : t.val = 1
    · have hz_ne : z ≠ t := fun h => by
        have hv := congrArg Fin.val h
        simp [z] at hv
        omega
      have htw_ne : tw ≠ t := fun h => by
        have hv := congrArg Fin.val h
        simp [tw] at hv
        omega
      have hvals := pair_equal z tw hz_ne htw_ne
      have hNat : z.val = tw.val := by exact_mod_cast hvals
      exact hzt hNat
    · have hz_ne : z ≠ t := fun h => by
        have hv := congrArg Fin.val h
        simp [z] at hv
        omega
      have ho_ne : o ≠ t := fun h => by
        have hv := congrArg Fin.val h
        simp [o] at hv
        omega
      have hvals := pair_equal z o hz_ne ho_ne
      have hNat : z.val = o.val := by exact_mod_cast hvals
      exact hzo hNat

/-! ## Pulling old barycentric colours back to simplex alcoves -/

theorem toKCell_injective {n k : ℕ} :
    Function.Injective (toKCell (n := n) k) := by
  intro c d hcd
  apply Prod.ext
  · funext i
    have hp := congrArg Prod.fst hcd
    have hi := congrFun hp i.castSucc
    simpa [toKCell] using hi
  · exact congrArg (fun x : ShenWork.Paper1.KCell n => x.2) hcd

/-- Pull an old barycentric labelling back to the Freudenthal simplex chart. -/
def pullLabel {n : ℕ} (k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) : Label n :=
  fun v => L (appendSlack k v)

theorem cellColorN_toKCell {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : Cell n) :
    ShenWork.Paper1.cellColorN L (toKCell k c) =
      cellColor (pullLabel k L) c := by
  funext t
  unfold ShenWork.Paper1.cellColorN cellColor pullLabel toKCell
  rw [old_chainVZ_appendSlack_eq]

theorem rainbow_toKCell_iff {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : Cell n) :
    Function.Bijective (ShenWork.Paper1.cellColorN L (toKCell k c))
      ↔ isRainbow (pullLabel k L) c := by
  rw [cellColorN_toKCell]
  rfl

theorem image_simplex_rainbow_eq_cellsN_rainbow {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    ((simplexCells n k).filter (fun c => isRainbow (pullLabel k L) c)).image
        (toKCell k)
      =
    (ShenWork.Paper1.cellsN n k).filter
        (fun c => Function.Bijective (ShenWork.Paper1.cellColorN L c)) := by
  classical
  ext c
  constructor
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, hdc⟩ := hc
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [← image_simplexCells_toKCell_eq_cellsN hn]
      exact Finset.mem_image.mpr ⟨d, hd.1, hdc⟩
    · rw [← hdc]
      exact (rainbow_toKCell_iff L d).mpr hd.2
  · intro hc
    rw [Finset.mem_filter] at hc
    rw [← image_simplexCells_toKCell_eq_cellsN hn] at hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, hdc⟩ := hc.1
    rw [Finset.mem_image]
    refine ⟨d, ?_, hdc⟩
    rw [Finset.mem_filter]
    refine ⟨hd, ?_⟩
    rw [← hdc] at hc
    exact (rainbow_toKCell_iff L d).mp hc.2

theorem card_simplex_rainbow_eq_cellsN_rainbow {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    ((simplexCells n k).filter (fun c => isRainbow (pullLabel k L) c)).card =
      ((ShenWork.Paper1.cellsN n k).filter
        (fun c => Function.Bijective (ShenWork.Paper1.cellColorN L c))).card := by
  rw [← image_simplex_rainbow_eq_cellsN_rainbow hn L]
  exact (Finset.card_image_of_injective _ toKCell_injective).symm

theorem cellsN_rainbow_odd_of_simplex_rainbow_odd {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1))
    (hodd : Odd ((simplexCells n k).filter
      (fun c => isRainbow (pullLabel k L) c)).card) :
    Odd ((ShenWork.Paper1.cellsN n k).filter
      (fun c => Function.Bijective (ShenWork.Paper1.cellColorN L c))).card := by
  rw [← card_simplex_rainbow_eq_cellsN_rainbow hn L]
  exact hodd

theorem exists_cellsN_rainbow_of_simplex_rainbow_odd {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1))
    (hodd : Odd ((simplexCells n k).filter
      (fun c => isRainbow (pullLabel k L) c)).card) :
    ∃ c ∈ ShenWork.Paper1.cellsN n k,
      Function.Bijective (ShenWork.Paper1.cellColorN L c) := by
  classical
  have hold := cellsN_rainbow_odd_of_simplex_rainbow_odd hn L hodd
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hold.pos
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.1, hc.2⟩

/-! ## Transporting simplex-alcove facets to the old barycentric carrier -/

theorem appendSlack_injective {n k : ℕ} :
    Function.Injective (appendSlack (n := n) k) := by
  intro v w hvw
  funext i
  have hi := congrFun hvw i.castSucc
  simpa [appendSlack] using hi

@[simp] theorem dropLast_appendSlack {n k : ℕ} (v : Fin n → ℤ) :
    dropLast (appendSlack k v) = v := by
  funext i
  rw [dropLast_apply, appendSlack_castSucc]

/-- Facets of the Freudenthal simplex-alcove subcomplex. -/
noncomputable def simplexFacets (n k : ℕ) : Finset (Finset (Fin n → ℤ)) :=
  ((simplexCells n k).product Finset.univ).image
    (fun ct : Cell n × Fin (n + 1) => facetSet ct.1.1 ct.1.2 ct.2)

theorem mem_simplexFacets_of_bounds {n k : ℕ} {c : Cell n}
    {F : Finset (Fin n → ℤ)} (hc : c ∈ simplexCells n k)
    (hb : cellBounds c F) :
    F ∈ simplexFacets n k := by
  classical
  obtain ⟨t, rfl⟩ := hb
  unfold simplexFacets
  rw [Finset.mem_image]
  exact ⟨(c, t), Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩, rfl⟩

theorem mem_simplexFacets_iff {n k : ℕ} {F : Finset (Fin n → ℤ)} :
    F ∈ simplexFacets n k ↔ ∃ c ∈ simplexCells n k, cellBounds c F := by
  classical
  constructor
  · intro hF
    unfold simplexFacets at hF
    rw [Finset.mem_image] at hF
    obtain ⟨ct, hct, hF⟩ := hF
    have hctp := Finset.mem_product.mp hct
    refine ⟨ct.1, hctp.1, ct.2, hF⟩
  · rintro ⟨c, hc, hb⟩
    exact mem_simplexFacets_of_bounds hc hb

/-- The old barycentric facet represented by a Freudenthal simplex-alcove facet. -/
def toKFacet {n : ℕ} (k : ℕ) (F : Finset (Fin n → ℤ)) :
    Finset (Fin (n + 1) → ℤ) :=
  F.image (appendSlack k)

theorem mem_toKFacet_iff {n k : ℕ} {F : Finset (Fin n → ℤ)}
    {v : Fin n → ℤ} :
    appendSlack k v ∈ toKFacet k F ↔ v ∈ F := by
  classical
  unfold toKFacet
  constructor
  · intro hv
    rw [Finset.mem_image] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    have h : w = v := appendSlack_injective hwv
    rwa [h] at hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem toKFacet_injective {n k : ℕ} :
    Function.Injective (toKFacet (n := n) k) := by
  intro F G hFG
  ext v
  rw [← mem_toKFacet_iff (k := k) (F := F), hFG, mem_toKFacet_iff]

theorem image_toKFacet_label {n k : ℕ}
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (F : Finset (Fin n → ℤ)) :
    (toKFacet k F).image L = F.image (pullLabel k L) := by
  unfold toKFacet pullLabel
  rw [Finset.image_image]
  rfl

/-! ### Post-projection zero-door cells in the Freudenthal simplex chart -/

/-- The post-projection colour set on the transported simplex-chart drop-`0` facet. -/
noncomputable def simplexZeroDoorPostLabels (n k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) (c : Cell n) :
    Finset (Fin (n + 1)) :=
  zeroDoorPostLabels L (toKCell k c)

/-- Freudenthal simplex-chart cells whose transported old cell has last base coordinate `n`
and whose drop-`0` facet is a lower-colour door after post-projection by
`transferLastMass`. -/
noncomputable def simplexZeroDoorCells (n k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) : Finset (Cell n) :=
  (simplexCells n k).filter
    (fun c => appendSlack k c.1 (Fin.last n) = (n : ℤ) ∧
      simplexZeroDoorPostLabels n k L c = Finset.univ.erase (Fin.last n))

/-! ### The legacy pre-projection zero-door cells in the Freudenthal simplex chart -/

/-- Legacy pre-projection door cells.  This is kept only for comparison with the old
`zeroDoorCellsN`; it is false as the recursive parity target. -/
noncomputable def simplexZeroDoorCellsOld (n k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) : Finset (Cell n) :=
  (simplexCells n k).filter
    (fun c => appendSlack k c.1 (Fin.last n) = (n : ℤ) ∧
      (facetSet c.1 c.2 0).image (pullLabel k L) =
        Finset.univ.erase (Fin.last n))

/-- The discrete label induced by the sanity-check map
`(x₀,x₁,x₂) ↦ (x₀,x₁+x₂,0)` at `n = 2`. -/
def counterexampleLabelN2 (q : Fin 3 → ℤ) : Fin 3 :=
  if 0 < q 0 then 0
  else if 0 < q 1 ∧ q 2 = 0 then 1
  else 2

theorem counterexampleLabelN2_simplexZeroDoorCells_card :
    (simplexZeroDoorCells 2 2 counterexampleLabelN2).card = 1 := by
  decide

theorem counterexampleLabelN2_simplexZeroDoorCellsOld_card :
    (simplexZeroDoorCellsOld 2 2 counterexampleLabelN2).card = 0 := by
  decide

/-- The post-projection box label for the sanity-check map on the bottom face:
`(a,b,2-a-b)` is relabelled after moving the slack mass to the middle coordinate. -/
def counterexampleBoxPostLabelN2 (v : Fin 2 → ℤ) : Fin 3 :=
  counterexampleLabelN2 ![v 0, (2 : ℤ) - v 0, 0]

theorem counterexampleLabelN2_boxBottomDoors_card :
    (bottomDoors 1 2 counterexampleBoxPostLabelN2).card = 1 := by
  decide

theorem counterexampleLabelN2_boxBottomDoors_odd :
    Odd (bottomDoors 1 2 counterexampleBoxPostLabelN2).card := by
  rw [counterexampleLabelN2_boxBottomDoors_card]
  exact ⟨0, rfl⟩

theorem image_simplexZeroDoorCellsOld_toKCell_eq_zeroDoorCellsN {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    (simplexZeroDoorCellsOld n k L).image (toKCell k) =
      ShenWork.Paper1.zeroDoorCellsN n k L := by
  classical
  ext c
  constructor
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, hdc⟩ := hc
    rw [simplexZeroDoorCellsOld, Finset.mem_filter] at hd
    rw [ShenWork.Paper1.zeroDoorCellsN, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [← image_simplexCells_toKCell_eq_cellsN hn]
      exact Finset.mem_image.mpr ⟨d, hd.1, hdc⟩
    · rw [← hdc]
      exact hd.2.1
    · rw [← hdc]
      unfold toKCell
      change (ShenWork.Paper1.facetSet (appendSlack k d.1) d.2 0).image L =
        Finset.univ.erase (Fin.last n)
      rw [old_facetSet_appendSlack_eq]
      change (toKFacet k (facetSet d.1 d.2 0)).image L =
        Finset.univ.erase (Fin.last n)
      rw [image_toKFacet_label]
      exact hd.2.2
  · intro hc
    rw [ShenWork.Paper1.zeroDoorCellsN, Finset.mem_filter] at hc
    rw [← image_simplexCells_toKCell_eq_cellsN hn] at hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, hdc⟩ := hc.1
    rw [Finset.mem_image]
    refine ⟨d, ?_, hdc⟩
    rw [simplexZeroDoorCellsOld, Finset.mem_filter]
    refine ⟨hd, ?_, ?_⟩
    · rw [← hdc] at hc
      exact hc.2.1
    · rw [← hdc] at hc
      have hdoorOld : (ShenWork.Paper1.facetSet (appendSlack k d.1) d.2 0).image L =
          Finset.univ.erase (Fin.last n) := by
        simpa [toKCell] using hc.2.2
      rw [old_facetSet_appendSlack_eq] at hdoorOld
      change (toKFacet k (facetSet d.1 d.2 0)).image L =
        Finset.univ.erase (Fin.last n) at hdoorOld
      rw [image_toKFacet_label] at hdoorOld
      exact hdoorOld

theorem card_simplexZeroDoorCellsOld_eq_zeroDoorCellsN {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    (simplexZeroDoorCellsOld n k L).card =
      (ShenWork.Paper1.zeroDoorCellsN n k L).card := by
  rw [← image_simplexZeroDoorCellsOld_toKCell_eq_zeroDoorCellsN hn L]
  exact (Finset.card_image_of_injective _ toKCell_injective).symm

theorem hR3_labelN_of_simplexZeroDoorCellsOld_odd {n k : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
      (stdSimplex ℝ (Fin (n + 1))))
    (hodd : Odd (simplexZeroDoorCellsOld n k (ShenWork.Paper1.labelN f k)).card) :
    Odd ((ShenWork.Paper1.facetsN n k).filter
      (fun F => (F.image (ShenWork.Paper1.labelN f k) =
          Finset.univ.erase (Fin.last n)) ∧
        ShenWork.Paper1.isBoundaryN hn k F)).card := by
  exact ShenWork.Paper1.hR3_labelN_of_zeroDoorCellsN_odd hn hk hmaps
    (by rwa [← card_simplexZeroDoorCellsOld_eq_zeroDoorCellsN hn
      (ShenWork.Paper1.labelN f k)])

theorem exists_rainbow_cellN_R2_labelN_of_simplexZeroDoorCellsOld_odd {n k : ℕ}
    (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
      (stdSimplex ℝ (Fin (n + 1))))
    (hodd : Odd (simplexZeroDoorCellsOld n k (ShenWork.Paper1.labelN f k)).card) :
    Odd ((ShenWork.Paper1.cellsN n k).filter
      (fun c => Function.Bijective
        (ShenWork.Paper1.cellColorN (ShenWork.Paper1.labelN f k) c))).card :=
  ShenWork.Paper1.exists_rainbow_cellN_R2 hn k (ShenWork.Paper1.labelN f k)
    (hR3_labelN_of_simplexZeroDoorCellsOld_odd hn hk hmaps hodd)

theorem image_simplexFacets_toKFacet_eq_facetsN {n k : ℕ} (hn : 0 < n) :
    (simplexFacets n k).image (toKFacet k) = ShenWork.Paper1.facetsN n k := by
  classical
  ext F
  constructor
  · intro hF
    rw [Finset.mem_image] at hF
    obtain ⟨G, hG, rfl⟩ := hF
    rw [mem_simplexFacets_iff] at hG
    obtain ⟨c, hc, t, ht⟩ := hG
    rw [← ht]
    have hvalid : ShenWork.Paper1.cellMemN k (toKCell k c) := by
      simpa [toKCell, ShenWork.Paper1.cellMemN] using
        old_cellValid_of_simplexCellValid (mem_simplexCells.mp hc)
    have hfacet :
        ShenWork.Paper1.facetSet (toKCell k c).1 (toKCell k c).2 t =
          toKFacet k (facetSet c.1 c.2 t) := by
      unfold toKCell toKFacet
      exact old_facetSet_appendSlack_eq c.1 c.2 t
    exact ShenWork.Paper1.mem_facetsN_of_bounds hvalid ⟨t, hfacet⟩
  · intro hF
    obtain ⟨c, hc, t, ht⟩ := ShenWork.Paper1.mem_facetsN_iff.mp hF
    have hcMem : c ∈ ShenWork.Paper1.cellsN n k := ShenWork.Paper1.mem_cellsN.mpr hc
    rw [← image_simplexCells_toKCell_eq_cellsN hn] at hcMem
    rw [Finset.mem_image] at hcMem
    obtain ⟨d, hd, hdc⟩ := hcMem
    rw [Finset.mem_image]
    refine ⟨facetSet d.1 d.2 t, ?_, ?_⟩
    · exact mem_simplexFacets_of_bounds hd ⟨t, rfl⟩
    · rw [← ht, ← hdc]
      unfold toKFacet toKCell
      exact (old_facetSet_appendSlack_eq d.1 d.2 t).symm

/-! ## Sperner parity on the Freudenthal simplex-alcove subcomplex -/

theorem simplex_doorFacets_filter_eq {n k : ℕ}
    {L : (Fin n → ℤ) → Fin (n + 1)} {c : Cell n}
    (hc : c ∈ simplexCells n k) :
    (simplexFacets n k).filter
        (fun F => cellBounds c F ∧ F.image L = Finset.univ.erase (Fin.last n))
      = (cellFacets c).filter (fun F => F.image L = Finset.univ.erase (Fin.last n)) := by
  classical
  ext F
  simp only [Finset.mem_filter, mem_cellFacets_iff]
  constructor
  · rintro ⟨_, hb, hd⟩
    exact ⟨hb, hd⟩
  · rintro ⟨hb, hd⟩
    exact ⟨mem_simplexFacets_of_bounds hc hb, hb, hd⟩

theorem simplex_hheart {n k : ℕ}
    {L : (Fin n → ℤ) → Fin (n + 1)} {c : Cell n}
    (hc : c ∈ simplexCells n k) :
    Odd ((simplexFacets n k).filter
        (fun F => cellBounds c F ∧ F.image L = Finset.univ.erase (Fin.last n))).card
      ↔ isRainbow L c := by
  classical
  unfold isRainbow
  rw [simplex_doorFacets_filter_eq hc, ← hheart_indexed (cellColor L c)]
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

/-- A simplex-alcove facet is on the subcomplex boundary if the partner leaves
`simplexCells`. -/
def simplexBoundary {n : ℕ} (hn : 0 < n) (k : ℕ)
    (F : Finset (Fin n → ℤ)) : Prop :=
  ∃ c ∈ simplexCells n k, cellBounds c F ∧
    ¬ simplexCellValid (k := k) (partnerCell hn c F)

noncomputable instance {n k : ℕ} (hn : 0 < n) (F : Finset (Fin n → ℤ)) :
    Decidable (simplexBoundary hn k F) :=
  Classical.propDecidable _

theorem simplex_partner_valid_of_not_boundary {n k : ℕ} (hn : 0 < n)
    {F : Finset (Fin n → ℤ)} (hnb : ¬ simplexBoundary hn k F)
    {c : Cell n} (hc : c ∈ simplexCells n k) (hb : cellBounds c F) :
    simplexCellValid (k := k) (partnerCell hn c F) := by
  by_contra hbad
  exact hnb ⟨c, hc, hb, hbad⟩

theorem simplex_hinterior_of_not_boundary {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) (hnb : ¬ simplexBoundary hn k F) :
    Even ((simplexCells n k).filter (fun c => cellBounds c F)).card := by
  classical
  set S := (simplexCells n k).filter (fun c => cellBounds c F) with hS
  have hmemS : ∀ c, c ∈ S → c ∈ simplexCells n k ∧ cellBounds c F := by
    intro c hc
    rw [hS, Finset.mem_filter] at hc
    exact hc
  have g_mem : ∀ c (_ : c ∈ S), partnerCell hn c F ∈ S := by
    intro c hc
    obtain ⟨hcell, hb⟩ := hmemS c hc
    rw [hS, Finset.mem_filter]
    exact ⟨mem_simplexCells.mpr
      (simplex_partner_valid_of_not_boundary hn hnb hcell hb),
      partnerCell_bounds hn c hb⟩
  refine even_card_of_involution S (fun c _ => partnerCell hn c F) ?_ g_mem ?_
  · intro c hc
    exact partnerCell_ne hn c (hmemS c hc).2
  · intro c hc
    exact partnerCell_involutive hn c (hmemS c hc).2

theorem simplex_even_validPartner_card {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    Even ((simplexCells n k).filter
      (fun c => cellBounds c F ∧
        simplexCellValid (k := k) (partnerCell hn c F))).card := by
  classical
  set S := (simplexCells n k).filter
    (fun c => cellBounds c F ∧
      simplexCellValid (k := k) (partnerCell hn c F)) with hS
  have hmemS : ∀ c, c ∈ S →
      c ∈ simplexCells n k ∧ cellBounds c F ∧
        simplexCellValid (k := k) (partnerCell hn c F) := by
    intro c hc
    rw [hS, Finset.mem_filter] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2⟩
  have g_mem : ∀ c (_ : c ∈ S), partnerCell hn c F ∈ S := by
    intro c hc
    obtain ⟨hcell, hb, hpvalid⟩ := hmemS c hc
    rw [hS, Finset.mem_filter]
    refine ⟨mem_simplexCells.mpr hpvalid, partnerCell_bounds hn c hb, ?_⟩
    rw [partnerCell_involutive hn c hb]
    exact mem_simplexCells.mp hcell
  refine even_card_of_involution S (fun c _ => partnerCell hn c F) ?_ g_mem ?_
  · intro c hc
    exact partnerCell_ne hn c (hmemS c hc).2.1
  · intro c hc
    exact partnerCell_involutive hn c (hmemS c hc).2.1

theorem simplex_bounds_card_odd_iff_invalid {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    Odd ((simplexCells n k).filter (fun c => cellBounds c F)).card
      ↔ Odd ((simplexCells n k).filter
          (fun c => cellBounds c F ∧
            ¬ simplexCellValid (k := k) (partnerCell hn c F))).card := by
  classical
  have hdisj : Disjoint
      ((simplexCells n k).filter
        (fun c => cellBounds c F ∧
          simplexCellValid (k := k) (partnerCell hn c F)))
      ((simplexCells n k).filter
        (fun c => cellBounds c F ∧
          ¬ simplexCellValid (k := k) (partnerCell hn c F))) := by
    rw [Finset.disjoint_left]
    intro c hcv hci
    rw [Finset.mem_filter] at hcv hci
    exact hci.2.2 hcv.2.2
  have hunion : (simplexCells n k).filter (fun c => cellBounds c F)
      = ((simplexCells n k).filter
          (fun c => cellBounds c F ∧
            simplexCellValid (k := k) (partnerCell hn c F)))
        ∪ ((simplexCells n k).filter
          (fun c => cellBounds c F ∧
            ¬ simplexCellValid (k := k) (partnerCell hn c F))) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro c _
    constructor
    · intro hb
      by_cases hp : simplexCellValid (k := k) (partnerCell hn c F)
      · exact Or.inl ⟨hb, hp⟩
      · exact Or.inr ⟨hb, hp⟩
    · rintro (⟨hb, _⟩ | ⟨hb, _⟩) <;> exact hb
  have hcard : ((simplexCells n k).filter (fun c => cellBounds c F)).card
      = ((simplexCells n k).filter
          (fun c => cellBounds c F ∧
            simplexCellValid (k := k) (partnerCell hn c F))).card
        + ((simplexCells n k).filter
          (fun c => cellBounds c F ∧
            ¬ simplexCellValid (k := k) (partnerCell hn c F))).card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  obtain ⟨m, hm⟩ := simplex_even_validPartner_card hn F
  rw [hcard, hm]
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

theorem simplex_hboundaryOdd_of_singleton {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ))
    (hsingle : ((simplexCells n k).filter
      (fun c => cellBounds c F ∧
        ¬ simplexCellValid (k := k) (partnerCell hn c F))).card = 1) :
    Odd ((simplexCells n k).filter (fun c => cellBounds c F)).card := by
  rw [simplex_bounds_card_odd_iff_invalid hn F, hsingle]
  exact ⟨0, rfl⟩

/-- Freudenthal simplex-alcove Sperner output with R2 and R3 supplied. -/
theorem exists_rainbow_simplex_R2 {n : ℕ} (hn : 0 < n) (k : ℕ)
    (L : (Fin n → ℤ) → Fin (n + 1))
    (hR2 : ∀ F ∈ simplexFacets n k,
      (F.image L = Finset.univ.erase (Fin.last n)) → simplexBoundary hn k F →
        ((simplexCells n k).filter
          (fun c => cellBounds c F ∧
            ¬ simplexCellValid (k := k) (partnerCell hn c F))).card = 1)
    (hR3 : Odd ((simplexFacets n k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last n)) ∧
        simplexBoundary hn k F)).card) :
    Odd ((simplexCells n k).filter (fun c => isRainbow L c)).card := by
  classical
  refine sperner_n_dim_combinatorial (simplexCells n k) (simplexFacets n k)
    (fun c F => cellBounds c F)
    (fun F => F.image L = Finset.univ.erase (Fin.last n))
    (simplexBoundary hn k)
    (isRainbow L)
    ?_ ?_ ?_ hR3
  · intro c hc
    exact simplex_hheart hc
  · intro F _ _ hb
    exact simplex_hinterior_of_not_boundary hn F hb
  · intro F hF hd hb
    exact simplex_hboundaryOdd_of_singleton hn F (hR2 F hF hd hb)

/-! ## Partner transport between simplex alcoves and old barycentric cells -/

theorem sum_unitVec {n : ℕ} (a : Fin n) :
    ∑ i : Fin n, unitVec a i = 1 := by
  classical
  rw [Finset.sum_eq_single a]
  · simp [unitVec]
  · intro b _hb hba
    simp [unitVec, hba]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ a))

theorem appendSlack_add_unitVec {n k : ℕ} (p : Fin n → ℤ) (a : Fin n) :
    appendSlack k (fun i => p i + unitVec a i) =
      fun i => appendSlack k p i + ShenWork.Paper1.stepVec a i := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [appendSlack_last, appendSlack_last, Finset.sum_add_distrib, sum_unitVec,
      ShenWork.Paper1.stepVec_last]
    ring
  · intro j
    rw [appendSlack_castSucc, appendSlack_castSucc, old_stepVec_castSucc]

theorem appendSlack_sub_unitVec {n k : ℕ} (p : Fin n → ℤ) (a : Fin n) :
    appendSlack k (fun i => p i - unitVec a i) =
      fun i => appendSlack k p i - ShenWork.Paper1.stepVec a i := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [appendSlack_last, appendSlack_last, Finset.sum_sub_distrib, sum_unitVec,
      ShenWork.Paper1.stepVec_last]
    ring
  · intro j
    rw [appendSlack_castSucc, appendSlack_castSucc, old_stepVec_castSucc]

theorem toKCell_endpointFwd {n k : ℕ} (hn : 0 < n) (c : Cell n) :
    toKCell k (endpointFwd hn c) =
      ShenWork.Paper1.endpointFwd hn (toKCell k c) := by
  apply Prod.ext
  · exact appendSlack_add_unitVec c.1 (c.2 ⟨0, hn⟩)
  · rfl

theorem toKCell_endpointInv {n k : ℕ} (hn : 0 < n) (c : Cell n) :
    toKCell k (endpointInv hn c) =
      ShenWork.Paper1.endpointInv hn (toKCell k c) := by
  apply Prod.ext
  · exact appendSlack_sub_unitVec c.1 ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩)
  · rfl

theorem swapAround_eq_old {n : ℕ} (t : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    swapAround t σ = ShenWork.Paper1.swapAround t σ := by
  by_cases h : 0 < t.val ∧ t.val < n
  · simp [swapAround, ShenWork.Paper1.swapAround, h]
  · simp [swapAround, ShenWork.Paper1.swapAround]

theorem cellMemN_toKCell_iff {n k : ℕ} (hn : 0 < n) (c : Cell n) :
    ShenWork.Paper1.cellMemN k (toKCell k c) ↔ simplexCellValid (k := k) c := by
  constructor
  · intro hc
    have hcValid : ShenWork.Paper1.cellValid k (toKCell k c).1 (toKCell k c).2 := by
      simpa [ShenWork.Paper1.cellMemN] using hc
    have hs := simplexCellValid_of_old_cellValid hn hcValid
    simpa [toKCell] using hs
  · intro hc
    simpa [toKCell, ShenWork.Paper1.cellMemN] using
      old_cellValid_of_simplexCellValid hc

theorem simplexZeroDoorPostLabels_labelN_door_iff_lower_rainbow {m k : ℕ}
    {f : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (m + 2)))
      (stdSimplex ℝ (Fin (m + 2))))
    {d : Cell (m + 1)} (hd : d ∈ simplexCells (m + 1) k) :
    simplexZeroDoorPostLabels (m + 1) k (ShenWork.Paper1.labelN f k) d =
        Finset.univ.erase (Fin.last (m + 1))
      ↔ isRainbow
        (postProjectedLowerLabel k (ShenWork.Paper1.labelN f k)
          (ShenWork.Paper1.faceCoordPerm (toKCell k d).2))
        (oldZeroDoorLowerCell (toKCell k d)) := by
  have hcOld : ShenWork.Paper1.cellMemN k (toKCell k d) :=
    (cellMemN_toKCell_iff (Nat.succ_pos m) d).mpr (mem_simplexCells.mp hd)
  simpa [simplexZeroDoorPostLabels] using
    zeroDoorPostLabels_labelN_door_iff_lower_rainbow
      (m := m) (k := k) (f := f) hk hmaps (c := toKCell k d) hcOld

theorem mem_simplexZeroDoorCells_labelN_iff_lower_rainbow {m k : ℕ}
    {f : (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (m + 2)))
      (stdSimplex ℝ (Fin (m + 2))))
    {d : Cell (m + 1)} :
    d ∈ simplexZeroDoorCells (m + 1) k (ShenWork.Paper1.labelN f k)
      ↔ d ∈ simplexCells (m + 1) k ∧
        appendSlack k d.1 (Fin.last (m + 1)) = ((m + 1 : ℕ) : ℤ) ∧
        isRainbow
          (postProjectedLowerLabel k (ShenWork.Paper1.labelN f k)
            (ShenWork.Paper1.faceCoordPerm (toKCell k d).2))
          (oldZeroDoorLowerCell (toKCell k d)) := by
  constructor
  · intro hd
    rw [simplexZeroDoorCells, Finset.mem_filter] at hd
    exact ⟨hd.1, hd.2.1,
      (simplexZeroDoorPostLabels_labelN_door_iff_lower_rainbow
        hk hmaps hd.1).mp hd.2.2⟩
  · rintro ⟨hd, hlast, hrain⟩
    rw [simplexZeroDoorCells, Finset.mem_filter]
    exact ⟨hd, hlast,
      (simplexZeroDoorPostLabels_labelN_door_iff_lower_rainbow
        hk hmaps hd).mpr hrain⟩

theorem old_dropOf_toKFacet_eq {n k : ℕ} {c : Cell n}
    {F : Finset (Fin n → ℤ)} (hb : cellBounds c F) :
    ShenWork.Paper1.dropOf (toKCell k c) (toKFacet k F) = dropOf c F := by
  obtain ⟨t, ht⟩ := hb
  have hdrop : dropOf c F = t := dropOf_eq c ht
  have hfacet :
      ShenWork.Paper1.facetSet (toKCell k c).1 (toKCell k c).2 t =
        toKFacet k F := by
    rw [← ht]
    unfold toKCell toKFacet
    exact old_facetSet_appendSlack_eq c.1 c.2 t
  rw [hdrop]
  exact ShenWork.Paper1.dropOf_eq (toKCell k c) hfacet

theorem toKCell_partnerCell {n k : ℕ} (hn : 0 < n) {c : Cell n}
    {F : Finset (Fin n → ℤ)} (hb : cellBounds c F) :
    toKCell k (partnerCell hn c F) =
      ShenWork.Paper1.partnerCell hn (toKCell k c) (toKFacet k F) := by
  have hdrop := old_dropOf_toKFacet_eq (k := k) hb
  by_cases h0 : (dropOf c F).val = 0
  · rw [partnerCell_of_zero hn c h0,
      ShenWork.Paper1.partnerCell_of_zero hn (toKCell k c) (by rw [hdrop]; exact h0)]
    exact toKCell_endpointFwd hn c
  · by_cases hlast : (dropOf c F).val = n
    · rw [partnerCell_of_last hn c h0 hlast,
        ShenWork.Paper1.partnerCell_of_last hn (toKCell k c)
          (by rw [hdrop]; exact h0) (by rw [hdrop]; exact hlast)]
      exact toKCell_endpointInv hn c
    · rw [partnerCell_of_internal hn c h0 hlast,
        ShenWork.Paper1.partnerCell_of_internal hn (toKCell k c)
          (by rw [hdrop]; exact h0) (by rw [hdrop]; exact hlast)]
      rw [hdrop]
      simp only [toKCell]
      apply Prod.ext
      · rfl
      · exact swapAround_eq_old (dropOf c F) c.2

theorem simplexBoundary_iff_isBoundaryN_toKFacet {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    simplexBoundary hn k F ↔
      ShenWork.Paper1.isBoundaryN hn k (toKFacet k F) := by
  constructor
  · rintro ⟨c, hc, hb, hbad⟩
    refine ⟨toKCell k c, ?_, ?_, ?_⟩
    · exact (cellMemN_toKCell_iff hn c).mpr (mem_simplexCells.mp hc)
    · obtain ⟨t, ht⟩ := hb
      refine ⟨t, ?_⟩
      rw [← ht]
      unfold toKCell toKFacet
      exact old_facetSet_appendSlack_eq c.1 c.2 t
    · intro hp
      apply hbad
      have hp' : ShenWork.Paper1.cellMemN k (toKCell k (partnerCell hn c F)) := by
        rwa [toKCell_partnerCell (k := k) hn hb]
      exact (cellMemN_toKCell_iff hn (partnerCell hn c F)).mp hp'
  · rintro ⟨c, hc, hb, hbad⟩
    have hcMem : c ∈ ShenWork.Paper1.cellsN n k := ShenWork.Paper1.mem_cellsN.mpr hc
    rw [← image_simplexCells_toKCell_eq_cellsN hn] at hcMem
    rw [Finset.mem_image] at hcMem
    obtain ⟨d, hd, hdc⟩ := hcMem
    have hbD : cellBounds d F := by
      obtain ⟨t, ht⟩ := hb
      have hfacet :
          ShenWork.Paper1.facetSet (toKCell k d).1 (toKCell k d).2 t =
            toKFacet k (facetSet d.1 d.2 t) := by
        unfold toKCell toKFacet
        exact old_facetSet_appendSlack_eq d.1 d.2 t
      have hto :
          toKFacet k (facetSet d.1 d.2 t) = toKFacet k F := by
        rw [← hfacet, hdc, ht]
      exact ⟨t, toKFacet_injective hto⟩
    refine ⟨d, hd, hbD, ?_⟩
    intro hs
    apply hbad
    have hp : ShenWork.Paper1.cellMemN k (toKCell k (partnerCell hn d F)) :=
      (cellMemN_toKCell_iff hn (partnerCell hn d F)).mpr hs
    rwa [toKCell_partnerCell (k := k) hn hbD, hdc] at hp

theorem image_simplexBoundaryDoors_toKFacet_eq_boundaryDoorsN {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    ((simplexFacets n k).filter
        (fun F => (F.image (pullLabel k L) = Finset.univ.erase (Fin.last n)) ∧
          simplexBoundary hn k F)).image (toKFacet k)
      =
    (ShenWork.Paper1.facetsN n k).filter
        (fun F => (F.image L = Finset.univ.erase (Fin.last n)) ∧
          ShenWork.Paper1.isBoundaryN hn k F) := by
  classical
  ext F
  constructor
  · intro hF
    rw [Finset.mem_image] at hF
    obtain ⟨G, hG, rfl⟩ := hF
    rw [Finset.mem_filter] at hG
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [← image_simplexFacets_toKFacet_eq_facetsN hn]
      exact Finset.mem_image.mpr ⟨G, hG.1, rfl⟩
    · rw [image_toKFacet_label]
      exact hG.2.1
    · exact (simplexBoundary_iff_isBoundaryN_toKFacet hn G).mp hG.2.2
  · intro hF
    rw [Finset.mem_filter] at hF
    rw [← image_simplexFacets_toKFacet_eq_facetsN hn] at hF
    rw [Finset.mem_image] at hF
    obtain ⟨G, hG, hGF⟩ := hF.1
    rw [Finset.mem_image]
    refine ⟨G, ?_, hGF⟩
    rw [Finset.mem_filter]
    refine ⟨hG, ?_, ?_⟩
    · rw [← image_toKFacet_label, hGF]
      exact hF.2.1
    · rw [← hGF] at hF
      exact (simplexBoundary_iff_isBoundaryN_toKFacet hn G).mpr hF.2.2

theorem hR3N_of_simplex_hR3 {n k : ℕ} (hn : 0 < n)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1))
    (hR3 : Odd ((simplexFacets n k).filter
      (fun F => (F.image (pullLabel k L) = Finset.univ.erase (Fin.last n)) ∧
        simplexBoundary hn k F)).card) :
    Odd ((ShenWork.Paper1.facetsN n k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last n)) ∧
        ShenWork.Paper1.isBoundaryN hn k F)).card := by
  rw [← image_simplexBoundaryDoors_toKFacet_eq_boundaryDoorsN hn L]
  rw [Finset.card_image_of_injective _ toKFacet_injective]
  exact hR3

theorem exists_rainbow_cellN_R2_of_simplex_hR3 {n : ℕ} (hn : 0 < n) (k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1))
    (hR3 : Odd ((simplexFacets n k).filter
      (fun F => (F.image (pullLabel k L) = Finset.univ.erase (Fin.last n)) ∧
        simplexBoundary hn k F)).card) :
    Odd ((ShenWork.Paper1.cellsN n k).filter
      (fun c => Function.Bijective (ShenWork.Paper1.cellColorN L c))).card :=
  ShenWork.Paper1.exists_rainbow_cellN_R2 hn k L
    (hR3N_of_simplex_hR3 hn L hR3)

theorem image_simplexInvalidPartners_toKCell_eq_invalidN {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    ((simplexCells n k).filter
        (fun c => cellBounds c F ∧
          ¬ simplexCellValid (k := k) (partnerCell hn c F))).image (toKCell k)
      =
    (ShenWork.Paper1.cellsN n k).filter
        (fun c => ShenWork.Paper1.cellBounds c (toKFacet k F) ∧
          ¬ ShenWork.Paper1.cellMemN k
            (ShenWork.Paper1.partnerCell hn c (toKFacet k F))) := by
  classical
  ext c
  constructor
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, hdc⟩ := hc
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [← image_simplexCells_toKCell_eq_cellsN hn]
      exact Finset.mem_image.mpr ⟨d, hd.1, hdc⟩
    · rw [← hdc]
      obtain ⟨t, ht⟩ := hd.2.1
      refine ⟨t, ?_⟩
      rw [← ht]
      unfold toKCell toKFacet
      exact old_facetSet_appendSlack_eq d.1 d.2 t
    · rw [← hdc]
      intro hp
      apply hd.2.2
      have hp' : ShenWork.Paper1.cellMemN k (toKCell k (partnerCell hn d F)) := by
        rwa [toKCell_partnerCell (k := k) hn hd.2.1]
      exact (cellMemN_toKCell_iff hn (partnerCell hn d F)).mp hp'
  · intro hc
    rw [Finset.mem_filter] at hc
    rw [← image_simplexCells_toKCell_eq_cellsN hn] at hc
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, hdc⟩ := hc.1
    have hbD : cellBounds d F := by
      obtain ⟨t, ht⟩ := hc.2.1
      have hfacet :
          ShenWork.Paper1.facetSet (toKCell k d).1 (toKCell k d).2 t =
            toKFacet k (facetSet d.1 d.2 t) := by
        unfold toKCell toKFacet
        exact old_facetSet_appendSlack_eq d.1 d.2 t
      have hto :
          toKFacet k (facetSet d.1 d.2 t) = toKFacet k F := by
        rw [← hfacet, hdc, ht]
      exact ⟨t, toKFacet_injective hto⟩
    rw [Finset.mem_image]
    refine ⟨d, ?_, hdc⟩
    rw [Finset.mem_filter]
    refine ⟨hd, hbD, ?_⟩
    intro hs
    apply hc.2.2
    have hp : ShenWork.Paper1.cellMemN k (toKCell k (partnerCell hn d F)) :=
      (cellMemN_toKCell_iff hn (partnerCell hn d F)).mpr hs
    rwa [toKCell_partnerCell (k := k) hn hbD, hdc] at hp

theorem card_simplexInvalidPartners_eq_invalidN {n k : ℕ} (hn : 0 < n)
    (F : Finset (Fin n → ℤ)) :
    ((simplexCells n k).filter
        (fun c => cellBounds c F ∧
          ¬ simplexCellValid (k := k) (partnerCell hn c F))).card =
    ((ShenWork.Paper1.cellsN n k).filter
        (fun c => ShenWork.Paper1.cellBounds c (toKFacet k F) ∧
          ¬ ShenWork.Paper1.cellMemN k
            (ShenWork.Paper1.partnerCell hn c (toKFacet k F)))).card := by
  rw [← image_simplexInvalidPartners_toKCell_eq_invalidN hn F]
  exact (Finset.card_image_of_injective _ toKCell_injective).symm

theorem simplex_boundary_singleton_invalid {n k : ℕ} (hn : 0 < n)
    {F : Finset (Fin n → ℤ)} (hb : simplexBoundary hn k F) :
    ((simplexCells n k).filter
      (fun c => cellBounds c F ∧
        ¬ simplexCellValid (k := k) (partnerCell hn c F))).card = 1 := by
  rw [card_simplexInvalidPartners_eq_invalidN hn F]
  exact ShenWork.Paper1.boundary_singleton_invalid hn k
    ((simplexBoundary_iff_isBoundaryN_toKFacet hn F).mp hb)

theorem exists_rainbow_simplex_of_hR3 {n : ℕ} (hn : 0 < n) (k : ℕ)
    (L : (Fin n → ℤ) → Fin (n + 1))
    (hR3 : Odd ((simplexFacets n k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last n)) ∧
        simplexBoundary hn k F)).card) :
  Odd ((simplexCells n k).filter (fun c => isRainbow L c)).card :=
  exists_rainbow_simplex_R2 hn k L
    (fun _ _ _ hb => simplex_boundary_singleton_invalid hn hb) hR3

/-! ## Concrete Sperner labels on appended slack vertices -/

/-- The old integer Sperner label avoids any zero barycentric coordinate. -/
theorem labelN_ne_of_zero {n k : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
      (stdSimplex ℝ (Fin (n + 1))))
    {q : Fin (n + 1) → ℤ} (hsum : ∑ i, (q i).toNat = k)
    {t : Fin (n + 1)} (hzero : q t = 0) :
    ShenWork.Paper1.labelN f k q ≠ t := by
  let qNat : Fin (n + 1) → ℕ := fun i => (q i).toNat
  have hv : embPt k qNat ∈ stdSimplex ℝ (Fin (n + 1)) :=
    embPt_mem_stdSimplex hk hsum
  have hfv : f (embPt k qNat) ∈ stdSimplex ℝ (Fin (n + 1)) := hmaps hv
  have hcoord : embPt k qNat t = 0 := by
    simp [embPt, qNat, hzero]
  unfold ShenWork.Paper1.labelN
  exact spernerLabelN_ne_of_zero hv hfv hcoord

theorem appendSlack_toNat_sum_of_nonneg {n k : ℕ} {v : Fin n → ℤ}
    (hnn : ∀ i : Fin (n + 1), 0 ≤ appendSlack k v i) :
    ∑ i : Fin (n + 1), (appendSlack k v i).toNat = k := by
  have hcast : ∑ i : Fin (n + 1), ((appendSlack k v i).toNat : ℤ) =
      ∑ i : Fin (n + 1), appendSlack k v i := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact Int.toNat_of_nonneg (hnn i)
  have hsum : ∑ i : Fin (n + 1), ((appendSlack k v i).toNat : ℤ) = (k : ℤ) := by
    rw [hcast, sum_appendSlack]
  exact_mod_cast hsum

/-- The Sperner label pulled back to the simplex chart. -/
noncomputable def simplexLabelN {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ) :
    Label n :=
  pullLabel k (ShenWork.Paper1.labelN f k)

theorem simplexLabelN_ne_of_appendSlack_zero {n k : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
      (stdSimplex ℝ (Fin (n + 1))))
    {v : Fin n → ℤ} (hnn : ∀ i : Fin (n + 1), 0 ≤ appendSlack k v i)
    {t : Fin (n + 1)} (hzero : appendSlack k v t = 0) :
    simplexLabelN f k v ≠ t := by
  unfold simplexLabelN pullLabel
  exact labelN_ne_of_zero hk hmaps (appendSlack_toNat_sum_of_nonneg hnn) hzero

theorem simplexLabelN_ne_last_of_slack_zero {n k : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
      (stdSimplex ℝ (Fin (n + 1))))
    {v : Fin n → ℤ} (hnn : ∀ i : Fin n, 0 ≤ v i)
    (hsum : ∑ i : Fin n, v i = (k : ℤ)) :
    simplexLabelN f k v ≠ Fin.last n := by
  have hlast : appendSlack k v (Fin.last n) = 0 := by
    rw [appendSlack_last, hsum]
    ring
  have hnn' : ∀ i : Fin (n + 1), 0 ≤ appendSlack k v i := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hlast]
    · intro j
      rw [appendSlack_castSucc]
      exact hnn j
  exact simplexLabelN_ne_of_appendSlack_zero hk hmaps hnn' hlast

theorem simplexLabelN_ne_castSucc_of_coord_zero {n k : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
      (stdSimplex ℝ (Fin (n + 1))))
    {v : Fin n → ℤ} (hnn : ∀ i : Fin (n + 1), 0 ≤ appendSlack k v i)
    {j : Fin n} (hzero : v j = 0) :
    simplexLabelN f k v ≠ j.castSucc := by
  refine simplexLabelN_ne_of_appendSlack_zero hk hmaps hnn ?_
  rw [appendSlack_castSucc, hzero]

theorem hR3N_labelN_of_simplexLabelN_hR3 {n k : ℕ} (hn : 0 < n)
    (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hR3 : Odd ((simplexFacets n k).filter
      (fun F => (F.image (simplexLabelN f k) = Finset.univ.erase (Fin.last n)) ∧
        simplexBoundary hn k F)).card) :
    Odd ((ShenWork.Paper1.facetsN n k).filter
      (fun F => (F.image (ShenWork.Paper1.labelN f k) =
          Finset.univ.erase (Fin.last n)) ∧
        ShenWork.Paper1.isBoundaryN hn k F)).card := by
  simpa [simplexLabelN] using
    hR3N_of_simplex_hR3 hn (ShenWork.Paper1.labelN f k) hR3

theorem exists_rainbow_cellN_R2_labelN_of_simplexLabelN_hR3 {n : ℕ}
    (hn : 0 < n) (k : ℕ)
    (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hR3 : Odd ((simplexFacets n k).filter
      (fun F => (F.image (simplexLabelN f k) = Finset.univ.erase (Fin.last n)) ∧
        simplexBoundary hn k F)).card) :
    Odd ((ShenWork.Paper1.cellsN n k).filter
      (fun c => Function.Bijective
        (ShenWork.Paper1.cellColorN (ShenWork.Paper1.labelN f k) c))).card := by
  simpa [simplexLabelN] using
    exists_rainbow_cellN_R2_of_simplex_hR3 hn k (ShenWork.Paper1.labelN f k) hR3

/-!
Status for the full R3/G1 propagation:

This file has the boundary-compatible Freudenthal/type-A finite carrier, global facets, drop
recovery, per-cell non-overlap (`chainSet_injective`), the partner-cell involution, the boundary
predicate, the interior/boundary parity reduction, and the Freudenthal `exists_rainbow_cellF_R2`
assembly.  It also turns box bottom-face doors into lower-dimensional rainbow cells as global
facet sets (`card_bottomDoorFacets_eq_rainbow`) and proves those bottom facets are genuine
boundary facets.

Closed here:
* Freudenthal endpoint reconstruction and R2 singleton invalid-partner:
  `boundary_singleton_invalid`;
* box bottom-face parity from recursive `BoundaryData`, and the stronger
  `BoundaryBottomData` route where R2 is supplied internally;
* simplex-alcove carriers `simplexCells`/`simplexFacets`;
* transport of cells, facets, labels, rainbow counts, partners, and boundary predicates between
  `simplexCells` and the old barycentric `cellsN`/`facetsN`;
* a slack-face audit for the transported `simplexCells` carrier:
  `no_simplexFacet_all_slack_zero_of_two_le` proves that, in dimension at least two, its facets
  cannot be literal facets of `appendSlack = 0`;
* simplex-alcove heart/interior/boundaryOdd with R2 discharged by transport from
  `boundary_singleton_invalid`;
* old hR3 transport: `hR3N_of_simplex_hR3`;
* old Sperner output from a simplex hR3 input:
  `exists_rainbow_cellN_R2_of_simplex_hR3`;
* concrete `labelN` wrappers:
  `hR3N_labelN_of_simplexLabelN_hR3`,
  `exists_rainbow_cellN_R2_labelN_of_simplexLabelN_hR3`;
* concrete zero-coordinate exclusion for the pulled Sperner label (`labelN_ne_of_zero`,
  `simplexLabelN_ne_of_appendSlack_zero`, `simplexLabelN_ne_last_of_slack_zero`).
* post-projection zero-door labelling:
  `simplexZeroDoorCells` now uses `transferLastMass` before relabelling on the literal face;
  the legacy pre-projection target is preserved as `simplexZeroDoorCellsOld`;
* the `n=2,k=2` sanity check for
  `(x₀,x₁,x₂) ↦ (x₀,x₁+x₂,0)`:
  `counterexampleLabelN2_simplexZeroDoorCells_card = 1` and
  `counterexampleLabelN2_simplexZeroDoorCellsOld_card = 0`; the matching
  box post-projection bottom-door check is
  `counterexampleLabelN2_boxBottomDoors_card = 1`;
* the local post-projection bridge:
  `zeroDoorPostLabels_labelN_door_iff_lower_rainbow` and
  `mem_simplexZeroDoorCells_labelN_iff_lower_rainbow`.

Still not closed here:
* the concrete recursive slack-face parity
  `Odd (simplexZeroDoorCells n k (labelN f k)).card)`.
  The local bridge rewrites each post door as a rainbow lower cell, but the induced lower
  label is rotated by the upper cell's `faceCoordPerm`; the remaining work is the global
  type-A aggregation that turns these local lower-rainbow witnesses into a single
  recursive parity count.
-/

#print axioms image_dropLast_bottomFacet
#print axioms valid_bottomFacet_projects
#print axioms chain_extend_castSucc
#print axioms restrictCell_extendCell
#print axioms bottomCells_eq_image_extend
#print axioms card_bottomCells
#print axioms mem_typeACells
#print axioms mem_typeAFacets_iff
#print axioms typeAChain_bottom_last_zero
#print axioms typeAFinalFacet_bottom_last_zero
#print axioms door_iff_bottomFaceColor_bijective
#print axioms door_iff_extendCell_rainbow
#print axioms card_bottomDoors_eq_rainbow
#print axioms unitVec_injective
#print axioms chainVZ_step
#print axioms sum_total_facetSet
#print axioms chainVZ_match_off
#print axioms cell_eq_of_facetSet_eq_zero
#print axioms cell_eq_of_facetSet_eq_last
#print axioms chainSet_injective
#print axioms hheart
#print axioms partnerCell_involutive
#print axioms partnerCell_bounds
#print axioms bounds_endpoint_dichotomy
#print axioms isBoundary_endpoint
#print axioms boundary_singleton_invalid
#print axioms hinterior_of_not_boundary
#print axioms bounds_card_odd_iff_invalid
#print axioms hboundaryOdd_of_singleton
#print axioms exists_rainbow_cellF_R2
#print axioms rainbow_count_zero_odd
#print axioms finalFacet_extendCell_injective
#print axioms card_bottomDoorFacets_eq_rainbow
#print axioms bottomDoorFacets_odd_of_lower_rainbow_odd
#print axioms zeroDoorFaceVertex_pull_eq_appendSlack
#print axioms zeroDoorPostLabels_door_iff_lower_rainbow
#print axioms zeroDoorPostLabels_labelN_door_iff_lower_rainbow
#print axioms mem_simplexZeroDoorCells_labelN_iff_lower_rainbow
#print axioms counterexampleLabelN2_simplexZeroDoorCells_card
#print axioms counterexampleLabelN2_simplexZeroDoorCellsOld_card
#print axioms counterexampleLabelN2_boxBottomDoors_card
#print axioms counterexampleLabelN2_boxBottomDoors_odd
#print axioms bottom_geometry_of_facet_last_zero
#print axioms extendCell_finalFacet_boundary
#print axioms bottomDoorFacets_subset_boundaryDoors
#print axioms boundaryDoors_subset_bottomDoorFacets_of_vertices_bottom
#print axioms boundaryDoors_eq_bottomDoorFacets_of_vertices_bottom
#print axioms hR3_of_boundaryDoors_eq_bottomDoorFacets
#print axioms hR3_of_boundary_door_vertices_bottom
#print axioms rainbow_count_succ_odd_of_boundary_data
#print axioms rainbow_count_succ_odd_of_boundary_vertices_bottom
#print axioms rainbow_count_succ_odd_of_boundary_vertices_bottom_R2
#print axioms rainbow_count_odd_of_boundaryData
#print axioms exists_rainbow_cellF_of_boundaryData
#print axioms rainbow_count_odd_of_boundaryBottomData
#print axioms bottomDoors_odd_of_boundaryBottomData
#print axioms exists_rainbow_cellF_of_boundaryBottomData
#print axioms zeroDoorFaceVertex_pull_castSucc
#print axioms oldZeroDoorLowerCell_cellValid
#print axioms oldZeroDoorLowerCell_mem_cells
#print axioms old_cellValid_of_simplexCellValid
#print axioms simplexCellValid_of_old_cellValid
#print axioms image_simplexCells_toKCell_eq_cellsN
#print axioms old_chainVZ_appendSlack_eq
#print axioms old_facetSet_appendSlack_eq
#print axioms appendSlack_chainVZ_last
#print axioms no_simplexFacet_all_slack_zero_of_two_le
#print axioms image_simplex_rainbow_eq_cellsN_rainbow
#print axioms card_simplex_rainbow_eq_cellsN_rainbow
#print axioms cellsN_rainbow_odd_of_simplex_rainbow_odd
#print axioms image_simplexFacets_toKFacet_eq_facetsN
#print axioms image_toKFacet_label
#print axioms simplex_hheart
#print axioms simplex_hinterior_of_not_boundary
#print axioms simplex_bounds_card_odd_iff_invalid
#print axioms exists_rainbow_simplex_R2
#print axioms toKCell_partnerCell
#print axioms simplexBoundary_iff_isBoundaryN_toKFacet
#print axioms image_simplexBoundaryDoors_toKFacet_eq_boundaryDoorsN
#print axioms hR3N_of_simplex_hR3
#print axioms exists_rainbow_cellN_R2_of_simplex_hR3
#print axioms simplex_boundary_singleton_invalid
#print axioms exists_rainbow_simplex_of_hR3
#print axioms image_simplexZeroDoorCellsOld_toKCell_eq_zeroDoorCellsN
#print axioms card_simplexZeroDoorCellsOld_eq_zeroDoorCellsN
#print axioms hR3_labelN_of_simplexZeroDoorCellsOld_odd
#print axioms exists_rainbow_cellN_R2_labelN_of_simplexZeroDoorCellsOld_odd
#print axioms labelN_ne_of_zero
#print axioms simplexLabelN_ne_of_appendSlack_zero
#print axioms simplexLabelN_ne_last_of_slack_zero
#print axioms hR3N_labelN_of_simplexLabelN_hR3
#print axioms exists_rainbow_cellN_R2_labelN_of_simplexLabelN_hR3

end Freudenthal

end ShenWork.Paper1
