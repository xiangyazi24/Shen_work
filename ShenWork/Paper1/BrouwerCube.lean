import ShenWork.Paper1.BrouwerNDimFreudenthal

namespace ShenWork.Paper1

open Set Finset Filter Topology

namespace Freudenthal

noncomputable section

/-- The closed coordinate cube `[0,1]^n`. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Valid cube-grid vertices at mesh `k`, including boundary vertices. -/
def cubeGridVertex {n : ℕ} (k : ℕ) (v : Fin n → ℤ) : Prop :=
  ∀ i, 0 ≤ v i ∧ v i ≤ (k : ℤ)

instance {n k : ℕ} (v : Fin n → ℤ) : Decidable (cubeGridVertex k v) := by
  unfold cubeGridVertex
  infer_instance

/-- Embed an integer mesh vertex as a point of the unit cube. -/
def cubePoint {n : ℕ} (k : ℕ) (v : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (v i : ℝ) / k

theorem cubePoint_mem_unitCube {n k : ℕ} (hk : 0 < k) {v : Fin n → ℤ}
    (hv : cubeGridVertex k v) : cubePoint k v ∈ unitCube n := by
  intro i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hvi := hv i
  constructor
  · exact div_nonneg (by exact_mod_cast hvi.1) (le_of_lt hkR)
  · have hle : (v i : ℝ) ≤ k := by exact_mod_cast hvi.2
    exact (div_le_one hkR).mpr hle

@[simp] theorem cubePoint_eq_zero_of_coord_zero {n k : ℕ} {v : Fin n → ℤ}
    {i : Fin n} (hi : v i = 0) : cubePoint k v i = 0 := by
  simp [cubePoint, hi]

theorem cubePoint_eq_one_of_coord_eq_k {n k : ℕ} (hk : 0 < k)
    {v : Fin n → ℤ} {i : Fin n} (hi : v i = (k : ℤ)) :
    cubePoint k v i = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [cubePoint, hi, hkR]

/-- Strict interior perturbation of a cube self-map. -/
def strictify {n : ℕ} (δ : ℝ) (T : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x i => (1 - 2 * δ) * T x i + δ

/-- Displacement of a map at a grid vertex. -/
def cubeDisp {n : ℕ} (T : (Fin n → ℝ) → Fin n → ℝ) (k : ℕ)
    (v : Fin n → ℤ) (i : Fin n) : ℝ :=
  T (cubePoint k v) i - cubePoint k v i

/-- Kuhn cumulative partial sum `S_j = g_0 + ... + g_{j-1}`. -/
def cubePartialSum {n : ℕ} (T : (Fin n → ℝ) → Fin n → ℝ) (k : ℕ)
    (v : Fin n → ℤ) (j : Fin (n + 1)) : ℝ :=
  ∑ r : Fin n, if r.val < j.val then cubeDisp T k v r else 0

theorem cubePartialSum_succ {n : ℕ} (T : (Fin n → ℝ) → Fin n → ℝ)
    (k : ℕ) (v : Fin n → ℤ) (i : Fin n) :
    cubePartialSum T k v i.succ =
      cubePartialSum T k v i.castSucc + cubeDisp T k v i := by
  unfold cubePartialSum
  calc
    (∑ r : Fin n, if r.val < i.succ.val then cubeDisp T k v r else 0)
        = ∑ r : Fin n,
            ((if r.val < i.castSucc.val then cubeDisp T k v r else 0)
              + if r = i then cubeDisp T k v i else 0) := by
          apply Finset.sum_congr rfl
          intro r _
          by_cases hri : r = i
          · subst r
            simp [Fin.val_succ, Fin.val_castSucc]
          · have hiff : (r.val < i.val + 1) ↔ r.val < i.val := by
              constructor <;> intro h <;> omega
            simp [Fin.val_succ, Fin.val_castSucc, hri, hiff]
    _ = (∑ r : Fin n, if r.val < i.castSucc.val then cubeDisp T k v r else 0)
          + ∑ r : Fin n, if r = i then cubeDisp T k v i else 0 := by
          rw [Finset.sum_add_distrib]
    _ = (∑ r : Fin n, if r.val < i.castSucc.val then cubeDisp T k v r else 0)
          + cubeDisp T k v i := by
          congr 1
          simp

/-- A finite argmin over `Fin m`, implemented with a deterministic classical witness. -/
noncomputable def argminFin {m : ℕ} [NeZero m] (F : Fin m → ℝ) : Fin m :=
  Classical.choose (Finset.univ.exists_minimalFor F (Finset.univ_nonempty))

theorem argminFin_le {m : ℕ} [NeZero m] (F : Fin m → ℝ) (j : Fin m) :
    F (argminFin F) ≤ F j := by
  classical
  let hmin := Classical.choose_spec
      (Finset.univ.exists_minimalFor F (Finset.univ_nonempty))
  by_cases h : F j ≤ F (argminFin F)
  · exact hmin.2 (Finset.mem_univ j) h
  · exact le_of_not_ge h

/-- Cube Kuhn cumulative-sum label, guarded off the mesh box. -/
noncomputable def cubeKuhnLabel {n : ℕ} (T : (Fin n → ℝ) → Fin n → ℝ)
    (k : ℕ) : Label n :=
  fun v =>
    if cubeGridVertex k v then
      argminFin (fun j : Fin (n + 1) => cubePartialSum T k v j)
    else 0

theorem cubeKuhnLabel_of_not_grid {n k : ℕ}
    (T : (Fin n → ℝ) → Fin n → ℝ) {v : Fin n → ℤ}
    (hv : ¬ cubeGridVertex k v) :
    cubeKuhnLabel T k v = 0 := by
  simp [cubeKuhnLabel, hv]

theorem cubeKuhnLabel_min_le {n k : ℕ}
    (T : (Fin n → ℝ) → Fin n → ℝ) {v : Fin n → ℤ}
    (hv : cubeGridVertex k v) (j : Fin (n + 1)) :
    cubePartialSum T k v (cubeKuhnLabel T k v) ≤ cubePartialSum T k v j := by
  simp [cubeKuhnLabel, hv, argminFin_le]

theorem cubeKuhnLabel_ne_of_partial_lt {n k : ℕ}
    (T : (Fin n → ℝ) → Fin n → ℝ) {v : Fin n → ℤ}
    (hv : cubeGridVertex k v) {a b : Fin (n + 1)}
    (hlt : cubePartialSum T k v a < cubePartialSum T k v b) :
    cubeKuhnLabel T k v ≠ b := by
  intro hb
  have hle := cubeKuhnLabel_min_le T hv a
  rw [hb] at hle
  exact not_lt_of_ge hle hlt

theorem strictify_disp_pos_of_lower_face {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n))
    {v : Fin n → ℤ} (hv : cubeGridVertex k v) {i : Fin n}
    (hi : v i = 0) : 0 < cubeDisp (strictify δ T) k v i := by
  have hx := cubePoint_mem_unitCube hk hv
  have hTx := hmaps hx i
  have hcoeff : 0 ≤ 1 - 2 * δ := by nlinarith
  have hx0 : cubePoint k v i = 0 := cubePoint_eq_zero_of_coord_zero hi
  have hnonneg : 0 ≤ T (cubePoint k v) i := hTx.1
  unfold cubeDisp strictify
  rw [hx0]
  nlinarith [mul_nonneg hcoeff hnonneg]

theorem strictify_disp_neg_of_upper_face {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n))
    {v : Fin n → ℤ} (hv : cubeGridVertex k v) {i : Fin n}
    (hi : v i = (k : ℤ)) : cubeDisp (strictify δ T) k v i < 0 := by
  have hx := cubePoint_mem_unitCube hk hv
  have hTx := hmaps hx i
  have hcoeff : 0 ≤ 1 - 2 * δ := by nlinarith
  have hx1 : cubePoint k v i = 1 := cubePoint_eq_one_of_coord_eq_k hk hi
  have hle : T (cubePoint k v) i ≤ 1 := hTx.2
  have hmul : (1 - 2 * δ) * T (cubePoint k v) i ≤ (1 - 2 * δ) * 1 :=
    mul_le_mul_of_nonneg_left hle hcoeff
  unfold cubeDisp strictify
  rw [hx1]
  nlinarith

theorem cubeKuhnLabel_ne_lower_forbidden {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n))
    {v : Fin n → ℤ} (hv : cubeGridVertex k v) {i : Fin n}
    (hi : v i = 0) :
    cubeKuhnLabel (strictify δ T) k v ≠ i.succ := by
  have hg := strictify_disp_pos_of_lower_face hk hδ hδle hmaps hv hi
  have hs := cubePartialSum_succ (strictify δ T) k v i
  have hlt : cubePartialSum (strictify δ T) k v i.castSucc <
      cubePartialSum (strictify δ T) k v i.succ := by
    rw [hs]
    linarith
  exact cubeKuhnLabel_ne_of_partial_lt (strictify δ T) hv hlt

theorem cubeKuhnLabel_ne_upper_forbidden {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n))
    {v : Fin n → ℤ} (hv : cubeGridVertex k v) {i : Fin n}
    (hi : v i = (k : ℤ)) :
    cubeKuhnLabel (strictify δ T) k v ≠ i.castSucc := by
  have hg := strictify_disp_neg_of_upper_face hk hδ hδle hmaps hv hi
  have hs := cubePartialSum_succ (strictify δ T) k v i
  have hlt : cubePartialSum (strictify δ T) k v i.succ <
      cubePartialSum (strictify δ T) k v i.castSucc := by
    rw [hs]
    linarith
  exact cubeKuhnLabel_ne_of_partial_lt (strictify δ T) hv hlt

/-- Boundary compatibility certificate for cube Kuhn labels. -/
structure CubeBoundaryCert (n k : ℕ) (L : Label n) : Prop where
  offGrid_zero : ∀ v : Fin n → ℤ, ¬ cubeGridVertex k v → L v = 0
  lower_ne : ∀ v : Fin n → ℤ, cubeGridVertex k v →
    ∀ i : Fin n, v i = 0 → L v ≠ i.succ
  upper_ne : ∀ v : Fin n → ℤ, cubeGridVertex k v →
    ∀ i : Fin n, v i = (k : ℤ) → L v ≠ i.castSucc

theorem cubeKuhnLabel_boundaryCert {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n)) :
    CubeBoundaryCert n k (cubeKuhnLabel (strictify δ T) k) where
  offGrid_zero := by
    intro v hv
    exact cubeKuhnLabel_of_not_grid (strictify δ T) hv
  lower_ne := by
    intro v hv i hi
    exact cubeKuhnLabel_ne_lower_forbidden hk hδ hδle hmaps hv hi
  upper_ne := by
    intro v hv i hi
    exact cubeKuhnLabel_ne_upper_forbidden hk hδ hδle hmaps hv hi

theorem appendZero_cubeGridVertex {n k : ℕ} {v : Fin n → ℤ}
    (hv : cubeGridVertex k v) :
    cubeGridVertex k (appendZero v) := by
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    constructor
    · simp [appendZero]
    · have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
      simp [appendZero, hk_nonneg]
  · let j : Fin n := i.castPred hi
    have hji : j.castSucc = i := Fin.castSucc_castPred i hi
    rw [← hji]
    simpa [appendZero] using hv j

theorem cubeGridVertex_of_appendZero {n k : ℕ} {v : Fin n → ℤ}
    (hv : cubeGridVertex k (appendZero v)) :
    cubeGridVertex k v := by
  intro i
  simpa [appendZero] using hv i.castSucc

theorem CubeBoundaryCert.bottom_havoid {n k : ℕ} {L : Label (n + 1)}
    (hcert : CubeBoundaryCert (n + 1) k L) :
    ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1) := by
  intro v
  by_cases hv : cubeGridVertex k (appendZero v)
  · have hne := hcert.lower_ne (appendZero v) hv (Fin.last n) (by simp)
    simpa using hne
  · have hzero := hcert.offGrid_zero (appendZero v) hv
    rw [hzero]
    simp

theorem CubeBoundaryCert.bottomLabel {n k : ℕ} {L : Label (n + 1)}
    (hcert : CubeBoundaryCert (n + 1) k L)
    (havoid : ∀ v : Fin n → ℤ, L (appendZero v) ≠ Fin.last (n + 1)) :
    CubeBoundaryCert n k (bottomLabel L havoid) where
  offGrid_zero := by
    intro v hv
    have hngrid : ¬ cubeGridVertex k (appendZero v) := by
      intro h
      exact hv (cubeGridVertex_of_appendZero h)
    have hzero := hcert.offGrid_zero (appendZero v) hngrid
    apply Fin.castSucc_injective
    rw [bottomLabel_castSucc]
    simp [hzero]
  lower_ne := by
    intro v hv i hi hb
    have hv' : cubeGridVertex k (appendZero v) := appendZero_cubeGridVertex hv
    have hne := hcert.lower_ne (appendZero v) hv' i.castSucc (by simpa [appendZero])
    apply hne
    apply Fin.castSucc_injective
    rw [← bottomLabel_castSucc L havoid v, hb]
    rfl
  upper_ne := by
    intro v hv i hi hb
    have hv' : cubeGridVertex k (appendZero v) := appendZero_cubeGridVertex hv
    have hne := hcert.upper_ne (appendZero v) hv' i.castSucc (by simpa [appendZero])
    apply hne
    apply Fin.castSucc_injective
    rw [← bottomLabel_castSucc L havoid v, hb]

theorem chainVZ_cubeGridVertex_of_mem_cells {n k : ℕ} {c : Cell n}
    (hc : c ∈ cells n k) (t : Fin (n + 1)) :
    cubeGridVertex k (chainVZ c.1 c.2 t) := by
  intro i
  have hi := mem_cells.mp hc i
  unfold chainVZ
  by_cases hlt : (c.2.symm i).val < t.val
  · simp [hlt]
    omega
  · simp [hlt]
    omega

theorem cubeGridVertex_of_mem_facet {n k : ℕ} {c : Cell n}
    (hc : c ∈ cells n k) {t : Fin (n + 1)} {v : Fin n → ℤ}
    (hv : v ∈ facetSet c.1 c.2 t) :
    cubeGridVertex k v := by
  classical
  unfold facetSet at hv
  rw [Finset.mem_image] at hv
  rcases hv with ⟨u, _hu, rfl⟩
  exact chainVZ_cubeGridVertex_of_mem_cells hc u

theorem zero_facet_subset_upper_face_of_endpointFwd_invalid {n k : ℕ}
    (hn : 0 < n) {c : Cell n} (hc : c ∈ cells n k)
    (hinv : ¬ cellValid k (endpointFwd hn c)) :
    ∀ v ∈ facetSet c.1 c.2 0, v (c.2 ⟨0, hn⟩) = (k : ℤ) := by
  classical
  let a : Fin n := c.2 ⟨0, hn⟩
  have hnotlt : ¬ c.1 a + 1 < (k : ℤ) := by
    intro hlt
    apply hinv
    unfold endpointFwd cellValid
    change ∀ i, 0 ≤ c.1 i + unitVec a i ∧
      c.1 i + unitVec a i < (k : ℤ)
    intro i
    have hi := mem_cells.mp hc i
    by_cases hia : i = a
    · subst i
      simp [unitVec]
      omega
    · simp [unitVec, hia]
      omega
  have ha_valid := mem_cells.mp hc a
  have ha_eq : c.1 a + 1 = (k : ℤ) := by omega
  intro v hv
  unfold facetSet at hv
  rw [Finset.mem_image] at hv
  rcases hv with ⟨u, hu, rfl⟩
  rw [Finset.mem_erase] at hu
  have hu_pos : 0 < u.val := by
    by_contra h
    have hval : u.val = 0 := Nat.eq_zero_of_not_pos h
    have hu0 : u = 0 := Fin.ext hval
    exact hu.1 hu0
  unfold chainVZ
  have hsymm : c.2.symm a = ⟨0, hn⟩ := by
    simp [a]
  change c.1 a + (if (c.2.symm a).val < u.val then (1 : ℤ) else 0) = (k : ℤ)
  rw [hsymm]
  rw [if_pos (by simpa using hu_pos)]
  exact ha_eq

theorem endpointInv_lowered_step_last {n : ℕ} (hn : 0 < n) (c : Cell n) :
    (c.2.symm ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩)).val = n - 1 := by
  have hpre :
      c.2.symm ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩) =
        (finRotate n).symm ⟨0, hn⟩ := by
    simp [Equiv.Perm.coe_mul]
  rw [hpre]
  exact ShenWork.Paper1.finRotate_symm_zero_val hn

theorem last_facet_subset_lower_face_of_endpointInv_invalid {n k : ℕ}
    (hn : 0 < n) {c : Cell n} (hc : c ∈ cells n k)
    (hinv : ¬ cellValid k (endpointInv hn c)) :
    ∀ v ∈ facetSet c.1 c.2 (Fin.last n),
      v ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩) = 0 := by
  classical
  let b : Fin n := (c.2 * (finRotate n)⁻¹) ⟨0, hn⟩
  have hnotpos : ¬ 0 < c.1 b := by
    intro hpos
    apply hinv
    unfold endpointInv cellValid
    change ∀ i, 0 ≤ c.1 i - unitVec b i ∧
      c.1 i - unitVec b i < (k : ℤ)
    intro i
    have hi := mem_cells.mp hc i
    by_cases hib : i = b
    · subst i
      simp [unitVec]
      omega
    · simp [unitVec, hib]
      omega
  have hb_valid := mem_cells.mp hc b
  have hb_zero : c.1 b = 0 := by omega
  intro v hv
  unfold facetSet at hv
  rw [Finset.mem_image] at hv
  rcases hv with ⟨u, hu, rfl⟩
  rw [Finset.mem_erase] at hu
  have hu_lt : u.val < n := by
    have hne : u.val ≠ n := by
      intro h
      exact hu.1 (Fin.ext (by simpa [Fin.val_last] using h))
    have hle : u.val ≤ n := by omega
    omega
  have hb_last_step : (c.2.symm b).val = n - 1 :=
    endpointInv_lowered_step_last hn c
  have hnot : ¬ (c.2.symm b).val < u.val := by
    rw [hb_last_step]
    omega
  unfold chainVZ
  change c.1 b + (if (c.2.symm b).val < u.val then (1 : ℤ) else 0) = 0
  rw [if_neg hnot, hb_zero]
  omega

theorem cubeBoundaryCert_boundaryBottom {n k : ℕ} {L : Label (n + 1)}
    (hcert : CubeBoundaryCert (n + 1) k L) :
    ∀ F ∈ facets (n + 1) k,
      (F.image L = Finset.univ.erase (Fin.last (n + 1))) →
        isBoundary (Nat.succ_pos n) k F →
          ∀ v ∈ F, v (Fin.last n) = 0 := by
  classical
  intro F _hF hdoor hb v hv
  rcases isBoundary_endpoint (Nat.succ_pos n) hb with
    ⟨c, hc, hcb, hpinv, hend⟩
  have hfacet_drop := facetSet_dropOf hcb
  rcases hend with hdrop0 | hdroplast
  · have hFzero : facetSet c.1 c.2 0 = F := by
      simpa [dropOf_eq_zero hdrop0] using hfacet_drop
    have hinvFwd : ¬ cellValid k (endpointFwd (Nat.succ_pos n) c) := by
      simpa [partnerCell_of_zero (Nat.succ_pos n) c hdrop0] using hpinv
    have hface :=
      zero_facet_subset_upper_face_of_endpointFwd_invalid (Nat.succ_pos n) hc hinvFwd
    let a : Fin (n + 1) := c.2 ⟨0, Nat.succ_pos n⟩
    have htarget : a.castSucc ∈ Finset.univ.erase (Fin.last (n + 1)) := by
      rw [Finset.mem_erase]
      exact ⟨Fin.castSucc_ne_last a, Finset.mem_univ _⟩
    have himage : a.castSucc ∈ F.image L := by
      rw [hdoor]
      exact htarget
    rw [Finset.mem_image] at himage
    rcases himage with ⟨w, hwF, hwL⟩
    have hwFacet : w ∈ facetSet c.1 c.2 0 := by simpa [hFzero] using hwF
    have hwgrid := cubeGridVertex_of_mem_facet hc hwFacet
    have hne := hcert.upper_ne w hwgrid a (hface w hwFacet)
    exact False.elim (hne hwL)
  · have hdrop_ne_zero : (dropOf c F).val ≠ 0 := by omega
    have hlast : dropOf c F = Fin.last (n + 1) := dropOf_eq_last hdroplast
    have hFlast : facetSet c.1 c.2 (Fin.last (n + 1)) = F := by
      simpa [hlast] using hfacet_drop
    have hinvInv : ¬ cellValid k (endpointInv (Nat.succ_pos n) c) := by
      simpa [partnerCell_of_last (Nat.succ_pos n) c hdrop_ne_zero hdroplast]
        using hpinv
    have hface :=
      last_facet_subset_lower_face_of_endpointInv_invalid (Nat.succ_pos n) hc hinvInv
    let b : Fin (n + 1) := (c.2 * (finRotate (n + 1))⁻¹) ⟨0, Nat.succ_pos n⟩
    by_cases hb_last : b = Fin.last n
    · have hvFacet : v ∈ facetSet c.1 c.2 (Fin.last (n + 1)) := by
        simpa [hFlast] using hv
      have hvzero := hface v hvFacet
      change v b = 0 at hvzero
      simpa [hb_last] using hvzero
    · have htarget : b.succ ∈ Finset.univ.erase (Fin.last (n + 1)) := by
        rw [Finset.mem_erase]
        constructor
        · exact (Fin.succ_ne_last_iff b).mpr hb_last
        · exact Finset.mem_univ _
      have himage : b.succ ∈ F.image L := by
        rw [hdoor]
        exact htarget
      rw [Finset.mem_image] at himage
      rcases himage with ⟨w, hwF, hwL⟩
      have hwFacet : w ∈ facetSet c.1 c.2 (Fin.last (n + 1)) := by
        simpa [hFlast] using hwF
      have hwgrid := cubeGridVertex_of_mem_facet hc hwFacet
      have hwzero := hface w hwFacet
      change w b = 0 at hwzero
      have hne := hcert.lower_ne w hwgrid b hwzero
      exact False.elim (hne hwL)

theorem BoundaryBottomData_of_cubeBoundaryCert {n k : ℕ} {L : Label n}
    (hcert : CubeBoundaryCert n k L) :
    BoundaryBottomData n k L := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      let havoid := hcert.bottom_havoid
      refine ⟨havoid, cubeBoundaryCert_boundaryBottom hcert, ?_⟩
      exact ih (hcert.bottomLabel havoid)

theorem cubeKuhnLabel_boundaryBottomData {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n)) :
    BoundaryBottomData n k (cubeKuhnLabel (strictify δ T) k) :=
  BoundaryBottomData_of_cubeBoundaryCert
    (cubeKuhnLabel_boundaryCert hk hδ hδle hmaps)

theorem exists_rainbow_cell_cubeKuhnLabel {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n)) :
    ∃ c ∈ cells n k, isRainbow (cubeKuhnLabel (strictify δ T) k) c :=
  exists_rainbow_cellF_of_boundaryBottomData hk
    (cubeKuhnLabel (strictify δ T) k)
    (cubeKuhnLabel_boundaryBottomData hk hδ hδle hmaps)

theorem rainbow_count_odd_cubeKuhnLabel {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n)) :
    Odd ((cells n k).filter
      (fun c => isRainbow (cubeKuhnLabel (strictify δ T) k) c)).card :=
  rainbow_count_odd_of_boundaryBottomData hk
    (cubeKuhnLabel (strictify δ T) k)
    (cubeKuhnLabel_boundaryBottomData hk hδ hδle hmaps)

theorem unitCube_eq_pi (n : ℕ) :
    unitCube n = Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · intro hx
    intro i _hi
    exact hx i
  · intro hx i
    exact hx i (Set.mem_univ i)

theorem isCompact_unitCube (n : ℕ) : IsCompact (unitCube n) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)

theorem strictify_mapsTo_unitCube {n : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n)) :
    Set.MapsTo (strictify δ T) (unitCube n) (unitCube n) := by
  intro x hx i
  have hTx := hmaps hx i
  have hcoeff : 0 ≤ 1 - 2 * δ := by nlinarith
  constructor
  · have hmul : 0 ≤ (1 - 2 * δ) * T x i :=
      mul_nonneg hcoeff hTx.1
    unfold strictify
    nlinarith
  · have hmul : (1 - 2 * δ) * T x i ≤ (1 - 2 * δ) * 1 :=
      mul_le_mul_of_nonneg_left hTx.2 hcoeff
    unfold strictify
    nlinarith

theorem strictify_continuousOn_unitCube {n : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hTcont : ContinuousOn T (unitCube n)) :
    ContinuousOn (strictify δ T) (unitCube n) := by
  rw [continuousOn_pi]
  intro i
  have hcoord : ContinuousOn (fun x => T x i) (unitCube n) :=
    (continuousOn_pi.mp hTcont) i
  exact (hcoord.const_mul (1 - 2 * δ)).add continuousOn_const

theorem base_cubeGridVertex_of_mem_cells {n k : ℕ} {c : Cell n}
    (hc : c ∈ cells n k) : cubeGridVertex k c.1 := by
  intro i
  have hi := mem_cells.mp hc i
  exact ⟨hi.1, le_of_lt hi.2⟩

theorem cubePoint_chainVZ_coord_close_base {n k : ℕ} (hk : 0 < k)
    (c : Cell n) (t : Fin (n + 1)) (i : Fin n) :
    |cubePoint k (chainVZ c.1 c.2 t) i - cubePoint k c.1 i| ≤ (1 : ℝ) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hinv_nonneg : 0 ≤ (1 : ℝ) / k := by positivity
  unfold cubePoint chainVZ
  by_cases hlt : (c.2.symm i).val < t.val
  · rw [if_pos hlt]
    have hdiff :
        ((c.1 i + 1 : ℤ) : ℝ) / (k : ℝ) - (c.1 i : ℝ) / (k : ℝ) =
          (1 : ℝ) / k := by
      push_cast
      ring_nf
    rw [hdiff, abs_of_nonneg hinv_nonneg]
  · rw [if_neg hlt]
    simpa using hinv_nonneg

theorem cubeDisp_nonneg_of_label_castSucc {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {v : Fin n → ℤ} {i : Fin n}
    (hv : cubeGridVertex k v)
    (hlabel : cubeKuhnLabel T k v = i.castSucc) :
    0 ≤ cubeDisp T k v i := by
  have hle := cubeKuhnLabel_min_le T hv i.succ
  rw [hlabel, cubePartialSum_succ] at hle
  linarith

theorem cubeDisp_nonpos_of_label_succ {n k : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {v : Fin n → ℤ} {i : Fin n}
    (hv : cubeGridVertex k v)
    (hlabel : cubeKuhnLabel T k v = i.succ) :
    cubeDisp T k v i ≤ 0 := by
  have hle := cubeKuhnLabel_min_le T hv i.castSucc
  rw [hlabel, cubePartialSum_succ] at hle
  linarith

theorem cubePoint_chainVZ_tendsto_base {n : ℕ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {c : ℕ → Cell n} {x : Fin n → ℝ}
    (htend :
      Tendsto (fun j => cubePoint (φ j + 1) (c (φ j)).1) atTop (𝓝 x))
    (t : ℕ → Fin (n + 1)) :
    Tendsto
      (fun j => cubePoint (φ j + 1)
        (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j)))) atTop (𝓝 x) := by
  rw [tendsto_pi_nhds]
  intro r
  have hbase_r : Tendsto
      (fun j => cubePoint (φ j + 1) (c (φ j)).1 r) atTop (𝓝 (x r)) :=
    ((continuous_apply r).continuousAt.tendsto).comp htend
  have hgap0 : Tendsto (fun j => (1 : ℝ) / (φ j + 1)) atTop (𝓝 0) := by
    have hmono : Tendsto (fun j => (φ j : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    simpa using hmono.inv_tendsto_atTop.const_mul (1 : ℝ)
  have hdiff0 : Tendsto
      (fun j =>
        cubePoint (φ j + 1)
            (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j))) r -
          cubePoint (φ j + 1) (c (φ j)).1 r) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun j => (1 : ℝ) / (φ j + 1))
    intro j
    simpa [Real.norm_eq_abs] using
      cubePoint_chainVZ_coord_close_base (Nat.succ_pos (φ j))
        (c (φ j)) (t (φ j)) r
    exact hgap0
  have := hdiff0.add hbase_r
  simpa using this

theorem cubeDisp_tendsto_of_chainVZ {n : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {c : ℕ → Cell n} {x : Fin n → ℝ} {t : ℕ → Fin (n + 1)}
    (hx : x ∈ unitCube n)
    (hc : ∀ m, c m ∈ cells n (m + 1))
    (hTcont : ContinuousOn T (unitCube n))
    (htend :
      Tendsto (fun j => cubePoint (φ j + 1) (c (φ j)).1) atTop (𝓝 x))
    (i : Fin n) :
    Tendsto
      (fun j => cubeDisp T (φ j + 1)
        (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j))) i)
      atTop (𝓝 (T x i - x i)) := by
  have hvtend := cubePoint_chainVZ_tendsto_base hφ htend t
  have hvmem : ∀ j,
      cubePoint (φ j + 1)
        (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j))) ∈ unitCube n := by
    intro j
    exact cubePoint_mem_unitCube (Nat.succ_pos (φ j))
      (chainVZ_cubeGridVertex_of_mem_cells (hc (φ j)) (t (φ j)))
  have hTtend : Tendsto
      (fun j =>
        T (cubePoint (φ j + 1)
          (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j)))))
      atTop (𝓝 (T x)) := by
    apply (hTcont.continuousWithinAt hx).tendsto.comp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hvtend (Eventually.of_forall hvmem)
  have hTcoord : Tendsto
      (fun j =>
        T (cubePoint (φ j + 1)
          (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j)))) i)
      atTop (𝓝 (T x i)) :=
    ((continuous_apply i).continuousAt.tendsto).comp hTtend
  have hvcoord : Tendsto
      (fun j =>
        cubePoint (φ j + 1)
          (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j))) i)
      atTop (𝓝 (x i)) :=
    (tendsto_pi_nhds.mp hvtend) i
  simpa [cubeDisp] using hTcoord.sub hvcoord

theorem strictify_fixedPoint_of_cube_parity {n : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ (1 : ℝ) / 2)
    (hmaps : Set.MapsTo T (unitCube n) (unitCube n))
    (hTcont : ContinuousOn T (unitCube n)) :
    ∃ x ∈ unitCube n, strictify δ T x = x := by
  classical
  let Tδ := strictify δ T
  have hTδcont : ContinuousOn Tδ (unitCube n) :=
    strictify_continuousOn_unitCube hTcont
  choose c hc hrain using fun m : ℕ =>
    exists_rainbow_cell_cubeKuhnLabel (Nat.succ_pos m) hδ hδle hmaps
  set xseq : ℕ → Fin n → ℝ := fun m => cubePoint (m + 1) (c m).1 with hxseq
  have hxseq_mem : ∀ m, xseq m ∈ unitCube n := by
    intro m
    exact cubePoint_mem_unitCube (Nat.succ_pos m)
      (base_cubeGridVertex_of_mem_cells (hc m))
  obtain ⟨x, hx, φ, hφ, htend⟩ :=
    (isCompact_unitCube n).tendsto_subseq hxseq_mem
  refine ⟨x, hx, ?_⟩
  funext i
  have hnonneg : 0 ≤ Tδ x i - x i := by
    have hsurj : ∀ m, ∃ t : Fin (n + 1),
        cellColor (cubeKuhnLabel Tδ (m + 1)) (c m) t = i.castSucc := by
      intro m
      exact (hrain m).2 i.castSucc
    choose t ht using hsurj
    have hdisp_tend :=
      cubeDisp_tendsto_of_chainVZ hφ hx hc hTδcont htend i (t := t)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hdisp_tend
    exact Eventually.of_forall (fun j => by
      have hv := chainVZ_cubeGridVertex_of_mem_cells (hc (φ j)) (t (φ j))
      have hlabel : cubeKuhnLabel Tδ (φ j + 1)
          (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j))) = i.castSucc := by
        simpa [cellColor] using ht (φ j)
      exact cubeDisp_nonneg_of_label_castSucc hv hlabel)
  have hnonpos : Tδ x i - x i ≤ 0 := by
    have hsurj : ∀ m, ∃ t : Fin (n + 1),
        cellColor (cubeKuhnLabel Tδ (m + 1)) (c m) t = i.succ := by
      intro m
      exact (hrain m).2 i.succ
    choose t ht using hsurj
    have hdisp_tend :=
      cubeDisp_tendsto_of_chainVZ hφ hx hc hTδcont htend i (t := t)
    apply le_of_tendsto_of_tendsto hdisp_tend tendsto_const_nhds
    exact Eventually.of_forall (fun j => by
      have hv := chainVZ_cubeGridVertex_of_mem_cells (hc (φ j)) (t (φ j))
      have hlabel : cubeKuhnLabel Tδ (φ j + 1)
          (chainVZ (c (φ j)).1 (c (φ j)).2 (t (φ j))) = i.succ := by
        simpa [cellColor] using ht (φ j)
      exact cubeDisp_nonpos_of_label_succ hv hlabel)
  change Tδ x i = x i
  linarith

theorem pi_norm_le_of_forall {n : ℕ} {f : Fin n → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ i, ‖f i‖ ≤ r) : ‖f‖ ≤ r := by
  cases n with
  | zero =>
      simp [Pi.norm_def, hr]
  | succ n =>
      haveI : Nonempty (Fin (n + 1)) := ⟨0⟩
      exact (pi_norm_le_iff_of_nonempty f).2 h

theorem brouwer_cube_approx {n : ℕ}
    {T : (Fin n → ℝ) → Fin n → ℝ}
    (hT : Set.MapsTo T (unitCube n) (unitCube n))
    (hTcont : ContinuousOn T (unitCube n)) :
    ∀ ε > 0, ∃ x ∈ unitCube n, ‖T x - x‖ ≤ ε := by
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 4)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδle_half : δ ≤ (1 : ℝ) / 2 := by
    have hmin : δ ≤ (1 : ℝ) / 4 := min_le_right _ _
    nlinarith
  have hδε : δ ≤ ε := by
    have hmin : δ ≤ ε / 2 := min_le_left _ _
    nlinarith
  obtain ⟨x, hx, hfix⟩ :=
    strictify_fixedPoint_of_cube_parity hδpos hδle_half hT hTcont
  refine ⟨x, hx, ?_⟩
  have hcoord : ∀ i, ‖(T x - x) i‖ ≤ δ := by
    intro i
    have hTx := hT hx i
    have hxi : strictify δ T x i = x i := congrFun hfix i
    have hdiff : (T x - x) i = δ * (2 * T x i - 1) := by
      change T x i - x i = δ * (2 * T x i - 1)
      rw [← hxi]
      unfold strictify
      ring
    have habs : |2 * T x i - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [hTx.1, hTx.2]
    rw [hdiff, Real.norm_eq_abs, abs_mul, abs_of_nonneg hδpos.le]
    have hmul := mul_le_mul_of_nonneg_left habs hδpos.le
    simpa using hmul
  exact le_trans (pi_norm_le_of_forall hδpos.le hcoord) hδε

#print axioms cubeKuhnLabel_boundaryBottomData
#print axioms rainbow_count_odd_cubeKuhnLabel
#print axioms exists_rainbow_cell_cubeKuhnLabel
#print axioms strictify_fixedPoint_of_cube_parity
#print axioms brouwer_cube_approx

end

end Freudenthal

end ShenWork.Paper1
