/-
# n-D Brouwer: the boundary-door count (R3) — the dimension-drop reduction

This file carries the heaviest remaining brick of the from-scratch n-dimensional Brouwer fixed
point theorem: the **odd boundary-door count** `hR3` consumed by
`ShenWork.Paper1.exists_rainbow_cellN`.  The door-bearing boundary face of `Δⁿ` is
`{q : q (Fin.last n) = 0}`, a copy of `Δⁿ⁻¹`; the boundary doors on that face biject with the
rainbow cells of the induced `(n-1)`-dimensional Kuhn complex, whose count is odd by the
`(n-1)` instance of the Sperner door lemma (base `n = 1` = the committed `sperner_one_dim`).

The genuine content is the *face re-encoding* (restrict `Fin (n+1) → ℤ` lattice points lying on
`{last = 0}` to `Fin n → ℤ`, restrict the labelling), the *door ↔ rainbow* bijection on the
face, and the *dimension-drop induction* wiring.  This file builds that re-encoding layer and
records the precise frontier (see the in-file stall report at the end).
-/
import ShenWork.Paper1.BrouwerNDimBoundary

namespace ShenWork.Paper1

open Set Finset

/-! ## The face restriction: dropping the last (vanishing) coordinate

A lattice point `v : Fin (n+1) → ℤ` lying on the distinguished boundary face
`{q : q (Fin.last n) = 0}` is determined by its first `n` coordinates `Fin.init v : Fin n → ℤ`
(the last coordinate is `0`).  The map `dropLast := Fin.init` restricts such points to
`Fin n → ℤ` and is injective on the face (its inverse `Fin.snoc · 0` re-appends the zero). -/

/-- Drop the last coordinate of a lattice point (`= Fin.init`). -/
def dropLast {n : ℕ} (v : Fin (n + 1) → ℤ) : Fin n → ℤ := Fin.init v

/-- Re-append a zero last coordinate (the inverse of `dropLast` on the face `{last = 0}`). -/
def appendZero {n : ℕ} (w : Fin n → ℤ) : Fin (n + 1) → ℤ := Fin.snoc w (0 : ℤ)

/-- `appendZero` lands on the face `{last = 0}`. -/
@[simp] theorem appendZero_last {n : ℕ} (w : Fin n → ℤ) :
    appendZero w (Fin.last n) = 0 := by
  simp [appendZero]

/-- `appendZero` agrees with `w` on the first `n` coordinates. -/
@[simp] theorem appendZero_castSucc {n : ℕ} (w : Fin n → ℤ) (i : Fin n) :
    appendZero w i.castSucc = w i := by
  simp [appendZero, Fin.snoc_castSucc]

/-- `dropLast` followed by `appendZero` recovers any point on the face `{last = 0}`. -/
theorem appendZero_dropLast {n : ℕ} {v : Fin (n + 1) → ℤ} (hv : v (Fin.last n) = 0) :
    appendZero (dropLast v) = v := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simpa using hv.symm
  · intro j
    simp [dropLast, appendZero, Fin.snoc_castSucc, Fin.init]

/-- `dropLast (appendZero w) = w` (left inverse, unconditionally). -/
@[simp] theorem dropLast_appendZero {n : ℕ} (w : Fin n → ℤ) :
    dropLast (appendZero w) = w := by
  funext j
  simp [dropLast, appendZero, Fin.init, Fin.snoc_castSucc]

/-- On the face `{last = 0}`, `dropLast` is injective. -/
theorem dropLast_injOn {n : ℕ} {v v' : Fin (n + 1) → ℤ}
    (hv : v (Fin.last n) = 0) (hv' : v' (Fin.last n) = 0)
    (h : dropLast v = dropLast v') : v = v' := by
  rw [← appendZero_dropLast hv, ← appendZero_dropLast hv', h]

/-! ## Boundary facets are endpoint drops

A facet is `isBoundaryN` iff *some* present cell bounding it has an invalid partner.  By the
internal squeeze (`cellValid_swapAround`: dropping an *internal* index `0 < t < n` always yields
a valid partner), the cell witnessing the boundary must drop `F` at an **endpoint**: either
`t = 0` (top last-coordinate `p(last)`) or `t = last` (the face `{last = 0}` when `p(last) = n`).
This pins the geometry of the boundary doors and is the structural entry point of R2/R3. -/

/-- **Boundary ⇒ endpoint drop.**  If `F` is a boundary facet (`isBoundaryN`), the cell `c`
witnessing it drops `F` at an endpoint: `(dropOf c F).val = 0` or `(dropOf c F).val = n`. -/
theorem isBoundaryN_endpoint {n : ℕ} (hn : 0 < n) (k : ℕ) {F : Finset (Fin (n + 1) → ℤ)}
    (hb : isBoundaryN hn k F) :
    ∃ c, cellMemN k c ∧ cellBounds c F ∧ ¬ cellMemN k (partnerCell hn c F) ∧
      ((dropOf c F).val = 0 ∨ (dropOf c F).val = n) := by
  obtain ⟨c, hck, hcb, hpinv⟩ := hb
  refine ⟨c, hck, hcb, hpinv, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, hn'⟩ := hcon
  -- internal drop: the squeeze gives a valid partner, contradicting `hpinv`
  have hlt : (dropOf c F).val < n := by
    have := (dropOf c F).isLt; omega
  have h0' : 0 < (dropOf c F).val := by omega
  rw [partnerCell_of_internal hn c (by omega) (by omega)] at hpinv
  apply hpinv
  unfold cellMemN at hck ⊢
  exact cellValid_swapAround h0' hlt hck

/-! ## The face labelling and the colour-drop on the face

The `n`-D labelling `L : (Fin (n+1) → ℤ) → Fin (n+1)` is `spernerLabelN f k ∘ toNat`.  On the
face `{q (Fin.last n) = 0}` (a lattice point with vanishing last coordinate, embedded into `Δⁿ`
with `embPt k · (last) = 0`), `spernerLabelN_ne_of_zero` forbids the top colour `Fin.last n`:
the label lands in `univ.erase (Fin.last n) ≃ Fin n`.  Thus a face point carries an
`(n-1)`-dimensional colour, the substrate of the door ↔ rainbow correspondence. -/

/-- The `(n+1)`-colour Kuhn labelling from a self-map `f` at mesh `k`, on integer bases:
`labelN f k v = spernerLabelN f k (toNat ∘ v)`. -/
noncomputable def labelN {n : ℕ} (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ)
    (v : Fin (n + 1) → ℤ) : Fin (n + 1) :=
  spernerLabelN f k (fun i => (v i).toNat)

/-- A face lattice point (vanishing last coordinate, a nonnegative valid lattice point) is sent
by `labelN` to a colour distinct from `Fin.last n`: the embedded point has last coordinate `0`,
so `spernerLabelN_ne_of_zero` forbids the top colour. -/
theorem labelN_ne_last_on_face {n k : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1))))
    {v : Fin (n + 1) → ℤ} (hsum : ∑ i, (v i).toNat = k)
    (hnn : ∀ i, 0 ≤ v i) (hlast : v (Fin.last n) = 0) :
    labelN f k v ≠ Fin.last n := by
  set q : Fin (n + 1) → ℕ := fun i => (v i).toNat with hq
  have hv : embPt k q ∈ stdSimplex ℝ (Fin (n + 1)) := embPt_mem_stdSimplex hk hsum
  have hfv : f (embPt k q) ∈ stdSimplex ℝ (Fin (n + 1)) := hmaps hv
  have hzero : embPt k q (Fin.last n) = 0 := by
    simp only [embPt, hq, hlast, Int.toNat_zero, Nat.cast_zero, zero_div]
  exact spernerLabelN_ne_of_zero hv hfv hzero

/-! ## The door-colour structure of a boundary door

A *door* facet (`F.image L = univ.erase (Fin.last n)`) carries exactly the `n` lower colours
`{0,…,n-1}`.  Combined with `labelN_ne_last_on_face`, this says: the `n` vertices of a boundary
door receive all and only the colours `{0,…,n-1}`, each exactly once (a *rainbow* face cell of
the induced `(n-1)`-complex).  The `(n-1)`-Sperner count on the face then makes the boundary-door
count odd.  We record the colour-set identity used by the door ↔ rainbow correspondence. -/

/-- A door facet's colour multiset is exactly the lower colours, each appearing once: the `L`-
image is `univ.erase (Fin.last n)` and `F` has `n` elements, so `L` is injective on `F`. -/
theorem door_injOn_of_card {n : ℕ} {L : (Fin (n + 1) → ℤ) → Fin (n + 1)}
    {F : Finset (Fin (n + 1) → ℤ)} (hcard : F.card = n)
    (hdoor : F.image L = Finset.univ.erase (Fin.last n)) :
    Set.InjOn L ↑F := by
  classical
  have himgcard : (F.image L).card = n := by
    rw [hdoor, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]; omega
  have hle : (F.image L).card = F.card := by rw [himgcard, hcard]
  exact Finset.injOn_of_card_image_eq hle

/-! ## The endpoint (face-end) partner base-shift, coordinatewise

The boundary doors live at the `t = last` end of cells with `p (Fin.last n) = n` (the chain
just reaches the face `{q (Fin.last n) = 0}` at its lowest vertex).  The relevant partner there
is `endpointInv`, which shifts the base by `-stepVec ((σ·(finRotate n)⁻¹) 0)`: it *raises* the
last coordinate by `1` (the chain would need an `(n+1)`-st step that exits `Δⁿ` through the face)
and lowers exactly one non-last coordinate by `1`.  These coordinatewise identities pin the
off-mesh condition (a base coordinate driven negative) that makes the partner invalid. -/

/-- The face-end partner raises the base's last coordinate by exactly `1`: the `endpointInv`
shift's last component is `-stepVec(...) (last) = -(-1) = +1`. -/
theorem endpointInv_base_last {n : ℕ} (hn : 0 < n) (c : KCell n) :
    (endpointInv hn c).1 (Fin.last n) = c.1 (Fin.last n) + 1 := by
  simp only [endpointInv]
  have hstep : stepVec ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩) (Fin.last n) = -1 := stepVec_last _
  rw [hstep]; ring

/-- Off the affected non-last coordinate, the `endpointInv` shift is identity.  Concretely, at
the coordinate `i = ((σ·(finRotate n)⁻¹) 0).castSucc` the base drops by `1`; everywhere else
(other than `last`, handled by `endpointInv_base_last`) it is unchanged. -/
theorem endpointInv_base_castSucc {n : ℕ} (hn : 0 < n) (c : KCell n) :
    (endpointInv hn c).1 ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩).castSucc
      = c.1 ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩).castSucc - 1 := by
  set a := (c.2 * (finRotate n)⁻¹) ⟨0, hn⟩ with ha
  simp only [endpointInv]
  have hstep : stepVec a a.castSucc = 1 := by
    unfold stepVec
    have hne : a.castSucc ≠ Fin.last n := by
      intro hc'; have := congrArg Fin.val hc'
      simp only [Fin.val_castSucc, Fin.val_last] at this; omega
    rw [if_pos rfl, if_neg hne]; ring
  rw [hstep]

/-- **Face-end off-mesh criterion.**  If the `endpointInv` shift lowers a base coordinate that
is already `0` (the affected non-last coordinate `a.castSucc` has `c.1 (a.castSucc) = 0`), then
the partner `endpointInv hn c` is INVALID at mesh `k`: its base (the `t = 0` chain vertex) is
negative there, violating nonnegativity.  This is the boundary-face condition — the partner
exits `Δⁿ` through `{q (Fin.last n) = 0}`. -/
theorem endpointInv_invalid_of_base_zero {n k : ℕ} (hn : 0 < n) (c : KCell n)
    (hzero : c.1 ((c.2 * (finRotate n)⁻¹) ⟨0, hn⟩).castSucc = 0) :
    ¬ cellMemN k (endpointInv hn c) := by
  set a := (c.2 * (finRotate n)⁻¹) ⟨0, hn⟩ with ha
  intro hv
  -- the base of `endpointInv c` is its `t = 0` chain vertex, which must be nonnegative
  have hbase : ∀ j, chainVZ (endpointInv hn c).1 (endpointInv hn c).2 0 j
      = (endpointInv hn c).1 j := by
    intro j
    rw [chainVZ_apply]
    have he : (Finset.univ.filter (fun s : Fin n => s.val < (0 : Fin (n + 1)).val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr; intro s _; simp
    rw [he, Finset.sum_empty, add_zero]
  have hnn : 0 ≤ chainVZ (endpointInv hn c).1 (endpointInv hn c).2 0 a.castSucc :=
    cellValid_nonneg hv 0 a.castSucc
  rw [hbase a.castSucc, endpointInv_base_castSucc hn c, hzero] at hnn
  -- now `0 ≤ 0 - 1`, contradiction
  norm_num at hnn

/-! ## The top-end (`t = 0`) partner base-shift, coordinatewise

Symmetrically, the `t = 0` drop's partner is `endpointFwd`, shifting the base by
`+stepVec (σ 0)`: it *lowers* the last coordinate by `1` and raises one non-last coordinate by
`1`.  The top-end off-mesh condition is the partner's chain reaching a negative last coordinate
(it tries to take an extra step out of the last coordinate when it is already exhausted). -/

/-- The top-end partner lowers the base's last coordinate by exactly `1`. -/
theorem endpointFwd_base_last {n : ℕ} (hn : 0 < n) (c : KCell n) :
    (endpointFwd hn c).1 (Fin.last n) = c.1 (Fin.last n) - 1 := by
  simp only [endpointFwd]
  have hstep : stepVec (c.2 ⟨0, hn⟩) (Fin.last n) = -1 := stepVec_last _
  rw [hstep]; ring

/-- The top-end partner raises the base at the affected non-last coordinate by exactly `1`. -/
theorem endpointFwd_base_castSucc {n : ℕ} (hn : 0 < n) (c : KCell n) :
    (endpointFwd hn c).1 (c.2 ⟨0, hn⟩).castSucc = c.1 (c.2 ⟨0, hn⟩).castSucc + 1 := by
  simp only [endpointFwd]
  have hstep : stepVec (c.2 ⟨0, hn⟩) (c.2 ⟨0, hn⟩).castSucc = 1 := by
    unfold stepVec
    have hne : (c.2 ⟨0, hn⟩).castSucc ≠ Fin.last n := by
      intro hc'; have := congrArg Fin.val hc'
      simp only [Fin.val_castSucc, Fin.val_last] at this; omega
    rw [if_pos rfl, if_neg hne]; ring
  rw [hstep]

/-- **Top-end off-mesh criterion.**  If a cell has `c.1 (Fin.last n) = 0` (its base already lies
on the face `{q (Fin.last n) = 0}`), then the top-end partner `endpointFwd hn c` is INVALID:
its base last coordinate is `-1 < 0`.  This is the geometric `∂Δⁿ` condition at the top end —
the top vertex of the partner's chain exits `Δⁿ` through `{q (Fin.last n) = 0}`. -/
theorem endpointFwd_invalid_of_base_last_zero {n k : ℕ} (hn : 0 < n) (c : KCell n)
    (hzero : c.1 (Fin.last n) = 0) :
    ¬ cellMemN k (endpointFwd hn c) := by
  intro hv
  have hbase : ∀ j, chainVZ (endpointFwd hn c).1 (endpointFwd hn c).2 0 j
      = (endpointFwd hn c).1 j := by
    intro j
    rw [chainVZ_apply]
    have he : (Finset.univ.filter (fun s : Fin n => s.val < (0 : Fin (n + 1)).val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr; intro s _; simp
    rw [he, Finset.sum_empty, add_zero]
  have hnn : 0 ≤ chainVZ (endpointFwd hn c).1 (endpointFwd hn c).2 0 (Fin.last n) :=
    cellValid_nonneg hv 0 (Fin.last n)
  rw [hbase (Fin.last n), endpointFwd_base_last hn c, hzero] at hnn
  norm_num at hnn

/-! ## Precise stall report — `BrouwerNDimR3`

**What is fully closed here (axiom-clean: `[propext, Classical.choice, Quot.sound]`).**

* `dropLast`, `appendZero`, `appendZero_last`, `appendZero_castSucc`, `appendZero_dropLast`,
  `dropLast_appendZero`, `dropLast_injOn` — **the face re-encoding (R3 substrate).**  The
  distinguished boundary face is `{q : q (Fin.last n) = 0}`; a face lattice point `v` is pinned
  by its first `n` coordinates `dropLast v = Fin.init v : Fin n → ℤ`, with two-sided inverse
  `appendZero w = Fin.snoc w 0`.  `dropLast` is injective on the face, the bijection that
  carries n-D face data to `(n-1)`-D Kuhn data.

* **`isBoundaryN_endpoint`** — **boundary facets are endpoint drops.**  If `F` is `isBoundaryN`
  (some present cell has an invalid partner), the witnessing cell drops `F` at an *endpoint*
  (`(dropOf c F).val = 0` or `= n`): an internal drop always has a valid partner by the squeeze
  `cellValid_swapAround`, so the boundary geometry is concentrated at the two chain ends.  This
  is the structural entry point for both R2 (which endpoint, uniqueness) and R3 (which end is the
  face `{last = 0}`).

* `labelN`, **`labelN_ne_last_on_face`** — **the face labelling restriction.**  The integer-base
  labelling `labelN f k = spernerLabelN f k ∘ toNat` never assigns the top colour `Fin.last n`
  to a face point (vanishing last coordinate): the embedded point has `embPt k · (last) = 0`, so
  `spernerLabelN_ne_of_zero` forbids it.  Hence a face point carries an `(n-1)`-dimensional
  colour in `univ.erase (Fin.last n) ≃ Fin n` — the labelling-drop the induction needs.

* **`door_injOn_of_card`** — **a door is rainbow on its face.**  A door facet (`L`-image
  `univ.erase (Fin.last n)`) with `n` vertices forces `L` injective on those vertices: it carries
  each lower colour `{0,…,n-1}` exactly once, i.e. it is a *rainbow* `(n-1)`-cell of the face
  complex.  This is the colour half of the door ↔ rainbow correspondence.

* `endpointInv_base_last`, `endpointInv_base_castSucc`, `endpointFwd_base_last`,
  `endpointFwd_base_castSucc` — **the endpoint partner base-shift, coordinatewise.**  At the face
  end (`t = last`), `endpointInv` *raises* the base's last coordinate by `1` and *lowers* one
  non-last coordinate `a.castSucc` (`a := (σ·(finRotate n)⁻¹) 0`) by `1`.  At the top end
  (`t = 0`), `endpointFwd` *lowers* the last coordinate by `1` and raises one non-last coordinate
  by `1`.  These pin exactly which base coordinate the off-mesh test reads.

* **`endpointFwd_invalid_of_base_last_zero`**, **`endpointInv_invalid_of_base_zero`** — **the
  off-mesh criteria (R2/boundary geometry, NOW CLOSED).**  The top-end partner `endpointFwd hn c`
  is INVALID whenever `c.1 (Fin.last n) = 0` (the base already on the face, so the shifted base
  last coordinate is `-1`).  The face-end partner `endpointInv hn c` is INVALID whenever the
  affected non-last coordinate is already exhausted, `c.1 a.castSucc = 0` (the shifted base is
  `-1` there).  Each is proved by reading the `t = 0` chain vertex (= the base) and contradicting
  `cellValid_nonneg`.  These are the genuine `∂Δⁿ` invalidity facts that drive `hsingle` (R2).

**Geometry correction (important).**  For `n ≥ 2` a boundary door is **NOT** a sub-simplex lying
*in* the face `{q (Fin.last n) = 0}`: by `chainVZ_last` the `n+1` chain vertices of a single cell
carry *distinct* last coordinates `p(last), …, p(last)−n`, so at most ONE chain vertex sits on
`{last = 0}`; a `facetSet … t` (drop one of the `n+1`) can never have all `n` of its vertices on
the face.  The boundary doors counted by `hR3` are therefore the facets that are (a) *rainbow on
the lower colours* (`image L = univ.erase last`, the top colour forbidden by the labelling, not
the geometry) and (b) `isBoundaryN` (a bounding cell's endpoint partner is off the mesh, via the
two criteria above).  The reduction to `(n-1)`-Sperner is consequently a **base-projection /
generating-path** argument (the 2-D `diag`-hypotenuse bijection of `hboundaryCount` is the
`n = 2` shadow), NOT a literal face-restriction of vertices.  The earlier `dropLast`/`appendZero`
layer is still the right vertex bookkeeping for the projected base, but the on-face-vertex framing
it suggested does not hold for the *door facets themselves*.

**The remaining frontier (the genuine `(n-1)`-Sperner induction — the heaviest brick).**

  (R3) BOUNDARY-DOOR COUNT.  The target consumed by `exists_rainbow_cellN` is

         `Odd ((facetsN n k).filter
            (fun F => F.image L = univ.erase (Fin.last n) ∧ isBoundaryN hn k F)).card`.

       By `isBoundaryN_endpoint` every such `F` is an *endpoint*-drop facet, and the off-mesh
       criteria pin the boundary side to a base coordinate hitting `0`.  The remaining
       construction, *from scratch*, is:

       (i)   the `(n-1)`-face Kuhn complex re-encoding: build the induced `(n-1)`-dimensional
             Kuhn subdivision via the base/step-order restriction `(p, σ) ↦ (dropLast p, σ')`
             (`σ' : Perm (Fin (n-1))` restricting `σ` once the boundary fixes the last Kuhn step);
             the vertex bookkeeping `dropLast`/`appendZero` is in place;

       (ii)  the door ↔ rainbow bijection: a boundary door (lower colours `{0,…,n-1}` once each by
             `door_injOn_of_card`, top colour forbidden by `labelN_ne_last_on_face`) corresponds —
             through the *base projection*, NOT a vertex restriction (see the geometry correction
             above) — to a rainbow cell of the `(n-1)` complex; a `Finset.card_nbij'` matching the
             2-D `hboundaryCount`'s `diag`-hypotenuse bijection at symbolic `n`;

       (iii) the dimension-drop induction: the rainbow-cell count of the `(n-1)` complex is odd by
             the `(n-1)` instance of `exists_rainbow_cellN` (the inductive hypothesis), base
             `n = 1` the committed `sperner_one_dim`.

       Size: comparable to the entire boundary block of `BrouwerTwoDim.lean` (`hypLabel`,
       `boundary_door_form`, `hboundaryCount`) re-derived at symbolic `n`.  No Mathlib shortcut.

  (R2) PER-DOOR SINGLETON INVALID PARTNER.  `hR2`: a boundary door bounds exactly ONE present
       cell with an invalid partner.  By `isBoundaryN_endpoint` that cell drops at an endpoint;
       the *invalidity* of the single side is now CLOSED by the two off-mesh criteria
       (`endpointFwd_invalid_of_base_last_zero` / `endpointInv_invalid_of_base_zero`: the partner
       is off the mesh exactly when the relevant base coordinate is already `0`).  What remains is
       the *uniqueness*: reconstruction (the converse of `dropOf_eq` across distinct cells) showing
       only ONE bounding cell sits at the off-mesh endpoint.  The backbone (`chainVZ_last`,
       `card_facetSet`, `facetSet_injective`, `isBoundaryN_endpoint`, and now the coordinatewise
       base-shifts) is in place; the at-most-one-crossing count over the two endpoint sides
       remains.

  Then `brouwer_stdSimplex_n {n} (f) (hf) (hmaps) : ∃ x ∈ stdSimplex ℝ (Fin (n+1)), f x = x` is
  `exists_rainbow_cellN` (with R2, R3, `L := labelN f k`) producing a rainbow cell at every mesh,
  fed through the committed `brouwer_of_rainbow_meshes`; `brouwer_compact_convex` then transports
  it to a compact convex `K ⊆ ℝⁿ` via the nearest-point retraction.

**Summary.**  This file closes — axiom-clean — the face re-encoding (`dropLast`/`appendZero` and
its injectivity on `{last = 0}`), the structural reduction of boundary facets to endpoint drops
(`isBoundaryN_endpoint`, via the committed internal squeeze), the face labelling restriction
(`labelN_ne_last_on_face`, the top colour is forbidden on the face), the door-is-rainbow colour
identity (`door_injOn_of_card`), and now the **endpoint partner base-shifts**
(`endpointInv/Fwd_base_last/castSucc`) together with the **two off-mesh invalidity criteria**
(`endpointFwd_invalid_of_base_last_zero`, `endpointInv_invalid_of_base_zero`) — the genuine
`∂Δⁿ`-invalidity facts that supply the *invalid side* of R2's singleton.  What remains is the
genuine dimension-drop construction R3 (the `(n-1)`-face complex, the door ↔ rainbow bijection
*through the base projection* — see the geometry correction — and the induction wiring) together
with the reconstruction-*uniqueness* half of R2 — each a from-scratch geometric brick on the scale
of a second 2-D file, not finite bookkeeping. -/

end ShenWork.Paper1
