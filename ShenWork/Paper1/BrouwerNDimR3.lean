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

/-! ## R2 — reconstruction-uniqueness: a facet pins its bounding cells

The remaining half of R2 is the *uniqueness* of the bounding cell at a fixed drop endpoint.
The backbone is `chainVZ_last`: the `n+1` chain vertices of a cell carry the *distinct,
consecutive* last coordinates `p(last), …, p(last)-n`.  Hence a facet `F` determines, point by
point, which chain index each of its vertices came from — and from that, the base `p` and the
step order `σ` are recovered.  Below we make this canonical reconstruction precise and conclude
that a boundary door bounds **exactly one** present cell with an off-mesh partner. -/

/-- `stepVec` is injective: the step vector `stepVec a` is `+1` exactly at coordinate
`a.castSucc` (and `-1` at `last`), so it determines `a`. -/
theorem stepVec_injective {n : ℕ} : Function.Injective (stepVec (n := n)) := by
  intro a b hab
  have hval := congrFun hab a.castSucc
  -- stepVec a (a.castSucc) = 1 ; stepVec b (a.castSucc) = 1 ⟹ a.castSucc = b.castSucc
  have hane : a.castSucc ≠ Fin.last n := by
    intro h; have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at this; omega
  have ha1 : stepVec a a.castSucc = 1 := by
    unfold stepVec; rw [if_pos rfl, if_neg hane]; ring
  rw [ha1] at hval
  -- now stepVec b (a.castSucc) = 1 forces the +1 coordinate, i.e. a.castSucc = b.castSucc
  unfold stepVec at hval
  by_cases hbc : a.castSucc = b.castSucc
  · exact Fin.castSucc_injective _ hbc
  · rw [if_neg hbc] at hval
    by_cases hbl : a.castSucc = Fin.last n
    · exact absurd hbl hane
    · rw [if_neg hbl] at hval; simp at hval

/-- A permutation is determined by its values away from a single point: if `σ` and `σ'` agree
on every `s ≠ s₀`, they agree everywhere (the remaining value is forced by bijectivity). -/
theorem perm_eq_of_eq_off_point {n : ℕ} {σ σ' : Equiv.Perm (Fin n)} {s₀ : Fin n}
    (h : ∀ s, s ≠ s₀ → σ s = σ' s) : σ = σ' := by
  have hs0 : σ s₀ = σ' s₀ := by
    by_contra hne
    -- σ s₀ ≠ σ' s₀.  σ' s₀ = σ s for some s (σ surjective); that s ≠ s₀ (else σ s₀ = σ' s₀)
    obtain ⟨s, hs⟩ := σ.surjective (σ' s₀)
    have hss0 : s ≠ s₀ := by
      intro he; rw [he] at hs; exact hne hs
    -- then σ' s = σ s = σ' s₀ ⟹ s = s₀ by injectivity of σ', contradiction
    have : σ' s = σ' s₀ := by rw [← h s hss0, hs]
    exact hss0 (σ'.injective this)
  refine Equiv.ext (fun s => ?_)
  by_cases hs : s = s₀
  · rw [hs]; exact hs0
  · exact h s hs

/-- A member of `facetSet p σ t` is exactly a chain vertex of `(p,σ)` at an index `u ≠ t`. -/
theorem mem_facetSet_exists {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) {v : Fin (n + 1) → ℤ} (hv : v ∈ facetSet p σ t) :
    ∃ u : Fin (n + 1), u ≠ t ∧ chainVZ p σ u = v := by
  unfold facetSet at hv
  rw [Finset.mem_image] at hv
  obtain ⟨u, hu, huv⟩ := hv
  rw [Finset.mem_erase] at hu
  exact ⟨u, hu.1, huv⟩

/-- **One Kuhn step.**  `chainVZ p σ (s.succ) = chainVZ p σ (s.castSucc) + stepVec (σ s)`:
advancing the chain index by one adds exactly the `s`-th step. -/
theorem chainVZ_step {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) (s : Fin n) :
    chainVZ p σ s.succ = fun i => chainVZ p σ s.castSucc i + stepVec (σ s) i := by
  classical
  funext i
  rw [chainVZ_apply, chainVZ_apply]
  have hset : (Finset.univ.filter (fun s' : Fin n => s'.val < s.succ.val))
      = insert s (Finset.univ.filter (fun s' : Fin n => s'.val < s.castSucc.val)) := by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc]
    constructor
    · intro h
      rcases Nat.lt_or_ge s'.val s.val with h' | h'
      · exact Or.inr h'
      · left; exact Fin.ext (by omega)
    · rintro (rfl | h') <;> omega
  have hnotmem : s ∉ Finset.univ.filter (fun s' : Fin n => s'.val < s.castSucc.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, not_lt,
      le_refl]
  rw [hset, Finset.sum_insert hnotmem]
  ring

/-- The sum of last coordinates over `facetSet p σ t` equals
`(n+1)·p(last) - (0+1+…+n) + t.val`: it is the full chain sum minus the dropped vertex's last
coordinate.  This is an `F`-invariant pinning `p(last)` once the drop *type* (`t.val`) is fixed. -/
theorem sum_last_facetSet {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) :
    ∑ v ∈ facetSet p σ t, v (Fin.last n)
      = (∑ u : Fin (n + 1), (p (Fin.last n) - (u.val : ℤ))) - (p (Fin.last n) - (t.val : ℤ)) := by
  classical
  unfold facetSet
  rw [Finset.sum_image (by
    intro a _ b _ hab
    exact chainVZ_injective p σ hab)]
  have hfun : ∀ u : Fin (n + 1), chainVZ p σ u (Fin.last n) = p (Fin.last n) - (u.val : ℤ) :=
    fun u => chainVZ_last p σ u
  rw [Finset.sum_congr rfl (fun u _ => hfun u)]
  have hsplit : (∑ u : Fin (n + 1), (p (Fin.last n) - (u.val : ℤ)))
      = (∑ u ∈ Finset.univ.erase t, (p (Fin.last n) - (u.val : ℤ)))
        + (p (Fin.last n) - (t.val : ℤ)) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ t)).symm
  rw [hsplit]; ring

/-- **Index-for-index matching.**  If two cells `(p,σ)` and `(p',σ')` produce the *same* facet
`F` by dropping the *same* index `t`, their chain vertices match at every surviving index:
`chainVZ p σ u = chainVZ p' σ' u` for all `u ≠ t`.  (The last-coordinate sum invariant forces
`p(last)=p'(last)`, then last coordinates being injective pin `u = u'`.) -/
theorem chainVZ_match_off {n : ℕ} (hn : 0 < n) {p p' : Fin (n + 1) → ℤ}
    {σ σ' : Equiv.Perm (Fin n)} {t : Fin (n + 1)}
    (hF : facetSet p σ t = facetSet p' σ' t) :
    ∀ u : Fin (n + 1), u ≠ t → chainVZ p σ u = chainVZ p' σ' u := by
  classical
  have hsum := sum_last_facetSet p σ t
  have hsum' := sum_last_facetSet p' σ' t
  rw [hF] at hsum
  have htel : ∀ q : ℤ, (∑ u : Fin (n + 1), (q - (u.val : ℤ)))
      = (n + 1 : ℤ) * q - (∑ u : Fin (n + 1), (u.val : ℤ)) := by
    intro q
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  rw [htel (p (Fin.last n))] at hsum
  rw [htel (p' (Fin.last n))] at hsum'
  have hlasteq : p (Fin.last n) = p' (Fin.last n) := by
    have h := hsum.symm.trans hsum'
    have hnpos : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    nlinarith [h, hnpos]
  intro u hu
  have hmem : chainVZ p σ u ∈ facetSet p' σ' t := by
    rw [← hF]; unfold facetSet; rw [Finset.mem_image]
    exact ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨u', _, hu'eq⟩ := mem_facetSet_exists p' σ' t hmem
  have hlu : chainVZ p σ u (Fin.last n) = chainVZ p' σ' u' (Fin.last n) := by rw [hu'eq]
  rw [chainVZ_last, chainVZ_last, hlasteq] at hlu
  have huu' : u = u' := Fin.ext (by exact_mod_cast (by omega : (u.val : ℤ) = (u'.val : ℤ)))
  rw [← hu'eq, huu']

/-- **Reconstruction at drop `0`.**  Two cells with the same drop-`0` facet are identical: the
surviving indices `{1,…,n}` are consecutive, so all steps `σ s` for `s ≠ 0` are recovered from
matched consecutive vertices; bijectivity forces `σ 0 = σ' 0` too, and the `u = 1` vertex then
pins `p = p'`. -/
theorem cell_eq_of_facetSet_eq_zero {n : ℕ} (hn : 0 < n) {p p' : Fin (n + 1) → ℤ}
    {σ σ' : Equiv.Perm (Fin n)} (hF : facetSet p σ 0 = facetSet p' σ' 0) :
    p = p' ∧ σ = σ' := by
  have hmatch := chainVZ_match_off hn hF
  -- step recovery: for s ≠ 0, both s.castSucc and s.succ are ≠ 0
  have hstep : ∀ s : Fin n, s ≠ ⟨0, hn⟩ → σ s = σ' s := by
    intro s hs
    have hsc0 : s.castSucc ≠ (0 : Fin (n + 1)) := by
      intro h; apply hs
      have hv : s.castSucc.val = (0 : Fin (n + 1)).val := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_zero] at hv
      exact Fin.ext hv
    have hss0 : s.succ ≠ (0 : Fin (n + 1)) := by
      intro h
      have hv : s.succ.val = (0 : Fin (n + 1)).val := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_zero] at hv
      omega
    have h1 := hmatch s.castSucc hsc0
    have h2 := hmatch s.succ hss0
    have hstepeq : stepVec (σ s) = stepVec (σ' s) := by
      have e1 := chainVZ_step p σ s
      have e2 := chainVZ_step p' σ' s
      funext i
      have := congrFun (e1 ▸ h2 : (fun i => chainVZ p σ s.castSucc i + stepVec (σ s) i)
        = chainVZ p' σ' s.succ) i
      rw [e2, h1] at this
      simp only at this ⊢; linarith
    exact stepVec_injective hstepeq
  have hσ : σ = σ' := perm_eq_of_eq_off_point hstep
  refine ⟨?_, hσ⟩
  -- p = p' from the u = 1 vertex (1 ≠ 0)
  have h1ne : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (0 : Fin (n + 1)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hm := hmatch ⟨1, by omega⟩ h1ne
  funext i
  have hc : chainVZ p σ ⟨1, by omega⟩ i = chainVZ p' σ' ⟨1, by omega⟩ i := congrFun hm i
  rw [chainVZ_apply, chainVZ_apply, hσ] at hc
  -- the prefix sums {s.val < 1} coincide (same σ' now), so p i = p' i
  linarith [hc]

/-- **Reconstruction at drop `last`.**  Two cells with the same drop-`last` facet are identical:
the surviving indices `{0,…,n-1}` are consecutive, so `p = p'` directly (`u = 0`) and all steps
`σ s` for `s ≠ ⟨n-1⟩` are recovered; bijectivity forces the last step too. -/
theorem cell_eq_of_facetSet_eq_last {n : ℕ} (hn : 0 < n) {p p' : Fin (n + 1) → ℤ}
    {σ σ' : Equiv.Perm (Fin n)} (hF : facetSet p σ (Fin.last n) = facetSet p' σ' (Fin.last n)) :
    p = p' ∧ σ = σ' := by
  have hmatch := chainVZ_match_off hn hF
  -- p = p' from u = 0 (0 ≠ last for n ≥ 1)
  have h0ne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h; have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this; omega
  have hp : p = p' := by
    have hm := hmatch 0 h0ne
    funext i
    have hc := congrFun hm i
    rw [chainVZ_apply, chainVZ_apply] at hc
    have he : (Finset.univ.filter (fun s : Fin n => s.val < (0 : Fin (n + 1)).val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr; intro s _; simp
    rw [he, Finset.sum_empty, add_zero, Finset.sum_empty, add_zero] at hc
    exact hc
  refine ⟨hp, ?_⟩
  -- step recovery for s ≠ ⟨n-1⟩: both s.castSucc and s.succ are ≠ last
  have hstep : ∀ s : Fin n, s ≠ ⟨n - 1, by omega⟩ → σ s = σ' s := by
    intro s hs
    have hsc : s.castSucc ≠ Fin.last n := by
      intro h
      have hv : s.castSucc.val = (Fin.last n).val := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_last] at hv
      have := s.isLt; omega
    have hss : s.succ ≠ Fin.last n := by
      intro h; apply hs
      have hv : s.succ.val = (Fin.last n).val := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_last] at hv
      apply Fin.ext
      show s.val = n - 1
      omega
    have h1 := hmatch s.castSucc hsc
    have h2 := hmatch s.succ hss
    have hstepeq : stepVec (σ s) = stepVec (σ' s) := by
      have e1 := chainVZ_step p σ s
      have e2 := chainVZ_step p' σ' s
      funext i
      have := congrFun (e1 ▸ h2 : (fun i => chainVZ p σ s.castSucc i + stepVec (σ s) i)
        = chainVZ p' σ' s.succ) i
      rw [e2, h1] at this
      simp only at this ⊢; linarith
    exact stepVec_injective hstepeq
  exact perm_eq_of_eq_off_point hstep

/-- A bounding cell realises `F` as its `dropOf`-facet. -/
theorem facetSet_dropOf {n : ℕ} {c : KCell n} {F : Finset (Fin (n + 1) → ℤ)}
    (hb : cellBounds c F) : facetSet c.1 c.2 (dropOf c F) = F := by
  obtain ⟨t, ht⟩ := hb
  rw [dropOf_eq c ht]; exact ht

/-- `(dropOf c F).val = 0` means the drop index is `0`. -/
theorem dropOf_eq_zero {n : ℕ} {c : KCell n} {F : Finset (Fin (n + 1) → ℤ)}
    (h : (dropOf c F).val = 0) : dropOf c F = 0 := Fin.ext (by simpa using h)

/-- `(dropOf c F).val = n` means the drop index is `Fin.last n`. -/
theorem dropOf_eq_last {n : ℕ} {c : KCell n} {F : Finset (Fin (n + 1) → ℤ)}
    (h : (dropOf c F).val = n) : dropOf c F = Fin.last n := Fin.ext (by simpa [Fin.val_last])

/-- **Endpoint reconstruction dichotomy.**  If two cells `c, c'` both bound `F` at an *endpoint*
drop (`(dropOf · F).val ∈ {0, n}`), then `c'` is either `c` itself or its `partnerCell`.  The
four endpoint-pair cases reduce — via the same-endpoint reconstruction lemmas
(`cell_eq_of_facetSet_eq_zero/last`) applied after pushing one cell through the committed
endpoint facet-sharing (`endpointFwd_facet`/`endpointInv_facet`) — to `c = c'` (same end) or
`c' = endpointFwd/Inv c = partnerCell hn c F` (opposite ends). -/
theorem bounds_endpoint_dichotomy {n : ℕ} (hn : 0 < n) {c c' : KCell n}
    {F : Finset (Fin (n + 1) → ℤ)} (hcb : cellBounds c F) (hcb' : cellBounds c' F)
    (he : (dropOf c F).val = 0 ∨ (dropOf c F).val = n)
    (he' : (dropOf c' F).val = 0 ∨ (dropOf c' F).val = n) :
    c' = c ∨ c' = partnerCell hn c F := by
  have hfc : facetSet c.1 c.2 (dropOf c F) = F := facetSet_dropOf hcb
  have hfc' : facetSet c'.1 c'.2 (dropOf c' F) = F := facetSet_dropOf hcb'
  rcases he with h0 | hl
  · -- c drops at 0
    rw [dropOf_eq_zero h0] at hfc
    rcases he' with h0' | hl'
    · -- c' drops at 0 too ⟹ c = c'
      rw [dropOf_eq_zero h0'] at hfc'
      have heq := cell_eq_of_facetSet_eq_zero hn (hfc.trans hfc'.symm)
      exact Or.inl (Prod.ext heq.1.symm heq.2.symm)
    · -- c' drops at last; partnerCell c F = endpointFwd c, which also drops F at last
      rw [dropOf_eq_last hl'] at hfc'
      have hfwd : facetSet (endpointFwd hn c).1 (endpointFwd hn c).2 (Fin.last n) = F := by
        rw [endpointFwd_facet hn c]; exact hfc
      have heq := cell_eq_of_facetSet_eq_last hn (hfc'.trans hfwd.symm)
      right
      rw [partnerCell_of_zero hn c h0]
      exact Prod.ext heq.1 heq.2
  · -- c drops at last
    rw [dropOf_eq_last hl] at hfc
    rcases he' with h0' | hl'
    · -- c' drops at 0; partnerCell c F = endpointInv c, which drops F at 0
      rw [dropOf_eq_zero h0'] at hfc'
      have hinv : facetSet (endpointInv hn c).1 (endpointInv hn c).2 0 = F := by
        rw [endpointInv_facet hn c]; exact hfc
      have heq := cell_eq_of_facetSet_eq_zero hn (hfc'.trans hinv.symm)
      right
      rw [partnerCell_of_last hn c (by rw [hl]; omega) hl]
      exact Prod.ext heq.1 heq.2
    · -- both drop at last ⟹ c = c'
      rw [dropOf_eq_last hl'] at hfc'
      have heq := cell_eq_of_facetSet_eq_last hn (hfc.trans hfc'.symm)
      exact Or.inl (Prod.ext heq.1.symm heq.2.symm)

/-- **R2 — per-door singleton invalid partner.**  A boundary facet `F` (`isBoundaryN`) bounds
*exactly one* present cell whose `partnerCell` is off the mesh.  Existence is the `isBoundaryN`
witness (`isBoundaryN_endpoint`); uniqueness is the endpoint reconstruction dichotomy: any other
present invalid-partner cell drops `F` at an endpoint, hence equals `c₀` or its partner — but the
partner is off the mesh (not present), so it must equal `c₀`. -/
theorem boundary_singleton_invalid {n : ℕ} (hn : 0 < n) (k : ℕ)
    {F : Finset (Fin (n + 1) → ℤ)} (hb : isBoundaryN hn k F) :
    ((cellsN n k).filter
        (fun c => cellBounds c F ∧ ¬ cellMemN k (partnerCell hn c F))).card = 1 := by
  classical
  obtain ⟨c₀, hc₀k, hc₀b, hc₀inv, hc₀end⟩ := isBoundaryN_endpoint hn k hb
  rw [Finset.card_eq_one]
  refine ⟨c₀, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨mem_cellsN.mpr hc₀k, hc₀b, hc₀inv⟩
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hck, hcb, hcinv⟩ := hc
    -- c drops F at an endpoint (else internal squeeze gives a valid partner)
    have hcend : (dropOf c F).val = 0 ∨ (dropOf c F).val = n := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨h0, hn'⟩ := hcon
      have hlt : (dropOf c F).val < n := by have := (dropOf c F).isLt; omega
      have h0' : 0 < (dropOf c F).val := by omega
      apply hcinv
      rw [partnerCell_of_internal hn c (by omega) (by omega)]
      unfold cellMemN at *
      exact cellValid_swapAround h0' hlt (mem_cellsN.mp hck)
    -- by the dichotomy, c = c₀ or c = partnerCell c₀ F; the latter is off the mesh, excluded
    rcases bounds_endpoint_dichotomy hn hc₀b hcb hc₀end hcend with h | h
    · exact h
    · exfalso; apply hc₀inv
      rw [← h]; exact mem_cellsN.mp hck

/-- **`hboundaryOddN`, unconditional on R2.**  A boundary facet `F` (`isBoundaryN`) bounds an
*odd* number of present cells, with the singleton invalid-partner crux now discharged by
`boundary_singleton_invalid`. -/
theorem hboundaryOddN_uncond {n : ℕ} (hn : 0 < n) (k : ℕ) {F : Finset (Fin (n + 1) → ℤ)}
    (hb : isBoundaryN hn k F) :
    Odd ((cellsN n k).filter (fun c => cellBounds c F)).card :=
  hboundaryOddN hn k F (boundary_singleton_invalid hn k hb)

/-- **n-D Sperner output with R2 discharged.**  Identical to `exists_rainbow_cellN` but with the
per-door singleton hypothesis `hR2` now *proved* (`boundary_singleton_invalid`); only the
boundary-door count `hR3` remains as a hypothesis. -/
theorem exists_rainbow_cellN_R2 {n : ℕ} (hn : 0 < n) (k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1))
    (hR3 : Odd ((facetsN n k).filter
      (fun F => (F.image L = Finset.univ.erase (Fin.last n)) ∧ isBoundaryN hn k F)).card) :
    Odd ((cellsN n k).filter (fun c => Function.Bijective (cellColorN L c))).card :=
  exists_rainbow_cellN hn k L
    (fun F _ _ hbF => boundary_singleton_invalid hn k hbF) hR3

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

* `stepVec_injective`, `perm_eq_of_eq_off_point`, `chainVZ_step`, `mem_facetSet_exists`,
  `sum_last_facetSet`, `chainVZ_match_off`, **`cell_eq_of_facetSet_eq_zero`**,
  **`cell_eq_of_facetSet_eq_last`** — **the reconstruction backbone (R2 uniqueness).**  The
  `n+1` chain vertices carry the distinct, consecutive last coordinates `p(last), …, p(last)-n`
  (`chainVZ_last`), so a facet's points match index-for-index across two cells dropping the same
  index (`chainVZ_match_off`, pinning `p(last)=p'(last)` by the last-coordinate sum invariant
  `sum_last_facetSet`).  The single Kuhn step `chainVZ_step` then recovers each `stepVec(σ s)`
  from matched consecutive vertices; `stepVec_injective` gives `σ s = σ' s` for all but one step,
  and `perm_eq_of_eq_off_point` (a permutation is pinned by its values off one point) forces the
  last step too.  Hence two cells dropping the *same* endpoint to the *same* facet coincide.

* **`facetSet_dropOf`, `dropOf_eq_zero`, `dropOf_eq_last`, `bounds_endpoint_dichotomy`,
  `boundary_singleton_invalid`** — **R2, NOW FULLY CLOSED.**  Any two cells bounding `F` at
  endpoint drops are either equal or `partnerCell`-partners (`bounds_endpoint_dichotomy`: the
  four endpoint-pair cases collapse via the same-endpoint reconstruction after pushing one cell
  through the committed `endpointFwd_facet`/`endpointInv_facet`).  Combined with the off-mesh
  criteria and `isBoundaryN_endpoint`, a boundary facet bounds *exactly one* present cell with an
  off-mesh partner (`boundary_singleton_invalid`): existence is the `isBoundaryN` witness, and any
  other such cell equals it or its partner — but the partner is off the mesh, so it equals the
  witness.  This discharges the `hR2` hypothesis of `exists_rainbow_cellN`.

* **`hboundaryOddN_uncond`, `exists_rainbow_cellN_R2`** — **the R2 discharge.**  Boundary parity
  is now unconditional (`hboundaryOddN_uncond`), and `exists_rainbow_cellN_R2` is the n-D Sperner
  output with `hR2` proved — only the boundary-door count `hR3` remains a hypothesis.

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

  (R2) PER-DOOR SINGLETON INVALID PARTNER — **CLOSED** (`boundary_singleton_invalid`, discharged
       into `exists_rainbow_cellN_R2`).  A boundary door bounds exactly ONE present cell with an
       invalid partner.  Existence is `isBoundaryN_endpoint`; the invalid side is the two off-mesh
       criteria; and the uniqueness — the converse of `dropOf_eq` across distinct cells — is now
       proved via the reconstruction backbone (`chainVZ_match_off` + `stepVec_injective` +
       `perm_eq_of_eq_off_point` ⟹ `cell_eq_of_facetSet_eq_zero/last`) and the endpoint dichotomy
       `bounds_endpoint_dichotomy` (any second bounding endpoint cell is the partner, which is off
       the mesh, hence not present).  Only R3 remains as a hypothesis of `exists_rainbow_cellN_R2`.

  Then `brouwer_stdSimplex_n {n} (f) (hf) (hmaps) : ∃ x ∈ stdSimplex ℝ (Fin (n+1)), f x = x` is
  `exists_rainbow_cellN_R2` (with R3, `L := labelN f k`) producing a rainbow cell at every mesh,
  fed through the committed `brouwer_of_rainbow_meshes`; `brouwer_compact_convex` then transports
  it to a compact convex `K ⊆ ℝⁿ` via the nearest-point retraction.

**Summary.**  This file closes — axiom-clean — the face re-encoding (`dropLast`/`appendZero` and
its injectivity on `{last = 0}`), the structural reduction of boundary facets to endpoint drops
(`isBoundaryN_endpoint`, via the committed internal squeeze), the face labelling restriction
(`labelN_ne_last_on_face`, the top colour is forbidden on the face), the door-is-rainbow colour
identity (`door_injOn_of_card`), and now the **endpoint partner base-shifts**
(`endpointInv/Fwd_base_last/castSucc`) together with the **two off-mesh invalidity criteria**
(`endpointFwd_invalid_of_base_last_zero`, `endpointInv_invalid_of_base_zero`) — the genuine
`∂Δⁿ`-invalidity facts that supply the *invalid side* of R2's singleton — and **the full R2
singleton itself** (`boundary_singleton_invalid`, discharged into `exists_rainbow_cellN_R2`): the
reconstruction-uniqueness backbone (`chainVZ_match_off`, `stepVec_injective`,
`perm_eq_of_eq_off_point`, `cell_eq_of_facetSet_eq_zero/last`) plus the endpoint dichotomy
(`bounds_endpoint_dichotomy`) prove that a boundary door bounds exactly one present cell with an
off-mesh partner.  The ONLY remaining frontier is the genuine dimension-drop construction R3 (the
`(n-1)`-face complex, the door ↔ rainbow bijection *through the base projection* — see the geometry
correction — and the induction wiring) — a from-scratch geometric brick on the scale of a second
2-D file, not finite bookkeeping. -/

end ShenWork.Paper1
