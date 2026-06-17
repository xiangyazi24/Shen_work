/-
# n-D Brouwer: assembling `brouwer_stdSimplex_n` and `brouwer_compact_convex`

This file builds on the committed `BrouwerNDim` / `BrouwerNDimComplete` pieces (the abstract
dimension-free Sperner engine `sperner_n_dim_combinatorial`, the structural heart
`heart_count_n`, the Kuhn chain `chainVZ`, and the internal-facet partner involution).

The n-D assembly proceeds by **induction on the dimension** with the committed 1-D
(`brouwer_fixedPoint_dim_one` / `sperner_one_dim`) and 2-D (`brouwer_stdSimplex_two`) as base
cases.  The genuine new analytic content lives in the two glue lemmas already committed
(`sperner_label_nonempty`, `eq_of_forall_le_on_stdSimplex`) which are stated for general `n`.

See the stall report at the end for the precise frontier.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Logic.Equiv.Fin.Rotate
import ShenWork.Paper1.BrouwerNDimComplete

namespace ShenWork.Paper1

open Set Finset Filter Topology

/-! ## Compactness of the standard simplex (reused glue) -/

/-- The standard simplex `stdSimplex ℝ (Fin (n+1))` is compact. -/
theorem isCompact_stdSimplex_fin (n : ℕ) :
    IsCompact (stdSimplex ℝ (Fin (n + 1))) :=
  isCompact_stdSimplex (𝕜 := ℝ) (Fin (n + 1))

/-! ## The dimension-agnostic mesh-limit engine

The combinatorial Sperner machinery, at every mesh `m`, produces a single cell whose `n+1`
vertices realise all `n+1` Sperner colours and are pairwise within `C/(m+1)` of each other
(coordinatewise).  Whatever the concrete triangulation, the *limit* argument is identical:
compactness extracts a convergent subsequence, the shrinking mesh forces all per-colour
vertices to the same limit `x`, continuity passes `f(P t) t ≤ (P t) t` to `f x t ≤ x t` for
every coordinate, and `eq_of_forall_le_on_stdSimplex` upgrades that to `f x = x`.

We isolate this as a standalone lemma whose hypothesis is exactly the Sperner output.  It
mirrors `brouwer_stdSimplex_two`'s final block verbatim, but at symbolic `n` and abstracted
over the source of the rainbow data. -/

/-- **Mesh-limit engine (dimension-agnostic).**  Suppose `f` is continuous on `Δⁿ`, maps `Δⁿ`
into itself, and — the Sperner output — for every `m : ℕ` there is a family
`P : Fin (n+1) → (Fin (n+1) → ℝ)` of points of `Δⁿ` with `f (P t) t ≤ P t t` for each colour
`t`, all pairwise within `C/(m+1)` coordinatewise (`C ≥ 0` a fixed constant).  Then `f` has a
fixed point in `Δⁿ`. -/
theorem brouwer_of_rainbow_meshes {n : ℕ} {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (C : ℝ) (_hC : 0 ≤ C)
    (hf : ContinuousOn f (stdSimplex ℝ (Fin (n + 1))))
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1))))
    (hrain : ∀ m : ℕ, ∃ P : Fin (n + 1) → (Fin (n + 1) → ℝ),
      (∀ t, P t ∈ stdSimplex ℝ (Fin (n + 1))) ∧
      (∀ t, f (P t) t ≤ P t t) ∧
      (∀ s t r, |P s r - P t r| ≤ C / (m + 1))) :
    ∃ x ∈ stdSimplex ℝ (Fin (n + 1)), f x = x := by
  classical
  choose P hPmem hPle hPclose using hrain
  -- the colour-0 vertex sequence lives in the compact simplex
  have hbmem : ∀ m, P m 0 ∈ stdSimplex ℝ (Fin (n + 1)) := fun m => hPmem m 0
  obtain ⟨x, hx, φ, hφ, htend⟩ :=
    (isCompact_stdSimplex_fin n).tendsto_subseq hbmem
  refine ⟨x, hx, ?_⟩
  -- the rainbow gap tends to 0 along the subsequence
  have hgap0 : Tendsto (fun j => C / (φ j + 1)) atTop (𝓝 0) := by
    have hmono : Tendsto (fun j => (φ j : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    simpa using hmono.inv_tendsto_atTop.const_mul C
  -- each colour's vertex converges to x along the subsequence
  have hPtend : ∀ t : Fin (n + 1), Tendsto (fun j => P (φ j) t) atTop (𝓝 x) := by
    intro t
    rw [tendsto_pi_nhds]
    intro r
    have hb_r : Tendsto (fun j => P (φ j) 0 r) atTop (𝓝 (x r)) :=
      ((continuous_apply r).continuousAt.tendsto).comp htend
    have hdiff0 : Tendsto (fun j => P (φ j) t r - P (φ j) 0 r) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun j => C / (φ j + 1)) ?_ hgap0
      intro j
      simpa [Real.norm_eq_abs] using hPclose (φ j) t 0 r
    have := hdiff0.add hb_r
    simpa using this
  -- continuity passes the per-colour label inequality to the limit
  have hfx_le : ∀ t : Fin (n + 1), f x t ≤ x t := by
    intro t
    have hfcont : Tendsto (fun j => f (P (φ j) t)) atTop (𝓝 (f x)) := by
      apply (hf.continuousWithinAt hx).tendsto.comp
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hPtend t) (Eventually.of_forall (fun j => hPmem (φ j) t))
    have hfx_t : Tendsto (fun j => f (P (φ j) t) t) atTop (𝓝 (f x t)) :=
      ((continuous_apply t).continuousAt.tendsto).comp hfcont
    have hxt : Tendsto (fun j => P (φ j) t t) atTop (𝓝 (x t)) :=
      (tendsto_pi_nhds.mp (hPtend t)) t
    exact le_of_tendsto_of_tendsto hfx_t hxt (Eventually.of_forall (fun j => hPle (φ j) t))
  exact eq_of_forall_le_on_stdSimplex x (f x) hx (hmaps hx) hfx_le

theorem brouwer_simplex_approx_of_rainbow_meshes {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ContinuousOn f (stdSimplex ℝ (Fin (n + 1))))
    (hmaps :
      Set.MapsTo f (stdSimplex ℝ (Fin (n + 1)))
        (stdSimplex ℝ (Fin (n + 1))))
    (hrain : ∀ m : ℕ, ∃ P : Fin (n + 1) → (Fin (n + 1) → ℝ),
      (∀ t, P t ∈ stdSimplex ℝ (Fin (n + 1))) ∧
      (∀ t, f (P t) t ≤ P t t) ∧
      (∀ s t r, |P s r - P t r| ≤ C / (m + 1))) :
    ∀ ε > 0, ∃ x ∈ stdSimplex ℝ (Fin (n + 1)), ‖f x - x‖ ≤ ε := by
  intro ε hε
  rcases brouwer_of_rainbow_meshes C hC hf hmaps hrain with ⟨x, hx, hfix⟩
  refine ⟨x, hx, ?_⟩
  simpa [hfix] using hε.le

/-! ## The n-D simplex embedding and Sperner labelling (dimension-agnostic)

A barycentric lattice point of `Δⁿ` at mesh `k` is `q : Fin (n+1) → ℕ` with `∑ q = k`; it
embeds into `Δⁿ` as `q i / k`.  The Sperner label is the least coordinate with `q i > 0` and
`f(emb q) i ≤ (emb q) i`; it is well-defined by `sperner_label_nonempty`.  These mirror the
`vertexPt` / `spernerLabel` / `labelSet` layer of `BrouwerTwoDim` but at symbolic `n`. -/

/-- The barycentric lattice point `q : Fin (n+1) → ℕ` (with `∑ q = k`) embedded into `Δⁿ`:
`embPt k q i = q i / k`. -/
noncomputable def embPt {n : ℕ} (k : ℕ) (q : Fin (n + 1) → ℕ) : Fin (n + 1) → ℝ :=
  fun i => (q i : ℝ) / k

/-- For `0 < k` and `∑ q = k`, the embedded lattice point lies in `Δⁿ`. -/
theorem embPt_mem_stdSimplex {n k : ℕ} (hk : 0 < k) {q : Fin (n + 1) → ℕ}
    (hsum : ∑ i, q i = k) : embPt k q ∈ stdSimplex ℝ (Fin (n + 1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · intro i
    exact div_nonneg (by positivity) (le_of_lt hkR)
  · simp only [embPt]
    rw [← Finset.sum_div]
    rw [show (∑ i, (q i : ℝ)) = ((∑ i, q i : ℕ) : ℝ) by push_cast; ring, hsum]
    field_simp

open scoped Classical in
/-- The Sperner colour-set of a point `v` with image `fv`: the coordinates `t` with
`v t > 0` and `fv t ≤ v t`.  Nonempty on `Δⁿ` by `sperner_label_nonempty`. -/
noncomputable def labelSetN {n : ℕ} (v fv : Fin (n + 1) → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun t => v t > 0 ∧ fv t ≤ v t)

/-- The Sperner label of a lattice point under `f` at mesh `k`: the least colour `t` with
`(embPt) t > 0` and `(f ∘ embPt) t ≤ (embPt) t`. -/
noncomputable def spernerLabelN {n : ℕ} (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ)
    (q : Fin (n + 1) → ℕ) : Fin (n + 1) :=
  if h : (labelSetN (embPt k q) (f (embPt k q))).Nonempty then
    (labelSetN (embPt k q) (f (embPt k q))).min' h else 0

/-- The label set is nonempty for an in-simplex lattice point mapped by a self-map. -/
theorem labelSetN_nonempty {n : ℕ} {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {k : ℕ}
    {q : Fin (n + 1) → ℕ} (hv : embPt k q ∈ stdSimplex ℝ (Fin (n + 1)))
    (hfv : f (embPt k q) ∈ stdSimplex ℝ (Fin (n + 1))) :
    (labelSetN (embPt k q) (f (embPt k q))).Nonempty := by
  obtain ⟨t, ht⟩ := sperner_label_nonempty (embPt k q) (f (embPt k q)) hv hfv
  exact ⟨t, by simp only [labelSetN, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht⟩

/-- The Sperner label lies in its own colour-set: positive and weakly decreasing there. -/
theorem spernerLabelN_spec {n : ℕ} {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {k : ℕ}
    {q : Fin (n + 1) → ℕ} (hv : embPt k q ∈ stdSimplex ℝ (Fin (n + 1)))
    (hfv : f (embPt k q) ∈ stdSimplex ℝ (Fin (n + 1))) :
    embPt k q (spernerLabelN f k q) > 0 ∧
      f (embPt k q) (spernerLabelN f k q) ≤ embPt k q (spernerLabelN f k q) := by
  have hne := labelSetN_nonempty hv hfv
  unfold spernerLabelN
  rw [dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  simpa only [labelSetN, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- The label avoids any coordinate where the embedded point is zero. -/
theorem spernerLabelN_ne_of_zero {n : ℕ} {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {k : ℕ}
    {q : Fin (n + 1) → ℕ} (hv : embPt k q ∈ stdSimplex ℝ (Fin (n + 1)))
    (hfv : f (embPt k q) ∈ stdSimplex ℝ (Fin (n + 1))) {t : Fin (n + 1)}
    (ht : embPt k q t = 0) : spernerLabelN f k q ≠ t := by
  intro heq
  have hpos := (spernerLabelN_spec hv hfv).1
  rw [heq, ht] at hpos
  exact lt_irrefl 0 hpos

/-! ## The concrete n-D Kuhn complex: cells and facets as Finsets

A **cell** of the Kuhn subdivision of `Δⁿ` at mesh `k` is a pair `(p, σ)` with `p : Fin (n+1) →
ℤ` the base lattice point and `σ : Equiv.Perm (Fin n)` the step order, subject to *validity*:
every chain vertex `chainVZ p σ t` is a nonnegative lattice point with barycentric sum `k`.
Since `sum_chainVZ` already gives the sum invariant, validity is the conjunction of "`∑ p = k`"
and "every chain vertex is coordinatewise `≥ 0`".

Encoding the base over `ℤ` (as `chainVZ` does) and packaging cells as
`Fin (n+1) → ℤ` ×ₚ `Equiv.Perm (Fin n)` makes `DecidableEq` automatic.  We carve the cells at
mesh `k` out of an explicit finite box of bases (`0 ≤ p i ≤ k`). -/

/-- A cell is *valid at mesh `k`* iff its base sums to `k` and every chain vertex is a
nonnegative lattice point. -/
def cellValid {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∑ i, p i = (k : ℤ)) ∧ ∀ t i, 0 ≤ chainVZ p σ t i

instance {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) :
    Decidable (cellValid k p σ) := by unfold cellValid; infer_instance

/-- The barycentric-sum invariant holds at *every* chain vertex of a valid cell. -/
theorem cellValid_sum {n k : ℕ} {p : Fin (n + 1) → ℤ} {σ : Equiv.Perm (Fin n)}
    (hc : cellValid k p σ) (t : Fin (n + 1)) : ∑ i, chainVZ p σ t i = (k : ℤ) := by
  rw [sum_chainVZ]; exact hc.1

/-- Each chain vertex of a valid cell is nonnegative. -/
theorem cellValid_nonneg {n k : ℕ} {p : Fin (n + 1) → ℤ} {σ : Equiv.Perm (Fin n)}
    (hc : cellValid k p σ) (t : Fin (n + 1)) (i : Fin (n + 1)) : 0 ≤ chainVZ p σ t i :=
  hc.2 t i

/-- The natural-number coordinates of a chain vertex of a valid cell (each coordinate is
`(chainVZ …).toNat`, recovering the genuine `ℕ` lattice point). -/
noncomputable def chainNat {n : ℕ} (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n))
    (t : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun i => (chainVZ p σ t i).toNat

/-- For a valid cell, the `ℕ`-coordinates of a chain vertex sum to `k`. -/
theorem chainNat_sum {n k : ℕ} {p : Fin (n + 1) → ℤ} {σ : Equiv.Perm (Fin n)}
    (hc : cellValid k p σ) (t : Fin (n + 1)) : ∑ i, chainNat p σ t i = k := by
  have hz : ∑ i, chainVZ p σ t i = (k : ℤ) := cellValid_sum hc t
  have hcast : ∑ i, ((chainNat p σ t i : ℤ)) = (k : ℤ) := by
    rw [← hz]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [chainNat]
    rw [Int.toNat_of_nonneg (cellValid_nonneg hc t i)]
  have hpc : ((∑ i, chainNat p σ t i : ℕ) : ℤ) = ∑ i, ((chainNat p σ t i : ℤ)) := by
    push_cast; ring
  have : ((∑ i, chainNat p σ t i : ℕ) : ℤ) = (k : ℤ) := by rw [hpc, hcast]
  exact_mod_cast this

/-! ## Global interior-facet parity from the slice involution

The cells of the Kuhn complex sharing an interior facet `F` via an *internal* drop come in
partner pairs (the committed `internal_hinterior_slice_even`).  We now record the global
consequence used by the engine's `hinterior`: for a *fixed base* `p` and a *fixed internal
drop index* `t`, the number of permutations whose drop-`t` facet is `F` is even.  This is the
genuine, route-independent half of the interior-facet incidence.

The remaining content for a *fully global* `hinterior` (a sum over the at-most-two contributing
`(base, t)` configurations of an interior facet) is the **reconstruction converse K2′**: an
interior facet of the Kuhn complex is the drop-`t` facet of cells from exactly one fixed-base
internal slice, *or* it is shared across the endpoint base-shift — see the stall report. -/

/-- **Per-(base, internal-`t`) interior-facet evenness** — the committed slice involution,
re-exposed for the assembly.  For a fixed base `p` and internal drop index `t` (`0 < t < n`),
the cells of base `p` whose drop-`t` facet equals `F` have even count. -/
theorem hinterior_internal_slice {n : ℕ} (p : Fin (n + 1) → ℤ) {t : Fin (n + 1)}
    (h0 : 0 < t.val) (hlt : t.val < n) (F : Finset (Fin (n + 1) → ℤ)) :
    Even (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => facetSet p σ t = F)).card :=
  internal_hinterior_slice_even p h0 hlt F

/-- A convenient repackaging: summing the per-slice even counts over a finite set of bases
keeps evenness (a sum of even numbers is even).  This is the shape the global `hinterior`
takes once the contributing bases of an interior facet are enumerated. -/
theorem hinterior_sum_even {n : ℕ} {t : Fin (n + 1)} (h0 : 0 < t.val) (hlt : t.val < n)
    (F : Finset (Fin (n + 1) → ℤ)) (B : Finset (Fin (n + 1) → ℤ)) :
    Even (∑ p ∈ B,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => facetSet p σ t = F)).card) := by
  classical
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [ZMod.natCast_eq_zero_iff_even]
  exact internal_hinterior_slice_even p h0 hlt F

/-! ## The endpoint base-shift partner (crux brick E)

The genuine n-D Kuhn incidence at an **endpoint** drop.  Dropping vertex `t = 0` of `(p, σ)`
leaves the chain `v_1, …, v_n`.  The *partner* cell sharing this facet has base `p' =
p + stepVec (σ 0)` (`= v_1`) and step order `σ' = σ * finRotate n` (cyclically advance every
step by one), and the shared facet is its **`t = last` drop**.  The content is the chain
correspondence `chainVZ p' σ' u = chainVZ p σ (u+1)` for `u < n`, established by a
`finRotate`-reindexing of the prefix sums (no wraparound in range). -/

/-- `finRotate n` advances a step index without wrapping below `n`: for `s : Fin n` with
`s.val + 1 < n`, `(finRotate n s).val = s.val + 1`. -/
theorem finRotate_val_of_lt {n : ℕ} {s : Fin n} (hs : s.val + 1 < n) :
    (finRotate n s).val = s.val + 1 := by
  cases n with
  | zero => exact absurd s.isLt (by omega)
  | succ m =>
    rw [finRotate_succ_apply]
    have : ((s + 1 : Fin (m + 1))).val = (s.val + 1) % (m + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt hs]

/-- **Endpoint chain correspondence (`t = 0` partner).**  With `p' = p + stepVec (σ 0)` and
`σ' = σ * finRotate n`, the partner's vertex `u` (for `u.val < n`) equals the original's
vertex `u + 1`: `chainVZ p' σ' u = chainVZ p σ ⟨u+1⟩`.  This is the chain identity underlying
the endpoint facet-sharing. -/
theorem chainVZ_endpoint_shift {n : ℕ} (hn : 0 < n) (p : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin n)) {u : Fin (n + 1)} (hu : u.val < n) :
    chainVZ (fun i => p i + stepVec (σ ⟨0, hn⟩) i) (σ * finRotate n) u
      = chainVZ p σ ⟨u.val + 1, by omega⟩ := by
  classical
  funext i
  rw [chainVZ_apply, chainVZ_apply]
  -- The two prefix index sets.
  set SL : Finset (Fin n) := Finset.univ.filter (fun s : Fin n => s.val < u.val) with hSL
  set SR : Finset (Fin n) := Finset.univ.filter (fun s : Fin n => s.val < u.val + 1) with hSR
  have hz : (⟨0, hn⟩ : Fin n) ∈ SR := by
    simp only [hSR, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  -- RHS sum over SR splits off the `s = 0` term.
  have hsplitR : ∑ s ∈ SR, stepVec (σ s) i
      = stepVec (σ ⟨0, hn⟩) i + ∑ s ∈ SR.erase ⟨0, hn⟩, stepVec (σ s) i :=
    (Finset.add_sum_erase SR (fun s => stepVec (σ s) i) hz).symm
  -- `finRotate n` maps SL bijectively onto `SR.erase 0` (value `s ↦ s+1`).
  have himg : SL.image (finRotate n) = SR.erase ⟨0, hn⟩ := by
    ext s
    simp only [Finset.mem_image, hSL, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, hSR]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hval : (finRotate n a).val = a.val + 1 := finRotate_val_of_lt (by omega)
      refine ⟨?_, by omega⟩
      intro hcon; rw [hcon] at hval; simp at hval
    · rintro ⟨hne, hlt⟩
      have hsval : 1 ≤ s.val := by
        rcases Nat.eq_zero_or_pos s.val with h | h
        · exact absurd (by ext; simpa using h) hne
        · exact h
      have hslt : s.val < n := s.isLt
      have hsub : s.val - 1 < n := by omega
      refine ⟨(finRotate n).symm s, ?_, by simp⟩
      have hrw : (finRotate n ⟨s.val - 1, hsub⟩).val = (s.val - 1) + 1 :=
        finRotate_val_of_lt (s := ⟨s.val - 1, hsub⟩) (by simpa using (by omega : s.val - 1 + 1 < n))
      have hpred : (finRotate n).symm s = ⟨s.val - 1, hsub⟩ := by
        apply (finRotate n).injective
        rw [Equiv.apply_symm_apply]
        ext
        rw [hrw]; exact (Nat.sub_add_cancel hsval).symm
      rw [hpred]
      show s.val - 1 < u.val
      omega
  -- reindex the SR.erase 0 sum back to SL
  have hbij : ∑ s ∈ SR.erase ⟨0, hn⟩, stepVec (σ s) i
      = ∑ s ∈ SL, stepVec (σ (finRotate n s)) i := by
    rw [← himg, Finset.sum_image (fun a _ b _ h => (finRotate n).injective h)]
  -- assemble
  rw [hsplitR, hbij]
  have hstep : ∀ s : Fin n, stepVec ((σ * finRotate n) s) i = stepVec (σ (finRotate n s)) i :=
    fun s => rfl
  simp only [hstep]
  ring

/-- **Endpoint facet-sharing (`t = 0` ↔ `t = last`).**  The drop-`0` facet of the cell
`(p, σ)` is identical to the drop-`last` facet of its endpoint partner
`(p + stepVec (σ ⟨0,hn⟩), σ * finRotate n)`.  Hence every interior facet arising from an
endpoint drop is shared by these two distinct-base cells — the missing half of the n-D
incidence, now proven from the chain correspondence. -/
theorem facetSet_endpoint_eq {n : ℕ} (hn : 0 < n) (p : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    facetSet (fun i => p i + stepVec (σ ⟨0, hn⟩) i) (σ * finRotate n) (Fin.last n)
      = facetSet p σ 0 := by
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
    have hv0 : (⟨u.val + 1, by omega⟩ : Fin (n + 1)).val = (0 : Fin (n + 1)).val := by rw [hcon]
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
      have hvl : (⟨w.val - 1, hwlt1⟩ : Fin (n + 1)).val = (Fin.last n).val := by rw [hcon]
      simp only [Fin.val_last] at hvl; omega
    · have hkey := chainVZ_endpoint_shift hn p σ (u := ⟨w.val - 1, hwlt1⟩) (by simpa using hwlt)
      rw [hkey]
      congr 1
      apply Fin.ext
      show w.val - 1 + 1 = w.val
      omega

/-- The endpoint partner genuinely shifts the base: `stepVec (σ ⟨0,hn⟩)` is nonzero (it moves a
unit of mass), so the partner base `p + stepVec (σ ⟨0,hn⟩)` differs from `p`.  Hence the two
cells sharing an endpoint facet are distinct. -/
theorem endpoint_base_ne {n : ℕ} (hn : 0 < n) (p : Fin (n + 1) → ℤ) (σ : Equiv.Perm (Fin n)) :
    (fun i => p i + stepVec (σ ⟨0, hn⟩) i) ≠ p := by
  intro hcon
  -- evaluate at the last coordinate, where stepVec contributes `-1`
  have hlast : (fun i => p i + stepVec (σ ⟨0, hn⟩) i) (Fin.last n) = p (Fin.last n) := by
    rw [hcon]
  simp only at hlast
  have hstep : stepVec (σ ⟨0, hn⟩) (Fin.last n) = -1 := by
    unfold stepVec
    have hne : Fin.last n ≠ (σ ⟨0, hn⟩).castSucc := by
      intro hc
      have hval := congrArg Fin.val hc
      simp only [Fin.val_last, Fin.val_castSucc] at hval
      omega
    rw [if_neg hne, if_pos rfl]; ring
  rw [hstep] at hlast; omega

/-- **Endpoint partner pair.**  The two cells `(p, σ)` and
`(p + stepVec (σ ⟨0,hn⟩), σ * finRotate n)` are distinct (different base) and share the
endpoint facet (drop-`0` of the first = drop-`last` of the second).  This is the endpoint
analogue of the committed internal `facetSet_partner_pair`. -/
theorem endpoint_partner_pair {n : ℕ} (hn : 0 < n) (p : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    (fun i => p i + stepVec (σ ⟨0, hn⟩) i) ≠ p ∧
      facetSet (fun i => p i + stepVec (σ ⟨0, hn⟩) i) (σ * finRotate n) (Fin.last n)
        = facetSet p σ 0 :=
  ⟨endpoint_base_ne hn p σ, facetSet_endpoint_eq hn p σ⟩

/-! ## Precise stall report — the remaining frontier to `brouwer_stdSimplex_n`

**What is fully closed here (axiom-clean: `[propext, Classical.choice, Quot.sound]`).**

* `brouwer_of_rainbow_meshes` — **the complete dimension-agnostic mesh-limit engine (doctrine
  brick K4), at symbolic `n`.**  Given the Sperner output as a hypothesis — for every mesh `m`,
  a family of `n+1` points of `Δⁿ` realising all `n+1` colours, pairwise within `C/(m+1)` and
  each weakly decreasing in its own colour — it produces a genuine fixed point.  This is the
  *entire* analytic assembly: compactness (`IsCompact.tendsto_subseq` on the compact
  `stdSimplex`), the shrinking-mesh collapse of all per-colour vertices to one limit,
  continuity passing `f(P t) t ≤ P t t` to the limit, and `eq_of_forall_le_on_stdSimplex`.  It
  mirrors `brouwer_stdSimplex_two`'s final block *verbatim* but at general `n`, abstracted over
  the triangulation.  Once the geometric brick below is discharged, `brouwer_stdSimplex_n` is
  this lemma applied to the Sperner-produced rainbow family.
* `embPt`, `embPt_mem_stdSimplex`, `labelSetN`, `spernerLabelN`, `labelSetN_nonempty`,
  `spernerLabelN_spec`, `spernerLabelN_ne_of_zero` — **the n-D Sperner labelling layer**, the
  general-`n` analogue of `BrouwerTwoDim`'s `vertexPt`/`spernerLabel`/`labelSet`.  The label is
  well-defined (`sperner_label_nonempty`), lies in its colour-set, and avoids zero coordinates
  (the input to the boundary-door argument K3).
* `cellValid`, `cellValid_sum`, `cellValid_nonneg`, `chainNat`, `chainNat_sum` — **the Kuhn
  cell validity layer**: a cell `(p, σ)` is valid at mesh `k` iff `∑ p = k` and every chain
  vertex is nonnegative; its `ℕ`-coordinates (`chainNat = (chainVZ …).toNat`) then form a
  genuine barycentric lattice point summing to `k`, ready to feed `embPt`.
* `hinterior_internal_slice`, `hinterior_sum_even` — **the internal-facet parity**, assembled
  from the committed slice involution: for a fixed base `p` and internal drop `t` (`0<t<n`) the
  cells whose drop-`t` facet equals `F` come in partner pairs (even count), and this stays even
  when summed over any finite set of bases (the shape the global `hinterior` takes).
* `finRotate_val_of_lt`, `chainVZ_endpoint_shift`, `facetSet_endpoint_eq`, `endpoint_base_ne`,
  `endpoint_partner_pair` — **the endpoint base-shift partner (the brick the committed
  `BrouwerNDim`/`BrouwerNDimComplete` stall reports flagged as "the genuine missing geometry",
  now CLOSED).**  Dropping the endpoint vertex `t = 0` of cell `(p, σ)` yields a facet shared
  with the *different-base* cell `(p + stepVec (σ ⟨0,hn⟩), σ * finRotate n)` via *its* `t = last`
  drop.  The crux is the chain correspondence `chainVZ_endpoint_shift`:
  `chainVZ (p + stepVec (σ ⟨0,hn⟩)) (σ * finRotate n) u = chainVZ p σ ⟨u+1⟩` for `u < n`, a
  `finRotate`-reindexing of the `chainVZ` prefix sums *across drop indices* (`0 ↔ last`) and
  *across the base shift* — the cross-index analogue the fixed-`t` slice machinery (and the
  committed adjacent-swap `chainVZ_swap_eq_of_prefix`) does not cover.  `facetSet_endpoint_eq`
  lifts it to the facet sets; `endpoint_base_ne` shows the bases genuinely differ (the step
  moves a unit of mass out of the last coordinate), so the two cells are distinct.

**The remaining frontier (the global bookkeeping atop the now-complete partner bricks).**
With BOTH partners in hand (internal: `facetSet_partner_pair`; endpoint: `endpoint_partner_pair`),
every interior facet is provably shared by a distinct partner cell.  What remains is the
*global accounting* that turns these per-facet involutions into the engine's `hinterior` /
`hboundaryOdd`, plus the boundary induction K3:

  (K2′) GLOBAL DECOMPOSITION.  Enumerate, for an interior facet `F`, the valid cells bounding
      it (`∃ t, facetSet p σ t = F`).  Each such cell drops some `t`; the partner (internal swap
      for `0<t<n`, base-shift `endpoint_partner_pair` for `t ∈ {0, n}`) is the unique other cell
      with that facet, giving a global fixed-point-free involution on the bounding-cell set —
      hence even cardinality — via `even_card_of_involution` (committed).  Oddness (= 1) holds on
      the geometric `∂Δⁿ`, where `cellValid` fails for the shifted base so the partner drops out.
      The bookkeeping is: (i) show the per-facet partner map is well-defined on the *global*
      bounding-cell Finset (each facet determines its drop index and side), and (ii) the
      boundary characterisation `cellValid (partner) ↔ ¬(F ⊆ ∂Δⁿ)`.

  (K3) BOUNDARY-DOOR COUNT.  `hboundaryCount` reduces by induction on `n` to
      `sperner_(n-1)_dim` on the distinguished face `{q : q (Fin.last n) = 0}` (the last
      barycentric coordinate vanishes; its induced Kuhn subdivision is the `(n-1)`-dimensional
      one), base case `n = 1` the committed `sperner_one_dim`.  The labelling layer above
      (`spernerLabelN_ne_of_zero`) supplies the "label avoids the vanishing coordinate" facts
      this induction consumes — exactly as `label_ne_*` feed `hboundaryCount` in 2-D.

  Then `brouwer_stdSimplex_n` = `sperner_n_dim_combinatorial` (with `hheart_indexed`, (K2′),
  (K3)) producing a rainbow cell at every mesh, fed through `brouwer_of_rainbow_meshes` above;
  and `brouwer_compact_convex` transports it to a compact convex `K ⊆ ℝⁿ` via the nearest-point
  retraction onto `K` precomposed with a homeomorphism `Δⁿ ≃ closedBall ⊇ K`.

The two genuine geometric crux bricks — the K4 limit engine (full, symbolic `n`) and BOTH
facet-sharing partners (internal + endpoint base-shift) — are discharged and compile.  What
remains (K2′, K3) is finite combinatorial bookkeeping + a clean induction on `n`, with no
remaining Mathlib gap (the `finRotate` reindexing, the one missing API, is now used and proven).
-/

#print axioms brouwer_simplex_approx_of_rainbow_meshes

end ShenWork.Paper1
