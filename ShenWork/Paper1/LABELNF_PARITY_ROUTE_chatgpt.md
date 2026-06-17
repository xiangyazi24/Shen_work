Yes—the right target is **not** the old `zeroDoorCellsN` door. It is the **post-projection / boundary-compatible Freudenthal door applied to `labelN f k`**.

In the current file, the distinction is already visible:

```lean
-- Correct post-projection door carrier
def simplexZeroDoorCells (n k : ℕ)
    (L : (Fin (n + 1) → ℤ) → Fin (n + 1)) : Finset (Cell n) :=
  (simplexCells n k).filter
    (fun c => appendSlack k c.1 (Fin.last n) = (n : ℤ) ∧
      simplexZeroDoorPostLabels n k L c = Finset.univ.erase (Fin.last n))

-- Legacy false pre-projection door carrier
def simplexZeroDoorCellsOld ...
```

The file explicitly comments that `simplexZeroDoorCellsOld` is kept only for comparison and “is false as the recursive parity target.” It also has the sanity counterexample: the **new** post-projection door count is `1`, while the old pre-projection door count is `0`. fileciteturn146file0L76-L123

So the answer to (1) is: **use `simplexZeroDoorPostLabels` / `simplexZeroDoorCells`, not `zeroDoorCellsN` and not `simplexZeroDoorCellsOld`.** The old counterexample only kills the pre-transition door. It does not kill Sperner parity for `labelN f` on the boundary-compatible Freudenthal/post-projection door.

## 1. Correct door for arbitrary `labelN f`

For a general lattice label

```lean
L : (Fin (n+1) → ℤ) → Fin (n+1)
```

the boundary-compatible zero-door in the simplex chart is:

```lean
simplexZeroDoorPostLabels n k L c = Finset.univ.erase (Fin.last n)
```

inside

```lean
simplexZeroDoorCells n k L.
```

For the box/bottom-face Freudenthal carrier, the corresponding door is:

```lean
isBottomDoor L c :=
  (facetSet c.1 c.2 (Fin.last (n + 1))).image L =
    Finset.univ.erase (Fin.last (n + 1))
```

and the associated carrier is `bottomDoors`. fileciteturn138file0L70-L86

This is the door that has the dimension-drop property:

```lean
card_bottomDoors_eq_rainbow
```

namely, bottom-door count equals lower-dimensional rainbow-cell count under the induced `bottomLabel`. fileciteturn138file0L95-L110

The old `zeroDoorCellsN` failure happened because it labels the wrong vertices: the legacy pre-projection door is literally

```lean
(facetSet c.1 c.2 0).image L = univ.erase last
```

transported into the simplex chart as `simplexZeroDoorCellsOld`. That is exactly the false target. fileciteturn146file0L93-L123

## 2. Does `labelN f` satisfy the needed boundary condition?

Yes. The Sperner label `labelN f k` satisfies the standard support-face condition:

```lean
if v t = 0, then labelN f k v ≠ t.
```

The current R3 file already proves this in the form:

```lean
theorem label_avoids_forbidden_coord_on_face
```

and the special bottom-face form:

```lean
theorem labelN_ne_last_on_face
```

Both follow from `spernerLabelN_ne_of_zero`, because if a barycentric coordinate is zero, that colour cannot be selected by the Sperner label. fileciteturn147file0L9-L44

So, conceptually, `labelN f k` is boundary-compatible in exactly the standard Sperner sense:

```lean
SpernerBoundary L :=
  ∀ v, validVertex v →
    ∀ i, v i = 0 → L v ≠ i
```

For any continuous self-map `f : Δⁿ → Δⁿ`, this boundary condition holds because the label is chosen from a coordinate where `f(x)_i ≤ x_i`, and the implementation additionally requires `x_i > 0`, so zero coordinates are forbidden.

## 3. What needs to be proved to feed the Freudenthal parity engine?

The Freudenthal parity theorem is already label-parametric, but not for arbitrary labels without boundary data. The relevant theorem is:

```lean
rainbow_count_odd_of_boundaryBottomData :
  Odd ((cells n k).filter (fun c => isRainbow L c)).card
```

assuming

```lean
BoundaryBottomData n k L.
```

`BoundaryBottomData` recursively requires:

```lean
∃ havoid : ∀ v, L (appendZero v) ≠ Fin.last ...
  (∀ F, F ∈ facets →
    F.image L = univ.erase last →
    isBoundary F →
      ∀ v ∈ F, v last = 0)
  ∧ BoundaryBottomData lower_dim (bottomLabel L havoid)
```

This is exactly the formal shape you need for `labelN f k`. fileciteturn142file0L87-L136

So for `labelN f k`, prove these fields:

### Field A: `havoid`

For the bottom face:

```lean
havoid :
  ∀ v : Fin n → ℤ,
    labelN f k (appendZero v) ≠ Fin.last n
```

This is the direct `labelN_ne_last_on_face` / `label_avoids_forbidden_coord_on_face` argument. You need the usual side hypotheses:

```lean
0 < k
MapsTo f (stdSimplex ℝ (Fin (n+1))) (stdSimplex ℝ (Fin (n+1)))
nonnegativity and mesh-sum of appendZero v
```

The existing file has these zero-coordinate avoidance lemmas for `labelN`. fileciteturn147file0L15-L44

### Field B: `hbottom`

This is the nontrivial geometric boundary step:

```lean
hbottom :
  ∀ F ∈ facets n k,
    F.image (labelN f k) = univ.erase last →
    isBoundary F →
      ∀ v ∈ F, v last = 0
```

For `postLabel`, this is almost tautological: off the bottom face it returns the top colour, while a door is `univ.erase last`, so door vertices must be bottom. The `postLabel` definition is:

```lean
if v last = 0 then lowerLabel(dropLast v).castSucc
else Fin.last
```

fileciteturn137file0L204-L215

For `labelN f`, it is not tautological, but it should be true by the Sperner boundary condition plus boundary geometry:

1. A boundary facet lies in some coordinate face `j = 0`.
2. If `j ≠ last`, then every vertex of that facet has coordinate `j = 0`, so `labelN f k` avoids colour `j` on every vertex.
3. But the door condition is `F.image L = univ.erase last`, which contains every lower colour, including `j`.
4. Contradiction.
5. Therefore the only possible boundary face for a lower-colour door is the bottom face `last = 0`.

This is the exact post-projection analogue of standard Sperner’s boundary-door argument. The current Freudenthal file already has a lemma in the opposite direction:

```lean
bottom_geometry_of_facet_last_zero
```

which says that if all vertices of a facet have last coordinate zero, then the facet is the literal bottom final facet. fileciteturn149file0L189-L242

What is still needed for the general `labelN f` route is the **general boundary-face detection lemma**:

```lean
theorem boundary_facet_lies_in_some_zero_face
    (hF : F ∈ facets n k)
    (hb : isBoundary hn k F) :
    ∃ j : Fin n, ∀ v ∈ F, v j = 0 ∨ ... -- depending on upper boundary convention
```

For the simplex/barycentric type-A model, the useful form should identify the invalid partner’s exhausted coordinate. Then combine it with `label_avoids_forbidden_coord_on_face`.

### Field C: recursive lower boundary data

The lower label is:

```lean
bottomLabel (labelN f k) havoid
```

You need to show it again satisfies the same Sperner boundary condition on the lower-dimensional face. There are two possible ways:

```lean
-- Stronger, nicer:
bottomLabel (labelN f k) havoid
  = labelN f_face k
```

for an explicitly restricted face self-map `f_face`, if you want a geometrically clean recursion.

But equality to a lower-dimensional `labelN` is not actually necessary for the parity theorem. It is enough to show:

```lean
BoundaryBottomData n k (bottomLabel (labelN f k) havoid)
```

by the same “label avoids zero coordinate” argument. The lower label avoids any lower coordinate whose appended face coordinate is zero because the upper `labelN f k` avoids that same coordinate.

So define an abstract predicate:

```lean
def SpernerBoundaryLabel {n : ℕ} (k : ℕ)
    (L : (Fin n → ℤ) → Fin (n+1)) : Prop :=
  ∀ v, validMeshVertex k v →
    ∀ i, vertexCoordZero v i → L v ≠ i
```

Then prove:

```lean
theorem labelN_spernerBoundary :
  SpernerBoundaryLabel k (labelN f k)

theorem bottomLabel_spernerBoundary :
  SpernerBoundaryLabel k L →
  SpernerBoundaryLabel k (bottomLabel L havoid)

theorem boundaryBottomData_of_spernerBoundary :
  SpernerBoundaryLabel k L →
  BoundaryBottomData n k L
```

The last theorem packages the actual Freudenthal boundary geometry.

## 4. Is `postLabelTower` just one instance?

Yes, morally. `postLabel` / `postLabelTower` is a **canonical boundary-compatible label** built so that the recursive boundary-data proof is easy: it returns `last` off the selected bottom face and agrees with the lower label on that face. The file proves that `bottomLabel (postLabel L) = L`. fileciteturn137file0L204-L230

But the correct general theorem should be:

```lean
theorem rainbow_count_odd_of_spernerBoundary
    (L : Label n)
    (hSperner : SpernerBoundaryLabel k L) :
    Odd ((cells n k).filter (fun c => isRainbow L c)).card
```

or, in the current code’s language:

```lean
theorem boundaryBottomData_of_labelN
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    BoundaryBottomData n k (freudenthalLabelN f k)

theorem rainbow_count_odd_labelN
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    Odd ((cells n k).filter
      (fun c => isRainbow (freudenthalLabelN f k) c)).card
```

Then `postLabelTower` is simply an easy label-family satisfying `BoundaryBottomData`, not the only label for which parity works.

## 5. Is there any obstruction special to `labelN f`?

There is no mathematical obstruction from `labelN f` itself. It is a standard Sperner label: it avoids zero-coordinate colours, and that is exactly the boundary condition needed for Freudenthal/Sperner parity.

The obstruction is purely from using the **wrong door/triangulation interface**:

```text
bad:  old fixed-last-chain pre-transition door
good: type-A / Freudenthal post-projection boundary door
```

The repo now explicitly demonstrates this: for the old counterexample label, the new `simplexZeroDoorCells` has odd count `1`, while `simplexZeroDoorCellsOld` has count `0`. fileciteturn146file0L111-L123

The file also proves the labelN-specific local bridge:

```lean
simplexZeroDoorPostLabels_labelN_door_iff_lower_rainbow
```

and

```lean
mem_simplexZeroDoorCells_labelN_iff_lower_rainbow
```

These say that the post-projection door for `labelN f k` is equivalent to a lower-dimensional rainbow condition, exactly what the old door lacked. fileciteturn144file0L144-L183

So the right conclusion is:

```text
labelN f is fine.
old zeroDoorCellsN is not fine.
prove labelN satisfies the boundary/Sperner condition, then run the Freudenthal post-projection parity engine.
```

## Recommended Lean target

I would introduce this theorem, rather than proving another `postLabelTower`-specific fact:

```lean
theorem BoundaryBottomData.of_spernerBoundary
    {n k : ℕ} (hk : 0 < k)
    {L : Label n}
    (hSperner : SpernerBoundaryLabel k L) :
    BoundaryBottomData n k L := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨havoid_from_hSperner hSperner, ?hbottom, ?hlower⟩
      · exact boundary_door_vertices_bottom_of_sperner hSperner
      · exact ih (bottomLabel_spernerBoundary hSperner)
```

Then specialize it:

```lean
theorem freudenthal_labelN_boundaryBottomData
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    BoundaryBottomData n k (freudenthalLabelN f k) :=
  BoundaryBottomData.of_spernerBoundary hk
    (labelN_spernerBoundary hk hmaps)
```

Then:

```lean
theorem rainbow_count_odd_freudenthal_labelN
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    Odd ((cells n k).filter
      (fun c => isRainbow (freudenthalLabelN f k) c)).card :=
  rainbow_count_odd_of_boundaryBottomData hk _
    (freudenthal_labelN_boundaryBottomData hk hmaps)
```

That is the clean route from arbitrary continuous `f` to a rainbow cell under the correct boundary-compatible Freudenthal door.
