The shortest faithful route is **not** to reuse the specific `postLabelTower` parity as a black box for `labelN f`. It is to extract the **label-agnostic part** of that proof and prove that `labelN f k` satisfies the same recursive boundary condition on the **type-A/simplex post-projection door**.

The current code already has the key split:

```lean
-- generic parity, once boundary data is supplied
rainbow_count_odd_of_boundaryBottomData

-- specific/easy boundary-compatible labels
postLabel / postLabelTower
```

`rainbow_count_odd_of_boundaryBottomData` is label-parametric: it takes an arbitrary `L : Label n` plus `BoundaryBottomData n k L`, and returns odd rainbow count. fileciteturn151file0L124-L156 What is missing for Brouwer is **not** the incidence parity engine; it is the theorem

```lean
BoundaryBottomData_for_labelN :
  BoundaryBottomData n k (labelN f k pulled to the type-A/simplex carrier)
```

or the equivalent simplex/type-A `hR3` boundary-door oddness theorem.

## (1) Cleanest induction for arbitrary `labelN f`

The clean Lean formulation is:

```lean
def ProperSimplexLabel
    (n k : ℕ)
    (L : (Fin (n+1) → ℤ) → Fin (n+1)) : Prop :=
  ∀ v : Fin (n+1) → ℤ,
    (∀ i, 0 ≤ v i) →
    (∑ i, (v i).toNat = k) →
    ∀ i, v i = 0 → L v ≠ i
```

Then prove:

```lean
theorem labelN_properSimplexLabel
    (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n+1)))
                            (stdSimplex ℝ (Fin (n+1)))) :
    ProperSimplexLabel n k (labelN f k)
```

This is essentially already present. The repo has:

```lean
label_avoids_forbidden_coord_on_face
```

which says that if a barycentric/lattice coordinate is zero, then `labelN f k` avoids that colour. fileciteturn147file0L31-L44 The bottom-face specialization is also already proved as `labelN_ne_last_on_face`. fileciteturn147file0L15-L29

Then prove the generic theorem:

```lean
theorem BoundaryBottomData.of_properSimplexLabel
    (hk : 0 < k)
    (hproper : ProperSimplexLabel n k L) :
    SimplexBoundaryBottomData n k L
```

or, if you keep the existing naming:

```lean
theorem boundaryBottomData_of_proper_labelN
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    BoundaryBottomData n k (freudenthalOrTypeALabelN f k)
```

The induction should mirror classical Sperner:

1. **Cell/facet incidence:** use the existing label-agnostic incidence engine. In the Freudenthal file, `exists_rainbow_cellF_R2` calls `sperner_n_dim_combinatorial` with arbitrary `L`; it is not specific to `postLabel`. fileciteturn149file0L55-L77

2. **Boundary-door count:** prove that lower-colour boundary doors live on the bottom/opposite-last face.

3. **Dimension drop:** identify those bottom doors with rainbow cells of the projected lower-dimensional complex.

4. **Recursive properness:** show the projected `bottomLabel` is again proper.

So the engine is **labeling-agnostic** at the incidence/parity layer. The existing `postLabelTower` proof bakes in a specific label only to make the boundary-data proof trivial; it should not be the final Brouwer label theorem.

## (2) Exact boundary condition for `labelN f`

For the existing box/Freudenthal `BoundaryBottomData`, the recursive step is:

```lean
∃ havoid : ∀ v : Fin n → ℤ,
    L (appendZero v) ≠ Fin.last (n+1),

  (∀ F ∈ facets (n+1) k,
    F.image L = Finset.univ.erase (Fin.last (n+1)) →
    isBoundary (Nat.succ_pos n) k F →
      ∀ v ∈ F, v (Fin.last n) = 0)

  ∧ BoundaryBottomData n k (bottomLabel L havoid)
```

The code shows exactly this shape. fileciteturn151file0L124-L133

For the **simplex/type-A** version, the same mathematical condition should be stated with the simplex/type-A facet and boundary predicates:

```lean
def SimplexBoundaryBottomData : (n k : ℕ) → SimplexLabel n → Prop
  | 0, _, _ => True
  | n+1, k, L =>
      ∃ havoid : ∀ v, L (appendBottom v) ≠ Fin.last (n+1),
        (∀ F ∈ simplexFacetsOrTypeAFacets (n+1) k,
          isDoor L F →
          isSimplexBoundary F →
            ∀ v ∈ F, v (Fin.last n) = 0)
        ∧ SimplexBoundaryBottomData n k (simplexBottomLabel L havoid)
```

The critical condition is:

```lean
hbottom :
  every boundary door with colour set `univ.erase last`
  lies on the bottom face `x_last = 0`.
```

For `postLabel`, this is nearly syntactic: off the bottom face, `postLabel` returns the top colour. The code defines:

```lean
postLabel L v :=
  if v last = 0 then (L (dropLast v)).castSucc
  else Fin.last
```

so a door whose image is `univ.erase last` cannot contain off-bottom vertices. fileciteturn137file0L204-L215

For `labelN f`, the proof is not syntactic but standard Sperner geometry:

```text
If a boundary facet lies in face i = 0, then every vertex v of that facet has v_i = 0.
Properness gives L(v) ≠ i for every vertex.
But a lower-colour door has image univ.erase(last), so if i ≠ last, colour i must appear.
Contradiction.
Therefore i = last, i.e. the door lies on the bottom face.
```

So yes: it is the **same abstract boundary condition** the specific tower satisfies. The proof differs:

```text
postLabelTower: by definition of postLabel.
labelN f: by Sperner support-face condition + simplex boundary-face geometry.
```

The label restriction on the lower face is also the same. The existing `bottomLabel` is:

```lean
bottomLabel L havoid v := (L (appendZero v)).castPred (havoid v)
```

and `bottomLabel_castSucc` says it embeds back to the original upper label on `appendZero v`. fileciteturn137file0L217-L230

For `labelN f`, recursive properness should be:

```lean
theorem bottomLabel_proper
    (hproper : ProperSimplexLabel (n+1) k L)
    (havoid : ∀ v, L (appendZero v) ≠ Fin.last (n+1)) :
    ProperSimplexLabel n k (bottomLabel L havoid)
```

Proof sketch:

```lean
intro v hnonneg hsum i hzero
-- assume bottomLabel L havoid v = i
-- castSucc both sides:
have hcast : L (appendZero v) = i.castSucc := by
  rw [← bottomLabel_castSucc L havoid v, assumption]
-- but appendZero v has coordinate i.castSucc = 0
exact hproper (appendZero v) ... i.castSucc (by simpa using hzero) hcast
```

That is the induction payload.

## The exact missing simplex/type-A geometry

The genuine missing theorem is not colour-theoretic; it is geometric:

```lean
theorem simplex_boundary_facet_lies_in_zero_face
    (hF : F ∈ simplexFacetsOrTypeAFacets n k)
    (hb : simplexBoundaryOrTypeABoundary F) :
    ∃ i : Fin (n+1), ∀ v ∈ F, v i = 0
```

Then derive:

```lean
theorem boundary_door_vertices_bottom_of_proper
    (hproper : ProperSimplexLabel n k L)
    (hdoor : F.image L = Finset.univ.erase (Fin.last n))
    (hb : simplexBoundary F) :
    ∀ v ∈ F, v (Fin.last n) = 0
```

Proof:

```lean
obtain ⟨i, hiF⟩ := simplex_boundary_facet_lies_in_zero_face hF hb
by_cases hi_last : i = Fin.last n
  · simpa [hi_last] using hiF
  · have i_in_door : i ∈ Finset.univ.erase (Fin.last n) := ...
    rw [← hdoor] at i_in_door
    rcases Finset.mem_image.mp i_in_door with ⟨v, hvF, hvlabel⟩
    exact hproper v ... i (hiF v hvF) hvlabel
```

This is precisely where the old model broke: it did not identify the correct post-projected boundary face. The current file already distinguishes the correct and incorrect zero-door carriers:

```lean
simplexZeroDoorCells      -- post-projection door
simplexZeroDoorCellsOld   -- legacy pre-projection door, false as parity target
```

and the counterexample has post-projection count `1` but old count `0`. fileciteturn146file0L76-L123

The code also already contains a labelN-specific post-projection door-to-lower-rainbow bridge:

```lean
simplexZeroDoorPostLabels_labelN_door_iff_lower_rainbow
mem_simplexZeroDoorCells_labelN_iff_lower_rainbow
```

These are exactly the local door ↔ lower-rainbow facts you need inside the recursive hR3 proof. fileciteturn144file0L144-L183

## (3) No useful shortcut from the specific-label parity

A rainbow cell for `postLabelTower` does **not** give an approximate fixed point for arbitrary `f`. The approximate fixed-point argument uses the defining property of `labelN f k`: each colour records a coordinate inequality involving `f(x)_i` and `x_i`. A rainbow cell under an unrelated fixed label has no such relation to `f`.

The possible shortcuts are all heavier than proving the missing boundary-data theorem:

### “Parity is labeling-invariant”

For proper Sperner labels, the parity is invariant mod 2, but proving that is essentially another proof of Sperner’s lemma. You would need a label-homotopy or one-vertex relabeling argument showing rainbow parity changes by an even number. That is not shorter than the boundary-door induction, and it would still require the proper-boundary condition for `labelN f`.

### Degree/retraction argument

A degree proof would bypass combinatorics only by introducing Brouwer degree or fixed-point index. That is much more infrastructure than the current finite parity setup. It also would undercut the existing mesh/rainbow → approximate fixed point pipeline.

### Retraction from box parity

The box parity for a special postLabelTower label does not transfer to arbitrary simplex `labelN f` without proving that the induced label has the same boundary-degree/parity. That again is the missing Sperner theorem in disguise.

So the shortest path is:

```text
prove properness of labelN f
+ prove simplex/type-A BoundaryBottomData from properness
+ run the existing label-agnostic parity engine
+ feed the resulting labelN-rainbow cell to Brouwer approximation.
```

## Recommended Lean assembly

I would implement the missing layer in this order.

### 1. Define proper simplex labels

```lean
def ProperSimplexLabel
    (n k : ℕ)
    (L : (Fin (n+1) → ℤ) → Fin (n+1)) : Prop :=
  ∀ v : Fin (n+1) → ℤ,
    (∀ i, 0 ≤ v i) →
    (∑ i, (v i).toNat = k) →
    ∀ i, v i = 0 → L v ≠ i
```

### 2. Prove `labelN f k` is proper

```lean
theorem labelN_properSimplexLabel
    (hk : 0 < k)
    (hmaps : Set.MapsTo f (stdSimplex ℝ (Fin (n+1)))
                            (stdSimplex ℝ (Fin (n+1)))) :
    ProperSimplexLabel n k (labelN f k) :=
by
  intro v hnonneg hsum i hzero
  exact label_avoids_forbidden_coord_on_face hk hmaps hsum hzero
```

modulo exact namespace/index choices. The core lemma already exists. fileciteturn147file0L31-L44

### 3. Prove properness descends to the bottom label

```lean
theorem bottomLabel_properSimplexLabel
    (hproper : ProperSimplexLabel (n+1) k L)
    (havoid : ∀ v, L (appendZero v) ≠ Fin.last (n+1)) :
    ProperSimplexLabel n k (bottomLabel L havoid)
```

### 4. Prove boundary doors lie on the bottom face

This is the hard missing geometry:

```lean
theorem simplex_boundary_door_vertices_bottom_of_proper
    (hproper : ProperSimplexLabel (n+1) k L) :
    ∀ F ∈ simplexFacetsOrTypeAFacets (n+1) k,
      F.image L = Finset.univ.erase (Fin.last (n+1)) →
      simplexBoundaryOrTypeABoundary F →
        ∀ v ∈ F, v (Fin.last n) = 0
```

This is the simplex analogue of the `hbottom` field in `BoundaryBottomData`.

### 5. Package recursive boundary data

```lean
theorem simplexBoundaryBottomData_of_proper
    (hk : 0 < k)
    (hproper : ProperSimplexLabel n k L) :
    SimplexBoundaryBottomData n k L
```

or directly:

```lean
theorem hR3_labelN_postProjection
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    Odd (simplexZeroDoorCells n k (labelN f k)).card
```

The latter can use the already-existing local bridge

```lean
mem_simplexZeroDoorCells_labelN_iff_lower_rainbow
```

to recurse on lower rainbow cells. fileciteturn144file0L161-L183

### 6. Final theorem

```lean
theorem exists_rainbow_cell_labelN_freudenthal
    (hk : 0 < k)
    (hmaps : MapsTo f Δ Δ) :
    ∃ c ∈ typeASimplexCells n k,
      isRainbow (labelN f k) c
```

Then use the existing approximate fixed-point bridge.

## Final diagnosis

The specific `postLabelTower` parity is not the Brouwer theorem. It is evidence that the **post-projection door geometry is correct**. For arbitrary `labelN f`, the correct theorem is the standard Sperner theorem on the type-A/simplex carrier:

```text
proper boundary label  ⇒  odd number of rainbow top cells.
```

`labelN f` is proper. The old fixed-last door was wrong. The post-projection/type-A door is right. The missing Lean work is the generic simplex/type-A boundary-door induction from `ProperSimplexLabel` to `BoundaryBottomData`, not another special-label construction.
