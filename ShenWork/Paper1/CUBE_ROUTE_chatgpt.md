## Recommendation

For the **wave G1** goal, the least-friction route is probably **cube Brouwer**, not the standard-simplex `cellsN/typeAFacets` route.

But the cube route should be stated carefully:

```text
Use the existing box/Freudenthal parity engine,
but feed it a cube Kuhn/Poincaré–Miranda label that satisfies `BoundaryBottomData`.

Do not try to use the raw 2n sign labels directly,
and do not try to reuse the specific `postLabelTower` label for an arbitrary Tmap.
```

The existing engine is already label-agnostic: it takes an arbitrary `L : Label n` plus `BoundaryBottomData n k L` and returns odd rainbow count. fileciteturn151file0L124-L156 The missing work on the cube route is therefore much smaller and more local than rebuilding a full type-A simplex parity engine.

---

## (1) Can the existing box engine close cube Brouwer?

Yes, if you use the **right cube label**.

The existing box engine is not a raw Poincaré–Miranda engine with labels `±i`. It is an `n+1`-colour Freudenthal/Kuhn engine:

```lean
Label n := (Fin n → ℤ) → Fin (n+1)
```

and it proves parity from `BoundaryBottomData`. The relevant door is the box bottom-door:

```lean
isBottomDoor L c :=
  (facetSet c.1 c.2 (Fin.last (n + 1))).image L =
    Finset.univ.erase (Fin.last (n + 1))
```

and the code proves bottom-door count equals lower rainbow count under the induced `bottomLabel`. fileciteturn138file0L70-L110

So the cube Brouwer label should be a **Kuhn cumulative-sum label**, not a `±i` sign label.

For a self-map

```text
T : [0,1]^n → [0,1]^n,
```

at a grid vertex `x`, set

```text
g_i(x) = T_i(x) - x_i.
```

Then define partial sums

```text
S_0(x) = 0,
S_j(x) = g_0(x) + ... + g_{j-1}(x),   j = 1,...,n.
```

Label `x` by the index where `S_j(x)` is minimal, with a fixed tie convention. A rainbow Freudenthal simplex then forces all partial sums to be nearly equal on a small cell, hence every difference

```text
g_i = S_{i+1} - S_i
```

is small, giving an approximate fixed point.

There is one nuisance: tie cases on boundary faces. The clean way to avoid them is to use a strict interior perturbation:

```text
T^δ(x) = (1 - 2δ) T(x) + δ · 1,
```

so that

```text
x_i = 0  ⇒  T^δ_i(x) - x_i ≥ δ > 0,
x_i = 1  ⇒  T^δ_i(x) - x_i ≤ -δ < 0.
```

Then the cumulative-sum label has strict face exclusions, and the `δ`-approximate fixed point for `T^δ` is an `(O(δ)+mesh)`-approximate fixed point for `T`.

This strictified cube Kuhn label should feed the **same box `BoundaryBottomData` engine**:

```lean
theorem cubeKuhnLabel_boundaryBottomData
    (hk : 0 < k)
    (hT : MapsTo T unitCube unitCube)
    (hδ : 0 < δ) :
    BoundaryBottomData n k (cubeKuhnLabel (strictify δ T) k)
```

Then:

```lean
have hodd :=
  rainbow_count_odd_of_boundaryBottomData hk
    (cubeKuhnLabel (strictify δ T) k)
    (cubeKuhnLabel_boundaryBottomData hk hT hδ)
```

The engine itself does **not** bake in `postLabelTower`; `postLabelTower` is only one easy way to produce `BoundaryBottomData`.

---

## What must be proved for the cube label?

I would split it into two generic lemmas.

### A. Cube face-avoidance condition

Define a boundary predicate for `n+1`-colour cube labels:

```lean
def CubeKuhnBoundary (k : ℕ) (L : (Fin n → ℤ) → Fin (n+1)) : Prop :=
  ∀ v, cubeVertexValid k v →
    -- lower face x_i = 0 excludes one adjacent colour
    (∀ i : Fin n, v i = 0 → L v ≠ lowerForbidden i) ∧
    -- upper face x_i = k excludes the other adjacent colour
    (∀ i : Fin n, v i = k → L v ≠ upperForbidden i)
```

The exact `lowerForbidden`/`upperForbidden` indices depend on whether you use `argmin` or `argmax` and your tie convention. With the strictified map, the proof is straightforward because the relevant partial sums are strictly ordered across a boundary coordinate.

### B. BoundaryBottomData from face-avoidance

Prove:

```lean
theorem BoundaryBottomData.of_cubeKuhnBoundary
    (hk : 0 < k)
    (hbdry : CubeKuhnBoundary k L) :
    BoundaryBottomData n k L
```

This theorem is the cube analogue of the standard Sperner boundary induction. Its key step is:

```lean
hbottom :
  ∀ F ∈ facets (n+1) k,
    F.image L = Finset.univ.erase (Fin.last (n+1)) →
    isBoundary (Nat.succ_pos n) k F →
      ∀ v ∈ F, v (Fin.last n) = 0
```

That is exactly the `hbottom` field consumed by the existing engine. fileciteturn151file0L124-L133

The proof pattern is:

```text
A boundary facet of the cube lies in some cube face x_i=0 or x_i=k.
If that face is not the distinguished bottom face, `CubeKuhnBoundary` says
one of the colours in `univ.erase last` is forbidden on every vertex.
Therefore the facet cannot be a door with image `univ.erase last`.
So any boundary door must lie on the distinguished bottom face.
```

Then `bottomLabel` inherits the same cube-boundary condition in dimension `n-1`, so the induction recurses.

This is exactly what your box engine wants. It avoids the `simplexCells` slack-face obstruction entirely.

---

## (2) Is the wave finite-dimensional trap more naturally cube-shaped?

Yes, more cube/order-polytope than standard simplex.

A finite-dimensional monotone-profile approximation usually has coordinates like

```text
U(x_0), U(x_1), ..., U(x_N)
```

with constraints

```text
0 ≤ U(x_i) ≤ Ubar(x_i),
U(x_0) ≥ U(x_1) ≥ ... ≥ U(x_N).
```

That is an **order polytope** inside a box, not a standard simplex. A simplex Brouwer theorem can still handle it after triangulation/retraction/barycentric encoding, but it is not the natural coordinate shape.

For G1, a cube theorem is often the cleanest finite-dimensional primitive:

```text
continuous self-map of a cube/order box
→ approximate fixed point
→ compactness/limit
→ Schauder fixed point.
```

There is one caveat: the monotonicity constraints mean the profile-value set is not literally a product cube unless you choose a parameterization or a retraction. You have three options:

```text
1. Work on an ambient product box and compose Tmap with a monotone-envelope/retraction.
2. Parameterize monotone profiles by independent cube variables.
3. Prove fixed point on the order polytope using cube Brouwer plus an explicit retraction.
```

Any of these is more naturally cube/order-polytope flavored than standard-simplex flavored.

The simplex route is still mathematically valid, but for this repo it has the known obstruction: `simplexCells`/`appendSlack` facets do not give a literal slack-face recursion in dimensions ≥ 2, which is why a genuine type-A simplex parity engine is still missing. The repo already distinguishes the correct post-projection simplex door from the old false one: `simplexZeroDoorCells` is the post-projection door, while `simplexZeroDoorCellsOld` is explicitly marked false as a recursive parity target, and the counterexample has new count `1` but old count `0`. fileciteturn146file0L76-L123

---

## (3) What should `brouwer_cube_approx` look like?

Use the cumulative-sum Kuhn label.

### Label

For a mesh vertex `v : Fin n → ℤ`, let

```lean
x_i = (v i : ℝ) / k
g_i = T_i x - x_i
S_j = ∑ i with i.val < j.val, g_i
```

Then define:

```lean
cubeKuhnLabel T k v : Fin (n+1) :=
  argmin j, S_j
```

using a deterministic tie convention. With strictification `T^δ`, ties at boundary faces are harmless or disappear where needed.

The raw Poincaré–Miranda signs are:

```text
x_i = 0 ⇒ g_i ≥ 0,
x_i = 1 ⇒ g_i ≤ 0.
```

These signs are not themselves the labels for the existing engine. They are used to prove the face-avoidance rules for `cubeKuhnLabel`.

### Approximate fixed point from a rainbow cell

Given a rainbow Freudenthal cell:

```lean
c ∈ cells n k
isRainbow (cubeKuhnLabel Tδ k) c
```

choose a point in the geometric simplex, usually one vertex or its barycenter. Since the cell diameter is `O(1/k)` and `Tδ` is uniformly continuous, all `g_i` and all partial sums `S_j` vary by at most a modulus `ω(O(1/k))` across the cell.

Because every label `j = 0,...,n` appears in the rainbow cell, every partial sum is approximately minimal somewhere. Transporting these inequalities to a common point gives:

```text
|S_j - S_l| ≤ C_n · ω(O(1/k))
```

for all `j,l`, hence

```text
|g_i| = |S_{i+1} - S_i| ≤ C_n · ω(O(1/k)).
```

Thus

```text
‖Tδ(x) - x‖∞ ≤ C_n · ω(O(1/k)).
```

Finally,

```text
‖T(x) - x‖∞
≤ ‖T(x) - Tδ(x)‖∞ + ‖Tδ(x) - x‖∞
≤ 2δ + C_n · ω(O(1/k)).
```

So the theorem shape should be:

```lean
theorem brouwer_cube_approx
    (hT : Continuous T)
    (hmaps : MapsTo T unitCube unitCube)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ unitCube, ‖T x - x‖ ≤ ε
```

proved by choosing `δ` small and `k` large.

---

## Does the cube label feed the same `BoundaryBottomData` engine?

Yes, if you define it as the `n+1`-colour Kuhn cumulative-sum label and prove the boundary-face avoidance rules. It does **not** feed the engine if you use raw `±i` sign labels.

So the route is:

```lean
cubeKuhnLabel_proper :
  CubeKuhnBoundary k (cubeKuhnLabel Tδ k)

BoundaryBottomData.of_cubeKuhnBoundary :
  CubeKuhnBoundary k L → BoundaryBottomData n k L

rainbow_count_odd_of_boundaryBottomData :
  BoundaryBottomData n k L →
  Odd ((cells n k).filter (fun c => isRainbow L c)).card

exists_rainbow_cellF_of_boundaryBottomData :
  ∃ rainbow cube/Freudenthal cell

brouwer_cube_approx :
  rainbow cube/Freudenthal cell → approximate fixed point
```

The code already has the label-agnostic parity and existence outputs:

```lean
rainbow_count_odd_of_boundaryBottomData
exists_rainbow_cellF_of_boundaryBottomData
```

for arbitrary labels satisfying the boundary data. fileciteturn151file0L135-L156 fileciteturn151file0L189-L193

---

## What if you stay with simplex?

Then you need a real type-A simplex parity engine:

```lean
typeABoundaryBottomData
typeAPartnerCell
typeAInteriorDoorsCancel
typeABoundaryDoors_eq_lowerRainbow
rainbow_count_odd_typeA_of_boundaryData
```

This is **not** just a small wrapper around the current box engine, because the current box theorem has concrete types:

```lean
cells n k
facets n k
cellBounds
isBoundary
partnerCell
BoundaryBottomData
```

and the type-A/simplex carrier has different cell/facet/boundary predicates. The current `simplexCells` transport also has the recorded slack-face obstruction, so you cannot simply coerce the existing box bottom-face proof into the simplex setting. You would be mirroring the whole incidence stack: heart, partner involution, boundary singleton, boundary-door dimension drop, and recursion.

That is a large rebuild.

---

## Final recommendation

For the wave G1 target, take the **cube route**.

The least-effort faithful path is:

```text
1. Prove cube Brouwer approximate fixed point using the existing box Freudenthal parity engine.
2. Use a strictified Kuhn cumulative-sum label for arbitrary cube self-maps.
3. Prove `BoundaryBottomData` for that cube label.
4. Prove rainbow cube-cell ⇒ approximate fixed point.
5. Use the cube theorem in the finite-dimensional wave/Schauder approximation, with an explicit cube/order-polytope parameterization or retraction.
```

This avoids the simplex slack-face obstruction and reuses the strongest completed asset: the box/Freudenthal `BoundaryBottomData` parity engine.

The only warning is that the cube label must be the **Kuhn cumulative-sum label**, not the raw Poincaré–Miranda `±i` sign label. The sign conditions prove the boundary compatibility; they are not the labels consumed by the existing `n+1`-colour parity engine.
