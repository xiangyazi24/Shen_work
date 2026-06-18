## Verdict

**Least-infrastructure faithful close: (c), with a clearly named `hboxCubeData` / `SourceBoxCubeApproxData` hypothesis.**

Do **not** claim the outer cube witness literally applies to the inner source box. The reusable part is the **Schauder bridge shape**, not the actual `proj/lift`. In the repo, `ProjectedCubeApproxData` is just the finite-dimensional data package: `dim`, `proj`, `lift`, `eps`, `localError`, plus `proj_trap`, `maps`, `cont`, `lift_trap`, and `residual_le`. Its conversion to `LocalUniformCubeApproxData` is direct. fileciteturn20file0L24-L66 The fixed-point bridge then consumes that cube data together with continuity and compact range. fileciteturn21file0L49-L59

So the faithful close is:

```lean
hboxCubeData :
  ProjectedCubeApproxData
    (PaperWeightedHolderExpSourceBox κ M B β H K σ aL)
    (fun R => paperStepSource_truncated u Z (greenConv R))
```

or the corresponding `LocalUniformCubeApproxData` after `.toLocalUniformCubeApproxData`.

This is not faking: the repo handoff explicitly identifies `hboxCubeData` as the one finite-net Schauder witness that may remain carried, and warns not to fake it. fileciteturn16file0L21-L25 It also says the inner `boxCubeData` is the same approximation-theory floor as the outer G1 finite-net floor. fileciteturn16file0L61-L65

If the final theorem must be **fully unconditional**, then implement the construction below. But for closing the PDE content of `hprodAll`, (c) is the least-risk Lean route.

---

## Why literal (a) is false

The outer witness is not a generic “sample/interpolate any compact Hölder box” construction. It is an **order-cube** construction for monotone wave profiles.

The outer mesh uses

```lean
waveCubeDim N     := 2 * (N + 1) * (N + 1) + 1
waveCubeRadius N  := (N + 1 : ℝ)
waveCubeMesh N    := ((N + 1 : ℝ))⁻¹
waveCubeNode N i  := -waveCubeRadius N + (i : ℕ) * waveCubeMesh N
```

and the lift is

```lean
waveRawLift κ M κtilde D N a x :=
  max (lowerBarrierPlateau κ κtilde D x)
    (min (upperBarrier κ M x) (waveOrderEnvelope M N a x))
```

with projection by point values divided by `M`. fileciteturn22file0L3-L51 The actual outer cube data assigns

```lean
dim        := waveCubeDim
proj       := waveValueProj M
lift       := waveRawLift κ M κtilde D
eps        := waveCubeEps
localError := waveCubeLocalError M
```

and then proves the fields from monotone/lower-pinned trap facts. fileciteturn10file0L175-L206

That lift preserves **antitonicity + lower/upper wave barriers**. It does not preserve:

```lean
|R x| ≤ B * upperBarrier κ M x
β-Hölder ≤ H
exp-left-rate / left-tail modulus ≤ K * exp (σ * (x - aL))
```

A naive piecewise-linear lift is also not the best Lean target. From arbitrary `a ∈ unitCube`, adjacent grid values need not satisfy the Hölder constraints, and clipping after interpolation against a variable bound `B * upperBarrier` plus an exponential left-rate tube can break the exact Hölder constant unless the obstacles themselves are included in the reconstruction proof.

So: **not literal (a)**. It is only mirrorable at the level of the `ProjectedCubeApproxData` interface.

---

## If you build the inner witness: use a clipped McShane reconstruction

This is the clean construction for the source box.

Assume the source box is formulated with an explicit exponential left-rate field:

```lean
∃ ℓ, ∀ x ≤ aL,
  |R x - ℓ| ≤ K * Real.exp (σ * (x - aL))
```

and derive the pairwise Cauchy modulus from it. If your public box field is instead the pairwise Cauchy modulus, keep an internal `ExpLeftRate` predicate and expose the derived Cauchy field.

### Basic definitions

Let

```lean
S : ℝ := B * M
b x : ℝ := B * upperBarrier κ M x
hN N : ℝ := waveCubeMesh N
RN N : ℝ := waveCubeRadius N
```

Reuse the outer grid:

```lean
sourceNode N i := waveCubeNode N i
```

Use one extra coordinate for the left limit:

```lean
sourceCubeDim N := waveCubeDim N + 1
```

Coordinate `0` encodes the left limit. Coordinates `1 + i` encode samples.

```lean
leftCoordDecode (a : Fin (sourceCubeDim N) → ℝ) : ℝ :=
  2 * S * a 0 - S
```

For the free sample value at node `i`:

```lean
freeNodeValue N a i : ℝ :=
  b (sourceNode N i) * (2 * a (sampleCoord i) - 1)
```

where `sampleCoord i : Fin (sourceCubeDim N)` is the shifted coordinate.

### Obstacles

Use a left-rate tube only on the left plateau and the weighted bound everywhere.

```lean
leftTubeRadius x :=
  K * Real.exp (σ * (x - aL))
```

For `x ≤ aL`:

```lean
lowerObs ℓ x := max (-(b x)) (ℓ - leftTubeRadius x)
upperObs ℓ x := min ( b x)  (ℓ + leftTubeRadius x)
```

For `x > aL`, make the left-rate tube inactive:

```lean
lowerObs ℓ x := -(b x)
upperObs ℓ x :=  b x
```

Require the harmless parameter inequality

```lean
2 * S ≤ K
```

so the obstacle is continuous at `aL` and the tube contains the whole plateau interval there.

Define the scalar clamp:

```lean
clampObs ℓ x y :=
  max (lowerObs ℓ x) (min (upperObs ℓ x) y)
```

Decode the actual node values by clamping free node values:

```lean
sourceNodeValue N a i :=
  clampObs (leftCoordDecode a) (sourceNode N i) (freeNodeValue N a i)
```

### McShane upper envelope

For arbitrary cube coordinates, define

```lean
sourceMcShane N a x :=
  Finset.univ.inf' (waveCubeUniv_nonempty N)
    (fun i =>
      sourceNodeValue N a i
        + H * |x - sourceNode N i| ^ β)
```

Then the lift is

```lean
sourceLift N a x :=
  clampObs (leftCoordDecode a) x (sourceMcShane N a x)
```

This is the right replacement for `waveRawLift`.

---

## Why this lift preserves the source box

For `a ∈ unitCube (sourceCubeDim N)`:

### 1. Weighted bound

The final clamp gives

```lean
lowerObs ℓ x ≤ sourceLift N a x ≤ upperObs ℓ x
```

and both obstacles are inside `[-b x, b x]`, hence

```lean
|sourceLift N a x| ≤ B * upperBarrier κ M x.
```

### 2. Exponential left-rate

For `x ≤ aL`, the same clamp gives

```lean
|sourceLift N a x - ℓ| ≤ K * exp (σ * (x - aL)),
```

where

```lean
ℓ = leftCoordDecode a.
```

Thus the lift has the required left limit `ℓ`, and the Cauchy field follows as

```lean
|sourceLift N a x - sourceLift N a y|
  ≤ 2*K * exp (σ * (A - aL))
```

for `x y ≤ A ≤ aL`. If the box’s stored modulus is pairwise `K * exp ...`, then use a rate constant `K/2` internally.

### 3. Hölder

The McShane envelope is `H`-Hölder because each function

```lean
x ↦ sourceNodeValue N a i + H * |x - sourceNode N i| ^ β
```

is `H`-Hölder for `0 < β ≤ 1`, and finite infima preserve the same Hölder constant.

The obstacle functions must be proved `H`-Hölder too:

```lean
Holder β H (fun x => lowerObs ℓ x)
Holder β H (fun x => upperObs ℓ x)
```

This is where you use the already-known Hölder bounds for `upperBarrier` and for `x ↦ exp (σ*(x-aL))` on the left plateau, plus the assumption that the source-box `H` was chosen large enough. Then `max`/`min` preserve the same Hölder constant.

So `sourceLift_mem_box` is a finite collection of clamp/envelope lemmas, not a PDE lemma.

---

## Exact `ProjectedCubeApproxData` fields

For the inner source box, define:

```lean
abbrev SourceBoxCubeApproxData
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Type :=
  ProjectedCubeApproxData
    (PaperWeightedHolderExpSourceBox κ M B β H K σ aL)
    Tmap
```

Then the witness should be:

```lean
noncomputable def sourceBoxProjectedCubeApproxData
    (hmap :
      ∀ R,
        PaperWeightedHolderExpSourceBox κ M B β H K σ aL R →
        PaperWeightedHolderExpSourceBox κ M B β H K σ aL (Tmap R))
    (hcont :
      LocalUniformContinuousOn
        (PaperWeightedHolderExpSourceBox κ M B β H K σ aL)
        Tmap)
    (hcompact :
      LocalUniformSequentiallyCompactRange
        (PaperWeightedHolderExpSourceBox κ M B β H K σ aL)
        Tmap)
    -- plus obstacle Hölder / positivity / parameter inequalities
    :
    ProjectedCubeApproxData
      (PaperWeightedHolderExpSourceBox κ M B β H K σ aL)
      Tmap :=
by
  refine
    { dim := sourceCubeDim
      proj := sourceProj κ M B β H K σ aL
      lift := sourceLift κ M B β H K σ aL
      eps := sourceCubeEps β
      localError := sourceCubeLocalError B M H K β
      eps_pos := sourceCubeEps_pos
      proj_trap := ?_
      maps := ?_
      cont := ?_
      lift_trap := ?_
      localError_nonneg := ?_
      localError_tendsto := ?_
      residual_le := ?_ }
```

### `proj`

Define `proj` by encoding the left limit and finite samples.

```lean
noncomputable def sourceProj N (R : ℝ → ℝ) :
    Fin (sourceCubeDim N) → ℝ :=
  fun j =>
    if hj : j = 0 then
      if hR : PaperWeightedHolderExpSourceBox κ M B β H K σ aL R then
        (leftLimitOfBox hR + S) / (2*S)
      else
        0
    else
      let i := sampleIndexOfNonzero hj
      (R (sourceNode N i) + b (sourceNode N i)) /
        (2 * b (sourceNode N i))
```

The `if hR : box R` is necessary because `proj` has type `(ℝ → ℝ) → ...`, not `Subtype box → ...`.

For `proj_trap`, the sample coordinates are in `[0,1]` from the weighted bound, and the limit coordinate is in `[0,1]` from the left bound plus the exponential-rate limit.

### `maps`

This is immediate:

```lean
intro N a ha
exact sourceProj_mem_unitCube N
  (hmap (sourceLift N a) (sourceLift_mem_box N a ha))
```

This is the same pattern as the outer construction, where `maps` is discharged by applying the map-invariance result and then `waveValueProj_mem_unitCube`. fileciteturn10file0L189-L194

### `cont`

The sample coordinates follow from `hcont` and local-uniform convergence evaluated at finitely many nodes.

The left-limit coordinate needs one extra reusable lemma:

```lean
lemma leftLimit_continuous_of_locallyUniform_of_uniformExpRate
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hFbox : ∀ n, PaperWeightedHolderExpSourceBox κ M B β H K σ aL (F n))
    (hfbox : PaperWeightedHolderExpSourceBox κ M B β H K σ aL f)
    (hconv : LocallyUniformConverges F f) :
    Tendsto
      (fun n => leftLimitOfBox (hFbox n))
      atTop
      (𝓝 (leftLimitOfBox hfbox))
```

Proof: choose `A << 0` so the exponential tails of `F n` and `f` are `< ε/3`, then use local-uniform convergence at the single point `A`.

This avoids needing an explicit formula for the source-map left limit.

### `lift_trap`

Prove with:

```lean
sourceLift_continuous
sourceLift_weighted_bound
sourceLift_holder
sourceLift_expLeftRate
```

Then package:

```lean
exact sourceLift_mem_box N a ha
```

### `localError`

Use:

```lean
sourceCubeEps N := (waveCubeMesh N) ^ β
```

and a deliberately fat constant:

```lean
sourceCubeLocalError N R :=
  if R ≤ waveCubeRadius N then
    Csrc * sourceCubeEps N
  else
    4*S + 2*K + 1
```

where a safe formal choice is

```lean
Csrc := 64 * (S + K + H + 1)
```

The exact constant is unimportant; it just needs to dominate:

```lean
decoded sample error
+ decoded left-limit error
+ obstacle endpoint error
+ McShane grid error H * hN^β.
```

Then:

```lean
sourceCubeLocalError_nonneg
sourceCubeLocalError_tendsto
```

follow from positivity and `waveCubeMesh N → 0`.

### `residual_le`

Let

```lean
f := Tmap (sourceLift N a)
```

Assume:

```lean
‖sourceProj N f - a‖ ≤ sourceCubeEps N.
```

For `x ∈ [-R,R]` and `R ≤ waveCubeRadius N`, choose a node `i` with

```lean
|x - sourceNode N i| ≤ waveCubeMesh N.
```

Then:

1. Coordinate closeness gives the left-limit error:

```lean
|ℓ_f - ℓ_a| ≤ 2*S * sourceCubeEps N.
```

2. Coordinate closeness gives node-value error:

```lean
|sourceNodeValue N a i - f (sourceNode N i)|
  ≤ C0 * sourceCubeEps N.
```

3. Hölder gives:

```lean
|f (sourceNode N i) - f x|
  ≤ H * |sourceNode N i - x|^β
  ≤ H * sourceCubeEps N.
```

4. McShane gives the upper and lower approximation bounds.

5. The final obstacle clamp changes the estimate only by the obstacle endpoint error, controlled by `|ℓ_f - ℓ_a|`.

So:

```lean
|Tmap (sourceLift N a) x - sourceLift N a x|
  ≤ Csrc * sourceCubeEps N.
```

For `R > waveCubeRadius N`, use the coarse global bound:

```lean
|f x - sourceLift N a x| ≤ 4*S + 2*K + 1.
```

This mirrors the outer residual shape: the outer proof uses coordinate closeness, a grid-cover lemma, lift stability in coordinates, and then a coarse fallback outside the covered interval. fileciteturn10file0L3-L20

---

## Practical recommendation

For the current `hprodAll` push, use:

```lean
(hboxCubeData :
  ProjectedCubeApproxData SourceBox Tmap)
```

or

```lean
(hboxCubeData :
  LocalUniformCubeApproxData SourceBox Tmap)
```

and wire it through the existing bridge. That is the smallest faithful close.

If later you want to discharge `hboxCubeData`, implement the clipped McShane construction above. Do **not** try to reuse `waveRawLift`; it is the wrong lift. The source-box witness is the same kind of approximation-theory floor, but its reconstruction is genuinely different.
