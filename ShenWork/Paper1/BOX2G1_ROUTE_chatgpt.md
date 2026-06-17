═══ BRIDGE cron2 | be665722 | 14714 chars 2141 words 413 lines | 543s | prov=network | OK ═══
═══ BRIDGE cron2 | be665722 | 14714 chars 2141 words 413 lines | 543s | prov=network | OK ═══
## Verdict

Use the **standard three-layer route**:

```text
combinatorial Sperner/Freudenthal
  → finite-dimensional continuous Brouwer / approximate Brouwer
  → approximate fixed sequence in the local-uniform profile topology
  → Helly/local-uniform compactness + continuity
  → genuine Schauder fixed point.
```

Do **not** try to make Helly replace Brouwer. Helly gives compactness of the image sequence; it does not create an approximate fixed point. Also do **not** try to prove a full abstract Schauder–Tychonoff theorem first; Mathlib lacks it, and the project already has the lighter sequential bridge you want.

In the repository, the bridge to target is essentially:

```lean
LocalUniformSequentiallyCompactRange.exists_fixed_of_approx_fixed
```

It says: if `seq n ∈ trap`, `seq` is locally-uniformly asymptotically fixed by `Tmap`, `Tmap` is locally-uniformly continuous on `trap`, and the range is locally-uniformly sequentially compact, then there is an actual fixed point. fileciteturn108file0L3-L41

So the missing G1-style theorem should be a wrapper:

```lean
localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences
```

whose only real input is a provider of `LocallyUniformApproxFixed` sequences. The rest is already in the bridge.

---

## (1) Finite combinatorial Brouwer → continuous Brouwer

The clean finite-dimensional route is:

```text
mesh k
  → Sperner labelling from T
  → rainbow Freudenthal/Kuhn cell C_k
  → choose barycenter x_k ∈ C_k
  → prove ‖T x_k - x_k‖ ≤ C · mesh(k) + modulus_T(C · mesh(k))
  → x_k is an approximate fixed point.
```

Then:

```text
compactness of the finite-dimensional domain
  → subsequence x_{k_j} → x*
continuity of T
  → T x_{k_j} → T x*
approx residual → 0
  → T x* = x*.
```

The repository has the combinatorial core: `sperner_n_dim_combinatorial` is the abstract dimension-free parity lemma, producing an odd number of rainbow cells from the local heart, boundary incidence, and odd boundary-door count hypotheses. fileciteturn92file0L35-L56 The boundary-compatible Freudenthal rebuild has the bottom-door/rainbow bridge, including `door_iff_extendCell_rainbow` and `card_bottomDoors_eq_rainbow`. fileciteturn89file0L94-L143

For the continuous Brouwer extraction, the exact finite-dimensional hypotheses are:

```lean
-- Domain
K : Set (Fin n → ℝ)
hKcompact : IsCompact K
hKconvex  : Convex ℝ K
hKnonempty : K.Nonempty

-- Map
T : (Fin n → ℝ) → (Fin n → ℝ)
hTcont : ContinuousOn T K
hTself : Set.MapsTo T K K

-- Triangulation / mesh
cells k : Finset Cell
vertices_of_cell : Cell → Finset (Fin n → ℝ)
hvertices_in_K : ...
hcell_diam : diameter(cell) ≤ δ k
hδ : Tendsto δ atTop (𝓝 0)

-- Sperner compatibility
label : meshVertex k → Fin (n+1)
hsperner_boundary : labels respect faces
hrainbow_exists : ∃ cell, isRainbow label cell
```

For the **standard simplex** `Δⁿ`, the labeling should be:

```text
label(v) = some i in support(v) with T(v)_i ≤ v_i.
```

This exists because `T(v) ∈ Δⁿ`; if `v` lies on a face with support `S`, not every `i ∈ S` can satisfy `T(v)_i > v_i`, since summing would exceed `1`. It is boundary-compatible because the selected label lies in the support face.

For a rainbow cell with vertices `v_i` labeled `i`, choose `x_k` inside the cell, usually the barycenter. Since each `v_i` has

```text
T(v_i)_i ≤ (v_i)_i,
```

uniform continuity gives

```text
T(x_k)_i - (x_k)_i
  ≤ |T(x_k)_i - T(v_i)_i| + |(v_i)_i - (x_k)_i|
  ≤ ω_T(diam C_k) + diam C_k.
```

This holds for every coordinate `i`. Since both `T(x_k)` and `x_k` lie in the simplex, the coordinate differences sum to zero, so upper bounds on all coordinates give lower bounds too. Thus

```text
‖T x_k - x_k‖∞ ≤ (n+1) · (ω_T(diam C_k) + diam C_k)
```

up to the exact norm constant you choose.

For the **cube** `[0,1]^n`, the analogous route is a sign/face labeling: on a lower face `x_i = 0`, `T_i(x) - x_i ≥ 0`; on an upper face `x_i = 1`, `T_i(x) - x_i ≤ 0`. You can either prove cube Brouwer directly on the Freudenthal subdivision, or reduce cube to simplex/compact-convex transport. The repo’s `BrouwerNDim.lean` notes exactly this intended mesh-limit/transport layer: after rainbow cells at every mesh, reuse compactness of `stdSimplex`, a subsequence, and transport to compact convex finite-dimensional sets. fileciteturn95file0L64-L70

Lean implementation recommendation: prove **approximate Brouwer first**, because the infinite-dimensional bridge consumes approximate fixed sequences anyway.

```lean
theorem brouwer_simplex_approx
    {n : ℕ} {T : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ)}
    (hTcont : ContinuousOn T stdSimplex)
    (hTself : Set.MapsTo T stdSimplex stdSimplex) :
    ∀ ε > 0, ∃ x ∈ stdSimplex, ‖T x - x‖ ≤ ε
```

Then derive exact finite-dimensional Brouwer by compactness if desired.

---

## (2) Infinite-dimensional trap: combine finite Brouwer with Helly at the correct layer

The wave trap is not finite-dimensional. The current profile topology is:

```lean
def LocallyUniformConverges (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x, x ∈ Icc (-R) R → |fs n x - f x| < ε
```

fileciteturn107file0L175-L180

The bridge’s approximate-fixed predicate is:

```lean
def LocallyUniformApproxFixed
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) (seq : ℕ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x, x ∈ Icc (-R) R →
      |Tmap (seq n) x - seq n x| < ε
```

fileciteturn104file0L148-L154

So the concrete G1 bridge should target:

```lean
def ApproxFixedSequenceProvider (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∀ Tmap,
    (∀ u, trap u → trap (Tmap u)) →
    LocalUniformContinuousOn trap Tmap →
    LocalUniformSequentiallyCompactRange trap Tmap →
      ∃ seq : ℕ → ℝ → ℝ,
        (∀ n, trap (seq n)) ∧ LocallyUniformApproxFixed Tmap seq
```

Then:

```lean
theorem localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences
    (H : ApproxFixedSequenceProvider trap) :
    LocalUniformSchauderFixedPointPrinciple trap := by
  intro Tmap hinv hcont hcompact
  rcases H Tmap hinv hcont hcompact with ⟨seq, hseq, happrox⟩
  exact hcompact.exists_fixed_of_approx_fixed hcont hseq happrox
```

This uses the committed bridge directly. fileciteturn108file0L3-L41

### How finite Brouwer supplies the approximate fixed sequence

For each `N`, choose:

```text
R_N → ∞
mesh h_N → 0 on [-R_N, R_N]
finite grid Γ_N ⊂ [-R_N, R_N]
finite-dimensional coordinate set K_N
extension E_N : K_N → (ℝ → ℝ)
sampling P_N : (ℝ → ℝ) → K_N
```

Then define the finite-dimensional map:

```lean
F_N(a) := P_N (Tmap (E_N a)).
```

Prove:

```lean
F_N maps K_N into K_N
F_N is continuous
K_N is compact convex
```

Apply finite-dimensional Brouwer to get:

```lean
a_N ∈ K_N
F_N a_N = a_N
```

or approximate equality if you only prove approximate Brouwer. Then set:

```lean
u_N := E_N a_N.
```

Now prove:

```lean
u_N ∈ trap
Tmap u_N ≈ u_N on [-R, R] for every fixed R, eventually in N.
```

The residual proof is just interpolation/equicontinuity:

```text
Tmap u_N and u_N agree at grid points by P_N(Tmap u_N)=P_N(u_N).
If both have a uniform modulus on [-R_N,R_N],
then between grid points their difference is ≤ 2 · modulus(mesh).
```

For the current Rothe map, the image side has exactly the kind of uniform Lipschitz data you want: `RotheOrbitData.limitLip` gives a shared Lipschitz bound for `rotheLimit (rotheSeq u)`, and the compact-range proof uses that every image is uniformly `M`-Lipschitz and uniformly bounded. fileciteturn84file0L88-L98 fileciteturn85file0L61-L66

The extension side `E_N a_N` should also be constructed with the same uniform Lipschitz or at least uniform modulus. For monotone wave profiles, a piecewise-linear monotone interpolant on the grid is natural. The delicate part is preserving the upper barrier `u ≤ upperBarrier κ M`; if linear interpolation can overshoot the curved barrier, use a clipped extension such as:

```text
E_N a := min (upperBarrier κ M) (monotone interpolation of a)
```

and, if using a lower-pinned trap,

```text
E_N a := max φ (min upperBarrier interpolation)
```

provided the pins are compatible. The repo already has a lower-pinned refinement of the Schauder data; the lower-pinned trap is `InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x`, and the `lowerPinned` wrapper passes the lower pin through compact-range limits. fileciteturn99file0L145-L175 fileciteturn100file0L1-L30

### Where Helly enters

Helly should **not** be mixed into the finite Brouwer construction. It enters after you have the approximate fixed sequence.

The repo’s compact-range field is already shaped exactly this way:

```lean
def LocalUniformSequentiallyCompactRange trap Tmap : Prop :=
  ∀ seq, (∀ n, trap (seq n)) →
    ∃ subseq, StrictMono subseq ∧
      ∃ U, trap U ∧
        LocallyUniformConverges (fun n => Tmap (seq (subseq n))) U
```

fileciteturn104file0L155-L164

For the Rothe map, `Tmap_compactRange` proves this modulo the named `HellyPointwiseSelection M`: Helly extracts a pointwise subsequence from uniformly bounded, equi-Lipschitz image profiles, and the code upgrades it to local-uniform convergence by `locallyUniform_of_pointwise_of_equiLipschitz`. fileciteturn85file0L25-L54 The theorem then assembles trappedness of the limit from antitone, nonnegative, and upper-barrier preservation. fileciteturn85file0L67-L125

So the final infinite-dimensional flow is:

```text
finite Brouwer/Galerkin
  → u_N ∈ trap and Tmap u_N - u_N → 0 locally uniformly
  → LocalUniformApproxFixed Tmap u_N

Helly compact range
  → subseq Tmap u_Nj → U locally uniformly, U ∈ trap

approx-fixed residual
  → u_Nj → U locally uniformly too

local-uniform continuity
  → Tmap u_Nj → Tmap U

uniqueness of local-uniform limits
  → Tmap U = U
```

This is exactly the proof pattern in `exists_fixed_of_approx_fixed`: it extracts a compact-range subsequence for `Tmap seq`, uses the approximate-fixed residual to show the original `seq` has the same local-uniform limit, then applies `fixed_of_common_limit`. fileciteturn108file0L3-L41

---

## (3) Is this the cleanest Lean route?

Yes. Given Mathlib lacks a ready Schauder–Tychonoff theorem, the least-infrastructure path is:

```text
Sperner/Freudenthal finite combinatorics
  → finite-dimensional approximate Brouwer
  → finite-dimensional Galerkin approximate-fixed sequence
  → existing local-uniform compactness/continuity bridge.
```

A direct abstract Schauder–Tychonoff theorem would be preferable if Mathlib already had it. It would avoid all projection/interpolation work. But formalizing Schauder–Tychonoff from scratch is heavier than what you need: locally convex topology, compact convex subsets, finite-rank approximations or partitions of unity, and a general fixed-point theorem. For this project, that is too much infrastructure compared with the sequential bridge already present.

The repository’s own architecture confirms this division:

* `FrozenStationaryMapSchauderData` needs invariance, diagonal cross-fixed-point, local-uniform continuity, and local-uniform sequential compact range. fileciteturn99file0L46-L63
* `exists_self_frozen_stationary` then invokes `LocalUniformSchauderFixedPointPrinciple` and uses the resulting fixed point to obtain the self-frozen stationary profile. fileciteturn100file0L32-L60
* The concrete Rothe data already reduces compactness to `HellyPointwiseSelection` and continuity to `RotheContinuousDependence`; the missing global topological ingredient is the G1 fixed-point principle itself. fileciteturn84file0L22-L44

So close G1 by proving the approximate fixed sequence provider. Do not attempt a full general Schauder theorem unless you want a reusable Mathlib-scale project.

---

## Concrete implementation checklist

### A. Finish finite-dimensional Brouwer as reusable approximate theorem

Create a file such as:

```text
ShenWork/Paper1/BrouwerApprox.lean
```

Expose:

```lean
theorem finite_brouwer_simplex_approx
theorem finite_brouwer_cube_approx
```

or one compact-convex transport theorem if you already have the affine transport layer.

Inputs:

```lean
ContinuousOn T K
Set.MapsTo T K K
IsCompact K
Convex ℝ K
mesh triangulation with diameter δ_k → 0
Sperner-compatible label from T
```

Output:

```lean
∀ ε > 0, ∃ x ∈ K, dist (T x) x < ε
```

You can later derive exact finite Brouwer, but the approximate theorem is the one needed downstream.

### B. Define finite profile approximants

Create a Galerkin/mesh profile layer:

```lean
structure ProfileGridApprox (trap : (ℝ → ℝ) → Prop) where
  K : ℕ → Set (Fin (N n) → ℝ)
  E : ∀ n, K n → (ℝ → ℝ)
  P : ∀ n, (ℝ → ℝ) → K n
  E_mem_trap : ∀ n a, trap (E n a)
  finite_compact_convex : ...
  selfmap : ...
  continuous : ...
  exact_grid_to_local_approx :
    P n (Tmap (E n a)) = P n (E n a) →
    local residual on [-R,R] ≤ error n R
  error_tendsto : ∀ R, error n R → 0
```

Then:

```lean
finite_brouwer_cube
  (F_N := fun a => P_N (Tmap (E_N a)))
```

gives `a_N`, and `seq N := E_N a_N` gives `LocallyUniformApproxFixed`.

### C. Wrap into G1

Use the committed bridge:

```lean
theorem localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences
    (Happrox : ApproxFixedSequenceProvider trap) :
    LocalUniformSchauderFixedPointPrinciple trap := by
  intro Tmap hinv hcont hcompact
  rcases Happrox Tmap hinv hcont hcompact with ⟨seq, hseq, happrox⟩
  exact hcompact.exists_fixed_of_approx_fixed hcont hseq happrox
```

This is the exact downstream connection.

### D. For the wave trap, prefer lower-pinned if nontriviality matters

The bare trap admits the zero profile, and the repository has already proved that the strengthened nontrivial Schauder principle is false on the bare trap using the constant-zero map. fileciteturn99file0L65-L143 If the target fixed point must be nontrivial/positive, build the approximate-fixed sequence in a lower-pinned trap or otherwise carry a nontrivial fixed-point principle. The lower-pinned trap machinery is already present. fileciteturn99file0L145-L175

## Bottom line

The cleanest Lean-formalizable bridge is:

```text
1. Finish finite-dimensional continuous approximate Brouwer from the Freudenthal/Sperner theorem.
2. Use it on finite profile grids to produce `seq n ∈ trap` with `LocallyUniformApproxFixed Tmap seq`.
3. Apply `LocalUniformSequentiallyCompactRange.exists_fixed_of_approx_fixed`.
4. Use the existing Helly compact-range theorem only in step 3, not in finite Brouwer.
```

That route reuses the project’s committed local-uniform topology and Helly compactness, minimizes new topology, and keeps the remaining work in concrete finite-dimensional mesh/projection estimates rather than a general Schauder–Tychonoff formalization.
