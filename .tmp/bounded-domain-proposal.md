# Bounded-Domain API Design Proposal

## Goal

Replace the abstract `BoundedDomainData` structure with a concrete instantiation
that Lean can verify, enabling end-to-end proofs for Paper2 and Paper3.

## The Mathematical Setting

Papers 2 and 3 study the parabolic-elliptic chemotaxis system on a bounded
smooth domain Ω ⊂ ℝ^N with Neumann boundary conditions:

```
u_t = Δu - χ₀ ∇·(u^m/(1+v)^β ∇v) + au - bu^{1+α},   x ∈ Ω
0   = Δv - μv + νu^γ,                                   x ∈ Ω
∂u/∂n = ∂v/∂n = 0,                                      x ∈ ∂Ω
```

## Current Abstract Interface

`BoundedDomainData` has 15 fields: Point, inside, boundary, volume, supNorm,
infValue, integral, gradNorm, timeDeriv, laplacian, chemotaxisDiv,
crossDiffusionEnergyTerm, normalDeriv, initialAdmissible, classicalRegularity.

## What Mathlib Currently Provides

Mathlib has:
- `MeasureTheory.MeasureSpace` for measure/integral on general spaces
- `Analysis.InnerProductSpace` for L² theory
- `Topology.MetricSpace` for bounded domains as metric subsets of ℝ^N
- `Analysis.Calculus` for derivatives on ℝ^N
- `MeasureTheory.Integral.Bochner` for Bochner integration
- NO: Sobolev spaces W^{k,p}(Ω), Neumann Laplacian, elliptic regularity,
  analytic semigroup on bounded domains, trace operators

## Proposed Architecture: Three Layers

### Layer 1: Domain Data (minimal, concrete where possible)

```lean
structure ConcreteBoundedDomain where
  N : ℕ
  hN : 0 < N
  Ω : Set (EuclideanSpace ℝ (Fin N))
  hΩ_open : IsOpen Ω
  hΩ_bounded : Bornology.IsBounded Ω
  hΩ_connected : IsConnected Ω
  hΩ_nonempty : Ω.Nonempty
  volume : ℝ
  hvolume_pos : 0 < volume
```

This uses Mathlib's `EuclideanSpace` and `IsOpen`/`IsBounded`. No abstract fields.

### Layer 2: PDE Operations (axiomatized interface)

```lean
structure NeumannPDEOps (D : ConcreteBoundedDomain) where
  -- Integration
  integral : (EuclideanSpace ℝ (Fin D.N) → ℝ) → ℝ
  integral_nonneg : ∀ f, (∀ x ∈ D.Ω, 0 ≤ f x) → 0 ≤ integral f
  integral_const : ∀ c, integral (fun _ => c) = c * D.volume
  
  -- Norms
  supNorm : (EuclideanSpace ℝ (Fin D.N) → ℝ) → ℝ
  supNorm_nonneg : ∀ f, 0 ≤ supNorm f
  
  -- Neumann Laplacian
  neumannLaplacian : (EuclideanSpace ℝ (Fin D.N) → ℝ) → 
                     EuclideanSpace ℝ (Fin D.N) → ℝ
  
  -- Neumann semigroup e^{tA} where A = Δ with Neumann BC
  neumannSemigroup : ℝ → (EuclideanSpace ℝ (Fin D.N) → ℝ) → 
                     EuclideanSpace ℝ (Fin D.N) → ℝ
  semigroup_nonneg : ∀ t f, 0 < t → (∀ x, 0 ≤ f x) → 
                     ∀ x, 0 ≤ neumannSemigroup t f x
  semigroup_mass : ∀ t f, 0 < t → 
                   integral (neumannSemigroup t f) = integral f
```

### Layer 3: Semigroup Estimates (the actual Lemma 2.1-2.4)

```lean
structure NeumannSemigroupEstimates (D : ConcreteBoundedDomain) 
    (ops : NeumannPDEOps D) where
  -- Lemma 2.1: L^p → L^q smoothing
  lp_lq_bound : ∀ p q, 1 < p → p ≤ q → 
    ∃ C > 0, ∀ t > 0, ∀ f, 
      ops.supNorm (ops.neumannSemigroup t f) ≤ 
        C * t ^ (-(1/2 : ℝ) * ((1:ℝ)/p - (1:ℝ)/q)) * 
          Real.exp (-ops.mu * t) * ... -- L^p norm of f
  
  -- etc. for gradient, divergence estimates
```

## Key Design Decisions

### Q1: Should `ConcreteBoundedDomain` carry smooth boundary data?

**Option A**: Abstract boundary (current approach). Pro: simple. Con: can't prove
trace theorems or boundary regularity.

**Option B**: Smooth boundary via `ContDiff` charts. Pro: rigorous. Con: heavy
Mathlib differential geometry dependency.

**Recommendation**: Option A for now. Boundary smoothness is used implicitly
in the paper but never explicitly computed. The Neumann BC is enforced through
the semigroup, not through explicit trace operators.

### Q2: Should we instantiate a concrete domain?

**Option A**: Keep domain abstract, axiomatize PDE operations.

**Option B**: Fix Ω = ball or Ω = cube, prove everything concretely.

**Recommendation**: Option A. The paper's results hold for any smooth bounded
domain. Fixing a specific domain would be over-specialization and wouldn't
match the paper's generality. The abstract interface IS the paper's approach.

### Q3: How to handle the Neumann semigroup?

The Neumann semigroup is the hardest piece. Options:

**Option A**: Axiomatize as a structure field with properties (current approach).

**Option B**: Construct from the Neumann eigenfunction expansion.

**Option C**: Construct from the reflected heat kernel on half-spaces.

**Recommendation**: Option A with clearer field names and honest documentation.
The semigroup construction is a textbook result (e.g., Lunardi, "Analytic
Semigroups and Optimal Regularity") but formalizing it requires spectral
theory for the Neumann Laplacian which Mathlib doesn't have.

## Migration Path

### Phase 1: Refactor `BoundedDomainData` (1-2 sessions)
- Split into `ConcreteBoundedDomain` + `NeumannPDEOps`
- Make `Point = EuclideanSpace ℝ (Fin N)` concrete
- Keep operations axiomatized but with clearer names
- Update Paper2/Paper3 to use new types

### Phase 2: Prove basic domain properties (2-3 sessions)
- `ConcreteBoundedDomain.volume_pos`
- Integration properties from Mathlib's `MeasureSpace`
- Sup norm from Mathlib's `BoundedContinuousFunction`

### Phase 3: Instantiate semigroup estimates (long-term)
- Prove Neumann semigroup mass conservation from integration by parts
- Prove L^∞ bound from maximum principle
- Prove L^p → L^q smoothing (requires Young's inequality + kernel bounds)

### Phase 4: Connect to Paper2/Paper3 theorems (per-theorem)
- Each theorem gets an end-to-end version taking `ConcreteBoundedDomain`
- Semigroup estimates are either proved or explicitly axiomatized

## What This Achieves for the 11-Point Audit

- **Point 3**: `ConcreteBoundedDomain` is a legitimate mathematical object,
  not an escape hatch. `NeumannPDEOps` is an explicit interface with
  documented axioms.
- **Point 5**: Theorem inputs are `ConcreteBoundedDomain` + `NeumannPDEOps`,
  not Prop definitions.
- **Point 6**: End-to-end theorems take concrete domain data.
- **Point 7**: Interface is minimal — only the operations actually used.
- **Point 11**: Honest reporting — "conditional on Neumann semigroup
  estimates" (standard PDE results, not open problems).

## For Discussion with Codex

1. Should we split the refactor into Paper2 first, then Paper3?
   (Paper3 imports Paper2, so Paper2 must go first.)

2. Should `NeumannPDEOps` include the elliptic resolvent for v?
   (Paper2's v equation `0 = Δv - μv + νu^γ` needs this.)

3. How to handle the `classicalRegularity` field?
   (Currently abstract. Could be replaced with Sobolev/Hölder regularity
   predicates, but these need Mathlib extensions.)
