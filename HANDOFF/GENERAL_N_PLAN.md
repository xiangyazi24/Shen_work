# General-N Architecture Plan (2026-07-17)

## Current State

The abstract statement layer `BoundedDomainData` (ShenWork/PDE/BoundedDomainData.lean)
already works for arbitrary dimension — it bundles Point, operators, and regularity
predicates without fixing N=1. All Paper2/Paper3 theorem statements are written in
terms of `BoundedDomainData D p`. The 1D proofs instantiate via `intervalDomain` and
`intervalDomainM` (ShenWork/PDE/IntervalDomain.lean:3011,3035).

## What General-N Requires

### Layer 1: Smooth Bounded Domain Type

A concrete `BoundedDomainData` instance for a smooth bounded domain Ω ⊂ ℝ^N with
Neumann boundary conditions. This needs:

- **Domain type**: `Ω : Set (EuclideanSpace ℝ (Fin N))` with `IsOpen Ω`, `IsBounded Ω`,
  smooth boundary ∂Ω (manifold with boundary).
- **Point**: `↥Ω` (subtype) or `↥(closure Ω)`.
- **Topology on Point**: inherited from `EuclideanSpace ℝ (Fin N)`, compact closure.
- **Volume**: `MeasureTheory.volume Ω` (Lebesgue measure of Ω).

**Mathlib status**: `EuclideanSpace`, `IsBounded`, `IsOpen` exist. `ManifoldWithBoundary`
exists (Mathlib.Geometry.Manifold.BoundaryManifold) but is at the category level, not
tied to concrete smooth subsets of ℝ^N. No "smooth bounded domain" API.

### Layer 2: Differential Operators

- **Laplacian**: `Δf = ∑_i ∂²f/∂x_i²`. Needs `iteratedFDeriv` on the subtype. Mathlib
  has `iteratedFDeriv` and `fderiv` for functions on normed spaces, but Neumann Laplacian
  on a bounded domain (self-adjoint extension) is not formalized.
- **Gradient norm**: `|∇f(x)| = ‖fderiv ℝ f x‖`. Available via `fderiv`.
- **Normal derivative**: `∂f/∂ν` on ∂Ω. Needs outward unit normal field on ∂Ω. Not in
  Mathlib.
- **Chemotaxis divergence**: `∇·(u^m ∇v)`. Needs `div(f · ∇g)` on a domain. Not in
  Mathlib as a bundled operation.

**Mathlib status**: `fderiv`, `iteratedFDeriv`, `divergence` exist for whole-space
functions. Boundary operators (normal derivative, trace) absent.

### Layer 3: Integration

- **Domain integral**: `∫ x in Ω, f x`. Mathlib has `∫ x in s, f x ∂μ` via
  `MeasureTheory.integral_indicator` — this works.
- **Integration by parts / Green's formula**: `∫_Ω Δf · g = -∫_Ω ∇f · ∇g + ∫_∂Ω (∂f/∂ν) g`.
  Not in Mathlib. This is load-bearing for the energy estimates.

### Layer 4: Neumann Semigroup / Eigenfunction Expansion

The 1D proofs rely heavily on the cosine-series Neumann heat kernel
(`intervalNeumannFullKernel`, `cosineCoeffs`, etc. in IntervalNeumannFullKernel.lean).
For general-N:

- **Neumann eigenvalues**: `0 = λ₀ < λ₁ ≤ λ₂ ≤ ...` with eigenfunctions `{φ_k}` forming
  an ONB of L²(Ω). Spectral theory for elliptic operators on bounded domains — entirely
  absent from Mathlib.
- **Heat semigroup**: `e^{tΔ} f = ∑_k e^{-λ_k t} ⟨f, φ_k⟩ φ_k`. Needs the spectral
  decomposition above.
- **Semigroup smoothing**: `‖e^{tΔ}f‖_{W^{k,p}} ≤ C t^{-α} ‖f‖_{L^q}`. This is the
  Henry-class infrastructure that's also the gap in Paper1 Thm 1.2.

**Mathlib status**: Spectral theory for compact self-adjoint operators exists
(Mathlib.Analysis.InnerProductSpace.Spectrum). Hilbert-Schmidt theory partially there.
But the connection to elliptic PDEs on bounded domains (Rellich compactness, trace
theorem, regularity) is absent.

### Layer 5: Maximum Principles & Regularity

- **Weak/strong maximum principle** for parabolic equations on bounded domains.
- **Moser iteration** (used for Prop 2.5 / L^p → L^∞ bound).
- **Schauder estimates** for parabolic regularity.

All absent from Mathlib. The 1D proofs use specialized interval-domain versions
(`IntervalDomainMoserActualAtoms.lean`, etc.) that exploit the 1D structure directly.

## Realistic Roadmap

### Phase 0 (already done)
Abstract `BoundedDomainData` structure + 1D instantiation. All theorem statements
are dimension-agnostic at the statement layer.

### Phase 1 (feasible, ~weeks)
Add topology, measure, and basic axioms to `BoundedDomainData`:
```lean
structure BoundedDomainData where
  ...
  hvolume_pos : 0 < volume
  hsupNorm_nonneg : ∀ f, 0 ≤ supNorm f
  hintegral_const : ∀ c, integral (fun _ => c) = volume * c
  hintegral_mono : ∀ f g, (∀ x ∈ inside, f x ≤ g x) → integral f ≤ integral g
  ...
```
These are algebraic axioms that all the 1D proofs already satisfy. Adding them lets
us prove theorem statements at the abstract level without fixing N=1.

### Phase 2 (feasible, ~months)
Concrete N-dimensional domain with volume, sup norm, integral — but operators still
bundled abstractly. Prove the "algebraic" theorems (mass conservation, comparison
principles, persistence lower bounds) at the abstract level.

### Phase 3 (research-grade, needs Mathlib growth)
Eigenfunction expansion and heat semigroup for general smooth bounded Neumann domains.
Requires: spectral theory for elliptic operators, trace theorem, Rellich compactness.
This is where the cosine-series 1D proofs need to be replaced by abstract spectral
methods.

### Phase 4 (research-grade, needs Mathlib growth)
Full PDE regularity: Schauder, Moser, Henry semigroup smoothing. Same gap as Paper1
Thm 1.2 avenue (a). Requires analytic semigroup / fractional power infrastructure.

## What Can Be Done Now

1. **Add axioms to `BoundedDomainData`** (Phase 1). The algebraic properties
   (volume positivity, integral monotonicity, sup norm properties) that all proofs
   currently discharge from the interval instantiation can be lifted to axioms.
   This is concrete, actionable, and lets some proofs be abstracted.

2. **Identify which theorems are already dimension-agnostic modulo axioms**.
   Many persistence/comparison results only use algebraic properties of the domain,
   not the cosine series or 1D structure. These can be proved abstractly once
   the axioms are added.

## Gap Summary

| Infrastructure | Mathlib Status | Shen_work 1D | General-N Difficulty |
|---|---|---|---|
| Domain type | Partial | intervalDomainPoint | C1 |
| Volume / integral | Good | ✓ | C1 |
| Gradient / Laplacian | Whole-space only | ✓ | C2 |
| Normal derivative | Absent | ✓ | C3 |
| Green's formula | Absent | ✓ | C3 |
| Neumann eigenvalues | Absent | cosineCoeffs | C3 |
| Heat semigroup | Absent | intervalFullSemigroupOperator | C3 |
| Semigroup smoothing | Absent | Henry tower | C3+ (= Paper1 gap) |
| Maximum principle | Absent | ✓ | C2 |
| Moser iteration | Absent | ✓ (MoserActualAtoms) | C3 |
| Schauder estimates | Absent | ✓ (Rothe) | C3 |
