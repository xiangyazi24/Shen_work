# Bounded-Domain API Design Proposal v3

## Executive Decision Point

This proposal supports two choices:

**A. Design-doc only.** Keep this as a written policy for future bounded-domain
work. Do not add Lean interfaces yet.

**B. First tiny Lean implementation.** Add only interval-measure helper
definitions plus one small theorem imported from Mathlib. Do not add Paper2
wrappers, semigroup estimate structures, or theorem names suggesting progress
on bounded-domain semigroup theory.

The recommended next step is A, or B if Xiang wants a concrete audit-passing
foothold.

## Audit Classification

### Existing `BoundedDomainData`

Classification: **not audit-passing as theorem source**.

Reason: fields such as `integral`, `supNorm`, `laplacian`, `normalDeriv`,
`chemotaxisDiv`, and `classicalRegularity` are arbitrary. If Paper2 Lemmas
2.1--2.4 or Paper3 conclusions are proved by calling those fields, fake
instances can invalidate the theorem interpretation.

Acceptable use:

- paper-aligned statement layer;
- obstruction-test target;
- documentation of intended analytic assumptions.

Not acceptable use:

- source of end-to-end theorem progress;
- source of any theorem name that suggests the analytic estimates are formalized.

### Conditional Bounded-Domain Theory

Classification: **conditional assumption layer only**.

This layer may record: “Assume the standard smooth bounded-domain Neumann heat
semigroup theory.” It must not be counted as theorem progress.

Allowed names:

```lean
Lemma_2_1_from_assumed_neumann_semigroup_estimates
global_existence_from_assumed_bounded_domain_theory
stability_from_assumed_neumann_heat_theory
```

Disallowed names in this track:

```lean
paper2_lemma_2_1_conditional
paper2_lemma_2_1_proved
bounded_domain_semigroup_estimates_proved
```

The first disallowed name is too close to the paper theorem and can later be
mistaken for progress. The latter two are false if they depend on assumptions.

### Concrete End-to-End Track

Classification: **audit-passing only when every analytic estimate is proved from
definitions and passes `#print axioms`**.

This track should start far below the full paper theorem: interval measure,
constants, and simple integral facts. Full Neumann semigroup positivity and
smoothing are later goals, not first-session targets.

## What This Changes Relative to `not_forall_*`

The existing `not_forall_*` obstruction theorems remain valid. They are not a
temporary nuisance; they are a design constraint.

This proposal does not replace one fakeable interface with another. Any new
end-to-end namespace must be narrow enough that its operations are definitions,
not arbitrary fields. For example:

- `intervalMeasure L := volume.restrict (Set.Icc 0 L)` is acceptable;
- `volume : ℝ` as a structure field is not;
- `intervalIntegralOf f := ∫ x in 0..L, f x` is acceptable;
- `integral : (X → ℝ) → ℝ` as a field is not;
- a proved Mathlib theorem about `volume (Set.Icc 0 L)` is acceptable;
- a field named `mass_preserving` is not end-to-end theorem progress.

The obstruction tests should continue to pass. If a proposed design makes the
obstructions irrelevant by hiding assumptions in a new structure, the design has
failed the audit.

## Conditional Track: Documentation-First Skeleton

If a Lean type is added at all, the geometric skeleton should contain only data
that is actually defined. It should not contain a smoothness proposition plus a
witness.

```lean
structure BoundedDomainSkeleton (N : ℕ) where
  hN : 0 < N
  Ω : Set (EuclideanSpace ℝ (Fin N))
  isOpen_Ω : IsOpen Ω
  isBounded_Ω : Bornology.IsBounded Ω
  nonempty_Ω : Ω.Nonempty
  connected_Ω : IsConnected Ω
```

Do not add:

```lean
boundarySmooth : Prop
boundarySmooth_witness : boundarySmooth
```

Smooth boundary, traces, outward normals, Neumann heat theory, elliptic
regularity, and semigroup estimates should be separate explicitly named
assumptions, preferably documentation-only until there is a concrete use.

If encoded in Lean, use names that cannot be confused with proved estimates:

```lean
-- Documentation/assumption namespace only.
structure AssumesSmoothBoundary (D : BoundedDomainSkeleton N) : Prop where
  -- Details intentionally not used as computational data.
  assumed : True

structure AssumesNeumannHeatTheory
    (D : BoundedDomainSkeleton N)
    (p : CM2Params) : Prop where
  -- This represents standard PDE theory not yet formalized.
  assumed_standard_theory : True
```

These assumptions are not useful as theorem content by themselves. They are only
labels for conditional statements. If this feels too easy to misuse, keep the
conditional track entirely in documentation and add no Lean declarations.

Module-level warning for any conditional file:

```lean
/-!
WARNING:
This file records conditional consequences from assumed smooth bounded-domain
Neumann PDE theory. The theorems here are not counted as formal theorem
progress on Paper2/Paper3 analytic estimates.
-/
```

## Spatial Functions and Measures

The domain must be present either in the type or in the measure.

Preferred for local PDE predicates:

```lean
abbrev DomainPoint (D : BoundedDomainSkeleton N) :=
  {x : EuclideanSpace ℝ (Fin N) // x ∈ D.Ω}

abbrev ScalarField (D : BoundedDomainSkeleton N) :=
  DomainPoint D → ℝ
```

Preferred for integration over ambient functions:

```lean
noncomputable def domainMeasure (D : BoundedDomainSkeleton N) :
    Measure (EuclideanSpace ℝ (Fin N)) :=
  volume.restrict D.Ω

noncomputable def domainIntegral
    (D : BoundedDomainSkeleton N)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ :=
  ∫ x, f x ∂ domainMeasure D
```

Do not add free fields:

```lean
volume : ℝ
integral : (Point → ℝ) → ℝ
supNorm : (Point → ℝ) → ℝ
laplacian : (Point → ℝ) → Point → ℝ
```

When a volume is needed, derive it:

```lean
noncomputable def domainVolume (D : BoundedDomainSkeleton N) : ℝ :=
  (domainMeasure D Set.univ).toReal
```

Finite and positive volume should be proved for concrete domains or assumed
under a clearly conditional name such as `AssumesFinitePositiveVolume D`.

## Parameter Alignment

Keep paper parameters in existing structures. In particular, `μ` belongs to
`CM2Params`; it should not appear as `ops.mu` or as a field of semigroup ops.

Sketches should use:

```lean
(p : CM2Params)
p.μ
p.ν
p.α
p.γ
```

not:

```lean
ops.mu
semigroup.mu
```

## Concrete End-to-End Target: Revised Sequence

The interval Neumann heat semigroup remains a plausible long-term target, but v2
overstated first-step feasibility. Positivity from a cosine expansion is not a
small first theorem because cosine coefficients can change sign. Positivity is
more naturally approached through a reflected heat kernel or a maximum principle.

### First Implementation Target

Define interval-measure helpers only:

```lean
namespace ShenWork.IntervalDomain

noncomputable def intervalSet (L : ℝ) : Set ℝ :=
  Set.Icc 0 L

noncomputable def intervalMeasure (L : ℝ) : Measure ℝ :=
  volume.restrict (intervalSet L)

noncomputable def intervalVolume (L : ℝ) : ℝ :=
  (intervalMeasure L Set.univ).toReal

end ShenWork.IntervalDomain
```

First theorem should be tiny and Mathlib-backed, for example:

```lean
theorem intervalVolume_eq
    {L : ℝ} (hL : 0 ≤ L) :
    intervalVolume L = L := ...
```

or an equivalent theorem about integrating the constant function over
`Set.Icc 0 L`, depending on the exact Mathlib lemmas available.

This theorem is not a Paper2 result. It is a concrete audit-passing helper.

### Second Implementation Target

After checking Mathlib support, define one of:

- an identity operator on interval fields and prove it preserves mass;
- a finite-mode Galerkin heat operator and prove constant-mode mass preservation;
- an exact reflected heat kernel, if the needed Gaussian integral facts are
  available.

Reasonable next theorem:

```lean
theorem finiteModeHeat_preserves_constant_mass
    {L : ℝ} (hL : 0 < L) :
    ...
```

Do not claim positivity or smoothing at this stage.

### Later Targets

Only later attempt:

- full interval Neumann heat kernel;
- positivity preservation;
- `L∞` contraction;
- `Lᵖ → Lᑫ` smoothing;
- Paper2-style semigroup lemmas specialized to the interval.

These should be marked as future work until proved from definitions.

## Naming Rules

Conditional assumption layer:

- Use `from_assumed_*`.
- Use module warning: “not counted as theorem progress”.
- Do not use names that match the paper lemma name too closely.
- Do not use `_proved`.

Concrete end-to-end layer:

- Use `_proved` only after the theorem is derived from definitions.
- Run `#print axioms` before accepting the name.
- Prefer narrow helper names first, e.g. `intervalVolume_eq`, not
  `boundedDomainTheory_proved`.

## Implementation Guardrail Checklist

Before adding or accepting any Lean declaration:

- No theorem named `_proved` may depend on conditional assumptions.
- No structure field may have the same type as a target theorem conclusion.
- No free `integral`, `supNorm`, `volume`, or `laplacian` fields in an
  end-to-end namespace.
- Every concrete theorem must get a `#print axioms` audit.
- Documentation must label every result as conditional or proved-from-definitions.
- Existing `not_forall_*` obstruction tests must remain meaningful.
- Paper2/Paper3 wrappers are forbidden until the concrete analytic helper
  theorems exist.

## Additive Migration Plan

### Round 1: Documentation

- Commit this proposal only.
- Keep `BoundedDomainData` unchanged.
- Add no Lean theorem wrappers.

### Round 2: Optional definitions-only file

- Add a new interval-domain helper file.
- Include definitions for interval set, restricted measure, and derived volume.
- Add at most one tiny Mathlib-backed theorem such as `intervalVolume_eq`.
- Run `#print axioms` for that theorem.

### Round 3: Optional finite-mode or kernel experiment

- Check Mathlib support before defining a heat operator.
- Start with mass preservation for constants or finite-mode projection.
- Keep positivity and smoothing as later targets unless a reflected kernel path
  is already available.

## Recommended Next PR/Commit

Preferred commit:

- Add only `.tmp/bounded-domain-proposal-v3.md`.

Alternative first Lean commit:

- Add a new file for interval measure helpers.
- Define interval restricted measure and derived volume.
- Prove one tiny theorem from Mathlib, such as interval volume or integral of a
  constant over `[0,L]`.
- Include `#print axioms` output in the commit message or PR description.

Do not include:

- Paper2 theorem wrappers;
- semigroup estimate assumption structures;
- theorem names suggesting bounded-domain semigroup estimates are done;
- any new arbitrary-field replacement for `BoundedDomainData`.

## Bottom Line

The honest conditional path is useful for documentation, but not theorem
progress. The audit-passing path should begin with tiny concrete interval
measure facts and only move toward heat semigroups after the required Mathlib
support is confirmed.
