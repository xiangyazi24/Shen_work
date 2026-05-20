# Bounded-Domain API Design Proposal v2

Historical note: v2 is an intermediate draft superseded by
`.tmp/bounded-domain-proposal-v4.md` and `BOUNDED_DOMAIN_DESIGN.md`. The
conditional-track examples below must be read under the stricter v4 rule:
conditional bounded-domain material is documentation-only unless Xiang
explicitly asks for Lean declarations, and any such declarations must use
unmistakable `from_assumed_*` names, never `_proved` or paper-lemma-looking
wrapper names.

## Purpose

This proposal replaces the v1 plan with an audit-aware design. The main change is
to separate two different projects:

1. **Honest conditional track**: state Paper2/Paper3 bounded-domain results
   conditional on unformalized standard Neumann PDE/semigroup theorems.
   These results must not be counted as `_proved` or end-to-end.
2. **End-to-end track**: instantiate a concrete setting where the heat kernel or
   spectral theory can actually be constructed in Lean and estimates can be
   proved from existing Mathlib infrastructure. Only this track can produce
   audit-passing `_proved` theorems.

The current `BoundedDomainData` interface should be preserved until a new theorem
actually improves on it. The migration should be additive.

## Audit Classification

### Current `BoundedDomainData`

Classification: **fails proof-integrity audit as theorem source**.

Reason: fields such as `integral`, `supNorm`, `laplacian`, `normalDeriv`,
`chemotaxisDiv`, and `classicalRegularity` are arbitrary structure fields. If
Paper2 Lemmas 2.1--2.4 or Paper3 conclusions are proved by calling these fields,
the proof can be refuted by fake instances. Existing `not_forall_*` obstruction
theorems already demonstrate this risk.

Acceptable use: specification layer, paper-aligned statement layer, or conditional
API target.

Not acceptable: final theorem source for audit-passing `_proved` results.

### Conditional Neumann Interface

Classification: **honest conditional, not end-to-end**.

Reason: a documented interface for smooth bounded domains and Neumann semigroup
estimates can faithfully record the standard PDE theorem being assumed. But if
the estimates are fields of a structure, using them to prove Paper2 Lemmas 2.1--2.4
does not make those lemmas fully formalized.

Allowed theorem names must say this explicitly, e.g.
`Lemma_2_1_from_assumed_neumann_semigroup_estimates` or
`global_existence_from_assumed_bounded_domain_theory`. Avoid `_proved`, avoid
paper-lemma-looking names, and do not count these declarations as theorem
progress.

### Concrete End-to-End Model

Classification: **audit-passing target if estimates are proved from definitions**.

Candidate targets:

- interval `[0,L]` with Neumann heat kernel by cosine expansion;
- flat torus, using periodic heat kernel / Fourier series;
- whole line or cube with explicit heat kernel bounds, if the paper statement is
  specialized accordingly.

Only this track should produce `_proved` theorem names.

## Correct Mathematical Setting

Papers 2 and 3 work on a bounded smooth domain `Ω ⊂ ℝ^N` with Neumann boundary
conditions:

```text
u_t = Δu - χ₀ ∇·(u^m/(1+v)^β ∇v) + au - bu^{1+α},   x ∈ Ω
0   = Δv - μv + νu^γ,                                x ∈ Ω
∂u/∂n = ∂v/∂n = 0,                                   x ∈ ∂Ω
```

So an integrity-preserving bounded-domain API must include at least:

- a smooth bounded domain, not merely open/bounded/connected;
- a boundary and outward normal;
- a semantic Neumann condition, preferably via trace/normal derivative or via
  a Neumann Laplacian domain;
- integrals and norms derived from restricted Lebesgue measure, not arbitrary
  fields;
- PDE predicates local to `Ω`.

## Conditional Track: Corrected Type Sketch

This track is a clear assumption interface for standard PDE facts. It is useful
for organizing the paper, but it is not an end-to-end proof.

Do not encode a `boundarySmooth : Prop` field plus witness in theorem files.
That pattern is too easy to misuse as an assumption-structure escape. If a Lean
geometric skeleton is introduced later, it should contain only defined
geometric data; smooth boundary, trace, outward normal, and Neumann heat theory
should remain documentation-only or be encoded as exact analytic hypotheses in
a clearly conditional namespace.

Spatial functions should use one of the following two designs.

Preferred local-function design:

```lean
abbrev DomainPoint (D : SmoothBoundedDomain N) :=
  {x : EuclideanSpace ℝ (Fin N) // x ∈ D.Ω}

abbrev ScalarField (D : SmoothBoundedDomain N) :=
  DomainPoint D → ℝ
```

Alternative ambient-function design:

```lean
def domainMeasure (D : SmoothBoundedDomain N) :
    Measure (EuclideanSpace ℝ (Fin N)) :=
  volume.restrict D.Ω

def domainIntegral (D : SmoothBoundedDomain N)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ :=
  ∫ x, f x ∂ domainMeasure D
```

Do not make `volume : ℝ` a free field. It should be derived:

```lean
noncomputable def domainVolume (D : SmoothBoundedDomain N) : ℝ :=
  (domainMeasure D Set.univ).toReal

class HasFinitePositiveVolume (D : SmoothBoundedDomain N) : Prop where
  volume_ne_top : domainMeasure D Set.univ ≠ ∞
  volume_pos : 0 < domainVolume D
```

Parameter names must align with existing paper structures. In particular, `μ`
belongs to `CM2Params`, not to PDE ops:

```lean
structure ConditionalNeumannSemigroup
    (D : SmoothBoundedDomain N) where
  heat : ℝ → ScalarField D → ScalarField D
  mass_preserving :
    ∀ t f, 0 < t →
      integralOnSubtype D (heat t f) = integralOnSubtype D f
  positivity_preserving :
    ∀ t f, 0 < t → (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ heat t f x
```

Here `integralOnSubtype` is a proposed helper for integrating fields
`DomainPoint D → ℝ` against the measure induced by restricted Lebesgue measure
on `D.Ω`. The implementation should define this helper before adding the
semigroup interface.

Semigroup estimates should be assumptions explicitly named as such:

```lean
structure AssumedNeumannSemigroupEstimates
    (D : SmoothBoundedDomain N)
    (S : ConditionalNeumannSemigroup D)
    (p : CM2Params) : Prop where
  lp_lq_smoothing :
    -- Paper2 Lemma 2.1 style estimate, using p.μ where needed.
    Prop
  gradient_smoothing :
    -- Paper2 Lemma 2.2 style estimate.
    Prop
  divergence_smoothing :
    -- Paper2 Lemma 2.3/2.4 style estimate.
    Prop
```

If such assumptions are encoded, theorem names must be visibly
assumption-dependent:

```lean
theorem Lemma_2_1_from_assumed_neumann_semigroup_estimates
    (hS : AssumedNeumannSemigroupEstimates D S p) : ...
```

Do not use names like:

```lean
theorem paper2_lemma_2_1_conditional : ...
theorem paper2_lemma_2_1_proved : ...
```

The first looks too much like a paper theorem wrapper; the second falsely
suggests proof progress if the estimates are assumed.

## End-to-End Track: Concrete Next Target

Recommended next implementation target:

**Neumann heat semigroup on a closed interval `[0,L]`, with `0 < L`, via cosine
eigenfunction expansion or an equivalent already-supported kernel model.**

Reasons:

- the domain is concrete and non-fake;
- boundary points and Neumann condition are explicit;
- measure is restricted Lebesgue measure on `[0,L]`;
- eigenfunctions `cos (nπx/L)` have zero normal derivative at endpoints;
- the heat semigroup has an explicit formula, so positivity/mass/smoothing can
  in principle be proved rather than assumed;
- it gives an audit-passing laboratory before returning to arbitrary smooth
  bounded domains.

Initial target theorem should be modest:

```lean
theorem interval_neumann_heat_mass_preserving_proved
    {L : ℝ} (hL : 0 < L) :
    ...
```

Then add:

```lean
theorem interval_neumann_heat_positivity_proved
theorem interval_neumann_heat_L∞_bound_proved
theorem interval_neumann_heat_Lp_Lq_smoothing_conditional_or_proved
```

Only after these are proved from definitions should Paper2-style lemmas be
specialized to the interval and marked `_proved`.

## Additive Migration Plan

### Round 1: Design and audit labels

- Keep `BoundedDomainData` unchanged.
- Add this design document or a new namespace/file only.
- Add naming rules:
  - `from_assumed_*` for theorem chains using assumed PDE/semigroup estimates.
  - `*_proved` only for theorem chains whose analytic estimates are proved from
    concrete definitions.

### Round 2: Conditional namespace

- Introduce `SmoothBoundedDomain` and `AssumedNeumannSemigroupEstimates` in a new
  namespace/file.
- Do not refactor Paper2/Paper3 yet.
- Prove only wrapper lemmas that clearly preserve assumptions.
- Add comments that this track is not audit-passing end-to-end.

### Round 3: Concrete interval target and paper connection gate

- Define the interval domain and its restricted measure.
- Define or import the concrete Neumann heat semigroup.
- Prove mass preservation and positivity first.
- Only then attempt smoothing estimates.
- Add specialized Paper2/Paper3 theorem variants for the concrete interval model
  only after the needed estimates are proved from definitions.
- Compare those variants with the current abstract statements.
- Refactor the old `BoundedDomainData` layer only if the concrete theorem chain
  demonstrably replaces a fakeable assumption.

## No-Claim Boundaries

Do not claim:

- that an arbitrary-field interface is the paper's method;
- that conditional semigroup assumptions prove Paper2 Lemmas 2.1--2.4 end-to-end;
- that open/bounded/connected/nonempty is enough for a smooth Neumann PDE layer;
- that a free `volume : ℝ` has proof integrity;
- that replacing `Point` by `EuclideanSpace ℝ (Fin N)` alone makes `Ω` part of
  the theorem.

Allowed claim:

> The conditional interface records the standard bounded-domain Neumann
> semigroup theorem assumed from PDE theory. It is useful for organization, but
> it is not counted as an audit-passing formal proof until instantiated and
> proved in a concrete model.

## Immediate Recommendation

Do not refactor all of Paper2 first. The next concrete task should be:

1. Create a new interval/Neumann heat sandbox file.
2. Define interval measure from `volume.restrict`.
3. Prove the first audit-passing theorem: mass preservation or `L∞` contraction
   for the concrete heat semigroup.

This gives a real theorem that improves on the current abstraction without
breaking the existing obstruction tests or paper statement layer.
