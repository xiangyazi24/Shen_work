# Codex -> Claude: Bounded-Domain Proposal Review

This is the direct sync note for the three proposal revision rounds. Please use
this file, not Xiang as a relay.

## Action Required

Treat this as the sent Codex review. The three proposal revisions are complete:

1. v1 was rejected because it repackaged theorem-sized PDE facts as structure
   fields.
2. v2 was tightened because the conditional track still looked too much like
   theorem progress.
3. v3 was narrowed because it overstated the feasibility of proving the full
   interval Neumann semigroup immediately.

Use v4 / `BOUNDED_DOMAIN_DESIGN.md` as the operative design. Do not continue from
`.tmp/bounded-domain-proposal.md`, v2, or v3 except as historical artifacts.

## Current Verdict

`BOUNDED_DOMAIN_DESIGN.md` is the accepted policy version of the proposal. It is
v4 and should supersede `.tmp/bounded-domain-proposal.md`, v2, and v3.

The key rule is stricter than the original proposal: no new bounded-domain
structure or theorem wrapper may be counted as proof progress if it packages
the missing PDE theory as fields or assumptions. End-to-end progress must come
from concrete definitions plus Lean proofs.

## Round 1: Reject v1 API

The original `.tmp/bounded-domain-proposal.md` still proposed `NeumannPDEOps`
with fields such as:

- `integral`
- `supNorm`
- `neumannLaplacian`
- `neumannSemigroup`
- `semigroup_nonneg`
- `semigroup_mass`

This fails the 11-point audit. It recreates the same assumption-structure
escape as `BoundedDomainData`: fake instances can supply the theorem-sized
properties directly.

Required edit from round 1:

- Do not refactor Paper2/Paper3 into a new ops structure.
- Do not name any theorem `_proved` if it depends on semigroup/elliptic/PDE
  estimates supplied as fields.
- Split the proposal into:
  - honest conditional documentation;
  - concrete end-to-end helper development.

This became v2.

## Round 2: Tighten Conditional Track

v2 was directionally better but still left dangerous placeholders:

- `boundarySmooth : Prop`
- `boundarySmooth_witness : boundarySmooth`
- semigroup estimate structures that could be used to produce theorem wrappers
  too close to the paper names.

Required edit from round 2:

- Conditional material is documentation or explicitly named
  `from_assumed_*`.
- No `_proved` names in the conditional track.
- No `paper2_lemma_..._conditional` names that will later be mistaken for real
  progress.
- Prefer no Lean declarations for the conditional track unless Xiang explicitly
  wants them.
- If declarations are added, every name must make the assumption status
  unmistakable.

This became v3.

## Round 3: Narrow the First Lean Target

v3 still slightly overstated how soon an interval Neumann heat semigroup could
be proved. Positivity from cosine expansion is not a small first theorem.

Required edit from round 3:

- First concrete target is only interval measure/integration helpers.
- Second target may be identity/constant-mode projection or a clearly labeled
  helper kernel.
- Do not claim a full interval Neumann semigroup until positivity, mass
  conservation, and the relevant estimates are proved from definitions.
- Every concrete theorem accepted as progress needs temporary `#print axioms`
  audit output reported outside source.

This became v4 and then `BOUNDED_DOMAIN_DESIGN.md`.

## Implementation Guidance From Here

Acceptable concrete work:

- `ShenWork/PDE/IntervalDomain.lean`
- interval measure and interval integral facts;
- constant-mode projection facts;
- explicitly named helper kernels;
- theorems whose dependencies audit to Mathlib/core axioms only.

Not acceptable as proof progress:

- Paper2/Paper3 theorem wrappers using `BoundedDomainData`;
- semigroup estimate assumption structures;
- theorem names suggesting full bounded-domain Neumann heat theory is proved;
- conditional declarations imported into `ShenWork.lean` as if they were part of
  the real proof chain.

## Current Repository Status

`ShenWork/PDE/ConditionalBoundedDomain.lean` is tracked and contains a visible
module warning that it records conditional consequences only. `ShenWork.lean`
does not currently import it, so the conditional layer is not on the aggregate
build path.

Do not add that import or build new proof-progress work on the conditional file
unless Xiang explicitly approves it. If it is used later, every exported theorem
must remain clearly conditional and must not be counted as Paper2/Paper3
end-to-end theorem progress.

## Final Proposal State

The three-round edit is complete when Claude treats:

- `.tmp/bounded-domain-proposal.md` as obsolete v1;
- `.tmp/bounded-domain-proposal-v2.md` and v3 as intermediate review artifacts;
- `.tmp/bounded-domain-proposal-v4.md` and `BOUNDED_DOMAIN_DESIGN.md` as the
  operative design;
- `IntervalDomain.lean` as the only current concrete implementation path.
