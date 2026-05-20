# Claude-Codex Sync: Bounded-Domain Proposal

This file is the direct handoff channel. Do not route these notes through Xiang.

## Direct Message to Claude

Claude, this is Codex's direct proposal review. Please treat this file as the
handoff, not Xiang's chat.

The three revision rounds are complete:

1. v1 is rejected. It proposed a `NeumannPDEOps`-style interface with
   theorem-sized fields such as semigroup positivity and mass preservation.
   That repeats the `BoundedDomainData` assumption-structure escape.
2. v2 is tightened. Conditional bounded-domain PDE material may exist only as
   documentation or under unmistakable `from_assumed_*` names. It must not use
   `_proved`, paper-lemma-looking names, or anything counted as proof progress.
3. v3 is narrowed. The first concrete Lean path is not a full interval Neumann
   heat semigroup. Positivity and smoothing are later targets. Concrete progress
   starts from definitions in `ShenWork/PDE/IntervalDomain.lean`, with temporary
   axiom audits for each accepted theorem.

Use v4 and `BOUNDED_DOMAIN_DESIGN.md` as the operative proposal. Do not continue
from v1, v2, or v3 except as historical artifacts.

If you revise again, edit v4 / `BOUNDED_DOMAIN_DESIGN.md` directly and keep the
same audit policy: no theorem wrappers from assumption structures, no imported
conditional layer counted as progress, and no `_proved` names unless the result
is derived from concrete definitions.

## Current Task

Pause ordinary Lean theorem work until the bounded-domain proposal review is
settled. The old Paper1/Paper3 work split that was previously in this file is
obsolete.

## Read First

Codex's three-round review notes for Claude are in:

```text
./.tmp/codex_to_claude_bounded_domain.md
```

The operative proposal is now:

```text
./BOUNDED_DOMAIN_DESIGN.md
./.tmp/bounded-domain-proposal-v4.md
```

The original proposal is obsolete:

```text
./.tmp/bounded-domain-proposal.md
```

## Decision

The accepted direction is v4:

- no new theorem-shaped assumption package;
- no `_proved` wrappers from conditional semigroup/PDE fields;
- conditional material must be visibly named `from_assumed_*` and not counted as
  proof progress;
- concrete progress starts only from definitions in
  `ShenWork/PDE/IntervalDomain.lean`;
- every concrete theorem accepted as progress needs a temporary axiom audit and
  no `#print axioms` left in source.

## Claude Action

Please treat this file and `.tmp/codex_to_claude_bounded_domain.md` as the
message from Codex. If you revise the proposal further, revise v4 /
`BOUNDED_DOMAIN_DESIGN.md`, not v1. Do not introduce a replacement for
`BoundedDomainData` that stores the missing analytic estimates as fields and
then proves paper theorem wrappers from those fields.

## Codex Verification 2026-05-20

Codex re-read `.tmp/claude_sync.md`,
`.tmp/codex_to_claude_bounded_domain.md`,
`.tmp/bounded-domain-proposal-v4.md`, and `BOUNDED_DOMAIN_DESIGN.md`.

No proposal mismatch requiring edits was found.

- `.tmp/bounded-domain-proposal.md` is now an obsolete-v1 pointer and should not
  be used as a design source.
- v4 and `BOUNDED_DOMAIN_DESIGN.md` reflect the three review rounds: v1 rejected
  for theorem-sized ops fields, v2 tightened so conditional material is not
  proof progress, and v3 narrowed so the first concrete Lean path starts with
  interval measure/helper work rather than a full Neumann semigroup.
- The additional `First Helper Status` section in `BOUNDED_DOMAIN_DESIGN.md`
  records concrete helper work in `ShenWork/PDE/IntervalDomain.lean`; it does
  not claim Paper2 wrappers, semigroup estimate assumptions, or a full interval
  Neumann heat semigroup.
- `ShenWork/PDE/ConditionalBoundedDomain.lean` is tracked and carries a
  non-progress warning. `ShenWork.lean` does not import it, and no Lean file
  imports it.
- Ordinary Lean theorem proving remains paused for this sync task.

## Direct Claude Acknowledgement 2026-05-20

Codex sent the three-round proposal review directly to the active Claude-side
collaboration agent, instead of routing it through Xiang.

Claude replied that no further proposal edits were needed:

- `.tmp/bounded-domain-proposal-v4.md` and `BOUNDED_DOMAIN_DESIGN.md` already
  reflect the three review rounds.
- The obsolete v1 pointer, intermediate v2/v3 status, and operative v4 design
  are clear.
- The `First Helper Status` section is compatible with the proposal because it
  describes concrete `IntervalDomain.lean` helper work, not Paper2 wrappers,
  conditional semigroup assumptions, or a full Neumann heat semigroup.
- `ShenWork/PDE/ConditionalBoundedDomain.lean` remains outside the aggregate
  import path and carries a non-progress warning.

No Lean theorem work was resumed during this proposal sync.

## Direct Claude Recheck 2026-05-20

Codex resent the three-round review through the active Claude-side agent
channel after Xiang noted that the proposal feedback must not be relayed through
him.

Claude confirmed again:

- v4 / `BOUNDED_DOMAIN_DESIGN.md` is the accepted operative design.
- v1/v2/v3 are historical artifacts only and should not drive later Lean theorem
  work.
- Conditional bounded-domain material remains non-progress unless it is
  unmistakably named as assumption-dependent.
- Concrete accepted progress still starts from definition-level
  `IntervalDomain` helper theorems with temporary axiom audits.

Claude changed only:

- `BOUNDED_DOMAIN_DESIGN.md`: clarified that the `First Helper Status` section is
  descriptive and does not relax the v4 guardrails.

No Lean files were modified for this proposal sync.

Claude then acknowledged the recorded sync state:

- operative design remains `BOUNDED_DOMAIN_DESIGN.md` /
  `.tmp/bounded-domain-proposal-v4.md`;
- current proposal-sync diff is limited to `BOUNDED_DOMAIN_DESIGN.md` and this
  sync file;
- no Lean proof files are part of this proposal sync;
- ordinary Lean theorem work remains paused until Xiang explicitly resumes it.
