# Q2390 shen1 — help

Repo: `xiangyazi24/Shen_work`

Invocation: `Q2390 (shen1): --help`

This is a help/usage response only.  No new Lean audit, proof search, or repository build was requested by the command body, so this drop does not claim any new theorem frontier or patch beyond documenting the `shen1` workflow.

## Usage

```text
QNNNN (shen1): <task>

----
IMPORTANT (git-drop): write your COMPLETE response into
scratch/_CHATGPT_DROP_shen1.md on the chatgpt-scratch branch of
xiangyazi24/Shen_work via the GitHub connector.
```

Use `shen1` when the desired output is a **repository-grounded Lean/statement-assembly audit** for the Shen_work project, delivered as a committed markdown drop rather than as an inline chat answer.

A good `shen1` task usually specifies:

1. The repository and branch/commit to audit.
2. The paper/file family, for example `Paper1`, `Paper2`, `Paper3`, or a specific `StatementAssembly` file.
3. The exact theorem wrappers, structures, or residual atoms under consideration.
4. Forbidden shortcuts, for example axioms, `sorry`, refuted routes, stale global interpolation statements, or legacy GN/Moser shortcuts.
5. The preferred kind of answer: exact names, import graph, cycle risks, theorem DAG, buildable Lean skeleton, or no-go frontier explanation.

## Typical request shapes

### Residual/frontier audit

```text
QNNNN (shen1): Repo xiangyazi24/Shen_work main at <commit>.
Audit <paper/file/theorem family>. Identify the next smallest honest residual/frontier input
that can be reduced by existing proved code, without using axioms, sorry, or refuted routes.
Prefer a buildable Lean patch outline with exact names. If no small patch exists, explain
which remaining inputs are genuine analytic frontiers.
```

Expected answer:

- current checked route summary;
- exact existing theorem/structure names;
- smallest honest reducible input, if one exists;
- Lean placement and imports;
- skeleton code with namespaces and all imports;
- explicit warning about false or cyclic routes;
- clear statement of any genuine analytic frontier.

### Statement assembly wiring question

```text
QNNNN (shen1): Repo xiangyazi24/Shen_work, branch <branch>.
I want to wire <new frontier/provider> into <StatementAssembly wrapper>.
Audit exact minimal Lean wiring. Should it live in a new file or directly in the assembly file?
Return exact imports/namespaces and conversion code skeleton. Warn about cycles.
```

Expected answer:

- recommended file location;
- import direction and cycle analysis;
- exact structure/field names;
- conversion theorem or `.to...` function skeleton;
- downstream wrappers that should remain unchanged;
- routes that must not be used.

### Full-statement wrapper audit

```text
QNNNN (shen1): Repo xiangyazi24/Shen_work main at <commit>.
Audit whether <full statement wrapper> can be assembled from <preferred atom route> plus
existing auxiliary producers. If not, identify the missing side-inputs and classify them as
statement-level plumbing versus real analytic frontiers.
```

Expected answer:

- yes/no answer first;
- exact blockers;
- distinction between wrapper bookkeeping and analytic content;
- patch outline only for the buildable part;
- no claim that an unproved analytic side condition is already discharged.

## Output contract

For git-drop prompts, the complete answer should be committed to:

```text
scratch/_CHATGPT_DROP_shen1.md
```

on:

```text
chatgpt-scratch
```

in:

```text
xiangyazi24/Shen_work
```

The chat reply after a successful drop should report only the essential delivery result:

```text
Committed to xiangyazi24/Shen_work on chatgpt-scratch: <commit-sha>
```

If the GitHub connector is unavailable or read-only, the correct failure response is:

```text
GIT-DROP FAILED: connector unavailable
```

A sandbox file, `/mnt/data` artifact, or inline-only answer is not a valid delivery for these prompts.

## Standards for a valid `shen1` audit

A valid audit should be conservative and repository-grounded.

It should:

- name exact Lean declarations rather than paraphrasing broad mathematical ideas;
- distinguish existing proved code from proposed new assumptions;
- explain why a patch is buildable, or why it is not;
- flag import cycles before suggesting file placement;
- avoid strengthening claims silently;
- preserve theorem statement shapes expected by downstream wrappers when possible;
- state when a remaining input is a genuine analytic frontier rather than Lean plumbing.

It should not:

- use `axiom`, `sorry`, or unsound placeholder interfaces as if they were reductions;
- route through known-refuted global interpolation statements;
- route through legacy GN/Moser shortcuts that the repo has already marked as false or obsolete;
- claim that a statement-level wrapper proves a PDE estimate;
- invent Lean names not present in the repository without labeling them as proposed names;
- recommend a broad refactor when a one-wrapper conversion suffices.

## Common no-go warnings in recent Shen_work audits

These names have repeatedly appeared as routes that must not be treated as valid proof sources unless the user explicitly asks for historical/diagnostic discussion:

```lean
-- false/obsolete global interval interpolation route
ShenWork.Paper2.IntervalDomainLemma41.IntervalDomainInterpolation

-- diagnostic counterexample family for interval interpolation
ShenWork.Paper2.IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation

-- false legacy GN/Young-for-Moser route
ShenWork.Paper2.IntervalDomainMCL.OldUnitIntervalPowerGNYoungForMoser
ShenWork.Paper2.IntervalDomainGNYObstruction.not_oldUnitIntervalPowerGNYoungForMoser
```

For Moser dissipation audits, also be careful not to claim that a generic energy inequality automatically implies the current physical-`B` pointwise dissipation atom.  Recent audits treated the nonnegative-`B` drop as a real atom unless an existing file contains a proved conversion with the exact required hypotheses.

## Minimal Lean skeleton style

When a task asks for code, use complete import blocks and keep proposed names clearly separated from existing names.

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-- Proposed wrapper name; this is new unless already present in the audited commit. -/
structure ProposedFrontierData (p : CM2Params) : Prop where
  -- fields go here, using exact existing target declaration names

/-- Proposed conversion into an existing frontier shape. -/
def ProposedFrontierData.toExistingFrontierData
    {p : CM2Params}
    (h : ProposedFrontierData p) :
    ExistingFrontierData p := by
  -- skeleton only; fill with exact existing declarations from the audit
  sorry

end

end ShenWork.Paper2
```

If the task forbids `sorry`, the code block should be labeled as a skeleton unless all proof terms are actually known from the repository.  Do not present a skeleton as build-verified code.

## Recommended answer order

1. One-sentence verdict.
2. Current route and exact declarations involved.
3. Smallest honest reduction, or explanation that none exists.
4. Buildable patch outline with imports/namespaces.
5. Cycle and no-go warnings.
6. Remaining analytic frontiers.

## Prompt template

```text
QNNNN (shen1): Repo xiangyazi24/Shen_work <branch> at <commit>.
Read <files>. Audit <theorem/wrapper/frontier>.
Question: <precise question>.
Constraints: no axioms, no sorry, no refuted <route>, no obsolete <route>.
Prefer exact Lean names and a buildable patch outline. If no small patch exists,
explain the genuine frontier.

----
IMPORTANT (git-drop): write your COMPLETE response into scratch/_CHATGPT_DROP_shen1.md
on the chatgpt-scratch branch of xiangyazi24/Shen_work via the GitHub connector —
UPDATE the existing file, overwriting its contents. After committing, report the commit SHA.
```
