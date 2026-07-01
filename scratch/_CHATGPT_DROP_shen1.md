# Q2771 (shen1) — help

Repo: `xiangyazi24/Shen_work`  
Branch for this drop: `chatgpt-scratch`  
Delivery target: `scratch/_CHATGPT_DROP_shen1.md`

## Purpose

This file is the GitHub-delivered scratch response target for Shen_work tasks. When you ask for a `git-drop`, I overwrite this file on the `chatgpt-scratch` branch and report the resulting commit SHA.

## Recommended prompt shape

```text
Q#### (shen1): <task title>

Repo: /Users/huangx/repos/Shen_work, Lean 4 Shen_work.
Current branch/main commit: <sha or branch state>.

Off-limits files:
- ShenWork/PDE/P3MoserHighExcursionProducer.lean
- ShenWork/PDE/P3MoserThresholdPlanProducer.lean

Relevant current interfaces:
1. <file> defines <names>
2. <file> defines <names>

Task:
<ask for an audit, proof route, safest next edit, exact Lean lemma statements, etc.>

Need:
1. exact recommendation;
2. exact theorem/interface names;
3. compile-plausible Lean code sketches if useful;
4. import-cycle / ownership risk analysis.

IMPORTANT (git-drop): write the complete response into
`scratch/_CHATGPT_DROP_shen1.md` on branch `chatgpt-scratch` of
`xiangyazi24/Shen_work`, overwriting it, and report the commit SHA.
```

## What to include for Lean route audits

Most helpful inputs:

- the exact theorem or residual package you want to close;
- commit SHA(s) currently on `main`;
- files to inspect;
- files that must not be touched or relied on;
- whether you want a proof-producing route, a wrapper route, or a no-edit audit;
- whether theorem consumers are stable or owned by another worker;
- whether import-cycle risk should be prioritized over residual reduction.

## What I will put in the committed response

For Shen_work Lean tasks, I will normally include:

- a concise verdict;
- the safest next edit or proof route;
- exact existing theorem and structure names;
- exact proposed lemma statements, ordered by likely compile success;
- import-cycle and ownership notes;
- likely Lean API names and conversion pain points;
- code snippets only when they are close to compiling.

## Default constraints I will respect

- Do not edit or propose edits to Zinan-owned files when listed as off-limits.
- Do not suggest `sorry`, `admit`, or axioms as a solution path.
- Prefer thin proof-producing lemmas over residual wrappers unless the task explicitly asks for statement-layer packaging.
- Avoid depending on moving worker-owned producer files unless the user explicitly says that dependency is stable.
- Deliver by a real GitHub commit, not by sandbox or local files.

## Common request examples

```text
Q#### (shen1): audit the shortest route from theorem A to target B.
Read files X/Y/Z. Give exact missing lemmas and compile-plausible skeletons.
Git-drop required.
```

```text
Q#### (shen1): choose safest next non-Zinan edit.
Options A/B/C. Prioritize no import cycle and no reliance on moving worker files.
Commit the recommendation to scratch/_CHATGPT_DROP_shen1.md.
```

```text
Q#### (shen1): inspect current main at commit <sha>.
Can existing lemmas prove <target>? If not, identify smallest analytic lemma.
Git-drop required.
```

## Minimal answer-only command

```text
Q#### (shen1): --help
```

This writes the help note you are reading now and commits it to `chatgpt-scratch`.
