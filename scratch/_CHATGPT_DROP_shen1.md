# Q2828 (shen1) — help

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Delivery target: `scratch/_CHATGPT_DROP_shen1.md`

## Purpose

This scratch file is the GitHub-delivered response target for Shen_work tasks. For a `git-drop`, I overwrite this file on `chatgpt-scratch` and report the resulting commit SHA.

## Standard prompt shape

```text
Q#### (shen1): <task title>

Repo: xiangyazi24/Shen_work on default branch main.
Current head/commit: <sha and short description>.

Do NOT touch or rely on Zinan-owned files:
- ShenWork/PDE/P3MoserHighExcursionProducer.lean
- ShenWork/PDE/P3MoserThresholdPlanProducer.lean

Task:
<what to audit, classify, prove-plan, or wire>

Please inspect:
- path/to/file1.lean
- path/to/file2.lean

Need:
1. exact declaration names;
2. proved vs conditional/frontier classification;
3. next Lean attack route;
4. code skeletons only if likely to typecheck.

IMPORTANT (git-drop): write the complete response into
`scratch/_CHATGPT_DROP_shen1.md` on branch `chatgpt-scratch`, overwrite it,
and report the commit SHA.
```

## Useful audit requests

```text
Q#### (shen1): audit current headline/frontier status.
Classify Paper1/Paper2/Paper3 wrappers as unconditional, conditional, or assumption aliases.
Rank remaining sorries by difficulty and dependency order.
Commit the answer via git-drop.
```

```text
Q#### (shen1): identify the next non-producer wrapper.
Avoid Zinan-owned producer files. Prefer Paper2/Paper3 statement assembly wrappers.
Give exact target file, structure names, theorem names, and whether the patch is pure wiring.
```

```text
Q#### (shen1): inspect direct 1D Moser/GN route.
List live sorries, dependencies, smallest missing lemmas, and the next compile-oriented lemma to attack.
```

## Default response contents

For Shen_work Lean tasks, I will normally include:

- a concise verdict;
- exact existing declaration names to grep;
- classification of wrappers as proved data, conditional frontier, or empty/assumption alias;
- stale-route warnings, especially for `χ₀ = 0` versus actual-linear `0 < χ₀` incompatibility;
- live `sorry` status when requested;
- prioritized Lean attack routes;
- small code skeletons only when they are likely to typecheck.

## Standing constraints I will respect

- Do not edit repository source unless explicitly asked.
- Do not touch or propose edits to Zinan-owned producer files when listed as off-limits.
- Do not suggest `sorry`, `admit`, or axioms as a solution path.
- Distinguish proved data from conditional wrappers/frontier packages.
- Avoid advertising aliases around assumptions as proved headline theorems.
- Deliver by a real GitHub commit, not a sandbox file.

## Minimal command

```text
Q#### (shen1): --help
```

This writes this help note to `scratch/_CHATGPT_DROP_shen1.md` and commits it.
