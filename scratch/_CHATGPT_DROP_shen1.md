# Q2748 (shen1) — help

Repo: `xiangyazi24/Shen_work`  
Branch for this drop: `chatgpt-scratch`  
Delivery target: `scratch/_CHATGPT_DROP_shen1.md`

## What this git-drop interface does

Use this when you want the answer committed into the repository instead of returned only in chat. I will write the complete response into:

```text
scratch/_CHATGPT_DROP_shen1.md
```

on branch:

```text
chatgpt-scratch
```

and report the resulting Git commit SHA.

## Recommended request format

```text
Q#### (shen1): <short title / task>

Repo: /Users/huangx/repos/Shen_work, Lean 4 / Mathlib 4.29.1.
Non-Zinan files only; do not propose edits to
ShenWork/PDE/P3MoserHighExcursionProducer.lean or
ShenWork/PDE/P3MoserThresholdPlanProducer.lean.

Current state:
<facts / theorem names / relevant definitions>

Task:
<what to audit, prove-plan, inspect, or patch-plan>

Please inspect/search if possible:
- path/to/file1.lean
- path/to/file2.lean

Need:
1. exact theorem names/signatures;
2. compile-plausible route or lemma statements;
3. likely troublesome conversions/API notes.

IMPORTANT (git-drop): write your COMPLETE response into
`scratch/_CHATGPT_DROP_shen1.md` on the `chatgpt-scratch` branch of
`xiangyazi24/Shen_work` via the GitHub connector — overwrite its contents.
```

## What to include for Lean audits

The most useful inputs are:

- exact target theorem/definition statement;
- current commit or branch to audit;
- files that must be inspected;
- files that must not be touched or relied on;
- whether you want a proof plan only, new lemma statements, or an actual patch plan;
- whether `sorry`/`admit`/axioms are forbidden;
- whether wrappers/frontiers are acceptable or you prefer proof-producing lemmas only.

## What I will return in the committed note

For a typical Lean-route audit, I will write:

- a short verdict;
- exact existing theorem names and signatures that can be composed;
- the smallest missing lemma statements, ordered by likely compile success;
- Lean-oriented proof skeletons when useful;
- conversion/API notes for `intervalDomain.integral`, `intervalDomainLift`, `gradNorm`, `rpow`, `ContDiffOn`, interval integrability, and endpoint/zero-extension behavior;
- a final recommended implementation order.

## Constraints I will respect

For the Shen_work tasks in this stream:

- I will not inspect, rely on, edit, or propose edits to:
  - `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
  - `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`
- I will not suggest axioms or `sorry` as a solution path.
- I will prefer thin proof-producing lemmas over residual wrappers unless the task asks for a statement-layer frontier.
- I will use the GitHub connector for the final delivery commit and will not fall back to sandbox files.

## Minimal command examples

```text
Q#### (shen1): audit theorem route from <new theorem> to <target theorem>.
Read files A/B/C. Need exact lemma names, missing lemmas, and compile-plausible skeletons.
Git-drop to scratch/_CHATGPT_DROP_shen1.md on chatgpt-scratch.
```

```text
Q#### (shen1): patch-plan only, no code edits. Determine smallest missing analytic lemma for <target>.
Do not touch Zinan files. Commit the report to scratch/_CHATGPT_DROP_shen1.md.
```

```text
Q#### (shen1): inspect current main at commit <sha>. Verify whether <theorem> can be proved from existing lemmas.
Return a Lean-oriented proof route and exact API names. Git-drop required.
```
