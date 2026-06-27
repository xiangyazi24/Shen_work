# Q1223 / cron1 — help

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Usage

Send a prompt with a concrete Lean/Mathlib/project question, plus any relevant theorem name, file path, hypotheses, error message, and desired proof shape. I will inspect the repository through the GitHub connector, write the full answer into this scratch drop file, commit it on `chatgpt-scratch`, and report the commit SHA.

## Good request shapes

```text
Q#### (cron1): I need to prove <theorem> in <file>. Here are the local hypotheses and the failing goal/error. Please inspect <related files> and give a concrete Lean proof skeleton.
```

```text
Q#### (cron1): What is the Mathlib4 API for <operation>? Please search the pinned Mathlib source and give exact working Lean terms.
```

```text
Q#### (cron1): This proof has one remaining sorry at <file>:<line>. The intended route is <route>. Please identify existing repo lemmas and write the replacement proof body, using sorry only for genuinely missing infrastructure.
```

## What to include for fastest useful output

```text
- repository path and branch, if not the usual xiangyazi24/Shen_work / chatgpt-scratch
- exact file path
- theorem/lemma name
- local context/hypotheses
- exact goal
- exact Lean error message, if any
- related files or lemmas you suspect are relevant
- whether a proof may introduce helper lemmas
- whether hard analytic gaps may remain as named sorry sublemmas
```

## Output format I will use

The scratch file will usually contain:

```text
1. short diagnosis
2. relevant existing API/lemmas found
3. exact Lean code block(s)
4. notes on likely imports and namespace opens
5. named hard sublemmas if the current theorem statement lacks necessary hypotheses
6. implementation order / caveats
```

## Git-drop contract

For requests with the `git-drop` instruction, the accepted delivery is a real commit to:

```text
xiangyazi24/Shen_work
branch: chatgpt-scratch
file: scratch/_CHATGPT_DROP_cron1.md
```

No sandbox file or download link is a substitute for the commit.

## Common Lean help topics I can answer

```text
-- Mathlib API lookup
-- exact proof term for ContDiff/HasDerivAt/fderivWithin/deriv goals
-- converting HasDerivAt chains to ContDiffOn/ContDiffAt
-- ContinuousOn / IntervalIntegrable / cosineCoeffs parameter differentiation
-- importing and opening the right namespaces
-- isolating missing hypotheses versus true API gaps
-- writing proof skeletons with named hard sublemmas
-- identifying existing project infrastructure for a sorry
```

## Minimal command

```text
Q#### (cron1): <question>

IMPORTANT (git-drop): write your COMPLETE response into scratch/_CHATGPT_DROP_cron1.md on chatgpt-scratch via the GitHub connector, overwriting its contents. After committing, report the commit SHA.
```
