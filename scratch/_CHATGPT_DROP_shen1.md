# Q2883 (shen1) — help

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Help

This scratch drop is for Lean 4 / Mathlib frontier audits in `xiangyazi24/Shen_work`, especially the Paper2/Paper3 PDE and Moser-window assembly layers.

A useful request usually includes:

```text
Q-number and tag, e.g. Q2884 (shen1)
Repo/branch or local path
Target file(s)
Current compiled declarations
Exact target theorem or residual to reduce
Constraints: no sorry/axioms, no producer files, etc.
Delivery requirement: git-drop path and branch
```

## Best request shapes

### 1. Ask for a no-sorry Lean theorem

```text
In ShenWork/PDE/P3MoserEnergyContinuity.lean, prove theorem X from declarations A/B/C.
Search names: ...
If exact proof is impossible, identify the missing lemma and give the thinnest residual.
```

Expected output: exact theorem statement, imports, namespace, proof skeleton or full proof, and a note about any name/orientation risks.

### 2. Ask for a frontier audit

```text
Audit the current next frontier around theorem X.
Do not edit producer files A/B.
Classify: already provable / needs residual / false API shape.
Give exact Lean interfaces to add.
```

Expected output: a short conclusion, dependency map, and suggested declarations.

### 3. Ask for residual design

```text
We have residual R1. Can it be reduced to more PDE-shaped residuals using theorem T?
Give exact bridge theorem(s), avoiding endpoint fakery.
```

Expected output: small `def`/`theorem` interfaces with no-sorry wiring code where possible.

## Current shen1 thread context

Recent work has focused on the chain:

```text
IntegratedMoserEnergyWindowFTC
  ← IntegratedMoserEnergyDerivativeWindowIntegrability
  ← initial-window + positive-start split
  ← IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability
  ← IntervalDomainLpWeightedTimeTermInitialWindowIntegrability
  ← IntervalDomainLpPDETermInitialWindowIntegrability
```

The key recurring endpoint rule is:

```text
Strict/positive-start windows are usually accessible from global classical regularity.
Initial windows over 0..b = Ioc 0 b require genuine near-zero time integrability.
Endpoint energy continuity does not imply derivative/PDE-term integrability.
```

## Useful Lean proof patterns

### Positive-start congruence over `0..b`

```lean
refine IntervalIntegrable.congr ?_ hKnown
intro s hs
rw [Set.uIoc_of_le hb.1] at hs
-- now `hs.1 : 0 < s`
```

### Use global classical at a positive time

```lean
have hTpos : 0 < s + 1 := by linarith
have hsol : IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
  hglobal.classical hTpos
-- then `s < s + 1` by `linarith`
```

### Convert continuity on `Icc a b` to interval integrability

```lean
apply ContinuousOn.intervalIntegrable
rwa [Set.uIcc_of_le hab]
```

### Dominated interval integral continuity pattern

```lean
refine intervalIntegral.continuousWithinAt_of_dominated_interval
  (bound := fun _ => B') ?h_meas ?h_bound intervalIntegrable_const ?h_cont
```

Use compact slab continuity to get `B'`, then supply measurability from slice continuity and continuity from the uncurried joint continuity.

## What not to claim

Do not claim:

```text
continuous energy at t=0 + strict derivative integrability ⇒ derivative integrability on 0..b
```

That is not a valid Mathlib/PDE step.  It needs an explicit near-zero integrability or absolute-continuity theorem.

Do not replace a missing time-integrability estimate with fixed-time spatial integrability.  Fixed-time spatial integrability does not integrate the scalar profile in time.

## Git-drop reminder

For requests with the usual delivery rule, the only successful delivery is a commit to:

```text
scratch/_CHATGPT_DROP_shen1.md
```

on branch:

```text
chatgpt-scratch
```

and the final chat response should report the commit SHA.
