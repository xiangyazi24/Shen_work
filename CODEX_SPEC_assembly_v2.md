# CODEX_SPEC: Update assembly filler to use v2 dissipation theorem

## Goal

Update `ShenWork/PDE/P3MoserAssemblyFiller.lean` to use the new v2 dissipation
theorem with `LpBootstrapEnergyInequalityWithGap` instead of the old
unsatisfiable universal gap condition.

## What changed

The old `hGap` hypothesis in the assembly filler was:
```lean
(hGap :
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T rho p0 →
      ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A)
```

This is UNSATISFIABLE. The new v2 theorem
(`intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2` in
`P3MoserIntegratedDissipationPDEv2.lean`) replaces this with:
```lean
(hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
```

## Steps

1. Read `ShenWork/PDE/P3MoserAssemblyFiller.lean` (current file, 151 lines)
2. Read `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` (the v2 theorem)
3. Make these changes to `P3MoserAssemblyFiller.lean`:

### Change 1: Add import
Add `import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2` at the top.

### Change 2: Replace hGap hypothesis
Replace the `hGap` hypothesis (lines 64-70) with:
```lean
(hGap :
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T rho p0 →
      LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
```

### Change 3: Update the proof
In `integratedMoserDissipationCore` (around line 113-134), change the call from:
```lean
exact
  _root_.ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDE.intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE
      hsol hcross hboot
      (hFTC hsol hcross hboot)
      hrel
      (hClassicalRegularity hsol hcross hboot)
      (hGap hsol hcross hboot)
```
to:
```lean
exact
  _root_.ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2.intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
      hsol hcross hboot
      (hFTC hsol hcross hboot)
      hrel
      (hClassicalRegularity hsol hcross hboot)
      (hGap hsol hcross hboot)
```

### Change 4: Open the v2 namespace
Add `open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2` to
the namespace opens (after line 14 area).

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserAssemblyFiller.lean
# must show no errors
# #print axioms must show [propext, Classical.choice, Quot.sound]
```

## Rules
- 0 sorry, 0 custom axiom, 0 native_decide
- Only modify P3MoserAssemblyFiller.lean
- Do NOT modify any other files
