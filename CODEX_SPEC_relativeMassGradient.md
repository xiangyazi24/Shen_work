# Task: Discharge relativeMassGradient from existing Agmon infrastructure

## Context

The `relativeMassGradient` field of `IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals`
(IntervalDomainIntegratedMoserAssembly.lean:51) requires 4 sub-components:

```lean
relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧                          -- (A)
          (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (pExp + rho) eta Ceta T u) ∧                                 -- (B)
          (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) *
                (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧  -- (C)
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0     -- (D)
```

## Existing infrastructure

### Sub-component (B) — ALREADY PROVED

`intervalDomain_classicalSolutionPositiveInterpolation` at
`ShenWork/PDE/IntervalAgmonInterpolation.lean:872` produces
`LpMassGradientInterpolationEstimate` unconditionally for all classical solutions
with q > 1 and eps > 0. This is proved via Agmon inequality on [0,1].

The only subtlety: the existing theorem takes `q > 1` but the assembly needs
`pExp + rho` where `p0 ≤ pExp` and `rho > 0`. Need to check that `pExp + rho > 1`
is derivable from the bootstrap hypothesis.

### Sub-component (A) — cGrad positive

This is the coefficient in the chain rule: `∫ u^{p+ρ-2}|∇u|² ≤ cGrad(p) · ∫|∇(u^{p/2})|²`.
By the chain rule, `∇(u^{p/2}) = (p/2) u^{p/2-1} ∇u`, so
`|∇(u^{p/2})|² = (p/2)² u^{p-2} |∇u|²`.
Therefore `∫ u^{p+ρ-2}|∇u|² = ∫ u^ρ · u^{p-2}|∇u|² ≤ ‖u‖_∞^ρ · (4/p²) ∫|∇(u^{p/2})|²`.
So `cGrad(p) = (4/p²) · ‖u(t)‖_∞^ρ`.

But `‖u(t)‖_∞` may depend on t, and `cGrad` should be uniform. From the bootstrap
hypothesis, `u` is bounded before time T, giving a uniform bound.

### Sub-component (C) — gradient-to-mass chain rule bound

Same chain rule as above. Need the classical solution's positivity (`u > 0` on `(0,T)`)
to handle the power `u^{p/2-1}`.

### Sub-component (D) — MoserMassPowerToCurrentLpLowerOrder

Definition at `IntervalDomainEnergyStep.lean:2061`:
```lean
∀ p, p0 ≤ p → ∀ Cmass, ∃ Crel, 0 ≤ Crel ∧ ∀ t, 0 < t → t < T →
    Cmass * (D.integral (u t)) ^ (p + rho) ≤ Crel * D.integral (fun x => (u t x) ^ p)
```

This says: `Cmass · (∫u)^{p+ρ} ≤ Crel · ∫u^p`. By Jensen's inequality,
`(∫u/|Ω|)^p ≤ ∫u^p/|Ω|`, so `(∫u)^p ≤ |Ω|^{p-1} · ∫u^p`.
For the extra `ρ` power: `(∫u)^{p+ρ} = (∫u)^p · (∫u)^ρ ≤ |Ω|^{p-1}(∫u^p) · (∫u)^ρ`.
Since `u` is bounded (from `IsPaper2ClassicalSolution` → `u_bounded`),
`(∫u)^ρ ≤ (|Ω| · ‖u‖_∞)^ρ`. So `Crel = Cmass · |Ω|^{p-1} · (|Ω|·‖u‖_∞)^ρ`.

On `intervalDomain`, `|Ω| = 1`, simplifying to `(∫u)^p ≤ ∫u^p` and `(∫u)^ρ ≤ ‖u‖_∞^ρ`.

## Goal

Create `ShenWork/PDE/P3MoserRelativeMassGradientProducer.lean` that produces the
full `relativeMassGradient` from `IsPaper2ClassicalSolution`.

### Step 1: Read existing infrastructure

Read these files first:
1. `ShenWork/PDE/IntervalAgmonInterpolation.lean` — find `intervalDomain_classicalSolutionPositiveInterpolation` (line 872) and `IntervalDomainClassicalSolutionPositiveInterpolation` (line 532 of IntervalDomainTheorem11.lean)
2. `ShenWork/Paper2/IntervalDomainEnergyStep.lean:2061` — `MoserMassPowerToCurrentLpLowerOrder` definition
3. `ShenWork/Paper2/IntervalDomainEnergyStep.lean:2076` — `moser_relative_eps_absorption_of_mass_gradient_estimate`
4. `ShenWork/Paper3/IntervalDomainIntegratedMoserAssembly.lean:51` — the assembly field
5. `ShenWork/Paper2/Statements.lean:1137` — `LpMassGradientInterpolationEstimate` definition
6. Grep for `u_pos\|u_bounded\|u_nonneg\|gradNorm.*chain` to find positivity/chain-rule lemmas

### Step 2: Produce the full `relativeMassGradient`

Write a theorem:
```lean
theorem intervalDomain_relativeMassGradient_of_classical
    {p : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain p T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0) :
    ∃ cGrad : ℝ → ℝ,
      (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
      (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
        LpMassGradientInterpolationEstimate intervalDomain (pExp + rho) eta Ceta T u) ∧
      (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
          (u t x) ^ (pExp + rho - 2) *
            (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad pExp * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
      MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
```

### Step 3: For each sub-component

**(B)** Use `intervalDomain_classicalSolutionPositiveInterpolation` to get `LpMassGradientInterpolationEstimate`.
Need to show `pExp + rho > 1`. Check what `AbstractLpBootstrapHypothesis` gives about `p0` and `rho`.

**(A, C)** Chain rule bound. The core identity is:
`∇(u^{p/2}) = (p/2) u^{p/2-1} ∇u`
so `|∇(u^{p/2})|² = (p²/4) u^{p-2} |∇u|²`
and `u^{p+ρ-2} |∇u|² = u^ρ · u^{p-2}|∇u|² = u^ρ · (4/p²)|∇(u^{p/2})|²`
≤ sup_x(u(t,x))^ρ · (4/p²) ∫|∇(u^{p/2})|².

Use classical solution's `u_bounded` or `u_pos` + compactness.

Grep for existing chain-rule lemmas: `gradNorm_rpow`, `grad_power`, `chain_rule_grad`.

**(D)** Jensen + boundedness on [0,1].

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserRelativeMassGradientProducer.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Work only in /Users/huangx/repos/Shen_work/
- Use the existing `intervalDomain_classicalSolutionPositiveInterpolation` for sub-component (B)
- If chain-rule lemmas don't exist, prove them inline
- If any sub-component is genuinely blocked, deliver the others + precise stall report
