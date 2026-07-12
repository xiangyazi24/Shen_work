# CODEX_SPEC: Fix the coefficient gap — bypass unsatisfiable universal quantification

## Problem

The current `intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE` (in
`P3MoserIntegratedDissipationPDE.lean`) carries:

```lean
(hgap : ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A)
```

This is UNSATISFIABLE: for `A = 1/(2q)` we get `2 < q * 1/(2q) = 1/2`, which is false.

The root cause: `intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap`
(in `P3MoserIntegratedClosure.lean:1759`) wraps the REAL theorem
`higherPowerWindowCoeffFrontier_of_regularEnergy` (line 1641), which only needs the
SURPLUS form:

```lean
(hsurplus : ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
    ∃ eps, 0 < eps ∧ (p * K) * eps ≤ p * A - theta)
```

The surplus is satisfiable when A is SPECIFIC (from `LpBootstrapEnergyInequality`),
not universally quantified.

## Goal

Create `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` that replaces the
`hgap` with the CORRECT condition: for the specific A from the energy inequality,
`2 < q * A` holds.

## Strategy

The `LpBootstrapEnergyInequality` gives:
```
∀ pExp ≥ p0, ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L, [energy inequality]
```

The A comes from the cross-diffusion PDE coefficients. The correct gap condition is:
```
∀ pExp ≥ p0, let (A, B, K, L) = energy_inequality_constants(pExp);
    2 < pExp * A
```

This is: the energy inequality's gradient coefficient A, for each exponent pExp, satisfies
`pExp * A > 2`. This is a condition on the PDE parameters (dimension N, cross-diffusion
constants), NOT a universal statement about all positive A.

## Implementation

Option A (preferred): Write a new theorem that uses
`higherPowerWindowCoeffFrontier_of_regularEnergy` directly (line 1641), providing
the surplus from the SPECIFIC A in `LpBootstrapEnergyInequality`:

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    -- NEW: gap condition on the SPECIFIC A from the energy inequality
    (hgap_specific :
      ∀ pExp, p0 ≤ pExp →
        ∀ A K : ℝ, 0 < A → 0 < K →
          (∀ t, 0 < t → t < T →
            (1 / pExp) * deriv (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
              A * intervalDomain.integral (fun x => (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
              ... ≤ K * ... + ...) →
          (2 : ℝ) < pExp * A) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

This is complex. A simpler approach:

Option B: Directly supply the surplus:

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_surplus
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hsurplus :
      ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K →
        ∃ eps : ℝ, 0 < eps ∧ (q * K) * eps ≤ q * A - 2) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

This uses the surplus form directly. The surplus `∃ eps > 0, (q*K)*eps ≤ q*A - 2`
requires `q*A > 2`, which is satisfiable for SPECIFIC A > 2/q.

## Implementation details

1. Copy the proof of `intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE`
   but replace the call to `intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap`
   with a direct call to the underlying chain:
   - `intervalDomain_LpBootstrapEnergyInequality_of_regularity` → `LpBootstrapEnergyInequality`
   - `higherPowerWindowCoeffFrontier_of_regularEnergy` with `hsurplus` instead of `hgap`
   - `integratedMoserDissipationDropBefore_of_coeff_two` from the frontier

2. Also update P3MoserAssemblyFiller.lean to use the v2 theorem with `hsurplus` instead
   of the unsatisfiable `hGap`.

## Rules
- 0 sorry, 0 custom axiom, 0 native_decide
- #print axioms = [propext, Classical.choice, Quot.sound]
- Do NOT modify existing files except ShenWork.lean (import) and P3MoserAssemblyFiller.lean
- Verify with `lake env lean ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean`

## Verification
```bash
lake env lean ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean
# must show no errors
```
