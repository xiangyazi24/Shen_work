# CODEX_SPEC: Produce LpBootstrapEnergyInequalityWithGap from classical PDE data

## Goal

Write a new file `ShenWork/PDE/P3MoserGapProducer.lean` that produces
`LpBootstrapEnergyInequalityWithGap` from `(hsol, hcross, hboot)`.

## Mathematical background

`LpBootstrapEnergyInequalityWithGap` (in `P3MoserIntegratedDissipationPDEv2.lean:30`) is:
```lean
def LpBootstrapEnergyInequalityWithGap
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      (∀ t, 0 < t → t < T →
        (1 / pExp) * deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A * D.integral (fun x => (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L) ∧
      (2 : ℝ) < pExp * A
```

The existing `intervalDomain_LpBootstrapEnergyInequality_of_regularity` 
(in `IntervalDomainLpBootstrapEnergyInequality.lean:407`) produces the energy inequality
WITHOUT the gap. It uses:
- `cGrad = (pExp / 2) ^ 2` (the Moser gradient chain-rule constant)
- `Acoef = (A0 - chiBound * eps) / cGrad`
- where `A0 = pExp - 1`

The problem: `pExp * Acoef → 2` as `pExp → ∞`, so `2 < pExp * Acoef` fails for large p.

## Fix strategy: use the H-term directly instead of converting through cGrad

The energy inequality in the existing proof is (line 548-551):
```
Y + (A0 - chiBound * eps) * G + E ≤ (chiBound * Ccross + Klow) * Z + Llow
```
where G is the WEIGHTED gradient dissipation (u^{p-2} |∇u|²) and H is the MOSER
gradient (|∇(u^{p/2})|²). The conversion G → H introduces the factor 1/cGrad = 4/p².

Instead, keep the inequality in terms of G directly. The coefficient on G is:
```
A0 - chiBound * eps = (pExp - 1)(1 - |χ₀|(pExp-1)/(2(|χ₀|(pExp-1)+1)))
                    ≥ (pExp - 1)/2   for all pExp ≥ 1
```

Then `pExp * (A0 - chiBound * eps) ≥ pExp * (pExp - 1)/2 > 2` for `pExp ≥ 2`.

BUT: `LpBootstrapEnergyInequalityWithGap` uses H (the Moser gradient
`|∇(u^{p/2})|²`), not G (the weighted gradient `u^{p-2}|∇u|²`). So the conversion
through cGrad is mandatory for the EXISTING formulation.

## Alternative: directly produce the WithGap version

The key insight: `H ≤ cGrad * G` (where `cGrad = (p/2)²`), so:
```
(A0 - chiBound*eps) * G ≥ (A0 - chiBound*eps) / cGrad * H = Acoef * H
```
This is the EXISTING conversion. But we can use a DIFFERENT split of the
gradient absorption:

Split `(A0 - chiBound*eps) * G` into TWO parts:
- Part 1: `Acoef' * H` where `Acoef' = (A0 - chiBound*eps) / cGrad` (same as before)
- Part 2: keep some residual `(A0 - chiBound*eps) * G - Acoef * H ≥ 0` on the left

This doesn't help because we're already tight.

## CORRECT approach: reformulate the energy inequality with a DIFFERENT A

Since the gap condition `2 < p * A` is used only by the dissipation integral,
and the integral `∫₀ᵀ A * H` with `A = Acoef` gives `∫₀ᵀ (A0-chi*eps)/cGrad * H`,
the integrated version accumulates `A * ∫H ≥ A * ∫G/cGrad`.

Actually — read the CONSUMER of the gap. In `P3MoserIntegratedDissipationPDEv2.lean`,
the gap is used by `surplus_of_energyWithGap` (line 59) to produce:
```
∃ eps > 0, (pExp * K) * eps ≤ pExp * A - 2
```

This surplus is then used by `higherPowerWindowCoeffFrontier_of_energyWithGap` to
absorb the higher-power term. The surplus only needs to be positive — ANY A with
`2 < pExp * A` works, even `A = 2/pExp + ε` for tiny ε.

## What to do

Read these files carefully first:
1. `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean` — the existing energy inequality proof (lines 407-590)
2. `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` — the consumer (LpBootstrapEnergyInequalityWithGap definition at line 30, and the surplus theorem at line 59)

Then write `ShenWork/PDE/P3MoserGapProducer.lean` with a theorem:

```lean
theorem intervalDomain_lpBootstrapEnergyInequalityWithGap_of_regularity
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0
```

The approach:
1. Start from the existing proof structure of `intervalDomain_LpBootstrapEnergyInequality_of_regularity`
2. Choose A to satisfy `2 < pExp * A` while still having the energy inequality hold
3. The key trade-off: making A larger means the gradient absorption is weaker, which means more goes to the K*Z+L right-hand side. This is fine — K and L can grow.
4. One approach: set `A_gap = 3/pExp` (so `pExp * A_gap = 3 > 2`). Then allocate `Acoef - A_gap` to the coefficient of H that gets absorbed into the RHS (if `Acoef > A_gap`, use `A_gap` as the claimed A; if `Acoef ≤ A_gap`, the entire H term goes to the RHS with a positive coefficient, and we need A_gap = 0... this doesn't work.)

Actually: the simplest approach is to NOT convert G → H at all. Define a VARIANT of WithGap that uses G (the weighted gradient) instead of H (the Moser gradient). The gap on G is `2 < pExp * (A0 - chiBound*eps)`, and since `A0 - chiBound*eps ≥ (pExp-1)/2`, we get `pExp * A_G ≥ pExp*(pExp-1)/2 > 2` for `pExp ≥ 2`.

But the consumer expects H, not G. So we'd need to change the consumer too.

## SIMPLEST CORRECT approach

Use the EXISTING `LpBootstrapEnergyInequality` and note that the coefficient A in
the existing proof is:
```
Acoef = (pExp - 1 - |χ₀|*(pExp-1)*eps_val) / ((pExp/2)²)
```
where eps_val is chosen to absorb the cross-diffusion term.

Compute `pExp * Acoef`:
```
pExp * Acoef = pExp * (pExp-1) * (1 - |χ₀|*(pExp-1)/(2*(|χ₀|*(pExp-1)+1))) / ((pExp/2)²)
             = 4 * (pExp-1)/pExp * (1 - |χ₀|*(pExp-1)/(2*(|χ₀|*(pExp-1)+1)))
```

For `pExp ≥ p0 > max(1, ρN/2)`, let's check if `pExp * Acoef > 2`:
- As `pExp → ∞`: `4 * 1 * (1 - 1/2) = 2`. So the limit IS 2.
- For FINITE pExp: `4*(p-1)/p < 4` and `(1 - ...) < 1`, so `pExp * Acoef < 4`.
- The product `4*(p-1)/p * (1 - |χ₀|(p-1)/(2(|χ₀|(p-1)+1)))` is NOT always > 2.

So the gap FAILS with the current coefficient. A different coefficient split is needed.

## RECOMMENDED approach: use a smaller epsilon in the Young absorption

In the existing proof, `eps = A0/(2*(chiBound+1))` absorbs HALF of A0 to the
cross-diffusion term. If we use a SMALLER epsilon:
```
eps_new = A0/(C*(chiBound+1))
```
with C > 2, then:
```
A0 - chiBound * eps_new = A0 * (1 - chiBound/(C*(chiBound+1)))
                        ≥ A0 * (1 - 1/C)
                        = A0 * (C-1)/C
```
Acoef_new = A0*(C-1)/C / cGrad = (pExp-1)*(C-1)/C / ((pExp/2)²)
pExp * Acoef_new = 4*(pExp-1)*(C-1)/(C*pExp)

For this to exceed 2: `4*(p-1)*(C-1)/(C*p) > 2`, i.e., `2*(p-1)*(C-1) > C*p`,
i.e., `C*(2p-2-p) > 2(p-1)`, i.e., `C*(p-2) > 2(p-1)`, i.e., `C > 2(p-1)/(p-2)`.

As `p → ∞`, this requires `C > 2`. As `p → 2+`, `C → ∞`. So for `p ≥ 4`,
`C > 2*3/2 = 3` works. For `p ≥ 3`, `C > 4` works.

So the fix is: choose C large enough depending on p0. Since p0 > 1, we need
`C > 2(p0-1)/(p0-2)`. For the assembly to work, we need `p0 > 2` (which is
guaranteed by `p0 > max(1, ρN/2)` when `ρN > 4`, i.e., for N ≥ 1 and ρ > 4/N`).

BUT: we need to check what the bootstrap hypothesis guarantees about p0.

If `p0 ≤ 2`, the gap might not hold with any fixed coefficient.

## INVESTIGATION TASK FOR CODEX

Rather than prescribing the exact fix, investigate:

1. Read the existing energy inequality proof carefully
2. Check whether `2 < pExp * Acoef` holds for the SPECIFIC coefficients used
3. If NOT, find a coefficient split that makes the gap hold while preserving
   the energy inequality
4. Write the theorem producing `LpBootstrapEnergyInequalityWithGap`

Key constraint: the `AbstractLpBootstrapHypothesis` guarantees `p0 > max(1, ρN/2)`.
For the interval domain, `N` is the dimension parameter from `CM2Params`. If the
gap requires `p0 > 2`, check whether this is implied by the bootstrap hypothesis.

## Rules

- 0 sorry, 0 custom axiom
- Do NOT modify existing files
- Write ONLY `ShenWork/PDE/P3MoserGapProducer.lean`
- Add `#print axioms` at the end
- Verify with: `lake env lean ShenWork/PDE/P3MoserGapProducer.lean`
- If the gap CANNOT be proved for the current coefficient structure, write the
  file with the partial result that gets as close as possible, and add a comment
  at the bottom explaining exactly what the obstruction is (specific numerical
  bound that fails).

## Imports needed

```lean
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2
```
