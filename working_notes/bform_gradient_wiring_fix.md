# B-form Gradient Wiring Fix

## Problem

The current `TruncatedGradientWindowWiring` instantiation in
`IntervalTruncatedPositiveTimeBootstrap.lean` has a structural mismatch:

- **Current `Src`**: `logistic(U_n(s)) - chi_0 * truncatedChemFlux(U_n(s))`
- **Actual iterate structure**: B-form with conjugate kernel operator,
  NOT heat semigroup applied to flux

The iterate satisfies:
```
U(n+1, t) = S(t)(u_0) + int_0^t S(t-s)(L_n(s)) ds - chi_0 int_0^t B_N(t-s)(Q_n(s)) ds
```
where `B_N = -int d_y K(t,x,y) Q(y) dy` is the conjugate kernel operator.

Taking the gradient `d_x U(n+1)` and bounding requires controlling
`d_x int B_N(t-s)(Q_n(s)) ds`, which has a 1/(t-s) singularity (not sqrt).

## Solution: IBP

The IBP identity (proved in `IntervalConjugateKernelIBP.lean`):
```
B_N(t)(Q)(x) = S(t)(Q')(x)   when Q(0) = Q(1) = 0
```

After IBP, the iterate becomes:
```
U(n+1, t) = S(t)(u_0) + int_0^t S(t-s)[L_n(s) - chi_0 * Q'_n(s)] ds
```

The source after IBP is `L_n - chi_0 * Q'_n` (flux DERIVATIVE, not flux).

## Correct parameters

### Flux derivative bound (product rule)

```
Q_n(y) = positivePart(lift(U_n)(y)) * resolverGrad(y) / (1 + R(y))^beta
```

Product rule with (1+R)^beta >= 1 and 0 <= positivePart <= M:
```
|Q'_n| <= G * Gamma_M + M * H_M + beta * M * Gamma_M^2
       = B_F * G + A_F
```

where:
- `Gamma_M` = sup |resolverGradReal| on M-ball (exists: resolverGrad_sup_le_of_bounded)
- `H_M` = sup |resolverGrad2Real| on M-ball (resolver second derivative)
- `B_F = Gamma_M`
- `A_F = M * H_M + beta * M * Gamma_M^2`

### Contraction condition

```
truncWindowB = Cg * 2*sqrt(hi - a) * |chi_0| * B_F
             = Cg * 2*sqrt(3t/4) * |chi_0| * Gamma_M
```

Contraction holds when `t < (1 / (2*Cg * |chi_0| * Gamma_M))^2`.

### What needs to be changed

1. **Src definition**: Change from `logistic - chi_0 * flux` to
   `logistic - chi_0 * flux_deriv`
2. **A_F**: Change from `M * Gamma_M` (L-inf flux bound) to
   `M * H_M + beta * M * Gamma_M^2` (W^{1,1} flux derivative bound)
3. **B_F**: Change from `0` to `Gamma_M`
4. **hsource_of_grad**: Prove the flux derivative bound (product rule)
5. **hkernel_step**: Now uses standard `gradDuhamel_shifted_sup_bound`
   since the after-IBP source goes through heat semigroup S
6. **Need**: `resolverGrad2Real` bound on the M-ball (H_M)
7. **Need**: IBP at iterate level (flux(0) = flux(1) = 0 already proved)

### Infrastructure check

- [x] `resolverGrad_sup_le_of_bounded` (Gamma_M)
- [x] `intervalConjugateKernelOperator_eq_semigroup_deriv` (IBP identity)
- [x] `truncatedChemFluxLifted_zero_left/right` (flux boundary vanishing)
- [x] `gradDuhamel_shifted_sup_bound` (Duhamel gradient after IBP)
- [ ] `resolverGrad2Real_bounded_on_ball` (H_M on M-ball, NOT from classical solution)
- [ ] Flux derivative product rule formalization
- [ ] IBP-Duhamel composition (connecting all pieces)

## Status (post d2e5a309)

Wiring COMMITTED with correct B_F = Γ_M. File compiles with 20 sorrys.

### Sorrys in the wiring (L185-L241):

| Line | Field | Difficulty | Notes |
|------|-------|-----------|-------|
| 185 | hBcontr (truncWindowB < 1) | Medium | Needs T-smallness; may add hypothesis to DT |
| 210 | hleft | Hard | Gradient on [a,lo] for ALL n; needs mini-contraction or bootstrap chain |
| 211 | hbase | Medium | 0th iterate = S(t)(u₀); use semigroup gradient bound |
| 236 | hsource_of_grad flux' bound | Hard | Product rule on truncatedChemFluxLifted derivative |
| 241 | hkernel_step | Hard | IBP converts conjugate kernel to S; then standard Duhamel gradient |
| 258 | DifferentiableAt | Hard | Picard iterate regularity at interior points |

### Key insight on hleft

`hleft` asks for gradient bound on ALL iterates on [a, lo] = [t/4, t/2].
This cannot be proved from the ball bound alone (B_F ≠ 0 means source
depends on gradient). Needs either:
(a) Separate contraction argument on [a, lo] (shorter window → smaller
    contraction coefficient → smaller fixed point → ≤ Gw), or
(b) Bootstrap chain from very small time where semigroup dominates, or
(c) Use G1profile (kernel route, χ₀=0) as initial bound, then show
    chemotaxis correction is small enough.

Approach (a) is cleanest: the contraction coefficient on [a, lo] is
truncWindowB(B_F, χ₀, a', lo) where a' < a. With a' = 0, the coefficient
is Cg * 2√lo * |χ₀| * Γ_M ≤ Cg * 2√(hi) * |χ₀| * Γ_M = truncWindowB
on the main window. So if the main window contracts, the early window
also contracts (with same or smaller coefficient).

BUT: the early window uses ∫_0^t (from 0!), not ∫_a^t, so the shifted
Duhamel bound √(t-a') might be √t (not √(t-a)). This makes the early
window contraction coefficient SAME as or larger than the main window.

Actually, the iterate at time t involves ∫_0^t S(t-s)(Src) ds, and the
shifted Duhamel bound gives √t. So on [a, lo]:
contraction ∝ 2√lo ≤ 2√hi → same or smaller than main window.
Initial term ∝ M/√a → LARGER than main window.

The fixed point on [a, lo] = M/√a * 1/(1 - contraction) is LARGER than
Gw = M/√(lo-a) * 1/(1 - contraction). Since a < lo - a, we have
1/√a > 1/√(lo-a), so the early-window fixed point > Gw.

PROBLEM: Gw is too small for hleft! We need a LARGER G.

Fix: use Gw = max(early_fixed_point, main_fixed_point). Or: set a = 0
(no early window), lo = 0, hi = t. But then truncWindowA has M/√(lo-a)
= M/0 = ∞. Not good.

Alternative fix: use a DIFFERENT splitting. Instead of a = t/4, lo = t/2,
hi = t, use a = 0, lo = t/2, hi = t, and for hleft just use the
semigroup gradient bound on [0, t/2] (which is Cg*M/√s for s > 0,
bounded by Cg*M/√a for a small positive a).

This is getting circular. The standard way: the early window needs a
SEPARATE argument, not the contraction. The semigroup initial data
contribution dominates at early time. For all iterates, the iterate at
time s is S(s)(u₀) + Duhamel, and the gradient of the Duhamel part grows
like √s (small near 0). So the iterate gradient at time s is dominated
by Cg*M/√s. This means:

For hleft on [a, lo] = [t/4, t/2]:
|∂_x U(n, s)| ≤ Cg*M/√(t/4) + Cg*2√(t/2) * ‖Src_n‖_∞

But ‖Src_n‖_∞ depends on gradient... circular unless B_F = 0.

CONCLUSION: With B_F ≠ 0, hleft CANNOT be proved independently of the
contraction. The framework structure needs modification.

POSSIBLE FIX: Merge hleft into the induction. Instead of requiring hleft
as a separate hypothesis, modify truncatedGradientWindow_all to do
induction on the FULL window [a, hi], not just [lo, hi]. The base case
would be iterate 0 (semigroup gradient), and the step would use the
source bound on [a, hi] to produce gradient on [a, hi] for iterate n+1.

This requires modifying IntervalTruncatedGradientWindow.lean.

## Source (ChatGPT Q3966, Codex gpt-5.5 xhigh analysis)

- Q3966 confirmed B_F = Gamma_M, gave explicit constants
- Codex identified the B-form structural mismatch
