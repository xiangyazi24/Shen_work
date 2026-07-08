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

## Source (ChatGPT Q3966, Codex gpt-5.5 xhigh analysis)

- Q3966 confirmed B_F = Gamma_M, gave explicit constants
- Codex identified the B-form structural mismatch
