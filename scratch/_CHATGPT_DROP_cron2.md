# Q85 (cron2): χ₀<0 chemotaxis — entropy route to convergence to the carrying capacity

## Executive verdict

For the repulsive sign `χ₀<0`, the clean Lyapunov functional is the **relative entropy**

```text
E(t) := ∫₀¹ h(u(t,x)) dx,
h(s) := s log s - s + 1.
```

For

```text
u_t = u_xx + a ∂x(u v_x) + u(1-u),   a := -χ₀ > 0,
μ v - v_xx = u,
Neumann BC,
```

this entropy has the decisive identity

```text
E'(t)
  = - ∫₀¹ u_x²/u dx
    - a ∫₀¹ u_x v_x dx
    + ∫₀¹ u(1-u) log u dx.
```

The chemotaxis term is **dissipative** for the repulsive sign:

```text
∫ u_x v_x dx ≥ 0,
```

because `v=(μ-Δ_N)^{-1}u` and, in Neumann cosine modes,

```text
∫ u_x v_x = ∑_{k≥1} λ_k /(μ+λ_k) |u_k|² ≥ 0.
```

The logistic term is also dissipative:

```text
u(1-u) log u = -u(u-1) log u ≤ 0.
```

Thus `E` is a genuine Lyapunov functional with no smallness condition on `|χ₀|`.

For **exponential decay**, however, you need a positive lower bound

```text
0 < m ≤ u(t,x) ≤ M < ∞
```

on the time interval where you want the exponential estimate. If the initial datum is strictly positive, this follows from scalar min/max comparison. If the initial datum is merely nonnegative and nontrivial, you need an eventual positivity / strong maximum principle input; then the exponential estimate starts after a positive time `t₀`.

The shortest first theorem to formalize is therefore:

```text
Assume 0<m≤u₀≤M. Then
  ||u(t)-1||²_{L²} ≤ C e^{-δt}
  and v(t)→1/μ exponentially in H²/L∞-type resolver norms.
```

For nonnegative nontrivial data without a positive lower bound, first prove/eventually assume positivity, then apply the same theorem from `t₀>0`.

## 1. The Lyapunov functional and derivative

Let

```text
a := -χ₀ > 0,
h(s) := s log s - s + 1,
E(t) := ∫ h(u(t,x)) dx.
```

The derivative of `h` is

```text
h'(s)=log s.
```

For a smooth positive solution,

```text
E'(t) = ∫ log u · u_t.
```

Insert the PDE:

```text
E'
 = ∫ log u · u_xx
   + a ∫ log u · ∂x(u v_x)
   + ∫ log u · u(1-u).
```

The diffusion term is

```text
∫ log u · u_xx
  = - ∫ (u_x/u) u_x
  = - ∫ u_x²/u.
```

For the taxis term, using Neumann boundary conditions,

```text
a ∫ log u · ∂x(u v_x)
  = -a ∫ (u_x/u) u v_x
  = -a ∫ u_x v_x.
```

Since `v=(μ-Δ_N)^{-1}u`, this term has a spectral sign:

```text
∫ u_x v_x
  = ∑_{k≥1} λ_k u_k v_k
  = ∑_{k≥1} λ_k /(μ+λ_k) |u_k|²
  ≥ 0.
```

Thus the repulsive chemotaxis contribution is nonpositive:

```text
-a ∫ u_x v_x ≤ 0.
```

For the logistic term,

```text
∫ u(1-u) log u
  = - ∫ u(u-1) log u.
```

Pointwise,

```text
u(u-1)log u ≥ 0
```

for every `u>0`, with equality only at `u=1`. Therefore

```text
E'(t)
  = - ∫ u_x²/u
    - a ∫ u_x v_x
    - ∫ u(u-1)log u
  ≤ - ∫ u(u-1)log u
  ≤ 0.
```

This is the clean Lyapunov identity.

## 2. Coercivity and exponential decay

Assume that along the solution

```text
0 < m ≤ u(t,x) ≤ M.
```

Define the pointwise logistic entropy dissipation

```text
d(s) := s(s-1)log s.
```

On the compact interval `[m,M]`, both `h(s)` and `d(s)` are nonnegative and vanish only at `s=1`. The quotient

```text
q(s) := d(s)/h(s)
```

extends continuously at `s=1`, with

```text
lim_{s→1} q(s)=2.
```

Hence

```text
δ := inf_{s∈[m,M]} q(s) > 0.
```

Then pointwise

```text
d(s) ≥ δ h(s),   s∈[m,M].
```

Using the entropy identity,

```text
E'(t) ≤ -∫ d(u(t,x)) dx ≤ -δ ∫ h(u(t,x)) dx = -δ E(t).
```

Therefore

```text
E(t) ≤ E(0) e^{-δt}.
```

To convert entropy decay into `L²` decay, use the compact-interval comparison

```text
h(s) ≥ c₂ (s-1)²,   s∈[m,M],
```

where

```text
c₂ := inf_{s∈[m,M], s≠1} h(s)/(s-1)² > 0
```

with value `1/2` at `s=1` by continuous extension. Then

```text
||u(t)-1||²_{L²}
  ≤ c₂^{-1} E(t)
  ≤ c₂^{-1} E(0) e^{-δt}.
```

So the cleanest formal theorem is:

```lean
entropy_exponential_L2_convergence :
  0 < m → (∀ t x, m ≤ u t x) → (∀ t x, u t x ≤ M) →
  EntropyIdentity u v →
  ∃ C δ > 0, ∀ t, ‖u t - 1‖_{L²}^2 ≤ C * Real.exp (-δ*t)
```

with explicit constants from the compact interval `[m,M]`.

## 3. Convergence of `v`

Let

```text
w := u-1,
z := v - 1/μ.
```

Then

```text
μ z - z_xx = w,
Neumann BC.
```

The Neumann resolver gives

```text
||z||_{H²} ≤ C_μ ||w||_{L²}.
```

Therefore the `L²` exponential decay of `u-1` gives

```text
||v(t)-1/μ||_{H²} ≤ C e^{-δt/2}
```

if the `u` estimate is stated as squared norm decay. Equivalently, adjust constants so that both are written with `e^{-γt}`.

In one dimension, `H²` embeds into `C¹`, so this also gives exponential convergence of `v` to `1/μ` in sup-type norms if your formal library has the embedding.

## 4. Does chemotaxis require a smallness condition?

For the entropy route: **no smallness condition is needed** for `χ₀<0`.

The entire chemotaxis contribution is

```text
-a ∫ u_x v_x ≤ 0,
```

and is discarded. It does not need to be dominated by diffusion or logistic damping.

This is the main advantage of the entropy `∫(u log u-u+1)` over a raw `L²` distance. If you differentiate

```text
1/2 ||u-1||²_{L²},
```

the taxis nonlinearity produces terms such as

```text
∫ (u-1) ∂x(u v_x),
```

which are not globally sign-definite in an obvious way and usually require perturbative smallness, eventual closeness, or more estimates. The entropy eliminates this issue because its derivative is `log u`, causing the taxis term to collapse to the signed form `-a∫u_xv_x`.

So:

```text
Global entropy decay for repulsive sign: unconditional in |χ₀|.
Raw L² energy decay: clean only after perturbative/equilibrium closeness, or with extra work.
```

## 5. Positive lower bound: the real caveat

The entropy identity itself only needs positivity. The **exponential coercivity** needs a uniform lower bound `m>0`.

If the initial datum satisfies

```text
0 < m₀ ≤ u₀(x) ≤ M₀,
```

then scalar min/max comparison gives explicit lower and upper barriers.

At a spatial maximum of `u`, the repulsive term is nonpositive and

```text
M'(t) ≤ M(t)(1-M(t)).
```

At a spatial minimum of `u`, the repulsive term is nonnegative and

```text
m'(t) ≥ m(t)(1-m(t)).
```

The logistic ODE preserves positivity and converges to `1`. Hence a positive lower bound is available globally, and indeed one can squeeze `u` between two scalar logistic ODE solutions. This comparison route alone can prove `L∞` convergence to `1` exponentially when `m₀>0`.

If `u₀≥0` is nontrivial but may vanish, the solution should become strictly positive for every `t>0` by the strong parabolic maximum principle. Then, for any fixed `t₀>0`, set

```text
m(t₀) := min_x u(t₀,x) > 0
```

and run the entropy exponential theorem from `t₀` onward. Formalizing this requires a strong-positivity/Harnack-type input or a separate smoothing positivity lemma.

If `u₀≡0`, then `u(t)≡0`; it does **not** converge to `1`. So the asymptotic theorem must exclude the zero datum or assume positive initial data.

## 6. Minimal input beyond global bounded H¹

For the clean `L²` exponential theorem, the minimal inputs are:

```text
1. global classical positive solution;
2. uniform upper bound u≤M;
3. uniform lower bound m≤u, or eventual lower bound after t₀;
4. Neumann resolver spectral positivity:
     ∫ u_x v_x = ∑ λ_k/(μ+λ_k)|u_k|² ≥ 0;
5. compact-interval coercivity lemmas for h and d on [m,M].
```

You do **not** need a Neumann Poincaré inequality for the entropy `L²` convergence, because the logistic term damps the zero mode as well as nonzero modes. Poincaré/spectral gap becomes useful for a perturbative `H¹` or linearized proof, but not for the first entropy-to-`L²` theorem.

You also do **not** need more than global bounded `H¹` for boundedness. For the entropy derivative, however, you need enough classical regularity and positivity to justify multiplying by `log u` and integrating by parts. If positivity at zero is inconvenient, prove the identity first for `h_ε(s)=(s+ε)log(s+ε)-(s+ε)+1` and pass to the limit, or state the first theorem under `m≤u`.

## 7. What about `H¹` exponential convergence?

Do not make `H¹` exponential convergence the first asymptotics target.

From entropy you get directly:

```text
||u(t)-1||_{L²} ≤ C e^{-γt},
||v(t)-1/μ||_{H²} ≤ C e^{-γt}.
```

To upgrade to `H¹`, use one of these later routes:

### Route A: smoothing + source decay

Use the equation for `w=u-1` and Duhamel on sliding windows. Once `u→1` in `L²` exponentially and `u` is uniformly bounded in `H¹`, in one dimension interpolation gives decay in `L∞` at a possibly weaker rate:

```text
||w||∞ ≤ C ||w||₂^{1/2} ||w||_{H¹}^{1/2}.
```

Then the nonlinear source decays, and heat smoothing gives `H¹` decay for `t≥1`.

### Route B: eventual perturbative H¹ energy

After `u` is close to `1` in `L∞`, write the equation for `w=u-1` and use the linear spectral gap around equilibrium. The linearization has mode eigenvalues

```text
-λ_k - a λ_k/(μ+λ_k) - 1,
```

for `K=1`, all strictly negative. Nonlinear terms are small for large time, so an `H¹` energy inequality closes exponentially.

Both routes are standard, but they are more work than the first `L²` entropy theorem.

## 8. Lean-oriented theorem sequence

Recommended theorem order:

### Theorem 1: entropy identity

```lean
entropy_deriv_identity :
  PositiveClassicalSolution u v →
  a = -χ₀ → 0 < a →
  HasDerivAt
    (fun t => ∫ x in Icc 0 1, u t x * log (u t x) - u t x + 1)
    ( - ∫ x, (ux t x)^2 / (u t x)
      - a * ∫ x, ux t x * vx t x
      - ∫ x, u t x * (u t x - 1) * log (u t x) )
    t
```

### Theorem 2: chemotaxis sign

```lean
resolver_entropy_chem_nonneg :
  v = (μ - Δ_N)^{-1} u →
  0 < μ →
  0 ≤ ∫ x, ux x * vx x
```

The spectral proof is likely shortest if the cosine infrastructure is already built.

### Theorem 3: compact interval coercivity

```lean
entropy_logistic_coercivity_on_Icc :
  0 < m → m ≤ 1 → 1 ≤ M →
  ∃ δ > 0, ∀ s ∈ Icc m M,
    s*(s-1)*log s ≥ δ * (s*log s - s + 1)
```

Do not require `m≤1≤M` if you do not want; just assume `1∈[m,M]`, which follows for asymptotic boxes around the carrying capacity. More generally use `m≤s≤M` and include the point `1` in the interval.

### Theorem 4: entropy exponential decay

```lean
entropy_exponential_decay :
  entropy_deriv_identity →
  chem_nonneg →
  logistic_entropy_coercivity →
  E t ≤ E 0 * exp (-δ*t)
```

### Theorem 5: L² convergence

```lean
L2_convergence_from_entropy :
  (∀ t x, m ≤ u t x ∧ u t x ≤ M) →
  E t ≤ E0 * exp (-δ*t) →
  ||u t - 1||²_{L²} ≤ C * exp (-δ*t)
```

### Theorem 6: resolver convergence

```lean
resolver_convergence_to_constant :
  ||u t - 1||_{L²} ≤ C e^{-γt} →
  ||v t - 1/μ||_{H²} ≤ Cμ*C e^{-γt}
```

This sequence is much shorter than a full LaSalle formalization and gives an explicit exponential rate under a positive lower bound.

## Final answer to the three questions

1. The right Lyapunov functional is

   ```text
   E(t)=∫(u log u-u+1).
   ```

   Its derivative is

   ```text
   E' = -∫u_x²/u - a∫u_xv_x - ∫u(u-1)logu ≤ -δE
   ```

   once `0<m≤u≤M`. This yields exponential entropy and `L²` decay.

2. No chemotaxis smallness is needed for `χ₀<0`. The taxis term has the good sign in the entropy identity and can be discarded. The real condition for exponential decay is not small `|χ₀|`; it is positivity/coercivity, i.e. a positive lower bound for `u` or eventual positivity.

3. The shortest formalizable first statement is

   ```text
   if 0<m≤u₀≤M and u is the global classical solution, then
   ||u(t)-1||²_{L²} ≤ C e^{-δt},
   ||v(t)-1/μ||_{H²} ≤ C e^{-δt}.
   ```

   Minimal inputs: the entropy identity, resolver sign lemma, compact-interval coercivity, and the positive lower/upper box. Do `H¹` exponential convergence later via smoothing or eventual perturbative spectral estimates.
