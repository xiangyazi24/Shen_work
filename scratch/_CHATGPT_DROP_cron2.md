# Q81 (cron2): χ₀<0 chemotaxis after uniform H¹ — global existence and asymptotics roadmap

## Executive answer

With a uniform-in-time `H¹` bound in hand, the **global existence theorem is now straightforward** if the local theory has the standard continuation property: the local lifespan from a time slice depends only on the `H¹` norm of that slice. Then a finite maximal time contradicts the ability to restart from a time close to the endpoint.

The asymptotic theorem is a separate layer. For nontrivial nonnegative data, the expected limit is the positive constant logistic equilibrium

```text
u(t,·) → K,
v(t,·) → K/μ,
```

where `K` is the carrying capacity, e.g. `K=1` for `f(u)=u(1-u)` or `f(u)=u(1-u^α)`. The zero datum stays zero. Exponential convergence is expected under the usual stable-logistic assumptions, but it is **not a direct consequence of the uniform H¹ bound alone**. It needs a convergence mechanism: Lyapunov/LaSalle, entropy dissipation plus an entropy gap, or an eventual perturbative spectral-stability argument.

The shortest next paper-style theorem is therefore:

```text
local mild/classical solution
+ nonnegativity/order box
+ uniform H¹ a-priori estimate
+ H¹ continuation criterion
⇒ global bounded classical solution, classical for t>0.
```

Do this before asymptotics. The asymptotics should be a later theorem.

## 1. Continuation lemma: precise statement

Let `X := H¹_N(0,1)` or the cosine `H¹` phase space compatible with Neumann boundary conditions.

A standard local well-posedness/continuation package is:

```text
(Local existence with lifespan bounded below on bounded sets)
For every R>0 there exists τ(R)>0 such that for every time t₀ and every datum
w∈X with ||w||_X≤R, the problem with initial datum w at t₀ has a unique mild
solution on [t₀,t₀+τ(R)].
```

Equivalently, the maximal solution `u:[0,Tmax)→X` satisfies the blow-up alternative

```text
Tmax < ∞  ⇒  limsup_{t↑Tmax} ||u(t)||_X = ∞.
```

Then the continuation lemma is:

```text
ContinuationLemma:
Assume u is the unique maximal X-solution on [0,Tmax).
Assume sup_{0≤t<Tmax} ||u(t)||_X ≤ R < ∞.
Then Tmax = ∞.
```

Proof:

1. Suppose `Tmax<∞`.
2. Let `τ := τ(R)`.
3. Pick `t₀∈[0,Tmax)` with `Tmax - t₀ < τ/2`.
4. Since `||u(t₀)||_X≤R`, local existence from `u(t₀)` gives a solution on `[t₀,t₀+τ]`.
5. By uniqueness, this new solution agrees with the old solution on `[t₀,Tmax)`.
6. Since `t₀+τ > Tmax`, this extends the old maximal solution past `Tmax`, contradiction.

So once you have

```text
sup_{t<Tmax} ||u(t)||_{H¹} ≤ C,
```

global existence follows immediately.

### Important formal detail

If your a-priori theorem is stated as `sup_{t>0} ||u(t)||_{H¹}≤C`, check the behavior at `t=0`.

- If `u₀∈H¹`, include `t=0` using the initial coefficient bound.
- If `u₀` is only `L∞` or `H^σ`, `σ<1`, then the global theorem should be phrased as existence for all time plus `sup_{t≥ε} ||u(t)||_{H¹}<∞` for every `ε>0`, unless you prove instantaneous smoothing and start continuation in a weaker phase space.

For an `H¹`-based continuation criterion from time zero, you need `u₀∈H¹`.

## 2. What exactly does the uniform H¹ bound buy?

On `[0,1]`, `H¹` embeds into `L∞`. But you already have a stronger order box. The uniform `H¹` bound gives:

```text
sup_t ||u(t)||_{H¹} < ∞,
sup_t ||u(t)||_{L∞} < ∞,
```

and, through the elliptic resolver,

```text
sup_t ||v(t)||_{H³} or at least resolver-controlled v, v_x, v_xx bounds
```

in the regularity scale your formalization uses.

For **global existence**, this is enough if the local theory is in `H¹`.

For **global bounded classical solution**, one normally adds parabolic smoothing:

```text
for every ε>0 and every finite or infinite T,
u is classical on [ε,T]×[0,1],
```

with bounds depending on `ε` and the uniform `H¹`/`L∞` bounds. If the initial datum is smooth and satisfies compatibility, classicality can include `t=0`; otherwise it is classical for `t>0`.

So the clean headline is:

```text
For nonnegative u₀∈H¹, the solution exists globally and remains bounded in H¹ and L∞.
Moreover, by parabolic regularization it is classical for t>0.
```

If your `IsPaper2ClassicalSolution` constructor already turns the mild solution plus source regularity into classicality, the remaining work is just to feed it the global time interval after continuation.

## 3. Expected steady state

For logistic source with carrying capacity `K>0`, the constant steady state is

```text
u_* = K,
v_* = K/μ.
```

There is also the zero steady state if the logistic source has the usual factor `u`, and the zero solution is selected by the zero initial datum.

For nontrivial nonnegative initial data, the expected asymptotic behavior is

```text
u(t) → K,
v(t) → K/μ,
```

usually exponentially fast in norms below the eventual classical regularity level, and then by interpolation/smoothing in stronger norms.

A useful maximum-principle uniqueness check for positive stationary states is short:

Let `(U,V)` be a positive stationary solution with Neumann boundary conditions:

```text
0 = U_xx + a (U V_x)_x + f(U),     a=-χ₀>0,
μV - V_xx = U.
```

At a maximum point of `U`, say `Umax`, we have `U_x=0`, `U_xx≤0`, and the elliptic maximum principle gives `μV≤Umax`, hence

```text
V_xx = μV-U ≤ 0
```

at that point. Therefore

```text
0 = U_xx + a U V_xx + f(Umax) ≤ f(Umax),
```

so `f(Umax)≥0`. For the logistic source, this forces `Umax≤K`.

At a minimum point `Umin`, the same reasoning gives `U_xx≥0`, `μV≥Umin`, hence `V_xx≥0`, and therefore

```text
0 = U_xx + a U V_xx + f(Umin) ≥ f(Umin),
```

so `f(Umin)≤0`, forcing `Umin≥K` for a positive solution. Hence `U≡K`.

Thus the only positive steady state is the carrying capacity. This is a very useful endpoint for LaSalle/omega-limit arguments.

## 4. Lyapunov / entropy functional

For the drift-diffusion part without logistic reaction, the repulsive sign gives a convex free energy. Write

```text
a := -χ₀ > 0,
z := v - K/μ = (μ-Δ_N)^{-1}(u-K),
Φ_K(s) := s log(s/K) - s + K.
```

A natural relative free energy is

```text
E[u] := ∫_0^1 Φ_K(u) dx + (a/2) ∫_0^1 (u-K) z dx.
```

Since the Neumann resolver is positive self-adjoint, the second term is nonnegative. The variational derivative is

```text
δE/δu = log(u/K) + a z.
```

The diffusion plus repulsive taxis can be written as

```text
u_xx + a ∂x(u v_x)
  = ∂x( u ∂x( log(u/K) + a z ) ).
```

Therefore along smooth positive solutions,

```text
dE/dt
  = - ∫_0^1 u |∂x(log(u/K)+a z)|² dx
    + ∫_0^1 (log(u/K)+a z) f(u) dx.                 (Entropy identity)
```

The first term is the entropy dissipation. The reaction contribution needs analysis.

For a pure scalar logistic ODE, the entropy part satisfies

```text
∫ log(u/K) f(u) dx ≤ 0
```

because `log(u/K)` and `f(u)` have opposite signs around `K`. The extra chemical piece

```text
a ∫ z f(u) dx
```

is not automatically sign-definite pointwise. It can often be controlled using the positivity of the resolver, the logistic monotonicity, and eventual bounds `0<δ≤u≤M`, but this is an additional estimate. Do not treat the full entropy as a one-line Lyapunov functional unless you have proved this reaction term is nonpositive or dominated by the entropy gap.

So the Lyapunov route is canonical, but not necessarily the shortest Lean route unless the entropy infrastructure is already present.

## 5. Is convergence exponential?

Expected answer: **yes for nontrivial nonnegative data under the usual stable logistic assumptions**, but proving it requires more than the uniform `H¹` bound.

The linearization around `(K,K/μ)` is very favorable. Let

```text
w := u-K,
z := v-K/μ = (μ-Δ_N)^{-1}w.
```

Ignoring nonlinear terms,

```text
w_t = w_xx + a K z_xx + f'(K) w.
```

On Neumann cosine mode `k`, with `λ_k=(kπ)²`,

```text
z_k = w_k/(μ+λ_k),
z_xx,k = -λ_k w_k/(μ+λ_k),
```

so the linear eigenvalue is

```text
-λ_k - aK λ_k/(μ+λ_k) + f'(K).
```

For `k=0`, it is `f'(K)<0`. For `k≥1`, it is even more negative. Thus the linearized operator has a spectral gap whenever the logistic equilibrium is stable, i.e. `f'(K)<0`.

A clean exponential proof can proceed as:

1. prove convergence/precompactness and identify the omega-limit as `K`; or prove eventual closeness by comparison;
2. use the spectral gap and nonlinear estimates to obtain

   ```text
   d/dt ||w||²₂ ≤ -γ ||w||²₂
   ```

   for large time;
3. bootstrap to higher norms by parabolic smoothing.

Alternatively, prove an entropy inequality of the form

```text
E[u(t)]' ≤ -c E[u(t)]
```

for large time or globally after establishing `0<δ≤u≤M`. This gives exponential convergence directly.

But the uniform `H¹` bound alone only gives precompactness after smoothing; it does not by itself provide a monotone functional or a decay rate.

## 6. Shortest path to the paper headline

For a clean paper theorem, split the results:

### Theorem A: global bounded classical solution

Assumptions:

```text
u₀≥0,
u₀∈H¹ or smoother depending on the local theory,
χ₀<0,
μ>0,
logistic source with an absorbing carrying capacity K.
```

Conclusion:

```text
There exists a unique global solution u on [0,∞).
The solution remains nonnegative and uniformly bounded:
  sup_{t≥0} ||u(t)||∞ ≤ M,
  sup_{t≥0} ||u(t)||H¹ ≤ C.
The associated v=(μ-Δ_N)^{-1}u satisfies the corresponding uniform resolver bounds.
The solution is classical for t>0, and from t=0 if the initial datum has the required compatibility/smoothness.
```

Proof dependencies:

```text
local well-posedness + continuation;
L∞ order box;
uniform H¹ estimate;
parabolic smoothing / classicality constructor.
```

This theorem does **not** need the asymptotic Lyapunov functional.

### Theorem B: convergence to steady state

Additional work:

```text
eventual positivity/lower bound, or entropy coercivity;
precompactness in a topology strong enough to pass to steady states;
unique positive stationary state;
LaSalle/entropy decay or spectral-gap perturbation.
```

Conclusion:

```text
if u₀ not identically zero, then u(t)→K and v(t)→K/μ;
under stable logistic assumptions, convergence is exponential.
```

This theorem may need eventual higher regularity or compactness, but those can be derived from the global bounded classical solution by smoothing.

## 7. What needs more than uniform H¹?

### For global existence

No more a-priori estimates are needed if the local continuation criterion is `H¹`-based.

### For bounded classicality

You need regularity/smoothing, but not a new dissipative a-priori estimate. Use the existing mild/classical constructor or semigroup smoothing on `[ε,∞)`.

### For asymptotics

Yes, you need something beyond the bare uniform `H¹` bound:

```text
precompactness / smoothing,
identification of stationary limits,
and a convergence mechanism: Lyapunov/LaSalle, entropy gap, comparison, or spectral stability.
```

Uniform `H¹` is the boundedness platform, not the decay proof.

## Final recommendation

Next formal theorem should be the continuation theorem:

```text
uniform_H1_bound + local_lifespan_lower_bound_on_H1_balls
  ⇒ global_solution.
```

Then prove the global bounded classical statement by combining global existence with the already-built `L∞` and `H¹` bounds plus classicality/smoothing.

Only after that should you start the convergence theorem. For convergence, the most concrete route is either:

```text
entropy/LaSalle using E[u]=∫Φ_K(u)+(a/2)∫(u-K)(μ-Δ_N)^{-1}(u-K),
```

with a proved reaction-term control, or

```text
eventual positivity + spectral-gap stability around K.
```

The second route is probably shorter in Lean if the cosine spectral infrastructure is already strong; the first route is more canonical in PDE prose but requires more entropy calculus.
