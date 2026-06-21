# P1 monotone stationary-Liouville route: root pinning to the constant state

## Executive verdict

The route is sound, but only with one important caveat.

Monotonicity plus boundedness gives the two end limits. Bounded second derivative gives uniform continuity of W', and together with boundedness/monotonicity it gives W'(x) -> 0 at both infinities. However, W''(x) -> 0 does not follow from only monotone + bounded + C2 + bounded W''. To pass the stationary equation to the limit, prove convergence of the right-hand side first and then use the additional fact that W' has finite limits and is uniformly continuous / integrable to force the second-derivative limit to be zero. Equivalently, if the equation gives W''(x) -> A at an end and W'(x) -> 0, then A must be 0, because otherwise W' would eventually grow linearly.

Thus the complete route is:

1. Antitone and bounded implies limits L_minus and L_plus exist.
2. Bounded W'' implies W' is uniformly continuous.
3. Since W is monotone and bounded, W' is integrable in the improper sense; uniform continuity then implies W' -> 0 at both ends.
4. The elliptic resolver is continuous under monotone end limits: if W(x) -> L, then V[W](x) -> (nu/mu) L^gamma, V'[W](x) -> 0, and the chemotaxis flux terms tend to 0.
5. The stationary equation then implies W'' has a finite end limit A = lambda L - reaction_part(L), up to the sign convention of the equation. Since W' -> 0, that finite limit A must be 0.
6. Hence the end limit L satisfies the scalar reaction equilibrium equation L(a - b L^alpha) = 0.
7. The lower pin c1 > 0 rules out L = 0, so L = Ustar = (a/b)^(1/alpha).
8. Both end limits equal Ustar. A monotone function whose two end limits are equal is constant. Hence W is identically Ustar.

This proves the desired unconditional conclusion, assuming the trap lower pin is genuinely positive and the resolver/flux convergence lemmas are proved. No smallness or stabilization axiom is needed.

---

## Notation and sign convention

Assume W solves on the real line

    W'' + c W' - lambda W + R(W,V[W]) = 0,

with c > 0 and lambda > 0. Equivalently,

    W'' = -c W' + lambda W - R(W,V[W]).

The reaction part is of logistic type

    reaction(W) = a W - b W^(1+alpha) = W (a - b W^alpha),

and the chemotaxis terms vanish at spatially constant states because V'[constant] = 0.

Depending on the exact Lean definition of `frozenWaveOperator`, the final scalar equation may appear as

    lambda L - R_lim(L) = 0

or, after expanding the shifted operator, as

    L (a - b L^alpha) = 0.

The key is to prove and use the repository-specific algebraic lemma:

    constant_limit_stationary_equation_iff_reaction_root

which rewrites the constant-state limit of the frozen wave operator to the logistic root equation.

---

## Step 1. Monotone bounded profile has end limits

### Analytic statement

Let W : R -> R be antitone, i.e.

    x <= y -> W y <= W x.

Assume

    c1 <= W x <= C2

for all x, with c1 > 0. Then the limits

    L_plus  = inf { W x : x in R }
    L_minus = sup { W x : x in R }

exist as finite real numbers and

    Tendsto W atTop (nhds L_plus)
    Tendsto W atBot (nhds L_minus)
    c1 <= L_plus
    c1 <= L_minus
    L_plus <= L_minus

hold.

For antitone W, the right limit is the infimum and the left limit is the supremum.

### Lean lemma shape

```lean
lemma antitone_bdd_has_limits_atTop_atBot
    {W : R -> R} {c1 C2 : R}
    (hanti : Antitone W)
    (hlb : forall x, c1 <= W x)
    (hub : forall x, W x <= C2) :
    exists Lp Lm,
      Tendsto W atTop (nhds Lp) /\
      Tendsto W atBot (nhds Lm) /\
      c1 <= Lp /\ c1 <= Lm /\ Lp <= Lm
```

### Mathlib dependencies

Likely useful APIs:

```lean
Monotone
Antitone
Filter.Tendsto
Filter.atTop
Filter.atBot
sInf
sSup
isLUB / isGLB
```

Mathlib has monotone convergence facts for conditionally complete linear orders, but the fastest formal route may be to define L_plus as `sInf (Set.range W)` and L_minus as `sSup (Set.range W)` and prove the epsilon characterization manually using the GLB/LUB properties.

Because R is conditionally complete and the image is bounded, `sInf` and `sSup` are available.

### Minimal proof sketch

For `atTop`, set `Lp = sInf (Set.range W)`. Given eps > 0, `Lp + eps` is not a lower bound unless all values equal Lp. Therefore choose x0 with W x0 < Lp + eps. For y >= x0, antitone gives W y <= W x0 < Lp + eps. Also Lp <= W y by definition of infimum. Hence abs(W y - Lp) < eps.

For `atBot`, apply the same argument to the monotone function `fun x => W (-x)` or use `sSup` directly.

---

## Step 2. W' tends to zero at both infinities

This is the first important analytic lemma.

### Correct statement

Bounded W'' is enough. One does not need W'' -> 0.

A clean formulation is:

```lean
lemma deriv_tendsto_zero_of_bounded_function_bounded_second_deriv_antitone
    {W : R -> R}
    (hC2 : ContDiff R 2 W)
    (hanti : Antitone W)
    (hW_bdd : exists M, forall x, abs (W x) <= M)
    (hWdd_bdd : exists B, forall x, abs (deriv (deriv W) x) <= B) :
    Tendsto (deriv W) atTop (nhds 0) /\
    Tendsto (deriv W) atBot (nhds 0)
```

The antitone assumption implies W' <= 0 wherever the classical derivative exists. With C2, this holds everywhere:

    deriv W x <= 0.

Also, for any A < B,

    integral_A^B (-W') = W A - W B <= 2M.

Thus -W' is nonnegative and has finite total mass on each tail. Since W'' is bounded, W' is uniformly continuous. A uniformly continuous nonnegative integrable function on a tail tends to 0. Apply this to -W' on atTop and to the reflected function on atBot.

### Alternative local contradiction proof

This proof is often easiest in Lean because it avoids improper integrals if the profile has explicit finite-interval bounds.

Suppose not atTop. Then there are eps > 0 and x_n -> +infinity such that

    abs(W'(x_n)) >= eps.

Since W is antitone, W' <= 0, so W'(x_n) <= -eps. Bounded W'' gives Lipschitz control on W':

    abs(W'(y) - W'(x_n)) <= B abs(y - x_n).

Choose rho = eps/(2B) if B > 0. Then for y in [x_n, x_n+rho],

    W'(y) <= -eps/2.

By taking a subsequence with intervals disjoint, W drops by at least eps*rho/2 on each interval. Infinite disjoint drops contradict boundedness below. If B = 0, W' is constant and boundedness forces W'=0.

The same reflection argument gives atBot.

### Minimal hypotheses

Enough assumptions are:

1. W is C1.
2. W' is uniformly continuous on each tail. Bounded W'' is a sufficient way to prove this.
3. W is bounded and monotone.

So the reusable lemma can be stated more generally as:

```lean
lemma tendsto_zero_of_uniformContinuous_deriv_antitone_bounded
    (hanti : Antitone W)
    (hW_bdd : exists M, forall x, abs (W x) <= M)
    (hderiv : forall x, HasDerivAt W (Wp x) x)
    (hWp_uc : UniformContinuous Wp) :
    Tendsto Wp atTop (nhds 0) /\ Tendsto Wp atBot (nhds 0)
```

Then instantiate `Wp = deriv W` and prove uniform continuity from bounded W''.

### Mathlib dependencies

```lean
HasDerivAt
DifferentiableAt
ContDiff
deriv
intervalIntegral.integral_eq_sub_of_hasDerivAt
Metric.uniformContinuous_iff
Filter.Tendsto
```

For the contradiction proof, useful ingredients are interval FTC and elementary estimates. It may be easiest to formulate a local lemma:

```lean
lemma derivative_negative_on_interval_forces_drop
    (hderiv : forall y in Icc x (x+rho), HasDerivAt W (Wp y) y)
    (hneg : forall y in Icc x (x+rho), Wp y <= -eta) :
    W (x+rho) <= W x - eta*rho
```

proved by integrating W' over the interval.

---

## Step 3. Passing the stationary equation to the end limit

Do not assume W'' -> 0 from monotone + bounded + C2 + bounded W''. That is false in general. The correct chain is:

1. W(x) -> L.
2. W'(x) -> 0.
3. The resolver and source terms have limits, so the right-hand side formula gives W''(x) -> A.
4. Since W'(x) -> 0 and W''(x) -> A, necessarily A = 0.

### Lemma: derivative with finite limit and derivative-of-derivative with finite limit

```lean
lemma deriv_limit_zero_forces_second_deriv_limit_zero
    {F Fp : R -> R} {A : R}
    (hFp_tendsto : Tendsto Fp atTop (nhds 0))
    (hFpp_tendsto : Tendsto (deriv Fp) atTop (nhds A))
    (hderiv : forall x, HasDerivAt Fp (deriv Fp x) x) :
    A = 0
```

A more direct version:

```lean
lemma tendsto_deriv_finite_of_tendsto_function_finite
    (hF_tendsto : Tendsto Fp atTop (nhds 0))
    (hF_deriv_tendsto : Tendsto Fpp atTop (nhds A))
    (hF_deriv : forall x, HasDerivAt Fp (Fpp x) x) :
    A = 0
```

Proof: if A > 0, then eventually Fpp >= A/2, hence Fp grows at least linearly on long intervals, contradicting Fp -> 0. If A < 0, similarly Fp decreases linearly. Therefore A = 0.

Same lemma at atBot follows by reflection.

### Stationary equation gives the W'' limit

From

    W'' = -c W' + lambda W - R(W,V[W])

and the already-proved limits:

    W -> L
    W' -> 0
    R(W,V[W]) -> R_const(L)

we get

    W'' -> lambda L - R_const(L).

Then the previous lemma gives

    lambda L - R_const(L) = 0.

This is the robust replacement for directly asserting W'' -> 0.

---

## Step 4. Resolver continuous at constant end limits

This is the second real analytic input.

Let V solve

    -V'' + mu V = nu W^gamma

on R, with the bounded/right-decaying or whole-line Green resolver used in the project. If

    W(x) -> L > 0

at an end, then

    W(x)^gamma -> L^gamma.

The constant solution associated to the limiting source is

    V_L = (nu/mu) L^gamma.

Need to prove:

```lean
lemma resolver_tendsto_const_atTop
    (hW : Tendsto W atTop (nhds L))
    (hW_bdd : forall x, 0 <= W x /\ W x <= M)
    (hV_def : V = frozenElliptic p W) :
    Tendsto V atTop (nhds ((nu/mu) * L^gamma))
```

and

```lean
lemma resolver_deriv_tendsto_zero_atTop
    (hW : Tendsto W atTop (nhds L))
    (hW_bdd : forall x, 0 <= W x /\ W x <= M)
    (hV_def : V = frozenElliptic p W) :
    Tendsto (deriv V) atTop (nhds 0)
```

The same lemmas are needed at atBot.

### Proof using Green kernel

If the resolver is represented as convolution with an integrable kernel G_mu, then

    V(x) = integral G_mu(x-y) nu W(y)^gamma dy.

Subtract the constant:

    V(x) - (nu/mu)L^gamma
      = integral G_mu(z) nu (W(x-z)^gamma - L^gamma) dz.

Here use the identity integral G_mu = 1/mu. Since W(x-z) -> L for each fixed z as x -> +infinity, and W is bounded, dominated convergence gives V(x) -> (nu/mu)L^gamma.

For V':

    V'(x) = integral G_mu'(z) nu W(x-z)^gamma dz.

Since integral G_mu' = 0, rewrite

    V'(x) = integral G_mu'(z) nu (W(x-z)^gamma - L^gamma) dz.

Use dominated convergence with integrable abs(G_mu') to get V'(x) -> 0.

This is the cleanest route if the project already has Green kernel L1 facts.

### Lean lemma names/dependencies

Use:

```lean
MeasureTheory.tendsto_integral_of_dominated_convergence
Integrable
Filter.Tendsto
Tendsto.comp
ContinuousAt.rpow
```

For the kernel:

```lean
greenKernel_integrable
greenKernelDeriv_integrable
greenKernel_l1_eq
greenKernelDeriv_l1_eq
```

or the corresponding resolver-kernel names in the repository.

The exact DCT theorem in Mathlib is:

```lean
MeasureTheory.tendsto_integral_of_dominated_convergence
```

### Chemotaxis flux vanishes

For a flux term such as

    Q = W^m V'

or

    W^m V' / (1+V)^beta,

we get

    W^m -> L^m
    V' -> 0
    V -> V_L

and the denominator tends to a positive number. Therefore

    Q -> 0.

If the stationary equation contains the derivative of the flux, use the repository-specific divergence-form algebra to identify the constant-state limit. For the root-pinning result, the needed final lemma should avoid exposing all flux derivatives:

```lean
lemma frozen_source_limit_at_constant
    (hW : Tendsto W atTop (nhds L))
    (hWp : Tendsto (deriv W) atTop (nhds 0))
    (hV : Tendsto V atTop (nhds V_L))
    (hVp : Tendsto (deriv V) atTop (nhds 0)) :
    Tendsto (fun x => R W V x) atTop
      (nhds (lambda*L + L*(a - b*L^alpha)))
```

or with whatever sign convention matches `frozenWaveOperator`.

The key requirement is that all chemotaxis contributions vanish at a constant state.

---

## Step 5. End limit satisfies the logistic root equation

For each end, combine:

1. W -> L.
2. W' -> 0.
3. resolver/flux convergence.
4. stationary equation.
5. derivative-limit lemma forcing the W'' limit to be zero.

Obtain:

    L (a - b L^alpha) = 0.

Since the lower pin gives L >= c1 > 0,

    L != 0.

Hence

    a - b L^alpha = 0.

Assuming a > 0, b > 0, alpha > 0, the positive root is unique:

    L = (a/b)^(1/alpha).

### Lean lemma shape

```lean
lemma positive_logistic_root_unique
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hLpos : 0 < L)
    (hroot : L * (a - b * L^alpha) = 0) :
    L = (a / b) ^ (1 / alpha)
```

Proof:

1. From hLpos and hroot, get a - b L^alpha = 0.
2. Therefore L^alpha = a/b.
3. Since both sides are positive and alpha > 0, apply rpow injectivity on positive reals or raise both sides to 1/alpha using rpow identities.

Useful Mathlib facts:

```lean
Real.rpow_pos_of_pos
Real.rpow_rpow
Real.rpow_eq_rpow
Real.rpow_left_injective_of_pos
```

If the exact injectivity lemma is inconvenient, make this a local arithmetic lemma and prove it once.

---

## Step 6. Equal end limits plus monotone implies constant

Once both limits satisfy the positive root equation, both are equal to

    Ustar = (a/b)^(1/alpha).

So

    L_minus = L_plus = Ustar.

For antitone W, every x satisfies

    L_plus <= W x <= L_minus.

Therefore W x = Ustar for all x.

### Lean lemma shape

```lean
lemma antitone_eq_const_of_equal_end_limits
    (hanti : Antitone W)
    (hTop : Tendsto W atTop (nhds L))
    (hBot : Tendsto W atBot (nhds L)) :
    forall x, W x = L
```

Proof: for fixed x, antitone implies values to the right are <= W x and values to the left are >= W x. Passing to limits gives

    L <= W x

from atTop and

    W x <= L

from atBot. Hence equality.

This can also be proved using the already-established formulas

    L_plus = inf range W
    L_minus = sup range W.

---

## Full named lemma chain

Recommended Lean-facing names:

```lean
antitone_bdd_has_limits_atTop_atBot
bounded_second_deriv_deriv_uniformContinuous
antitone_bdd_uniformContinuous_deriv_tendsto_zero_atTop
antitone_bdd_uniformContinuous_deriv_tendsto_zero_atBot
resolver_tendsto_const_atTop
resolver_tendsto_const_atBot
resolver_deriv_tendsto_zero_atTop
resolver_deriv_tendsto_zero_atBot
chemotaxis_flux_tendsto_zero_atTop
chemotaxis_flux_tendsto_zero_atBot
stationary_rhs_tendsto_limit_atTop
stationary_rhs_tendsto_limit_atBot
deriv_tendsto_zero_and_second_deriv_tendsto_const_forces_const_zero_atTop
deriv_tendsto_zero_and_second_deriv_tendsto_const_forces_const_zero_atBot
end_limit_satisfies_logistic_root_atTop
end_limit_satisfies_logistic_root_atBot
positive_logistic_root_unique
antitone_eq_const_of_equal_end_limits
monotone_stationary_root_pinning_constant
```

Final theorem shape:

```lean
theorem monotone_stationary_root_pinning_constant
    (htrap : InMonotoneWaveTrapSet ... W)
    (hlower : forall x, c1 <= W x)
    (hc1 : 0 < c1)
    (hC2 : ContDiff Real 2 W)
    (hWdd_bdd : exists B, forall x, abs (deriv (deriv W) x) <= B)
    (hstat : forall x, frozenWaveOperator p c W W x = 0)
    (hresolver : V = frozenElliptic p W)
    (hparams : 0 < a /\ 0 < b /\ 0 < alpha /\ 0 < mu /\ 0 <= nu) :
    forall x, W x = (a / b) ^ (1 / alpha)
```

The actual theorem should use the repository parameter structure instead of loose `a b alpha mu nu` variables.

---

## What secretly needs more than monotone + bounded + C2 + bounded W''?

The following steps require extra input beyond monotone + bounded + C2 + bounded W'':

1. **Resolver convergence at constant limits.** This uses the specific elliptic Green resolver and integrability of its kernel and derivative.
2. **Chemotaxis terms vanish at constant states.** This uses the exact formula of the chemotaxis source and the fact V' -> 0.
3. **Stationary equation algebra reduces to logistic root.** This uses the repository-specific definition of `frozenWaveOperator` and the shift parameter lambda.
4. **Uniqueness of the positive logistic root.** This uses a > 0, b > 0, alpha > 0 and positivity of the end limit.

The following do **not** require extra input:

1. Existence of end limits from monotone + bounded.
2. W' -> 0 from monotone + bounded + bounded W''.
3. Equality of W with a constant once both end limits agree.

The dangerous false shortcut is:

    monotone + bounded + C2 + bounded W'' implies W'' -> 0.

This is not true by itself. The correct proof obtains a finite limit for W'' from the stationary equation and resolver convergence, then proves that finite limit must be zero because W' -> 0.
