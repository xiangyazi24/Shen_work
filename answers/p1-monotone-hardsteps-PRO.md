# P1 monotone stationary root-pinning: hard steps, Lean-ready

## Executive verdict

The monotone root-pinning proof is sound, but two points must be handled carefully.

1. **Derivative vanishing at infinity.** From `W` antitone, bounded, `C^2`, and bounded `W''`, one can prove `W'(x) -> 0` as `x -> +infty` and as `x -> -infty`. This is a Barbalat-type lemma. Mathlib v4.29.1 should not be assumed to contain Barbalat as a ready theorem; prove a local lemma. The cleanest formal proof avoids improper integrals and uses a fixed-drop contradiction: if `W'` is bounded away from zero at arbitrarily large points, bounded `W''` gives fixed-width intervals on which `W'` remains bounded away from zero, and monotonicity forces infinitely many fixed drops of `W`, contradicting the lower bound.

2. **Resolver at a constant limit.** If `W(x) -> L` at an end, then the whole-line elliptic response satisfies `V[W](x) -> (nu/mu) * L^gamma` and `V'[W](x) -> 0`. This is not a consequence of monotonicity alone. It uses the specific whole-line elliptic resolver, preferably its Green-kernel convolution representation. The proof is dominated convergence against the integrable Green kernel and its derivative.

After these two inputs, the root-pinning chain is complete: limits exist, `W' -> 0`, resolver and flux terms have constant-state limits, the stationary equation gives a finite limit for `W''`, this finite limit must be zero because `W' -> 0`, the end limit solves `L * (1 - L^alpha) = 0`, the lower pin gives `L > 0`, hence `L = 1`, and equal end limits squeeze the antitone profile to `W == 1`.

The important false shortcut to avoid is: monotone + bounded + C2 + bounded `W''` does **not** by itself imply `W'' -> 0`. Instead, first derive that `W''` has a finite end limit from the stationary equation and resolver convergence, then prove that this finite limit is zero because `W' -> 0`.

---

## Standing hypotheses and notation

The stationary equation is

```text
W'' + c * W' - lambda * W + R(W,V[W]) = 0
```

with `c > 0`, `lambda > 0`, and normalized logistic equilibrium `U_- = 1`. The trap gives:

```lean
hanti    : Antitone W
hlower   : forall x, c1 <= W x
hupper   : forall x, W x <= C2
hc1      : 0 < c1
hC2      : ContDiff R 2 W
hWdd_bdd : exists B, 0 <= B /\ forall x, abs (deriv (deriv W) x) <= B
hstat    : forall x, frozenWaveOperator p c W W x = 0
```

Use the repository's exact operator definitions to rewrite `hstat` into the scalar ODE. The algebraic limit should reduce to

```text
L * (1 - L^alpha) = 0
```

or, in unnormalized variables,

```text
L * (a - b * L^alpha) = 0.
```

---

# A. Derivative vanishing at infinity

## A1. Monotone bounded functions have end limits

### Lemma statement

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

For an antitone `W`, define

```text
Lp = sInf (Set.range W)
Lm = sSup (Set.range W)
```

Then `W -> Lp` at `atTop` and `W -> Lm` at `atBot`.

### Proof outline

For `atTop`, fix `eps > 0`. Since `Lp` is the infimum of the range, choose `x0` with `W x0 < Lp + eps`. For `y >= x0`, antitonicity gives `W y <= W x0 < Lp + eps`. Also `Lp <= W y`. Thus `abs (W y - Lp) < eps`.

For `atBot`, either repeat with `sSup` or apply the atTop result to `fun x => W (-x)`.

### Mathlib pieces

Use:

```lean
Antitone
Filter.Tendsto
Filter.atTop
Filter.atBot
sInf
sSup
Set.range
```

If existing monotone-convergence lemmas do not match exactly, prove this locally by epsilon arguments and the defining properties of `sInf` and `sSup` for a bounded set in `R`.

---

## A2. Bounded second derivative gives uniform continuity of the derivative

### Lemma statement

```lean
lemma bounded_second_deriv_lipschitz_deriv
    {W : R -> R} {B : R}
    (hC2 : ContDiff R 2 W)
    (hBnonneg : 0 <= B)
    (hB : forall x, abs (deriv (deriv W) x) <= B) :
    LipschitzWith (Real.toNNReal B) (deriv W)
```

A weaker version is enough:

```lean
lemma bounded_second_deriv_uniformContinuous_deriv
    (hC2 : ContDiff R 2 W)
    (hB : exists B, 0 <= B /\ forall x, abs (deriv (deriv W) x) <= B) :
    UniformContinuous (deriv W)
```

### Proof outline

Use the mean-value inequality. If `abs ((deriv W)' x) <= B` for all `x`, then

```text
abs (deriv W x - deriv W y) <= B * abs (x - y).
```

### Mathlib pieces

Possible useful lemmas:

```lean
Convex.lipschitzOnWith_of_nnnorm_deriv_le
Convex.norm_image_sub_le_of_norm_deriv_le_segment
LipschitzWith.uniformContinuous
```

If these are hard to apply globally, prove a one-dimensional local mean-value inequality on `Icc x y` using the interval mean value theorem, then generalize by `min x y` / `max x y`.

---

## A3. Derivative sign from antitonicity

### Lemma statement

```lean
lemma deriv_nonpos_of_antitone
    (hanti : Antitone W)
    (hdiff : forall x, DifferentiableAt R W x) :
    forall x, deriv W x <= 0
```

### Proof outline

For `h > 0`, antitonicity gives

```text
(W (x+h) - W x) / h <= 0.
```

Pass to the right-derivative limit. Since the derivative exists, the full derivative equals the right derivative. If Mathlib has a monotone derivative sign lemma, use it; otherwise this is a small local lemma.

This sign lemma is useful, but the fixed-drop proof below can also be written directly using interval FTC and the negative derivative intervals.

---

## A4. Barbalat lemma / derivative decay

Mathlib should not be assumed to have a theorem named Barbalat. Prove the needed version locally.

### General Barbalat version

```lean
lemma barbalat_atTop_nonneg
    {f : R -> R}
    (hf_uc : UniformContinuous f)
    (hf_nonneg : forall x, 0 <= f x)
    (hf_integrable_tail : IntegrableOn f (Set.Ioi A)) :
    Tendsto f atTop (nhds 0)
```

Proof by contradiction: if not, there are `eps > 0` and points `x_n -> +infty` with `f x_n >= eps`. Uniform continuity gives a fixed `rho > 0` such that `f >= eps/2` on intervals around each `x_n`. Choose disjoint intervals in the tail. Their integrals give infinitely many fixed positive contributions, contradicting integrability.

### Specialized fixed-drop lemma for monotone profiles

This is the recommended Lean route because it avoids developing an improper-integral API.

```lean
lemma antitone_bdd_bounded_second_deriv_deriv_tendsto_zero_atTop
    {W : R -> R}
    (hC2 : ContDiff R 2 W)
    (hanti : Antitone W)
    (hlb : exists m, forall x, m <= W x)
    (hub : exists M, forall x, W x <= M)
    (hWdd_bdd : exists B, 0 <= B /\ forall x, abs (deriv (deriv W) x) <= B) :
    Tendsto (deriv W) atTop (nhds 0)
```

Symmetric atBot version:

```lean
lemma antitone_bdd_bounded_second_deriv_deriv_tendsto_zero_atBot
    ... :
    Tendsto (deriv W) atBot (nhds 0)
```

### Fixed-drop proof details

Assume atTop convergence fails. Since `deriv W <= 0`, there exists `eps > 0` such that for every large `X`, some `x >= X` satisfies

```text
deriv W x <= -eps.
```

Let `B` bound `abs W''`. If `B = 0`, then `deriv W` is constant; boundedness of `W` forces that constant to be zero. If `B > 0`, set

```text
rho = eps / (2*B).
```

The Lipschitz estimate for `deriv W` gives, for `y in [x, x+rho]`,

```text
deriv W y <= -eps/2.
```

By interval FTC,

```text
W (x+rho) - W x = int t in x..x+rho, deriv W t <= -(eps/2)*rho.
```

Now recursively pick `N` disjoint intervals far to the right. Each causes a drop at least `(eps/2)*rho`. For `N` so large that

```text
N * (eps/2) * rho > upper_bound - lower_bound,
```

this contradicts `lower_bound <= W <= upper_bound`.

### Mathlib pieces

Use:

```lean
Filter.Tendsto
Filter.atTop
Filter.atBot
ContDiff
HasDerivAt
DifferentiableAt
LipschitzWith
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

For the finite drop contradiction, it is useful to prove a helper lemma:

```lean
lemma derivative_le_negative_on_interval_forces_drop
    (hderiv : forall y in Set.Icc x (x+rho), HasDerivAt W (Wp y) y)
    (hneg : forall y in Set.Icc x (x+rho), Wp y <= -eta)
    (hrho : 0 <= rho) :
    W (x+rho) <= W x - eta * rho
```

Then another helper builds finitely many disjoint intervals and sums the drops.

---

# B. Resolver at a constant end limit

## B1. This step uses the specific resolver

The statement is clean for the whole-line convolution/Green resolver. It is not a consequence of monotone boundedness alone.

Assume normalized elliptic equation

```text
-V'' + mu * V = nu * W^gamma
```

with bounded whole-line solution represented as

```text
V(x) = nu * int z, Gmu z * W(x-z)^gamma
```

where

```text
Gmu(z) = (1 / (2 * sqrt mu)) * exp(-sqrt(mu) * abs z)
int Gmu = 1 / mu.
```

Then for constant source `W == L`,

```text
V_L = (nu / mu) * L^gamma.
```

For the derivative:

```text
V'(x) = nu * int z, GmuDeriv z * W(x-z)^gamma
```

and

```text
int GmuDeriv = 0.
```

---

## B2. Resolver value tends to the constant response

### Lemma statement

```lean
lemma elliptic_resolver_tendsto_const_atTop
    {W V : R -> R} {L : R}
    (hW_lim : Tendsto W atTop (nhds L))
    (hW_nonneg : forall x, 0 <= W x)
    (hW_bdd : exists M, forall x, W x <= M)
    (hgamma_pos : 0 < gamma)
    (hV_green : forall x,
      V x = nu * int z, Gmu z * (W (x - z))^gamma)
    (hG_int : Integrable Gmu)
    (hG_mass : int z, Gmu z = 1 / mu)
    (hmu : 0 < mu) :
    Tendsto V atTop (nhds ((nu / mu) * L^gamma))
```

### Proof

Rewrite:

```text
V x - (nu/mu)*L^gamma
  = nu * int z, Gmu z * (W (x-z)^gamma - L^gamma).
```

For each fixed `z`, `x-z -> +infty` as `x -> +infty`, so

```text
W (x-z)^gamma -> L^gamma.
```

Boundedness gives a domination:

```text
abs (Gmu z * (W (x-z)^gamma - L^gamma)) <= abs (Gmu z) * C
```

with `C` depending on the bound for W and L. Since `Gmu` is integrable, dominated convergence applies.

### Mathlib pieces

Use:

```lean
MeasureTheory.tendsto_integral_of_dominated_convergence
Integrable
Filter.Tendsto.comp
Tendsto.const_sub
Tendsto.sub_const
Tendsto.rpow_const
Real.rpow_nonneg
```

If `Tendsto.rpow_const` is awkward, prove a local composition lemma using continuity of `fun y => y^gamma` on the positive/bounded range. The lower pin makes this easier because the limit and eventually the profile stay positive.

---

## B3. Resolver derivative tends to zero

### Lemma statement

```lean
lemma elliptic_resolver_deriv_tendsto_zero_atTop
    {W V : R -> R} {L : R}
    (hW_lim : Tendsto W atTop (nhds L))
    (hW_nonneg : forall x, 0 <= W x)
    (hW_bdd : exists M, forall x, W x <= M)
    (hgamma_pos : 0 < gamma)
    (hV_deriv_green : forall x,
      deriv V x = nu * int z, GmuDeriv z * (W (x - z))^gamma)
    (hGd_int : Integrable GmuDeriv)
    (hGd_mass_zero : int z, GmuDeriv z = 0) :
    Tendsto (deriv V) atTop (nhds 0)
```

### Proof

Use the zero-mass identity:

```text
V'(x) = nu * int z, GmuDeriv z * (W (x-z)^gamma - L^gamma).
```

For each fixed `z`, the bracket tends to zero. Dominate by `abs GmuDeriv z * C`. Apply dominated convergence.

The atBot version is identical, using `x-z -> -infty`.

---

## B4. Chemotaxis flux terms vanish

Typical flux factors have the form

```text
W^m * V'
```

or

```text
W^m * V' / (1 + V)^beta.
```

From

```text
W -> L
V -> V_L
V' -> 0
```

and denominator positivity,

```text
W^m * V' / (1 + V)^beta -> 0.
```

Lean lemma:

```lean
lemma chemotaxis_flux_tendsto_zero_atTop
    (hW : Tendsto W atTop (nhds L))
    (hV : Tendsto V atTop (nhds VL))
    (hVp : Tendsto (deriv V) atTop (nhds 0))
    (hden : 0 < 1 + VL) :
    Tendsto (fun x => W x^m * deriv V x / (1 + V x)^beta)
      atTop (nhds 0)
```

Use:

```lean
Tendsto.mul
Tendsto.div
Tendsto.rpow_const
```

If the operator contains a derivative of the flux, do not infer its limit merely from flux -> 0. Instead prove a repository-specific source-limit lemma by unfolding `frozenWaveOperator`:

```lean
lemma frozen_source_tendsto_constant_state_atTop
    ... :
    Tendsto (fun x => R(W,V) x) atTop
      (nhds <constant_state_source L>)
```

This is the one lemma that should encode that all chemotaxis contributions vanish at constant states.

---

# C. Passing the ODE to the limit

## C1. Finite W'' limit from the equation

From

```text
W'' = -c*W' + lambda*W - R(W,V)
```

and the limits

```text
W -> L
W' -> 0
R(W,V) -> R_const(L)
```

obtain

```text
W'' -> A := lambda*L - R_const(L).
```

Do not assume `W'' -> 0` before this.

## C2. If f -> 0 and f' -> A, then A = 0

Apply this to `f = W'` and `f' = W''`.

```lean
lemma tendsto_zero_and_deriv_tendsto_const_forces_const_zero_atTop
    {f fp : R -> R} {A : R}
    (hf : Tendsto f atTop (nhds 0))
    (hfp : Tendsto fp atTop (nhds A))
    (hderiv : forall x, HasDerivAt f (fp x) x) :
    A = 0
```

Proof: if `A > 0`, then eventually `fp >= A/2`; by interval FTC, `f` grows at least linearly on long intervals, contradicting `f -> 0`. If `A < 0`, similarly. Hence `A = 0`.

Mathlib pieces:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
Filter.Tendsto
Eventually
```

At atBot, use reflection or prove the symmetric lemma.

## C3. Limit equation and root

Combining C1 and C2 gives:

```text
lambda*L - R_const(L) = 0.
```

After the constant-state algebra of the shifted equation and vanishing chemotaxis terms, this becomes:

```text
L * (1 - L^alpha) = 0.
```

Package this as:

```lean
lemma end_limit_satisfies_logistic_root_atTop
    (hlimW : Tendsto W atTop (nhds L))
    (hlimWp : Tendsto (deriv W) atTop (nhds 0))
    (hresolver : resolver_limit_data_atTop W V L)
    (hstat : forall x, frozenWaveOperator p c W W x = 0) :
    L * (1 - L^p.alpha) = 0
```

and similarly at atBot.

---

# D. Root selection and squeeze

## D1. Positive logistic root equals one

With `L >= c1 > 0`, the zero root is impossible. In normalized variables:

```lean
lemma positive_root_one_of_logistic_root
    (halpha : 0 < alpha)
    (hLpos : 0 < L)
    (hroot : L * (1 - L^alpha) = 0) :
    L = 1
```

In unnormalized variables:

```lean
lemma positive_logistic_root_unique
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hLpos : 0 < L)
    (hroot : L * (a - b * L^alpha) = 0) :
    L = (a / b)^(1 / alpha)
```

Use positivity and rpow injectivity on positive reals. If Mathlib's exact injectivity lemma is awkward, prove this as a local arithmetic lemma.

## D2. Equal end limits force a monotone function to be constant

```lean
lemma antitone_eq_const_of_equal_end_limits
    (hanti : Antitone W)
    (hTop : Tendsto W atTop (nhds L))
    (hBot : Tendsto W atBot (nhds L)) :
    forall x, W x = L
```

Proof: for fixed `x`, antitonicity gives for `y >= x`, `W y <= W x`; taking `y -> +infty` gives `L <= W x`. For `y <= x`, `W x <= W y`; taking `y -> -infty` gives `W x <= L`. Hence equality.

---

# E. Final theorem chain

Recommended final theorem:

```lean
theorem monotone_stationary_root_pinning_constant
    (htrap : InMonotoneWaveTrapSet ... W)
    (hlower : forall x, c1 <= W x)
    (hc1 : 0 < c1)
    (hC2 : ContDiff R 2 W)
    (hWdd_bdd : exists B, 0 <= B /\ forall x,
      abs (deriv (deriv W) x) <= B)
    (hstat : forall x, frozenWaveOperator p c W W x = 0)
    (hresolverGreen : ResolverGreenRepresentation p W V)
    (hparams : parameter_positivity p) :
    forall x, W x = 1
```

Internal chain:

1. `antitone_bdd_has_limits_atTop_atBot` gives limits `L_plus`, `L_minus`.
2. `antitone_bdd_bounded_second_deriv_deriv_tendsto_zero_atTop` gives `W' -> 0` at `+infty`.
3. AtBot version gives `W' -> 0` at `-infty`.
4. Resolver value and derivative convergence give `V -> V[L]` and `V' -> 0` at both ends.
5. Constant-state source lemma plus stationary equation gives finite limits for `W''`.
6. `tendsto_zero_and_deriv_tendsto_const_forces_const_zero_atTop/atBot` forces those `W''` limits to be zero.
7. The limit equation reduces to `L * (1 - L^alpha) = 0` at both ends.
8. The lower pin gives both limits positive, so both equal `1`.
9. Equal end limits plus antitone imply `W == 1`.

---

# F. Gap audit

The derivative-vanishing step needs only:

```text
antitone + bounded + C1 + uniformly continuous derivative.
```

Bounded `W''` is a sufficient hypothesis for uniform continuity of `W'`.

The resolver-at-constant-limit step needs more than monotonicity. It requires the specific elliptic resolver representation or an equivalent theorem. In practice, use the Green-kernel convolution plus dominated convergence. This step also needs boundedness of `W`, positivity/nonnegativity for `rpow`, and integrability of the Green kernel and its derivative.

The reduction to the reaction root needs repository-specific algebra: the definition of `frozenWaveOperator`, the lambda shift, and the fact that chemotaxis terms vanish at constant states.

The proof is gap-free once these resolver and algebra lemmas are supplied. The one invalid shortcut to avoid is claiming `W'' -> 0` directly from monotone + bounded + C2 + bounded `W''`; instead, get a finite `W''` limit from the equation and then force it to be zero from `W' -> 0`.
