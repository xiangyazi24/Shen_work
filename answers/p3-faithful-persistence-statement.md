# Paper 3 Theorem 2.1: faithful persistence statement

## Executive verdict

The persistence theorem must be formalized in **liminf form**, not as a sharp eventual lower bound.

The faithful statement is of the shape

    liminf_{t -> infinity} inf_x u(t,x) >= theta,
    liminf_{t -> infinity} inf_x v(t,x) >= (nu / mu) * theta^gamma,

or in the qualitative first part,

    liminf_{t -> infinity} inf_x u(t,x) > 0,
    liminf_{t -> infinity} inf_x v(t,x)
      >= (nu / mu) * (liminf_{t -> infinity} inf_x u(t,x))^gamma > 0.

It is **not** the stronger assertion

    exists T, forall t >= T, inf_x u(t,x) >= theta.

That stronger sharp-eventual statement is false in general: a scalar function like

    z(t) = theta - exp(-t)

has `liminf z = theta`, but it is never eventually `>= theta`.

The correct eventual reformulation of `liminf >= theta` is the epsilon-loss version:

    forall eps > 0, exists T, forall t >= T,
      inf_x u(t,x) >= theta - eps.

So any Lean field currently requiring sharp eventual lower bound at the exact paper threshold should be weakened to a liminf statement, or to the equivalent eventual epsilon-loss statement.

## 1. What Paper 3 Theorem 2.1 states

For globally defined, bounded, positive classical solutions, Paper 3 Theorem 2.1 is a persistence theorem stated using `liminf`.

The theorem has several parts.  The relevant non-minimal positive-logistic parts are:

### Qualitative persistence

Assuming `m >= 1`, any globally defined bounded positive solution satisfies

    liminf_{t -> infinity} inf_x u(t,x) > 0,

and

    liminf_{t -> infinity} inf_x v(t,x)
      >= (nu / mu) * (liminf_{t -> infinity} inf_x u(t,x))^gamma > 0.

This is qualitative and does not display the sharp theta.

### Explicit m = 1 branch

Assume

    a > 0,
    b > 0,
    chi0 > 0,
    m = 1,
    beta >= 1,
    chi0 < a / (mu * Theta_{beta-1}).

Then

    liminf_{t -> infinity} inf_x u(t,x)
      >= ((a - chi0 * mu * Theta_{beta-1}) / b)^(1 / alpha),

and

    liminf_{t -> infinity} inf_x v(t,x)
      >= (nu / mu)
          * ((a - chi0 * mu * Theta_{beta-1}) / b)^(gamma / alpha).

Equivalently, with

    Cchi = chi0 * mu * Theta_{beta-1},
    theta = ((a - Cchi) / b)^(1 / alpha),

under `a > Cchi`, the statement is

    liminf inf u >= theta,
    liminf inf v >= (nu / mu) * theta^gamma.

This is the branch corresponding to the spatial-minimum Dini inequality with a linear loss term `Cchi * z`, because `m = 1`.

### Explicit m > 1 branch

Assume

    a > 0,
    b > 0,
    chi0 > 0,
    m > 1,
    beta >= 1.

Then the paper gives the lower bound

    theta_m = min(1, (a / (b + chi0 * mu * Theta_{beta-1}))^max(1/(m-1), 1/alpha)),

and

    liminf inf u >= theta_m,
    liminf inf v >= (nu / mu) * theta_m^gamma.

This branch does not need the strict `a > Cchi` condition, because the chemotaxis loss is higher order in the spatial minimum when `m > 1`.

### Minimal model branch

When `a = b = 0`, the theorem has a separate minimal-model statement under its own smallness assumptions.  It is not the same as the logistic `theta = ((a-Cchi)/b)^(1/alpha)` branch, since that expression is not meaningful when `b = 0`.

## 2. The chemotaxis loss constant

For the signal-dependent sensitivity

    chi(v) = chi0 / (1 + v)^beta,

with `chi0 > 0` and `beta >= 1`, the spatial-minimum estimate uses

    v / (1 + v)^beta <= Theta_{beta-1},

where

    Theta_s = s^s * (1+s)^(-(1+s))

with the convention `Theta_0 = 1`.

At a spatial minimum of u, the chemotaxis divergence term satisfies

    -d_x(u^m * chi(v) * v_x)
      >= -chi0 * mu * Theta_{beta-1} * z^m,

where

    z(t) = inf_x u(t,x).

Thus

    Cchi = chi0 * mu * Theta_{beta-1}.

For `m = 1`, the Dini inequality is

    D_+ z >= (a - Cchi) * z - b * z^(1 + alpha).

The positive threshold is therefore

    theta = ((a - Cchi) / b)^(1 / alpha),

and its positivity requires exactly

    a > Cchi,

equivalently

    chi0 < a / (mu * Theta_{beta-1}).

## 3. Is the theorem unconditional?

There are two different senses of unconditional.

### Qualitative part

The qualitative persistence part is stated for `m >= 1` for globally defined bounded positive solutions.  It is conditional on already having such a solution, but it does not require the explicit smallness condition `chi0 < a/(mu Theta)`.

### Explicit m = 1 threshold part

The explicit sharp lower-bound part is **not unconditional**.  It carries the hypotheses

    a > 0,
    b > 0,
    chi0 > 0,
    m = 1,
    beta >= 1,
    chi0 < a / (mu * Theta_{beta-1}).

Equivalently, it assumes

    a - chi0 * mu * Theta_{beta-1} > 0.

This smallness condition on the effective attractive sensitivity is part of the faithful theorem.  It should be an explicit Lean hypothesis.

### Explicit m > 1 threshold part

The displayed `m > 1` lower bound carries

    a > 0,
    b > 0,
    chi0 > 0,
    m > 1,
    beta >= 1,

but not the same `a > Cchi` condition.  The formula instead uses `b + Cchi` in the denominator and the exponent `max(1/(m-1), 1/alpha)`.

## 4. The v-component comparison

The v persistence follows from the u persistence by comparison for the v equation.

Consider the parabolic chemical equation

    v_t = d2 v_xx + nu u^gamma - mu v,

with Neumann boundary condition.

If

    liminf_{t -> infinity} inf_x u(t,x) >= theta,

then for every eps with `0 < eps < theta`, there exists T such that

    u(t,x) >= theta - eps

for all `t >= T` and all x.

Therefore for `t >= T`,

    v_t - d2 v_xx + mu v >= nu * (theta - eps)^gamma.

Let y solve the scalar ODE

    y' + mu y = nu * (theta - eps)^gamma,
    y(T) = min_x v(T,x).

By the parabolic comparison principle with Neumann boundary conditions,

    v(t,x) >= y(t)

for all `t >= T`.  Since

    y(t) -> (nu / mu) * (theta - eps)^gamma,

we get

    liminf_{t -> infinity} inf_x v(t,x)
      >= (nu / mu) * (theta - eps)^gamma.

Letting `eps -> 0+` gives

    liminf_{t -> infinity} inf_x v(t,x)
      >= (nu / mu) * theta^gamma.

For the elliptic chemical equation

    -d2 v_xx + mu v = nu u^gamma,

the argument is even simpler.  Once `u(t,x) >= theta - eps`, the constant

    (nu / mu) * (theta - eps)^gamma

is a subsolution of the elliptic equation, and elliptic comparison gives

    v(t,x) >= (nu / mu) * (theta - eps)^gamma.

Again let `eps -> 0+`.

## 5. Lean-faithful Prop shapes

The current over-strong shape

    exists T, forall t >= T, theta <= infValue (u t)

should be replaced.  Use one of the following two equivalent forms.

### Preferred liminf form

    def EventuallyLiminfLowerBound
        (D : BoundedDomainData) (u : R -> D.Point -> R) (theta : R) : Prop :=
      theta <= Filter.liminf (fun t => D.infValue (u t)) Filter.atTop

Then the m = 1 explicit branch should be shaped as:

    def UniformPersistencePart2LiminfRaw
        (D : BoundedDomainData) (p : CM2Params) : Prop :=
      0 < p.a -> 0 < p.b -> 0 < p.chi0 -> p.m = 1 -> 1 <= p.beta ->
      p.chi0 < p.a / (p.mu * Theta_beta (p.beta - 1)) ->
        forall u v,
          PositiveGlobalBoundedSolution D p u v ->
            let theta := ((p.a - p.chi0 * p.mu * Theta_beta (p.beta - 1)) / p.b)^(1 / p.alpha)
            EventuallyLiminfLowerBound D u theta and
            EventuallyLiminfLowerBound D v (p.nu / p.mu * theta^p.gamma)

Use actual field names from the repo, e.g. `p.χ₀`, `p.μ`, `p.ν`, if working in Lean source.  This markdown uses ASCII names for readability.

### Equivalent epsilon-eventual form

This form avoids direct dependence on `Filter.liminf` API:

    def LiminfLowerBoundEps
        (D : BoundedDomainData) (u : R -> D.Point -> R) (theta : R) : Prop :=
      forall eps > 0,
        forallᶠ t in Filter.atTop,
          theta - eps <= D.infValue (u t)

Then the same branch becomes:

    def UniformPersistencePart2EpsRaw
        (D : BoundedDomainData) (p : CM2Params) : Prop :=
      0 < p.a -> 0 < p.b -> 0 < p.chi0 -> p.m = 1 -> 1 <= p.beta ->
      p.chi0 < p.a / (p.mu * Theta_beta (p.beta - 1)) ->
        forall u v,
          PositiveGlobalBoundedSolution D p u v ->
            let theta := ((p.a - p.chi0 * p.mu * Theta_beta (p.beta - 1)) / p.b)^(1 / p.alpha)
            LiminfLowerBoundEps D u theta and
            LiminfLowerBoundEps D v (p.nu / p.mu * theta^p.gamma)

This is often the easiest form for proofs, because the Dini scalar comparison naturally gives eventual lower bounds with an arbitrary epsilon loss.

### Do not use sharp eventual form

Avoid:

    def EventuallyLowerBoundAtSharpTheta ... :=
      exists T, forall t >= T, theta <= D.infValue (u t)

or

    forallᶠ t in atTop, theta <= D.infValue (u t)

at the exact theta.  That is stronger than the paper's liminf statement and is not implied by the scalar Dini comparison at the sharp equilibrium.

## 6. Faithful theorem summary

For the m = 1 branch, the faithful Lean statement is:

    hypotheses:
      a > 0,
      b > 0,
      chi0 > 0,
      m = 1,
      beta >= 1,
      chi0 < a / (mu * Theta_{beta-1}),
      (u,v) is a globally defined bounded positive classical solution.

    define:
      Cchi = chi0 * mu * Theta_{beta-1},
      theta = ((a - Cchi) / b)^(1/alpha).

    conclusion:
      theta <= liminf_{t -> infinity} inf_x u(t,x),
      (nu/mu) * theta^gamma <= liminf_{t -> infinity} inf_x v(t,x).

Equivalently, for every eps > 0, eventually

    inf_x u(t,x) >= theta - eps,

and for every eps > 0, eventually

    inf_x v(t,x) >= (nu/mu) * theta^gamma - eps.

When proving the v part from u, it is cleaner to use the stronger intermediate statement: for every eps with `0 < eps < theta`, eventually

    inf_x v(t,x) >= (nu/mu) * (theta - eps)^gamma,

and then pass eps to zero.
