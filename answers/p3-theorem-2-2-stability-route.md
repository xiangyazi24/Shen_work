# Paper 3 Theorem 2.2: stability route for Lean formalization

## Executive verdict

For the Paper 3 stability theorem, separate three statements that are often conflated.

1. **Theorem 2.2 in the paper is the local spectral-stability theorem.**  It says that the positive constant equilibrium is locally exponentially stable when the sensitivity is below the critical linear threshold, and linearly unstable when it is above that threshold.  This is a small-data theorem.

2. **Global convergence is a different theorem.**  It needs stronger hypotheses such as negative sensitivity, sufficiently weak chemotaxis, sufficiently strong logistic damping, or a Lyapunov/rectangle condition.  Do not formalize Theorem 2.2 as unconditional global attraction unless the paper explicitly states that form.

3. **The most Lean-friendly route for Theorem 2.2 is the spectral-gap plus Duhamel small-data route**, not the global entropy route.  A Lyapunov functional is useful for later global-stability theorems, but it is not the minimal faithful proof of Theorem 2.2.

Thus the faithful theorem to formalize is:

    If chi is below the critical per-mode threshold chi*, then there are eps, C, eta > 0 such that
    initial data within eps of (u*,v*) generate a global solution and
    ||u(t)-u*||_{C1} + ||v(t)-v*||_{C1} <= C exp(-eta t).

The nonlinear part is handled by a small-data Duhamel contraction or sectorial perturbation theorem.

## 1. Expected precise form of Theorem 2.2

### Positive equilibrium

For the non-minimal model with a,b > 0,

    u* = (a / b)^(1 / alpha),
    v* = (nu / mu) * (u*)^gamma.

For a bounded interval [0,L] with Neumann boundary conditions,

    lambda_k = (k*pi/L)^2,     k = 0,1,2,...

and lambda_0 = 0.

### Parabolic-elliptic chemical

For the elliptic chemical

    -d2 v_xx + mu v = nu u^gamma,

linearizing around (u*,v*) gives the resolver

    vhat_k = (nu * gamma * (u*)^(gamma-1) / (mu + d2*lambda_k)) * uhat_k.

For the model

    u_t = d1 u_xx - chi * d_x(u * v_x) + u(a - b u^alpha),

that is, the m = 1 constant-sensitivity model, the k-th scalar eigenvalue is

    sigma_k = -(d1*lambda_k + alpha*a)
              + chi * nu * gamma * (u*)^gamma
                * lambda_k / (mu + d2*lambda_k).

For the more general term u^m * chi0/(1+v)^beta, replace the chemotaxis coefficient by

    chi0 * nu * gamma * (u*)^(m+gamma-1) / (1+v*)^beta.

So in the general paper-style case,

    sigma_k = -(d1*lambda_k + alpha*a)
              + chi0 * nu * gamma * (u*)^(m+gamma-1)
                * lambda_k / ((1+v*)^beta * (mu + d2*lambda_k)).

There is no extra factor m in the linearization, because v* is spatially constant and therefore the term coming from differentiating u^m multiplies grad v* = 0.

The zero mode is always stable in the non-minimal model:

    sigma_0 = -alpha*a < 0.

### Critical threshold

For k >= 1, stability of the k-th mode is equivalent to

    chi0 < ((1+v*)^beta * (d1*lambda_k + alpha*a) * (mu + d2*lambda_k))
            / (nu * gamma * (u*)^(m+gamma-1) * lambda_k).

Therefore

    chi* = inf_{k >= 1}
      ((1+v*)^beta * (d1*lambda_k + alpha*a) * (mu + d2*lambda_k))
       / (nu * gamma * (u*)^(m+gamma-1) * lambda_k).

Theorem 2.2 local stability is the condition

    chi0 < chi*.

Linearly unstable means that some mode satisfies sigma_k > 0, equivalently chi0 is above at least one per-mode threshold.

### Parabolic-parabolic chemical

For

    v_t = d2 v_xx + nu u^gamma - mu v,

linearization on mode k gives the 2 by 2 matrix

    [ -(d1*lambda_k + alpha*a)       chi * u* * lambda_k ]
    [  nu*gamma*(u*)^(gamma-1)      -(d2*lambda_k + mu)  ]

for the m = 1 constant-sensitivity model.  In the general u^m/(1+v)^beta model, replace chi*u* by chi0*(u*)^m/(1+v*)^beta.

The trace is always negative:

    -((d1+d2)*lambda_k + alpha*a + mu) < 0.

The determinant condition is

    (d1*lambda_k + alpha*a)*(d2*lambda_k + mu)
      - chi0 * nu * gamma * (u*)^(m+gamma-1) * lambda_k / (1+v*)^beta > 0.

This gives the same per-mode threshold as the elliptic case, with d2*lambda_k + mu in the denominator after rearrangement.

## 2. Binding mode and sharp spectral condition

The threshold depends on

    g(lambda) = ((d1*lambda + alpha*a) * (mu + d2*lambda)) / lambda
              = d1*d2*lambda + (alpha*a*mu)/lambda + (d1*mu + alpha*a*d2).

This function is U-shaped on lambda > 0.  Its continuous minimizer is

    lambda_* = sqrt(alpha*a*mu / (d1*d2)).

The binding discrete mode is the k >= 1 for which lambda_k is nearest to lambda_* in the metric determined by g.

Adjacent-mode comparison:

    g(lambda_{k+1}) - g(lambda_k)
      = (lambda_{k+1} - lambda_k)
        * (d1*d2 - alpha*a*mu/(lambda_k*lambda_{k+1})).

Hence the minimizer occurs at the transition where

    lambda_{k-1}*lambda_k <= alpha*a*mu/(d1*d2) <= lambda_k*lambda_{k+1}.

The first nonzero mode binds if

    alpha*a*mu <= d1*d2*lambda_1^2.

On [0,L], lambda_1 = (pi/L)^2, so the first-mode-dominant condition is

    alpha*a*mu <= d1*d2*(pi/L)^4.

Under first-mode dominance,

    chi* = ((1+v*)^beta * (d1*lambda_1 + alpha*a) * (mu + d2*lambda_1))
            / (nu * gamma * (u*)^(m+gamma-1) * lambda_1).

Without this condition, do not hard-code k = 1.  Use the infimum over all nonzero Neumann modes.

## 3. Route for local exponential stability

The clean route is:

1. spectral threshold gives a positive gap:

       a_k = -sigma_k >= delta > 0

   for every relevant mode k;

2. the linear semigroup satisfies fractional smoothing:

       ||A^sigma e^{-tA}|| <= M_sigma * t^(-sigma) * exp(-omega*t),

   with omega less than or equal to the gap, usually omega = delta/2;

3. in the fractional space D(A^sigma), sigma in (1/2,1), the nonlinear remainder is quadratic:

       ||N(z)-N(w)|| <= K*(||z||_sigma + ||w||_sigma)*||z-w||_sigma;

4. solve the integrated Duhamel equation by contraction in

       sup_{t >= 0} exp(theta*t) ||z(t)||_sigma;

5. upgrade the mild solution to the classical solution and convert the fractional norm decay to C1 decay for u and v.

This is the most faithful route for Theorem 2.2.

The abstract fixed point is:

    z(t) = e^{-tA} z0 - integral_0^t e^{-(t-s)A} N(z(s)) ds.

Use theta with 0 < theta < omega and

    I_{sigma,omega,theta} = integral_0^infty tau^(-sigma) exp(-(omega-theta)*tau) dtau < infinity.

If

    ||e^{-tA}z0||_sigma <= M0 exp(-omega*t)||z0||_sigma

and

    ||A^sigma e^{-tA}f|| <= M_sigma t^(-sigma) exp(-omega*t)||f||,

then the Duhamel map is a contraction on the ball of radius r provided

    2*M_sigma*K*r*I_{sigma,omega,theta} <= 1/2.

A convenient initial-data threshold is

    eps = min { r/(2*M0), 1/(8*M0*M_sigma*K*I_{sigma,omega,theta}) }.

This yields global existence and exponential decay for ||z0||_sigma <= eps.

## 4. Lyapunov route and what it proves

A Lyapunov functional is the natural route for global convergence theorems, not the minimal route for Theorem 2.2 local stability.  It is still useful to know the correct structure.

For the m = 1 constant-sensitivity parabolic-parabolic system, a standard candidate is

    E(t) = integral [u - u* - u* log(u/u*)]
           + eta/2 * integral (v - v*)^2.

For the elliptic chemical, replace the chemical part by an elliptic energy such as

    eta/2 * integral (d2 |v_x|^2 + mu (v-v*)^2),

or eliminate v by the elliptic resolver and estimate the chemotactic term directly.

The entropy part is well-defined once u is bounded below away from zero.  This is why persistence is useful for global Lyapunov arguments.

Let the eventual bounds be

    theta <= u(t,x) <= M.

Define the power Lipschitz and monotonicity constants on [theta,M]:

    L_gamma = gamma * max(theta^(gamma-1), M^(gamma-1)),
    c_alpha = alpha * min(theta^(alpha-1), M^(alpha-1)).

Then

    (u^alpha - u*^alpha)(u-u*) >= c_alpha * |u-u*|^2,

and the logistic entropy production controls

    b*c_alpha * ||u-u*||_2^2.

For the entropy derivative, the diffusion term gives

    -d1*u* * integral |u_x|^2/u^2.

The chemotaxis term gives a cross term of the form

    chi*u* * integral (u_x/u) * v_x.

Young's inequality gives, for any epsilon in (0,1),

    |chi|*u* * integral |u_x/u| |v_x|
      <= epsilon*d1*u* * integral |u_x|^2/u^2
         + (chi^2*u*)/(4*epsilon*d1) * integral |v_x|^2.

For the parabolic v-energy,

    eta/2 d/dt ||v-v*||_2^2
      = -eta*d2 ||v_x||_2^2 - eta*mu ||v-v*||_2^2
        + eta*nu integral (u^gamma-u*^gamma)(v-v*).

Using the Lipschitz bound for u^gamma and Young's inequality,

    eta*nu integral |u^gamma-u*^gamma| |v-v*|
      <= (k_u/2)||u-u*||_2^2
         + (eta^2*nu^2*L_gamma^2)/(2*k_u) ||v-v*||_2^2,

where k_u can be chosen below b*c_alpha.

Thus a concrete sufficient entropy-coercivity condition is: there exist eta > 0 and epsilon in (0,1) such that

    eta*d2 > (chi^2*u*)/(4*epsilon*d1),

and

    eta*mu > (eta^2*nu^2*L_gamma^2)/(2*k_u),

with 0 < k_u < b*c_alpha.  Equivalently, one sufficient smallness condition is that the interval

    (chi^2*u*)/(4*epsilon*d1*d2) < eta < (2*k_u*mu)/(nu^2*L_gamma^2)

is nonempty for some epsilon in (0,1).  A simpler but rough sufficient condition is

    chi^2 < 8*epsilon*d1*d2*k_u*mu / (u*nu^2*L_gamma^2)

for some epsilon in (0,1).

This gives

    E'(t) <= -kappa_u ||u-u*||_2^2
             -kappa_v ||v-v*||_{H1-like}^2.

The constants are not meant to be sharp.  They are a Lean-friendly sufficient condition.  If the paper states a sharper condition, formalize the paper condition, not this rough one.

## 5. Logical dependency chain for the Lyapunov route

For global convergence by entropy, the dependency chain is:

1. Persistence theorem:

       liminf_t inf_x u(t,x) >= theta > 0.

2. Eventual boundedness above:

       u(t,x) <= M for t large.

3. Entropy well-defined and equivalent to L2 distance on [theta,M]:

       c1 ||u-u*||_2^2 <= integral [u-u* - u* log(u/u*)] <= c2 ||u-u*||_2^2.

4. Differential entropy inequality:

       E'(t) <= -D(t),

   with D controlling the desired norms.

5. Coercive version under the smallness condition:

       E'(t) <= -kappa E(t),

   which gives exponential convergence by Gronwall.

6. If only E' <= -D and D is integrable, use Barbalat/LaSalle plus compactness to get convergence.  This is weaker and harder in Lean than the coercive Gronwall route.

Persistence is therefore a prerequisite for the global entropy route, because it supplies the positive floor needed for the logarithmic entropy and for the uniform power estimates.  Persistence is not a prerequisite for local Theorem 2.2: small initial data around u* already gives a positive lower bound, and the sectorial small-data theorem keeps the solution in a small positive neighborhood.

## 6. Faithfulness warning

Do not state Theorem 2.2 as unconditional global attraction unless the paper explicitly does so.  The faithful split is:

- Theorem 2.2: local exponential stability below the linear critical sensitivity, and instability above it.
- Later global theorems: global convergence under extra structural assumptions such as negative sensitivity, weak chemotaxis, strong logistic damping, or a Lyapunov/rectangle condition.

A carried smallness hypothesis is mathematically correct when the paper states one.  Inventing a global smallness condition and calling it Theorem 2.2 would not be faithful.

## 7. Lean formalization plan

Use three independent layers.

### Layer A: spectral gap

Define mode decay rates

    a_k = d1*lambda_k + alpha*a
          - chi0*nu*gamma*(u*)^(m+gamma-1)*lambda_k
             / ((1+v*)^beta*(mu+d2*lambda_k)).

Prove:

    chi0 < chi* -> exists delta > 0, forall k != 0, delta <= a_k.

Then prove the semigroup multiplier estimate using

    r^sigma * exp(-r*t)
      <= (2*sigma/e)^sigma * t^(-sigma) * exp(-delta*t/2),

for r >= delta.

### Layer B: small-data Duhamel theorem

Formalize the abstract weighted-sup contraction theorem:

    linear smoothing + quadratic N + small initial data
    -> global mild solution + exponential decay.

This is pure semigroup bookkeeping.

### Layer C: chemotaxis nonlinear remainder

Prove the PDE-specific estimate:

    ||N(z)-N(w)|| <= K*(||z||_sigma+||w||_sigma)*||z-w||_sigma.

Use:

- elliptic/parabolic chemical resolver estimates;
- D(A^sigma) embedding into L-infinity for sigma > 1/2;
- product estimates in the fractional domain;
- smoothness of real powers near the positive equilibrium.

This is the main nonlinear analytic obligation.

## 8. Recommended Lean theorem statements

Local theorem:

    theorem theorem22_local_exponential_stability
      (ha : 0 < a) (hb : 0 < b)
      (hgap : chi0 < chiCritical)
      (Hlin : LinearFractionalSemigroupBounds ...)
      (Hquad : ChemotaxisQuadraticRemainder ... ) :
        exists eps C eta, 0 < eps and 0 < C and 0 < eta and
          forall initial data with ||z0||_sigma <= eps,
            global solution exists and
            ||u(t)-u*||_{C1} + ||v(t)-v*||_{C1} <= C*exp(-eta*t).

Global Lyapunov theorem, if needed separately:

    theorem global_convergence_of_entropy_coercive
      (hpersist : eventual lower floor theta)
      (hupper : eventual upper bound M)
      (hentropy : entropy_dissipation_condition chi theta M ... ) :
        Tendsto (fun t => ||u(t)-u*|| + ||v(t)-v*||) atTop (nhds 0).

Keep these two theorems separate.  The first is Theorem 2.2.  The second belongs to the later global-stability part of the paper.
