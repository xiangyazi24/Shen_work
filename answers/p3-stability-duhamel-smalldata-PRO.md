# Paper 3 Theorem 2.2: Duhamel small-data stability route

## Executive verdict

The faithful stability half of Paper 3 Theorem 2.2 is a **local** theorem.  It has two hypotheses:

1. the linear spectral condition `chi < chi*`, equivalently all linearized modes are strictly stable;
2. the initial perturbation is small in the chosen phase norm.

It is not an unconditional global-attraction theorem.  The global convergence statements belong to later global-stability theorems and require stronger structural hypotheses.

For Lean, the most honest route is:

    spectral gap -> linear semigroup decay/smoothing
    + quadratic nonlinear remainder
    + Duhamel contraction in an exponentially weighted norm
    -> global small solution and exponential decay.

The analytic-semigroup infrastructure is the hard formal part.  If Mathlib does not provide the required sectorial/fractional-power theorem, use a project-local Fourier-mode semigroup estimate and carry the nonlinear Duhamel estimate as a named frontier.

## 1. Linearization and per-mode matrix

Consider the parabolic-parabolic system on `[0,L]` with Neumann boundary conditions:

    u_t = d1 u_xx - chi * d_x(u v_x) + u(a - b u^alpha),
    v_t = d2 v_xx + nu u^gamma - mu v.

The positive equilibrium is

    u* = (a / b)^(1 / alpha),
    v* = (nu / mu) * (u*)^gamma.

Set

    p = u - u*,
    q = v - v*.

Since `v*` is constant, `v*_x = 0`.  The chemotaxis term linearizes as

    -chi * d_x((u* + p) q_x)
      = -chi * u* q_xx - chi * d_x(p q_x).

Thus the linearized system is

    p_t = d1 p_xx - chi * u* q_xx - alpha*a*p,
    q_t = d2 q_xx + nu*gamma*(u*)^(gamma-1)*p - mu*q.

On the Neumann cosine mode

    cos(k*pi*x/L),
    lambda_k = (k*pi/L)^2,

write the mode vector as `(p_hat_k, q_hat_k)`.  The generator matrix is

    A_k = [ -(d1*lambda_k + alpha*a)       chi*u*lambda_k              ]
          [  nu*gamma*(u*)^(gamma-1)      -(d2*lambda_k + mu)          ].

For the general paper sensitivity `chi0 * u^m/(1+v)^beta`, replace `chi*u*` in the top-right entry by

    chi0 * (u*)^m / (1+v*)^beta.

The determinant condition then contains

    chi0 * nu * gamma * (u*)^(m+gamma-1) * lambda_k / (1+v*)^beta.

There is no extra factor `m` in the linearization, because the derivative of `u^m` multiplies `v*_x`, and `v*_x = 0`.

## 2. Eigenvalues and the spectral gap

For the m=1 constant-sensitivity matrix, define

    A = d1*lambda_k + alpha*a,
    D = d2*lambda_k + mu,
    B = chi*u*lambda_k,
    C = nu*gamma*(u*)^(gamma-1).

Then

    A_k = [ -A  B ]
          [  C -D ].

The trace is

    tr(A_k) = -(A + D) < 0.

The determinant is

    det(A_k) = A*D - B*C
             = (d1*lambda_k + alpha*a)*(d2*lambda_k + mu)
               - chi*nu*gamma*(u*)^gamma*lambda_k.

The eigenvalues are real:

    rho_{k,±} = -(A+D)/2 ± (1/2)*sqrt((A-D)^2 + 4*B*C).

The larger eigenvalue is `rho_{k,+}`.  The mode is stable iff

    det(A_k) > 0.

For k=0, lambda_0=0, B=0, and the eigenvalues are

    -alpha*a,  -mu,

so the constant mode is always strictly stable when `a > 0` and `mu > 0`.

For k >= 1, stability is equivalent to

    chi < chi_k,

where

    chi_k = ((d1*lambda_k + alpha*a)*(d2*lambda_k + mu))
            / (nu*gamma*(u*)^gamma*lambda_k)

in the m=1 constant-sensitivity case.  In the general paper form,

    chi_k = ((1+v*)^beta * (d1*lambda_k + alpha*a)*(d2*lambda_k + mu))
            / (nu*gamma*(u*)^(m+gamma-1)*lambda_k).

The critical threshold is

    chi* = inf_{k >= 1} chi_k.

The faithful hypothesis is

    chi < chi*.

### Uniform gap

Let

    S = nu*gamma*(u*)^gamma

for m=1 constant sensitivity.  If `chi < chi*`, then for k >= 1,

    det(A_k) = S*lambda_k*(chi_k - chi)
             >= S*lambda_k*(chi* - chi).

The positive decay rate of the larger eigenvalue is

    a_k = -rho_{k,+}
        = 2*det(A_k) / (A + D + sqrt((A-D)^2 + 4*B*C)).

Because det(A_k) > 0, one has `B*C < A*D`, hence

    sqrt((A-D)^2 + 4*B*C) < A + D.

Therefore

    a_k >= det(A_k)/(A+D)
        >= S*(chi* - chi)*lambda_k
           / ((d1+d2)*lambda_k + alpha*a + mu).

Since lambda_k >= lambda_1 for k >= 1, and the function

    lambda / ((d1+d2)*lambda + alpha*a + mu)

is increasing for lambda >= 0, we get the explicit nonzero-mode gap

    eta_nonzero = S*(chi* - chi)*lambda_1
                  / ((d1+d2)*lambda_1 + alpha*a + mu).

Including the zero mode, a valid uniform gap is

    eta = min(alpha*a, mu, eta_nonzero).

For the general paper sensitivity, replace `S` by

    S_general = nu*gamma*(u*)^(m+gamma-1)/(1+v*)^beta.

Then

    eta_nonzero = S_general*(chi* - chi0)*lambda_1
                  / ((d1+d2)*lambda_1 + alpha*a + mu).

This is a clean Lean-friendly quantitative gap.  It is not necessarily sharp, but it is positive and follows directly from `chi < chi*`.

## 3. Binding mode and chi*

The threshold is governed by

    g(lambda) = ((d1*lambda + alpha*a)*(d2*lambda + mu))/lambda
              = d1*d2*lambda + alpha*a*mu/lambda + d1*mu + alpha*a*d2.

This is U-shaped on `lambda > 0`, with continuous minimizer

    lambda_* = sqrt(alpha*a*mu/(d1*d2)).

Thus the binding discrete mode is the k >= 1 for which `lambda_k` minimizes `g(lambda_k)`.  The first nonzero mode binds if

    alpha*a*mu <= d1*d2*lambda_1^2.

On `[0,L]`, `lambda_1 = (pi/L)^2`, so first-mode dominance is

    alpha*a*mu <= d1*d2*(pi/L)^4.

Without this condition, do not hard-code mode 1.  Use the infimum over all nonzero Neumann modes.

## 4. Linear semigroup decay

Let `L` denote the full linearized generator.  In Fourier cosine variables, the semigroup is the direct sum of the finite-dimensional semigroups

    exp(t A_k).

From the uniform spectral gap above, the spectral bound is at most `-eta`.  To turn this into an operator norm bound, one needs either:

1. an analytic/sectorial semigroup theorem; or
2. an explicit mode-wise estimate for the 2 by 2 matrices `A_k`.

The desired estimate is

    ||exp(t L)|| <= M * exp(-eta0*t)

for any `0 < eta0 < eta`, or with `eta0 = eta` if the chosen mode estimates provide a uniform constant.

For smoothing in fractional spaces, one wants

    ||A^sigma exp(t L)|| <= M_sigma * t^(-sigma) * exp(-omega*t),

with `0 < omega < eta`.

A scalar spectral inequality useful for the Fourier proof is

    r^sigma * exp(-r*t)
      <= (2*sigma/e)^sigma * t^(-sigma) * exp(-delta*t/2)

whenever `r >= delta > 0` and `t > 0`.

For the 2 by 2 parabolic-parabolic system, the matrices are not self-adjoint in the standard product L2 norm.  This means the gap alone is not literally an operator norm estimate without some control of eigenvector condition numbers or a sectorial estimate.  In a Lean development, this should be a named linear-semigroup theorem:

    LinearizedSemigroupDecayAndSmoothing

rather than silently inferred from the scalar gap.

## 5. Nonlinear remainder

Write the perturbation equation as

    w_t = L w + N(w),

where `w = (p,q) = (u-u*, v-v*)`.

The nonlinear terms are:

    N1(p,q) = -chi * d_x(p q_x)
              + [f(u*+p) - f(u*) - f'(u*)p],

where

    f(u) = u(a - b u^alpha),
    f'(u*) = -alpha*a,

and

    N2(p,q) = nu*((u*+p)^gamma - (u*)^gamma - gamma*(u*)^(gamma-1)*p).

The logistic remainder is quadratic:

    f(u*+p) - f(u*) - f'(u*)p = O(p^2)

for `p` small in L-infinity, because `u* > 0` and the power function is smooth near `u*`.

The chemical production remainder is similarly quadratic:

    (u*+p)^gamma - (u*)^gamma - gamma*(u*)^(gamma-1)*p = O(p^2).

The chemotaxis nonlinear remainder is

    -chi * d_x(p q_x).

This is bilinear.  Its exact mapping property depends on the phase space.  This is a serious formal point:

- If the base space is L2 and the fractional domain is only `D(A^sigma)` with sigma in `(1/2,1)`, then the divergence term may not map quadratically into L2 unless the chosen sigma and p-norm give enough spatial regularity.
- In one dimension, `H^s` is an algebra for `s > 1/2`, and `H^s` embeds into C1 only for `s > 3/2`.  The term `d_x(p q_x)` requires enough regularity to control either `p_x q_x + p q_xx` or to treat the derivative through a divergence-form semigroup estimate.

Therefore the clean Lean statement should not assert the quadratic bound for free.  It should carry a genuine hypothesis:

    QuadraticRemainderBound:
      ||N(w)-N(z)||_X <= K*(||w||_Y + ||z||_Y)*||w-z||_Y

for the selected spaces `Y -> X`.

If using a high-regularity phase space such as H2 or a C1-type space, this bound is straightforward by product estimates.  If using the paper's fractional sectorial spaces, the proof must use the exact embeddings and divergence-form smoothing estimates available in that framework.

## 6. Duhamel fixed-point proof

Let the linear semigroup satisfy

    ||e^{tL}||_Y <= M0 * exp(-omega*t),

and the smoothing/Duhamel estimate satisfy

    ||e^{(t-s)L} F||_Y <= M_sigma * (t-s)^(-sigma) * exp(-omega*(t-s)) * ||F||_X.

Let

    I = integral_0^infty tau^(-sigma) * exp(-(omega-theta)*tau) dtau,

where `0 < theta < omega` and `0 < sigma < 1`.  Then `I < infinity`.

Define the weighted space

    ||w||_B = sup_{t >= 0} exp(theta*t) * ||w(t)||_Y.

The Duhamel map is

    Phi(w)(t) = e^{tL} w0 + integral_0^t e^{(t-s)L} N(w(s)) ds.

Assume

    ||N(w)||_X <= K ||w||_Y^2,

and the local Lipschitz form

    ||N(w)-N(z)||_X <= K*(||w||_Y+||z||_Y)*||w-z||_Y.

On the ball `||w||_B <= r`,

    ||Phi(w)||_B <= M0 ||w0||_Y + M_sigma*K*I*r^2,

and

    ||Phi(w)-Phi(z)||_B <= 2*M_sigma*K*I*r*||w-z||_B.

Thus the map is a contraction if

    2*M_sigma*K*I*r <= 1/2.

It maps the ball to itself if

    M0 ||w0||_Y <= r/2

and

    M_sigma*K*I*r^2 <= r/2.

A convenient threshold is

    epsilon = min( r/(2*M0), 1/(8*M0*M_sigma*K*I) ).

More transparently, choose `r` first with

    2*M_sigma*K*I*r <= 1/2,

then set

    epsilon = r/(2*M0).

For `||w0||_Y <= epsilon`, Banach's fixed point theorem gives a global mild solution and

    ||w(t)||_Y <= r * exp(-theta*t).

With the smoothing/regularity upgrade, this gives the theorem's exponential decay in the desired C1 or classical norm.

## 7. Gronwall alternative

Instead of a contraction on the full trajectory, one can use an a priori bootstrap.

Let

    phi(t) = sup_{0 <= s <= t} exp(theta*s)*||w(s)||_Y.

Duhamel gives

    phi(t) <= M0 ||w0||_Y + M_sigma*K*I*phi(t)^2.

If

    4*M0*M_sigma*K*I*||w0||_Y <= 1,

then a continuity argument yields

    phi(t) <= 2*M0 ||w0||_Y

for all t.  This proves global existence by continuation and exponential decay.  This route is sometimes easier than constructing the complete weighted Banach fixed-point space in Lean.

## 8. Mode-wise alternative to analytic semigroups

If Mathlib lacks the needed analytic semigroup and fractional-power API, the mode-wise route is more concrete.

1. Expand p and q in Neumann cosine modes.

2. For each k, solve the linear ODE

       y_k'(t) = A_k y_k(t).

3. Prove explicit estimates for `exp(t A_k)`.  For k=0 this is diagonal.  For k >= 1 use the eigenvalue formula or a 2 by 2 matrix exponential estimate.

4. Establish a uniform mode decay bound:

       ||exp(t A_k)|| <= M * exp(-eta0*t)

   and a smoothing bound with powers of lambda_k.

5. Sum over modes to get L2/Hs estimates.

6. Write the nonlinear problem in Fourier variables:

       y_k(t) = exp(t A_k)y_k(0)
                + integral_0^t exp((t-s)A_k) N_k(y(s)) ds.

7. Prove the same weighted fixed-point theorem for the sequence norm corresponding to Hs.

This route avoids abstract sectorial theory but replaces it with substantial Fourier bookkeeping and nonlinear convolution estimates.  It is likely more Lean-tractable if the repository already has cosine spectral infrastructure.

For the parabolic-elliptic reduction, the mode-wise route is simpler because there is only one scalar mode equation:

    p_hat_k' = sigma_k p_hat_k + nonlinear_k.

Then semigroup estimates are purely scalar.  For the parabolic-parabolic system, the 2 by 2 matrix estimates are the additional work.

## 9. Faithfulness to the paper

The faithful hypotheses for Theorem 2.2 are:

1. subcritical sensitivity:

       chi < chi*,

   where chi* is the infimum of the nonzero per-mode thresholds;

2. small initial perturbation:

       ||u0 - u*|| in the paper's chosen norm is less than some delta.

The conclusion is local exponential stability:

    ||u(t)-u*||_{C1} + ||v(t)-v*||_{C1} <= C exp(-lambda*t)

for all t >= 0, with global existence for those small data.

Do not state this theorem as global attraction for all bounded positive solutions.  That is a different result and needs different hypotheses.

## 10. Lean dependency chain

Recommended structures:

    structure ModeSpectralGap where
      eta : R
      eta_pos : 0 < eta
      mode_gap : forall k, spectralBound A_k <= -eta

    structure LinearizedSemigroupBounds where
      omega : R
      M0 : R
      M_sigma : R
      omega_pos : 0 < omega
      semigroup_decay : forall t >= 0, ||S t||_{Y->Y} <= M0*exp(-omega*t)
      smoothing : forall t > 0, ||S t||_{X->Y} <= M_sigma*t^(-sigma)*exp(-omega*t)

    structure QuadraticRemainderBound where
      K : R
      local_lip : forall w z, normY w <= r -> normY z <= r ->
        normX (N w - N z) <= K*(normY w + normY z)*normY (w-z)
      zero : N 0 = 0

    theorem smallData_duhamel_contraction
      (Hlin : LinearizedSemigroupBounds)
      (Hquad : QuadraticRemainderBound)
      (hI : kernel integral bound)
      (hsmall : normY w0 <= epsilon) :
        exists global mild solution with exp decay.

    theorem theorem22_local_stability
      (hchi : chi < chiStar)
      (Hgap : spectral gap from hchi)
      (Hlin : semigroup bounds from gap)
      (Hquad : chemotaxis quadratic remainder)
      (Hupgrade : mild-to-classical and C1 estimate) :
        local exponential stability.

This keeps the proof faithful and prevents the two common mistakes:

- treating the scalar parabolic-elliptic eigenvalue as the full parabolic-parabolic matrix without proof;
- assuming the chemotaxis divergence nonlinearity is quadratic into L2 in a fractional space where this has not been proved.
