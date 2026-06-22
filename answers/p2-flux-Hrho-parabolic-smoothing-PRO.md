# Paper 2: flux H^rho from B-form parabolic smoothing

## Executive verdict

Yes: although the B-form divergence term does **not** give `u(s) in H1` from only `F in L^infty_t L2_x`, it does give a strictly positive fractional gain:

    F in L^infty(0,T; L2_x)
      -> u(s,.) in H^sigma_x for every 0 <= sigma < 1 and every s > 0.

That positive fractional regularity is enough to bootstrap the flux:

    u(s) in H^sigma,
    elliptic v(s) in H^{sigma+2},
    F(s) = u^m * chi0 * (1+v)^(-beta) * v_x in H^sigma.

Then, with `F in H^rho` for some `rho = sigma > 0`, the B-form estimate **does** give `u(s) in H1` because the terminal singularity becomes integrable:

    integral_0^s r^{-(1-rho/2)} dr < infinity.

Thus the non-circular chain is:

    bounded solution
      -> F in L^infty L2
      -> B-form smoothing gives u in H^sigma for any sigma < 1
      -> elliptic gain gives v in H^{sigma+2}
      -> Sobolev product gives F in H^sigma
      -> B-form smoothing with H^sigma flux gives u in H1
      -> elliptic gain gives v in H3-ish / enough for flux H1 if needed.

So the answer is positive, but with an important two-step structure: `F in L2` gives only `u in H^sigma`, sigma < 1; then that positive `sigma` gives `F in H^sigma`; then the B-form closes the H1 estimate.

## 1. B-form smoothing from L2 flux gives H^sigma for sigma < 1

Let

    lambda_k = (k*pi/L)^2,

and let `F_k(t)` denote the sine/flux coefficient of the divergence flux.  The B-form contribution to the cosine coefficient of u is

    u_k^B(s) = integral_0^s sqrt(lambda_k)
                 exp(-d1*lambda_k*(s-tau)) F_k(tau) dtau.

The homogeneous heat term is standard.  The reaction term is easier because it has no spatial derivative.  The hard term is this B-form term.

For the H^sigma seminorm, use coefficient weight `lambda_k^sigma`.  Then

    lambda_k^(sigma/2) * u_k^B(s)
      = integral_0^s lambda_k^((sigma+1)/2)
          exp(-d1*lambda_k*(s-tau)) F_k(tau) dtau.

Therefore

    ||u^B(s)||_{H^sigma}
      <= integral_0^s
           ||A^((sigma+1)/2) exp(-d1*(s-tau)A) F(tau)||_L2 dtau.

The spectral multiplier estimate is

    sup_{lambda >= 0} lambda^theta exp(-d1*r*lambda)
      <= C_theta * d1^(-theta) * r^(-theta),

where

    C_theta = theta^theta * exp(-theta)

for theta > 0, with the usual harmless convention at theta = 0.

Here

    theta = (sigma + 1)/2.

Thus

    ||A^((sigma+1)/2) exp(-d1*r*A)||_{L2 -> L2}
      <= C_{sigma,d1} * r^(-(sigma+1)/2).

This is integrable near r = 0 exactly when

    (sigma + 1)/2 < 1,

i.e.

    sigma < 1.

Hence if

    ||F(t)||_L2 <= M_F

on `[0,T]`, then for every `0 <= sigma < 1`,

    ||u^B(s)||_{H^sigma}
      <= C_{sigma,d1} * M_F * integral_0^s r^(-(sigma+1)/2) dr
      = C_{sigma,d1} * M_F * (2/(1-sigma)) * s^((1-sigma)/2).

This is finite for every `s > 0`.  It is uniform for `s in [0,T]` as a bound, and together with the initial heat term it is uniform on `[s0,T]` for any `s0 > 0`.

### Initial heat term

For `u0 in L2`,

    ||e^{s d1 Delta_N} u0||_{H^sigma}
      <= C_{sigma,d1} * s^(-sigma/2) * ||u0||_L2,

because

    sup_lambda lambda^sigma exp(-2*d1*s*lambda)
      <= C_sigma * (2*d1*s)^(-sigma).

If the H^sigma norm uses `(1+lambda)^sigma`, then use

    (1+lambda)^sigma exp(-2*d1*s*lambda)
      <= C_sigma * (1 + s^(-sigma)).

### Reaction term

If the reaction source `G(t) = u(t)(a-bu(t)^alpha)` is bounded in L2, then

    integral_0^s e^{d1(s-tau)Delta_N} G(tau) dtau

belongs to H^sigma for `sigma < 2`, because the multiplier singularity is `r^(-sigma/2)`.  Thus it is harmless for all `sigma < 1`.

## 2. Non-circular source of F in L2

Assume the bounded solution satisfies

    0 <= u(t,x) <= M.

For the elliptic chemical equation

    -d2 v_xx + mu v = nu u^gamma,
    Neumann,

we have

    u^gamma in L2,

because the interval has finite measure.  Elliptic regularity gives

    v(t) in H2,

and therefore

    v_x(t) in H1 subset L2.

Thus

    F(t) = u(t)^m * chi0 * (1+v(t))^(-beta) * v_x(t)

is in L2, with a bound depending on `M`, `chi0`, `beta`, and the elliptic H2 bound for v.  This does not use the flux derivative and is non-circular.

So the first fractional smoothing step is legitimate:

    bounded u + elliptic v
      -> F in L^infty_t L2_x
      -> u(s) in H^sigma for all sigma < 1.

## 3. Fractional bootstrap ladder

Choose any fixed

    rho in (0,1).

From the first B-form smoothing step, for every positive time interval `[s0,T]`,

    u(t) in H^rho uniformly for t in [s0,T].

The elliptic resolver gains two derivatives:

    u(t)^gamma in H^rho
      -> v(t) in H^{rho+2}.

The composition `u -> u^gamma` is valid because `u` is bounded and nonnegative, and for `0 < rho < 1` Lipschitz/C1 composition on the bounded range preserves H^rho.  If the real exponent has low regularity at zero, use the already known nonnegative bounded range and the standard fractional composition theorem for the specific exponent, or assume a positive floor if needed.  For many Paper 2 boundedness arguments, bounded nonnegative and gamma >= 1 is enough for the fractional composition in 0 < rho < 1.

Then

    v_x(t) in H^{rho+1}.

In one dimension, `H^{rho+1}` embeds into `L^infty` for every `rho > 0`, because `rho+1 > 1/2`.

Now prove the flux regularity:

    F = u^m * chi0 * (1+v)^(-beta) * v_x in H^rho.

The needed product rules are standard in one dimension:

1. For `0 < rho < 1`,

       H^rho cap L^infty

   is an algebra, with

       ||fg||_{H^rho}
         <= C (||f||_Linf ||g||_{H^rho} + ||g||_Linf ||f||_{H^rho}).

2. If `f in H^rho cap L^infty` and `Phi` is C1 with bounded derivative on the range of f, then

       Phi(f) in H^rho.

3. Since `v in H^{rho+2}`, it is in `W^{1,infty}` in one dimension.  The map

       y -> (1+y)^(-beta)

   is smooth on the range `y >= 0`, so `(1+v)^(-beta)` is at least H^rho and bounded.

4. Since `v_x in H^{rho+1}`, in particular `v_x in H^rho cap L^infty`.

Thus each factor is in `H^rho cap L^infty`, and the product is in `H^rho`.

So the ladder closes:

    u in H^rho
      -> v in H^{rho+2}
      -> v_x in H^{rho+1}
      -> F in H^rho.

This works for every fixed `rho` with

    0 < rho < 1.

For Lean, choose a concrete value, e.g.

    rho = 1/2

or any rational in `(0,1)`.  Choosing a fixed rational avoids carrying many parameter inequalities.  If product lemmas at exactly `rho=1/2` are inconvenient, choose `rho = 1/4` or `rho = 3/4` depending on available embeddings.  Mathematically, any `rho in (0,1)` works.

## 4. B-form smoothing from F in H^rho gives u in H1

Now use the improved flux regularity.  The H1 seminorm of the B-term is controlled by

    ||A^{1/2} integral_0^s A^{1/2} e^{-d1(s-tau)A} F(tau) dtau||_L2.

Insert `A^{rho/2}F`:

    A e^{-rA} F
      = A^{1-rho/2} e^{-rA} A^{rho/2}F.

The multiplier estimate gives

    ||A^{1-rho/2} e^{-d1*r*A}||
      <= C_{rho,d1} * r^{-(1-rho/2)}.

This is integrable because

    1 - rho/2 < 1

for every `rho > 0`.

Therefore, if

    ||F(t)||_{H^rho} <= M_rho

on `[0,T]`, then

    ||u^B(s)||_{H1}
      <= C_{rho,d1} * M_rho * integral_0^s r^{-(1-rho/2)} dr
      = C_{rho,d1} * M_rho * (2/rho) * s^{rho/2}.

The free heat term is in H1 for every s > 0 with bound `s^{-1/2}` from L2 data, and the reaction Duhamel term is also in H1 because its singularity is `r^{-1/2}`.

Thus, for every `s0 > 0`,

    sup_{s in [s0,T]} ||u(s)||_{H1} < infinity.

This is the precise way the B-form recovers H1: not directly from `F in L2`, but from the first fractional bootstrap giving `F in H^rho` for some `rho > 0`.

## 5. Standardness of the result

This is a standard parabolic smoothing bootstrap for divergence-form semilinear parabolic equations in one dimension.  The key point is the exact smoothing index:

    divergence source in L2 gives H^sigma for sigma < 1;
    any positive sigma improves the flux;
    improved flux regularity gives H1.

No external maximal-regularity theory is required if one works spectrally with the cosine basis and accepts standard fractional Sobolev product/composition lemmas.

The core multiplier bound is:

    sup_{lambda >= 0} lambda^theta exp(-d1*r*lambda)
      <= C_theta * d1^(-theta) * r^(-theta).

All smoothing estimates above reduce to this inequality.

## 6. Lean-formalizable statements

### 6.1 Multiplier bound

A reusable scalar theorem:

    theorem spectral_multiplier_bound
      (theta d r : R) (htheta : 0 <= theta) (hd : 0 < d) (hr : 0 < r) :
      forall lambda >= 0,
        lambda^theta * Real.exp (-d*r*lambda)
          <= Ctheta theta * d^(-theta) * r^(-theta)

where for theta > 0,

    Ctheta theta = theta^theta * exp(-theta).

For Lean, it is often easier to state it existentially:

    exists Ctheta > 0, forall d r lambda,
      0 < d -> 0 < r -> 0 <= lambda ->
        lambda^theta * exp(-d*r*lambda) <= Ctheta * d^(-theta) * r^(-theta).

### 6.2 B-form L2 flux to H^sigma

Coefficient theorem:

    theorem bform_L2_flux_to_Hsigma
      (hsigma0 : 0 <= sigma) (hsigma1 : sigma < 1)
      (hF : forall tau in Icc 0 T, l2norm (Fcoeff tau) <= M) :
      forall s in Icc 0 T,
        HsigmaNorm sigma (Bduhamel Fcoeff s)
          <= C * M * s^((1-sigma)/2)

with the exact coefficient expression

    (Bduhamel F s)_k
      = integral_0^s sqrt(lambda_k) * exp(-d1*lambda_k*(s-tau)) * F_k(tau) dtau.

### 6.3 Elliptic gain

    theorem ellipticResolver_Hsigma_to_HsigmaPlus2
      (hrho : 0 <= rho)
      (hg : Hsigma rho g) :
      Hsigma (rho+2) (ellipticResolver g)

with a norm bound.  This is coefficientwise:

    v_k = nu * g_k / (mu + d2*lambda_k).

### 6.4 Fractional flux product

    theorem chemotaxisFlux_mem_Hrho
      (hrho0 : 0 < rho) (hrho1 : rho < 1)
      (hu : Hsigma rho u) (hu_bdd : LinftyBound u M) (hu_nonneg : Nonnegative u)
      (hv : Hsigma (rho+2) v) (hv_nonneg : Nonnegative v) :
      Hsigma rho (fun x => u x^m * chi0 * (1+v x)^(-beta) * deriv v x)

This theorem packages the 1D product and composition facts.

### 6.5 B-form H^rho flux to H1

    theorem bform_Hrho_flux_to_H1
      (hrho0 : 0 < rho) (hrho1 : rho <= 2)
      (hF : forall tau in Icc 0 T, HsigmaNorm rho (F tau) <= M_rho) :
      forall s in Icc 0 T,
        H1Norm (Bduhamel F s)
          <= C * M_rho * s^(rho/2)

The singular exponent is `1-rho/2`, and the integral gives `(2/rho)*s^(rho/2)`.

### 6.6 Final smoothing theorem

A clean final theorem:

    theorem positive_time_flux_Hrho_and_u_H1
      (hsol_bdd : forall t x, 0 <= u t x and u t x <= M)
      (hmild : BFormMildSolution u F reaction)
      (helliptic : forall t, EllipticChemical v (u t))
      (s0 T rho : R)
      (hs0 : 0 < s0) (hT : s0 <= T)
      (hrho0 : 0 < rho) (hrho1 : rho < 1) :
        (forall s in Icc s0 T, Hsigma rho (u s)) and
        (forall s in Icc s0 T, Hsigma (rho+2) (v s)) and
        (forall s in Icc s0 T, Hsigma rho (F s)) and
        (forall s in Icc s0 T, H1 (u s))

This is the exact non-circular regularity bridge needed for Paper 2.

## 7. Where circularity is avoided

The bootstrap avoids circularity as follows:

1. The first regularity gain uses only `F in L2`, which follows from bounded `u` and elliptic `v in H2`.
2. It does not assume `F in H1` or `d_x F in L2`.
3. The positive fractional regularity of `u` obtained from the B-form gives positive fractional regularity of `F` by independent Sobolev product rules.
4. Only after `F in H^rho` is proved does one use the B-form to obtain `u in H1`.
5. Therefore the flux-H1 bridge is downstream, not assumed.

## 8. Bottom line

The precise answer is:

    F in L_infty_t L2_x alone does not imply u(s) in H1.

But it does imply

    u(s) in H^sigma for every sigma < 1.

This positive fractional smoothing, combined with elliptic gain for v and one-dimensional product/chain rules, gives

    F(s) in H^rho

for any chosen `rho in (0,1)`.  Then the B-form estimate with H^rho flux gives

    u(s) in H1.

So Paper 2 can close non-circularly through the B-form smoothing ladder, with the genuine analytic inputs reduced to:

1. cosine multiplier estimates;
2. elliptic H^rho -> H^{rho+2} gain;
3. one-dimensional fractional Sobolev product/composition rules.
