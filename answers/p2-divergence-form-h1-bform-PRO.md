# Paper 2: divergence-form H1 smoothing and the B-form frontier

## Executive verdict

The B-form/conjugate kernel is the right non-circular way to interpret the divergence source in `L2`: it gives the chemotaxis Duhamel term as

    integral_0^s A^{1/2} e^{-(s-tau)A} F(tau) dtau

in spectral variables, where `A = -d1 Delta_N` and `F = u v_x` or its weighted chemotaxis flux.  This is enough to recover an `L2` contribution from `F in L_infty_t L2_x`, because the `A^{1/2}` heat singularity is `(s-tau)^(-1/2)`, which is integrable.

But it is **not** enough, by itself, to prove `u(s) in H1` from only `F in L_infty_t L2_x`.  The H1 norm applies another `A^{1/2}` to the result, so the relevant kernel becomes

    A e^{-(s-tau)A},

whose operator norm behaves like `(s-tau)^(-1)`.  That singularity is not integrable.  More importantly, this is not merely a bad estimate: there is no bounded estimate

    L_infty(0,s; L2_x) -> H1_x at time s

for the divergence Duhamel term in general.  One can build an explicit lacunary-in-time, lacunary-in-frequency counterexample.

Therefore the B-form closes the mild `L2` interpretation non-circularly, but it does **not** close positive-time `H1` smoothing from `F in L_infty_t L2_x` alone.  To get `H1`, one needs one genuine extra input: positive spatial regularity of the flux, Dini/Hölder time regularity of the flux, or a maximal-regularity/parabolic-regularity theorem.

## 1. Spectral form of the B-term

Let

    lambda_k = (k*pi/L)^2,        k >= 1,

and use the Neumann cosine modes for `u` and the compatible sine coefficients for the flux `F`.  For the divergence source

    -d_x F,

its contribution to the k-th cosine coefficient of u is of the form

    u_k^B(s) = integral_0^s sqrt(lambda_k)
                 exp(-d1*lambda_k*(s-tau)) F_k(tau) dtau,

where `F_k(tau)` is the sine coefficient of `F(tau)` with the project's chosen normalization.

This is the single-derivative B-form.  It is correct: the divergence contributes one factor `sqrt(lambda_k)`.

The L2 norm of the B-term has coefficients

    |u_k^B(s)|.

Using Minkowski,

    ||u^B(s)||_L2
      <= integral_0^s ||A^{1/2} exp(-d1*(s-tau)A) F(tau)||_L2 dtau
      <= C integral_0^s (s-tau)^(-1/2) ||F(tau)||_L2 dtau.

Thus if

    ||F(tau)||_L2 <= M

for `0 <= tau <= s`, then

    ||u^B(s)||_L2 <= C_d1 * M * sqrt(s).

This is the part the B-form genuinely fixes: it makes the divergence source a well-defined L2-valued mild term from merely L2 flux.

## 2. Why H1 still does not follow from F in L_infty L2

The H1 seminorm of the B-term is

    sum_k lambda_k |u_k^B(s)|^2.

Equivalently, define

    y_k(s) = sqrt(lambda_k) * u_k^B(s)
           = integral_0^s lambda_k exp(-d1*lambda_k*(s-tau)) F_k(tau) dtau.

Then

    ||u^B(s)||_{H1-seminorm}^2 = sum_k |y_k(s)|^2.

The corresponding operator is

    F |-> integral_0^s A exp(-d1*(s-tau)A) F(tau) dtau.

The norm of `A exp(-r A)` on L2 is comparable to `1/r`.  The crude estimate gives

    integral_0^s (s-tau)^(-1) dtau = infinity.

This is not only a failure of the crude estimate.  The mapping is not bounded from `L_infty_t L2_x` to `H1_x` at a fixed terminal time.

### Counterexample to an L_infty L2 -> H1 bound

Fix a terminal time `s`.  Choose a lacunary sequence of modes `k_j` so that the intervals

    I_j = [1/(2 d1 lambda_{k_j}), 1/(d1 lambda_{k_j})]

are pairwise disjoint and contained in `(0,s)`.  This is possible by taking `lambda_{k_j}` rapidly increasing.

Define a time-dependent coefficient vector by setting, in the variable `r = s - tau`,

    F_{k_j}(s-r) = M   for r in I_j,
    F_k = 0 otherwise.

Because the intervals are disjoint, at each time only one mode is active, hence

    ||F(tau)||_L2 <= M

for all tau.

But for each selected mode,

    y_{k_j}(s)
      = integral_{I_j} lambda_{k_j} exp(-d1*lambda_{k_j} r) M dr
      = (M/d1) * (exp(-1/2) - exp(-1)).

This is a nonzero constant independent of j.  Therefore

    sum_j |y_{k_j}(s)|^2 = infinity.

So the B-term need not belong to H1 at time s.  Consequently there can be no estimate of the form

    ||u^B(s)||_H1 <= C(s) ||F||_{L_infty(0,s;L2)}.

This answers the crux question: the single `sqrt(lambda_k)` in the B-form is not enough for H1, because the H1 norm supplies the second `sqrt(lambda_k)`.

## 3. What the identity B_N Q = S_N Q' actually means

For smooth `Q` with the correct boundary behavior, integration by parts gives

    B_N(t) Q = S_N(t) Q'

up to sign and normalization conventions.

But if `Q` is only in L2, then `Q'` does not exist as an L2 function.  In that case `B_N(t)Q` is best understood as the heat semigroup applied to the distributional divergence, with the derivative placed on the kernel.  This is legitimate for producing a smoothed L2 output, but it does not create a strong derivative of `Q`.

Thus:

- `B_N Q` is well-defined from `Q in L2` because the kernel derivative is square-integrable after positive heat time.
- The identity with `S_N Q'` is an IBP identity valid only when `Q'` is already meaningful, or in a weak/distributional sense.
- It cannot be used to prove `Q in H1`; that would be circular.

## 4. Extra hypotheses that do close H1

There are several clean non-circular ways to close H1.

### Option A: positive spatial regularity of the flux

Assume

    F in L_infty(0,s; D(A^{rho/2}))

for some `rho > 0`.  In Sobolev language, this is `F in L_infty_t H^rho_x`.

Then

    ||A integral_0^s e^{-d1*(s-tau)A} F(tau) dtau||_L2
      <= integral_0^s ||A^{1-rho/2} e^{-d1*(s-tau)A}||
            ||A^{rho/2}F(tau)||_L2 dtau.

The semigroup bound is

    ||A^{1-rho/2} e^{-d1*r*A}|| <= C r^{-(1-rho/2)}.

Since `rho > 0`, the singularity exponent satisfies

    1 - rho/2 < 1,

so the integral is finite:

    integral_0^s r^{-(1-rho/2)} dr = (2/rho) s^{rho/2}.

Thus

    ||u^B(s)||_H1 <= C_{d1,rho} s^{rho/2} ||F||_{L_infty(0,s;H^rho)}.

This is the cleanest purely spatial strengthening.  It is weaker than flux H1 if `0 < rho < 1`, so it is not logically identical to the flux-H1 conclusion.  Whether it is non-circular depends on how `F in H^rho` is obtained.

### Option B: Dini or Holder time regularity of the flux

Assume `F` is continuous at time `s` in L2 with Dini modulus:

    ||F(s-r) - F(s)||_L2 <= omega(r),
    integral_0^s omega(r)/r dr < infinity.

Then split

    integral_0^s A e^{-d1*r*A} F(s-r) dr
      = integral_0^s A e^{-d1*r*A} F(s) dr
        + integral_0^s A e^{-d1*r*A} (F(s-r)-F(s)) dr.

The constant-in-time part is bounded because

    integral_0^s A e^{-d1*r*A} dr = (1/d1) (I - e^{-d1*s*A}).

The difference term is bounded by

    C integral_0^s omega(r)/r dr.

Holder continuity in time, `omega(r) <= C r^alpha` for any alpha > 0, is sufficient.

This route is also non-circular if the time regularity of F comes from an independent regularity theorem.

### Option C: maximal regularity

Parabolic maximal regularity can give

    A u^B in L^p(0,T;L2)

from

    F in L^p(0,T;L2)

for suitable p.  This yields H1 information for almost every time and, with additional continuity/trace regularity, can be upgraded.  This is powerful but heavier to formalize.

For a Lean project, Option A or Option B is usually more transparent than full maximal regularity.

## 5. Does the P2 bridge close from F = u v_x in L2?

If the only available bound is

    u in L_infty,
    v_x in L2,
    hence F = u v_x in L2,

then no: this does not imply `u(s) in H1` through the divergence B-form.

It does imply the divergence Duhamel term is L2.  It does not imply H1.

To obtain H1 non-circularly, one needs one of the following:

1. independent parabolic regularity for the divergence-form equation;
2. a positive spatial regularity bound on F, such as `F in H^rho` for some rho > 0;
3. time Dini/Holder regularity of F near the terminal time;
4. maximal regularity plus a trace/continuity upgrade.

## 6. A clean Lean-formalizable spectral lemma for the positive-spatial-regularity route

Let `lambda k >= 0` be the Neumann eigenvalues and let `q_k(t)` be flux coefficients.  Suppose

    sum_k lambda_k^rho |q_k(t)|^2 <= M_rho^2

for all `t in [0,s]`, with `rho > 0`.

Define

    y_k(s) = integral_0^s lambda_k exp(-d1*lambda_k*(s-tau)) q_k(tau) dtau.

Then

    sum_k |y_k(s)|^2 <= C(d1,rho)^2 * s^rho * M_rho^2.

Proof:

    ||y||_l2
      <= integral_0^s sup_k [lambda_k^(1-rho/2) exp(-d1*lambda_k*r)]
           * (sum_k lambda_k^rho |q_k(s-r)|^2)^(1/2) dr
      <= M_rho * C(d1,rho) integral_0^s r^{-(1-rho/2)} dr
      = M_rho * C(d1,rho) * (2/rho) * s^{rho/2}.

The scalar estimate is

    lambda^(1-rho/2) exp(-d1*r*lambda)
      <= C(d1,rho) * r^{-(1-rho/2)}.

More explicitly, for `alpha = 1 - rho/2 > 0`,

    x^alpha exp(-x) <= alpha^alpha exp(-alpha),

so with `x = d1*r*lambda`,

    lambda^alpha exp(-d1*r*lambda)
      <= (alpha^alpha * exp(-alpha)) * (d1*r)^(-alpha).

Lean theorem shape:

    theorem bform_divergence_H1_of_flux_Hrho
      (hrho : 0 < rho)
      (hrho_lt : rho <= 2) -- optional, so alpha >= 0
      (hflux : forall tau in Icc 0 s,
        sum_k lambda k ^ rho * |q k tau|^2 <= M^2) :
      sum_k |integral_0^s lambda k * exp(-d1*lambda k*(s-tau)) * q k tau dtau|^2
        <= C * s^rho * M^2

This is a true non-circular smoothing lemma, but it requires flux `H^rho`, not just flux `L2`.

## 7. Clean Lean-formalizable lemma for Dini time regularity

Assume flux coefficients satisfy

    ||q(s-r) - q(s)||_l2 <= omega(r),
    integral_0^s omega(r)/r dr < infinity.

Then the H1 coefficient vector satisfies

    ||y(s)||_l2
      <= (1/d1) ||q(s)||_l2
        + C integral_0^s omega(r)/r dr.

The constant part is coefficientwise:

    integral_0^s lambda_k exp(-d1*lambda_k*r) q_k(s) dr
      = (1/d1) * (1 - exp(-d1*lambda_k*s)) q_k(s),

hence bounded in l2 by `(1/d1)||q(s)||_l2`.

The difference part uses

    ||A e^{-d1*r*A}|| <= C/r.

Lean theorem shape:

    theorem bform_divergence_H1_of_flux_timeDini
      (hmod : forall r, 0 < r -> r < s ->
        l2norm (fun k => q k (s-r) - q k s) <= omega r)
      (hDini : IntegrableOn (fun r => omega r / r) (Ioc 0 s)) :
      l2norm (fun k => integral_0^s lambda k * exp(-d1*lambda k*r) * q k (s-r) dr)
        <= (1/d1) * l2norm (q . s)
           + C * integral_0^s omega r / r dr

This is often the sharpest explanation of the cancellation hidden by the nonintegrable operator norm.

## 8. Recommended P2 dependency chain

The correct dependency chain should be one of the following.

### Chain 1: independent parabolic regularity

    bounded mild/classical solution
      -> positive-time parabolic regularity for divergence-form equation
      -> u(t) in H1
      -> elliptic resolver gives v(t) in H2
      -> flux F(t) in H1 by Sobolev product rules
      -> source bridge / cosine weak-derivative identity.

This is conceptually clean but requires a genuine parabolic regularity theorem.

### Chain 2: B-form plus extra flux regularity

    F in L_infty_t H^rho_x for some rho > 0
      -> B-form Duhamel term is H1
      -> u(t) in H1
      -> v(t) in H2
      -> eventually F in H1
      -> source bridge.

This uses the B-form smoothing non-circularly but needs the extra `H^rho` input for F.

### Chain 3: B-form plus time Dini regularity

    F in L_infty_t L2_x and time-Dini continuous into L2 near s
      -> B-form Duhamel term is H1 at time s
      -> u(s) in H1
      -> v(s) in H2
      -> F(s) in H1
      -> source bridge.

This exploits the exact cancellation of the time integral for the constant-in-time part.

## 9. Bottom line

The B-form/conjugate representation does **not** by itself circumvent the H1 obstruction from only `F in L_infty_t L2_x`.

It reduces the divergence source to a single spatial derivative in the L2 mild formulation, but the target H1 norm supplies the second half-derivative.  The resulting kernel is `A e^{-rA}`, and without additional spatial or temporal regularity of the flux, the terminal-time H1 estimate fails.

Therefore P2 cannot close the flux-H1 bridge solely from

    F = u v_x in L_infty_t L2_x.

A genuine additional analytic input is required.  The cleanest candidates are:

1. positive-time divergence-form parabolic regularity;
2. flux `H^rho` for some rho > 0;
3. flux time-Dini or Holder continuity in L2;
4. maximal regularity plus trace continuity.

For Lean, the most modular route is to formalize the B-form estimates as conditional lemmas and keep the extra regularity input explicit.  Do not encode an unconditional `L_infty_t L2_x -> H1_x` B-form theorem; it is false.
