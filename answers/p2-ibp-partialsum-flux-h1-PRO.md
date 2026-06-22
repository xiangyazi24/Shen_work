# Paper 2: flux H1 / source bridge by partial-sum IBP

## Executive verdict

The partial-sum integration-by-parts idea is rigorous, but only after one is precise about the object being expanded.

For the chemotaxis flux

    F(x) = u(x)^m * chi0/(1+v(x))^beta * v_x(x),

partial sums of the cosine expansion of `u` do not give the weak derivative of `F`.  They give information about `u` or about nonlinear approximants built from projected `u`, not about the actual flux unless one separately proves those nonlinear approximants converge to `F` in a topology strong enough to pass derivatives.

The non-circular and clean route is:

1. obtain spatial regularity of `u` and `v` at the time slice from parabolic/elliptic smoothing, independently of the flux derivative being proved;
2. prove by Sobolev product and chain rules that the actual flux `F` belongs to `H1(0,L)`;
3. use the standard cosine theory for `H1` functions to identify the weak derivative and the derivative coefficients;
4. use partial-sum IBP only as a verification of the spectral weak-derivative identity, not as the source of regularity.

Thus, the single genuine analytic input should be a smoothing/regularity theorem such as

    u(t,.) in H1 or H2, v(t,.) in H2, for t > 0,

with bounds coming from the heat semigroup and elliptic resolver.  Once this is available, the flux-H1 bridge is a standard Sobolev calculus lemma.  This avoids circularity.

## 1. What partial-sum IBP actually proves

Let `F in L2(0,L)`, and define its Neumann cosine coefficients

    b_k = <F, e_k>,

where `e_k` are the orthonormal Neumann cosine modes.  Let

    P_N F = sum_{k=0}^N b_k e_k.

Then `P_N F` is smooth, and for any test function `phi in C_c^infty(0,L)`,

    integral (P_N F) phi' = - integral (P_N F)' phi.

Since `P_N F -> F` in L2, the left side converges to

    integral F phi'.

But this alone does **not** prove that `(P_N F)'` converges to an L2 function.  It only shows that any distributional limit of `(P_N F)'`, if such a limit exists, is the weak derivative of `F`.

To conclude `F in H1`, one needs an additional bound/convergence condition such as

    sup_N ||(P_N F)'||_L2 < infinity,

or equivalently

    sum_{k >= 1} lambda_k |b_k|^2 < infinity.

Then `(P_N F)'` is bounded in L2; after weak compactness it has a weak L2 limit `G`; the IBP identity passes to the limit and proves

    integral F phi' = - integral G phi,

so `G = weak_deriv F` and `F in H1`.

Therefore:

- Partial-sum IBP for the flux's own cosine coefficients is a rigorous way to identify a weak derivative **if** the derivative coefficients are L2-summable or if an H1 bound is known.
- Partial-sum IBP for `S_N u` proves a derivative statement about `u`, not about the nonlinear flux `F(u,v)`.
- Partial-sum IBP for a nonlinear projected flux

      F_N = (S_N u)^m * chi0/(1+V[S_N u])^beta * d_x V[S_N u]

  proves an identity for `F_N`, not for `F`, unless one separately proves `F_N -> F` and `F_N' -> G` in a suitable weak or strong topology.

This is the main subtlety: the flux coefficients are not simple algebraic transforms of the coefficients of `u`.  The nonlinear flux must be treated as its own function.

## 2. Minimal non-circular regularity for the flux

In one dimension, the clean Sobolev route is:

    u in H1(0,L) and L_infty,
    v in H2(0,L),
    v >= 0,
    u >= 0,
    u bounded above,
    beta >= 0,
    m >= 1.

Then

    F = u^m * (1+v)^(-beta) * v_x

belongs to `H1(0,L)`.

### Why H1 for u and H2 for v are enough

In one dimension:

    H1(0,L) embeds into L_infty(0,L),
    H1(0,L) is an algebra,
    if f in H1 and Phi is C1 with bounded derivative on the range of f, then Phi(f) in H1.

Assume `0 <= u <= M`.  For `m >= 1`, the function

    s |-> s^m

is C1 on `[0,M]` with bounded derivative.  Hence

    u^m in H1,

and weakly

    d_x(u^m) = m u^(m-1) u_x.

Assume `v >= 0`.  Then `1+v >= 1`, and for beta >= 0,

    s |-> (1+s)^(-beta)

is C1 with bounded derivative on `[0,Vmax]`.  Hence

    (1+v)^(-beta) in H1,

and weakly

    d_x (1+v)^(-beta) = -beta (1+v)^(-beta-1) v_x.

Since `v in H2`,

    v_x in H1,
    v_x in L_infty,
    v_xx in L2.

Now set

    A = u^m,
    B = (1+v)^(-beta),
    C = v_x.

Then `A, B, C in H1 cap L_infty`.  Because `H1(0,L)` is an algebra in one dimension,

    F = A * B * C in H1.

Its weak derivative is

    F_x = A_x B C + A B_x C + A B C_x,

i.e.

    F_x = m u^(m-1) u_x * (1+v)^(-beta) * v_x
          - beta u^m * (1+v)^(-beta-1) * v_x^2
          + u^m * (1+v)^(-beta) * v_xx.

Each term is in L2:

- `u^(m-1)` and `(1+v)^(-beta)` are L_infty;
- `u_x in L2` and `v_x in L_infty`, so first term is L2;
- `u^m` and `(1+v)^(-beta-1)` are L_infty, and `v_x^2 in L_infty`, hence L2 on a bounded interval;
- `u^m` and `(1+v)^(-beta)` are L_infty, and `v_xx in L2`, so third term is L2.

Thus `F in H1` non-circularly.

### Is u,v in H1 enough?

No, not for `F in H1` by the direct product rule.  If only `v in H1`, then `v_x in L2` but there is no `v_xx in L2`.  The term

    d_x(v_x) = v_xx

is not available, so the derivative of `F` need not be in L2.  One can still have `F in L2` because `u^m` and `(1+v)^(-beta)` are L_infty, but H1 requires one more derivative on `v`.

Therefore the minimal clean assumption is essentially:

    u in H1 cap L_infty,
    v in H2,

plus bounded positivity conditions for the compositions.

For the elliptic chemical equation, `v in H2` follows directly from `u^gamma in L2`.  In one dimension, if `u in H1`, then `u in L_infty`, so `u^gamma in L2`.  Thus the elliptic resolver supplies `v in H2` non-circularly.

## 3. Cleaner route than partial-sum IBP

Yes.  The clean route is:

1. prove parabolic/elliptic smoothing for time slices;
2. prove the actual flux is H1 by Sobolev chain and product rules;
3. then use the standard cosine expansion theorem for H1 functions.

This avoids the partial-sum gymnastics as the primary regularity source.

For a mild parabolic solution on an interval with Neumann boundary conditions, heat semigroup smoothing gives, for every `t > 0`,

    u(t,.) in H^s(0,L)

for suitable positive `s`, depending on the source regularity.  For classical solutions, or for a mild solution after restarting at any positive time, one typically has enough spatial regularity to conclude

    u(t,.) in H1,
    v(t,.) in H2.

For the elliptic chemical equation

    -v_xx + mu v = nu u^gamma,
    Neumann,

if `u(t,.) in H1` and `u` is bounded, then `u^gamma in L2`, and elliptic regularity gives

    v(t,.) in H2.

Then the flux-H1 statement follows by the product rule above.

This is genuinely non-circular because the regularity comes from the parabolic heat semigroup and the elliptic resolver, not from the chemotaxis flux derivative.  The downstream boundedness argument may use the flux derivative later, but it did not assume it.

## 4. Cosine representation once F is H1

Let `F in H1(0,L)`, and let

    b_k = <F, e_k>

be its Neumann cosine coefficients.  Then

    P_N F -> F in H1,

where `P_N` is the cosine projection.  In particular,

    P_N F -> F in L2,
    (P_N F)' -> F_x in L2.

For every test function `phi in C_c^infty(0,L)`,

    integral F phi' = - integral F_x phi.

The partial-sum IBP proof is then harmless:

    integral P_N F phi' = - integral (P_N F)' phi,

and both sides converge to the corresponding limits because of H1 convergence.

If the spectral source coefficients are defined as the sine/derivative coefficients of the flux, the H1 regularity justifies them.  More concretely, using the non-normalized cosine modes `cos(k*pi*x/L)`,

    d_x cos(k*pi*x/L) = -(k*pi/L) sin(k*pi*x/L).

So the distributional derivative of F has sine coefficients related to the cosine coefficients of F by the usual factor `k*pi/L`, with the expected sign, once normalization conventions are fixed.

This is the correct spectral source bridge:

    flux F in H1
    -> weak derivative F_x in L2
    -> derivative coefficients are L2-summable
    -> partial-sum IBP identifies the coefficient-level source with F_x.

## 5. What partial sums can and cannot do

### Valid statement

If `F in L2` and the cosine coefficients of `F` satisfy

    sum lambda_k |b_k|^2 < infinity,

then partial-sum IBP proves `F in H1` and identifies its weak derivative.

### Circular use to avoid

Do not prove the derivative coefficient summability of `F` by invoking the downstream source estimate that itself assumes the flux derivative.  That is circular.

### Nonlinear-projection route

One could define smooth flux approximants

    F_N = (P_N u)^m * (1+V[P_N u])^(-beta) * d_x V[P_N u]

and prove

    F_N -> F in L2,
    F_N' -> G in L2 or weakly in L2.

Then partial-sum IBP for `F_N` would identify `G` as the weak derivative of `F`.  This is valid but more work than the direct Sobolev route.  It requires strong convergence of nonlinear compositions and elliptic resolvers, plus uniform derivative bounds.  Unless there is a strong reason to use this approach, it is not the best Lean decomposition.

## 6. Lean-formalizable dependency chain

Use the following chain.

### Step A: time-slice smoothing input

A clean theorem shape:

    theorem positive_time_slice_regulariy
        (hsol : MildOrClassicalSolution p u v)
        (ht : 0 < t) :
        H1 (u t) and LinftyBound (u t) and Nonnegative (u t) and
        H2 (v t) and Nonnegative (v t)

For an elliptic chemical resolver, split this:

    u(t) in H1 cap L_infty
    -> u(t)^gamma in L2
    -> v(t) in H2 by elliptic regularity.

This is the genuine analytic input.  It comes from semigroup smoothing or the classical solution interface.

### Step B: Sobolev chain rules

Prove or reuse:

    H1_comp_C1_bounded_deriv:
      f in H1, range f subset I, Phi C1 with bounded derivative on I
      -> Phi o f in H1.

Instances:

    u -> u^m,
    v -> (1+v)^(-beta).

For real exponents, carry nonnegativity and upper bounds so the scalar maps are C1 with bounded derivative on the relevant compact interval.

### Step C: H1 algebra/product rules in 1D

Use:

    H1(0,L) embeds into L_infty(0,L),
    H1(0,L) is closed under multiplication.

Then:

    u^m in H1,
    (1+v)^(-beta) in H1,
    v_x in H1,
    F = u^m * (1+v)^(-beta) * v_x in H1.

A direct product lemma is:

    theorem flux_mem_H1
        (hu : H1 u) (hu_bdd : 0 <= u <= M)
        (hv : H2 v) (hv_nonneg : 0 <= v)
        (hm : 1 <= m) (hbeta : 0 <= beta) :
        H1 (fun x => u x ^ m * (1 + v x)^(-beta) * deriv v x)

and its derivative formula:

    weakDeriv F =
      m u^(m-1) u_x (1+v)^(-beta) v_x
      - beta u^m (1+v)^(-beta-1) v_x^2
      + u^m (1+v)^(-beta) v_xx.

### Step D: Fourier/cosine H1 bridge

A theorem shape:

    theorem cosine_partial_sum_flux_H1_bridge
        (hF : H1 F) :
        P_N F -> F in H1 and
        forall phi in C_c_infty(0,L),
          integral F phi' = - integral weakDeriv(F) phi.

Coefficient version:

    theorem flux_source_coefficients_identify_weak_derivative
        (hF : H1 F) :
        sourceCoeffs(F) are the Fourier coefficients of weakDeriv(F)

with the exact sine/cosine normalization used in the project.

### Step E: B-form source bridge

Use the preceding theorem to justify the chemotaxis source term in the B-form:

    -d_x F

as an H^{-1} or L2 source, depending on the downstream theorem.  If downstream needs L2, require `F in H1`.  If it only needs H^{-1}, `F in L2` already suffices by

    phi |-> integral F phi'

as an H^{-1} distribution.

## 7. Where circularity is avoided

Circularity is avoided because:

- `F in H1` is proved from independent time-slice regularity of `u` and `v`, namely `u in H1` and `v in H2`;
- `v in H2` comes from the elliptic chemical equation and `u^gamma in L2`, not from differentiating the flux;
- partial-sum IBP is used only after `F in H1` is known, or after an independent derivative-coefficient summability proof is known;
- no downstream boundedness estimate that requires the flux source is used to prove the flux source itself.

## 8. Bottom line

The partial-sum IBP construction is rigorous only for the flux's own partial sums, and it identifies the weak derivative only if derivative convergence or summability is independently available.  It does not magically differentiate the nonlinear flux from the cosine series of u.

The best decomposition for Lean is:

    parabolic/elliptic smoothing
      -> u in H1 cap L_infty, v in H2
      -> Sobolev chain/product rules
      -> flux F in H1
      -> standard H1 cosine expansion and partial-sum IBP
      -> source bridge.

The single genuine analytic input is positive-time spatial regularity from the heat semigroup and elliptic resolver.  Once that is in place, the flux-H1 bridge is standard Sobolev calculus plus Fourier bookkeeping.
