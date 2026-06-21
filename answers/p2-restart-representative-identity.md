# P2 restart representative identity

## Verdict

The restart/cosine representative identity is non-circular when stated in L2, or as an a.e. identity after representatives are chosen. For each fixed time s, the profile is defined as the L2 limit of finite Neumann-cosine Duhamel sums. Therefore the identity is a Hilbert-space reconstruction fact, not a downstream regularity fact.

The core statement is: if b is the Neumann cosine Hilbert basis of L2(0,L), and u_s is the L2 limit of finite sums using restart coefficients a_k(s), then u_s is the Hilbert-basis sum of those coefficients. No H1 estimate, flux regularity, pointwise derivative, or classical PDE regularity is needed.

## Minimal assumptions

The proof needs only the following data for each time s.

1. u_s is an element of L2(0,L).
2. There are finite cosine sums P_N(s) built from the Duhamel/restart coefficients.
3. P_N(s) converges to u_s in L2.
4. The normalized Neumann cosine family is complete, preferably packaged as a HilbertBasis.
5. The restart coefficients agree with the Hilbert-basis coordinates of u_s. If this is not definitional, prove it by continuity of the fixed-mode inner product along the L2 convergence P_N(s) -> u_s.

These assumptions are construction-level facts. They do not require H1.

## Lean/Mathlib chain

Once the cosine basis is packaged as

    cosBasis : HilbertBasis Nat Real L2I

Mathlib gives reconstruction by

    HilbertBasis.hasSum_repr

with shape

    HasSum (fun k => (cosBasis.repr u_s k) • cosBasis k) u_s.

Coefficient identification uses

    HilbertBasis.repr_apply_apply.

The coefficient-identification lemma is: for fixed k, the map z |-> inner (cosBasis k) z is continuous; since P_N(s) -> u_s in L2, the inner products converge. For all N >= k, orthonormality gives inner (cosBasis k) (P_N(s)) = a_k(s). Hence a_k(s) = cosBasis.repr u_s k.

After this rewrite, the reconstruction theorem gives

    HasSum (fun k => a_k(s) • cosBasis k) u_s.

To move from equality in Lp to a.e. equality of representatives, use

    MeasureTheory.MemLp.toLp_eq_toLp_iff.

Thus the safe representative identity is an L2 identity or an a.e. identity. A pointwise EqOn identity requires extra summability or uniform convergence and should be a separate theorem.

## Closed-span version

Without a HilbertBasis, a weaker non-circular statement is: every finite partial sum lies in the span of the cosine modes, and the L2 limit lies in the topological closure of that span. If the closed span is all of L2, the profile lies in the cosine closed span. However, the HilbertBasis route is cleaner because it gives the actual coefficient expansion.

## What would be circular

Do not prove the basic representative identity using u(s,.) in H1, weighted coefficient estimates, the flux-H1 provider, pointwise convergence of differentiated series, or classical PDE regularity. Those are downstream. The restart identity comes before them.

## Final Lean theorem shape

A clean theorem has two parts.

First, prove coefficient equality from the construction-level L2 limit:

    restartCoeff_eq_repr_of_l2_limit :
      Tendsto P atTop (nhds u_s) ->
      (forall N, P N is the finite cosine sum with coefficients a_k) ->
      forall k, a_k = cosBasis.repr u_s k.

Second, apply Hilbert-basis reconstruction:

    restart_series_hasSum_L2 :
      HasSum (fun k => a_k • cosBasis k) u_s.

This is the exact non-circular representative identity needed for the boundedness proof.
