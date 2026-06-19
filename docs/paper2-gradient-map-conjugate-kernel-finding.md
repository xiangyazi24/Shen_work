# Paper 2 — gradient mild map: output-derivative vs conjugate-kernel (DESIGN DECISION for Xiang)

Found 2026-06-19 (overnight /automode), verified against source + ChatGPT-grounded.

## The finding (verified)
`intervalGradientDuhamelMap` (IntervalGradientDuhamelMap.lean:58) defines the chemotaxis term as the
OUTPUT derivative of the Neumann semigroup applied to the C⁰ flux Q:
  (−χ₀) ∫₀ᵗ deriv(z ↦ S_N(t−s)(Q(u(s)))(z))(x) ds      [verified: `deriv (fun z => intervalFullSemigroupOperator (t-s) (chemFluxLifted) z) x.1`]
On [0,1] with the Neumann cosine semigroup S_N (modes cos(nπx)), ∂x S_N maps cosₙ ↦ −nπ sinₙ — so this
gradient term is a SINE (Dirichlet) series: it vanishes at x=0,1 but its x-derivative does NOT.

## Why it matters
For the mild fixed point u=Φ(u) to be a CLASSICAL NEUMANN solution (∂xu=0 at endpoints, satisfying
u_t=u_xx−χ₀·chemDiv+L), the chemotaxis term must be the NEUMANN-COSINE source form
  −χ₀ ∫₀ᵗ S_N(t−s)(chemDiv(s)) ds,  chemDiv = ∂x(flux) = Q_x,
i.e. the CONJUGATE-KERNEL operator B_N(r)Q := −∫₀¹ ∂_yK_N(r,x,y)Q(y)dy = S_N(r)(Q_x), which IS a cosine
(Neumann) series. The KEY: B_N Q (cosine) ≠ ∂x(S_N Q) (sine) on the interval (they only coincide on the
whole line, by translation invariance). The boundary term in the IBP B_N vs output-deriv vanishes BECAUSE
Q(0)=Q(1)=0 (PROVED: chemFluxLifted_endpoint_zero/one — Q=u^m S(v) v_x, v_x=0 by v Neumann), but the two
operators are still NOT equal (∫∂xK_N·Q ≠ −∫∂yK_N·Q for the cos·cos kernel).

## The decision (Xiang's call — NOT self-authorized)
The slice agreement CoupledDuhamelT6SliceAgreement (needed for the mild-to-classical pde_u → localExistence)
is only FAITHFUL if the gradient mild map is the conjugate-kernel form B_N, not the output-derivative form.
Options:
  (A) CORRECT the core map: redefine the chemotaxis term as −χ₀∫S_N(t−s)(B_N-form / S_N(Q_x)). Ripples through
      the entire existence construction (Banach FP / Picard, the bounds, the contraction) — they'd need re-checking
      against the corrected map. Big, but faithful.
  (B) Add a RECONCILIATION lemma: prove the output-deriv fixed point and the conjugate-kernel solution coincide
      (UNLIKELY — ChatGPT shows they differ; would need a special structural cancellation).
  (C) Verify whether the existing framework ALREADY reconciles this elsewhere (the weak→classical bridge may
      handle it) — audit before concluding the map is non-faithful.
RECOMMENDATION: (C) first (audit — don't over-claim a bug in audited work), then (A) if genuinely needed.
The endpoint-zero lemmas + the diagnosis are banked (IntervalCoupledDuhamelT6SliceAgreement.lean). hagree is
BLOCKED on this decision; the other Paper-2 frontier (hsrc) + avenue-c (Paper-1 parabolic) are NOT blocked.
