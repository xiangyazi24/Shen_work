# Layer-2 (C⁰ mild local existence) — design transcript

Source: ChatGPT (Shen channel), rescued by Xiang paste (the cron3 bridge capture truncated to 117B twice).
Recorded 2026-06-18. Repo pinned mathlib v4.29.1 / lean v4.29.1.

## Verdict
Layer 2 = a **truncated C⁰ mild fixed-point engine** on `C([0,T]; C⁰([0,1]))`. The transport divergence
`−χ ∂x q(u)` enters as `−χ ∫₀ᵗ ∂xE(t−τ) q(u(τ)) dτ` — the derivative lands on the (Layer-1) heat
semigroup, so the nonlinear flux only needs to be C⁰-bounded and locally Lipschitz.

### Two honest caveats (load-bearing)
1. **CLAMPED nonlinearities on [0,M], NOT an a-priori positivity hypothesis.** All real powers are applied
   to `clipC0 M u = min(M, max(0, u))`, never to a possibly-negative C⁰ function. Positivity/comparison is a
   LATER layer, needed to prove the clamp is INACTIVE and thereby recover the original Paper-3 PDE with real
   powers. (Mirrors the Paper-1 truncated-fixed-source lesson: clamp at the foundation, prove inactivity later.)
2. **The `+ c u_x` drift is NOT automatically compatible with the even-reflection Neumann heat kernel unless
   c = 0** (or unless `c u_x` is intentionally part of the same derivative-on-semigroup mild formulation).
   Recommendation: set `c = 0` in the FIRST production theorem; keep `c` as an optional interface field with
   a warning. To prove equivalence to the classical Neumann advection PDE for c≠0 needs a separate
   drift-Neumann semigroup / boundary-correction lemma.

## Spaces and the Duhamel map
- `C0 := BoundedContinuousFunction I01 ℝ` (spatial Banach), `Path T := BCF (IT T) C0` (fixed-point space),
  metric = BCF sup. `I01 = Icc 0 1`, `IT T = Icc 0 T`.
- NEW param struct `P3Params` (do NOT reuse CMParams unchanged): m α γ β (with 1≤m,1≤α,1≤γ,0≤β), χ c a b.
  Logistic `a·u − b·u^{1+α}`; normalized paper case a=b=1.
- `clip01M M z := min M (max 0 z)`; `clipC0` its C⁰ lift. `v(u)=R(clip^γ)`, `vx(u)=∂xR(clip^γ)`,
  `S(v)=(1+v)^{-β}`, flux `q_M(u)=clip^m·S(v)·vx`, reaction `F_M=a·clip − b·clip^{1+α}`,
  div-primitive `B_M=c·clip − χ·q_M`.
- `Φ(U)(t) = E(t)u₀ + ∫₀ᵗ E(t−τ)F_M(U(τ))dτ + ∫₀ᵗ ∂xE(t−τ)B_M(U(τ))dτ`.

## Contraction constants + short time
- `A=‖u₀‖`, `M=2(A+1)`, ball `𝔅_{T,M}=closedBall 0 M` (complete as closed subset). `C_E=π^{-1/2}`.
- THE key estimate: `∫₀ᵗ(t−τ)^{-1/2}dτ = 2√t` → the √T smallness in the transport term; reaction gets only T.
- Power-Lipschitz on [0,M]: `L_r(M)=r·M^{r-1}`. Resolvent-grad const `C_R^1` (crude `cosh 1`).
  Flux Lipschitz `L_Q = C_R^1[L_m·M^γ + M^m·L_γ + β·M^m·L_γ·M^γ]`.
- `Φ` self-maps + contracts on `𝔅_{T_*,M}` for `T_* = min(T_map, T_ctr)` with explicit T_map/T_ctr;
  contraction const `K = T·L_F + 2C_E√T·L_B < 1/2`. Package via `ContractingWith (1/2)`.

## 36-lemma DAG (names + key deps)
A. Spaces: (1) CompleteSpace C0, (2) CompleteSpace (Path T), (3) localBall_isComplete, (4) pathEval_le_norm.
B. Clamp/powers: (5) clip01M_bounds_lipschitz, (6) clipC0_norm_lipschitz, (7) rpow_lipschitz_Icc_nonneg
   (restrict to [0,M] — NOT negative bases; mirrors repo logistic-Lipschitz mean-value pattern),
   (8) powClipC0_bound_lipschitz.
C. Resolvent interface: (9) resolvent_nonneg_bound_lipschitz, (10) **resolventGrad_bound_lipschitz**
   (∂xR as C⁰→C⁰ with op-norm + Lipschitz — see Layer-1 GAP below), (11) ellipticV_bound_lipschitz.
D. Sensitivity/flux/reaction: (12) sensitivity_bound_lipschitz_nonneg, (13) transportFlux_bound,
   (14) transportFlux_lipschitz (product-difference identity), (15) reaction_bound_lipschitz,
   (16) divFluxPrimitive_bound_lipschitz.
E. Heat/Duhamel: (17) heatC0_contract (‖E(t)f‖≤‖f‖), (18) heatGradC0_bound (‖∂xE(t)f‖≤C_E·t^{-1/2}‖f‖),
   (19) **integral_sing_sqrt_bound** (∫(t−τ)^{-1/2}=2√t — genuine missing utility),
   (20) duhamel0_bound_lipschitz, (21) duhamel1_bound_lipschitz (the analytic HEART),
   (22) duhamel0_continuous_time, (23) **duhamel1_continuous_time** (weakly-singular kernel at τ=t —
   genuine Mathlib gap; ParametricIntegral alone does NOT discharge it).
F. Fixed point: (24) Phi (BCF constructor), (25) Phi_maps_localBall, (26) Phi_lipschitz_on_localBall,
   (27) Phi_contracting_localBall (ContractingWith 1/2), (28) exists_unique_local_mild_clamped
   (ContractingWith.efixedPoint'), (29) fixedPoint_satisfies_mild_equation,
   (30) **mild_unclamped_of_range** (clamp identity on [0,M] → genuine PDE; range proof belongs to positivity layer).
Continuation: (31) mild_restart_at_time, (32) mild_concatenate (heat semigroup law + Duhamel splitting),
   (33) extend_if_uniformly_bounded_before_endpoint, (34) maximal_clamped_mild_exists (use ℝ≥0∞ for Tmax),
   (35) blowup_alternative, (36) global_of_apriori_C0_bound (hook for the energy/Moser global layer).

## Mathlib gaps
Genuinely missing (build): heatC0/heatGradC0 interval-Neumann semigroup; the t^{-1/2} grad estimate (Layer-1);
**resolventGradC0 ∂xR : C0→C0 with C⁰ op-norm + Lipschitz** (Layer-1 currently only pins R''=Rf−f and the
resolvent itself — the GRADIENT C⁰ map is NOT yet pinned; without it the flux u^m·S(v)·vx is not even a closed
C⁰ map, so Layer-2 cannot START); ∫(t−τ)^{-1/2}=2√t + its Bochner version; time-continuity of the singular
Duhamel term; BCF-valued Duhamel constructors; Duhamel splitting/concatenation; maximal-mild framework;
positivity/comparison for clamp removal; c≠0 Neumann drift compatibility.
Derivable-not-one-line: clamp 1-Lipschitz; real-power Lipschitz on [0,M]; sensitivity Lipschitz on v≥0; C⁰
product-Lipschitz; Path-T closed-ball completeness; the T_* arithmetic packaging.
Mathlib primitives confirmed present: ContractingWith (fixed point on complete subset), BCF completeness,
interval-integral norm bounds.

## Convergence check
Layer 2 **closes** (local clamped existence + uniqueness) from Layer 1 + the elliptic-resolvent facts.
It does **NOT** by itself discharge the full Paper-3 PDE — two remaining deps:
(1) **clamp removal** needs 0≤U≤M on the local interval (a max-principle / positivity-cone layer — NOT the
contraction); (2) **global existence** needs a later a-priori C⁰ bound to rule out finite-time blow-up
(restricted regimes via comparison/logistic damping; full theorem likely needs the energy/Moser/Alikakos layer).
HIDDEN Layer-1 dependency to pin NOW: `resolventGradC0_bound_lipschitz` (∂xR as a C⁰ map with operator norm).
