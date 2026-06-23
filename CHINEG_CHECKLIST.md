# χ₀<0 H^1-envelope CarrySeam — atom board (挨个 check 掉)

Goal: `meanReach_H1_conjugate` (capstone, IntervalChiNegSeamFixedReach.lean) UNCONDITIONAL on satisfiable
CMParams + initial regularity. Tracks the `CarrySeam` fields + base.

## DISCHARGED ✅
- hEhatH (supersolution H^σ) — direct Duhamel-deflation route, memHSigma_deflate (aa8fe53)
- hWsum (reflCircle ℓ¹ of W=lift(u)·denom) — reflCircle_mul_fourier_summable (820b383)
- hvnn (resolver positivity) — carrySeam_hvnn ← ConjugateMildSolutionData cone + resolverValue_nonneg (820b383)
- hmean (k=0 mean bound) — mean_bound_of_mild (capstone)
- hdecomp_pos τ=0 — decomp_tau0 (capstone)

## WIREABLE 🟡 (landed producer exists, needs assembly to the conj-mild trajectory)
- hu_sum / hwfac_sum / hvxsum (reflCircle ℓ¹) — MemHSigma→Summable|·| (IntervalWienerAlgebra:211) +
  fourierCoeff_reflCircle_summable_of_cosineCoeff_abs (IntervalDomainPdeUWiring:93); reduces to H^σ of u/denom/vx
- hbr / hbridge (CosineMulBridge/MixedMulBridge) — downstream of the reflCircle ℓ¹ family

## OPEN ⬜ (genuine analytic gap — needs a named producer; grep first, notes may be STALE)
- hmd (per-τ>0 k≠0 Duhamel three-term decomp) — conjugateSlice_decomp_tauLift_pos consumes the heat-kernel/
  cosine-transform/Fubini bundle: hpt_heat, hswap_chem/hswap_log, hheat_cont/hchemI_cont/hlogI_cont, hQcont/hLcont/hLM
- hvrel (Envelopes (resolverCoeff) (cosineCoeffs v)) — resolver-envelope domination
- hdiv (|sineCoeffs vx k| = √λ·|cosineCoeffs v k|) — gradient/divergence spectral identity (vx=v')
- E₀ (base H^{σ₀} envelope) — the L² base / energy method
- L (logistic-flux trajectory envelope) + hFl_cont

## FAITHFUL HYPOTHESIS (keep — not a residual)
- hû₀ : MemHSigma (σ+1/4) (initial data) — legitimate initial-regularity assumption

Last verified: 820b383 (3634 jobs, axiom-clean)

## [2026-06-23] BASE E₀ analysis — the genuine final residual, route identified
IntervalTrajectoryEnvelopeClosure.lean:196-211 documents the precise stall: the L² seed
`conjugatePicardLimit_slice_memHSigma_zero` gives per-slice `MemHSigma 0 (cosineCoeffs (u τ))`, but the τ-UNIFORM
coordinatewise `env ∈ H^{σ₀}` (σ₀>0) is NOT pointwise from it — the mild L∞ ball gives `k↦2M ∉ H^{σ₀}` (no decay).
The base needs the FIRST positive-time smoothing (heat instantaneous regularization). KEY: that IS the
trajBanach fixed point (trajBanach_envelope_of_invariance, IntervalChiNegTrajBanach) at the direct-route
supersolution Estar (IntervalChiNegDirectSupersolution, hEhatH discharged) — the coordinatewise envelope as the
Banach OUTPUT (domination by uniqueness), NOT a prior-envelope-dependent ladder step. So E₀ = the EnvBall/
trajBanach fixed point at Estar, combining the machinery already built this session. NEXT: wire trajBanach +
direct-route supersolution + the MapsTo into the base E₀ producer (the genuine local-existence core).

## [2026-06-23] STRUCTURAL: BCF base is τ=0-broken; redirect to DIRECT domination (no BCF)
trajPhi (Traj t = C(closed box [0,t]×Ω)) requires hcontFam = the Duhamel map continuous on the CLOSED box. But
intervalConjugateDuhamelMap at t=0 = intervalFullSemigroupOperator 0 (lift u₀) + 0 + 0 = 0 (intervalFull
SemigroupOperator_zero: Neumann kernel is a Dirac at t=0, represented as 0), while τ→0⁺ → u₀ (strong continuity).
So the map JUMPS at τ=0 for u₀≢0 ⟹ hcontFam UNSATISFIABLE ⟹ the BCF/trajBanach base (a54820ef + the G1/G2/G3
bridges) is VACUOUSLY conditional. The BCF approach is over-engineered AND broken at τ=0.
REDIRECT: meanReach_H1_of_base takes E₀ as a plain TrajectoryHSigmaEnvelope STRUCTURE (env/henv/hdom), no BCF, no
map-continuity. hdom for u=conjugatePicardLimit holds DIRECTLY: s=0 trivial (u 0 = 0 → 0 ≤ E₀, the τ=0 convention
HELPS), s>0 via conjugateSlice_decomp_tauLift + the direct supersolution bounds (heat≤|û₀|, chemDuhamel≤chemE via
chemDuhamel_direct, log≤logE). The genv(E₀) self-reference resolves as a SEQUENCE-space supersolution fixed point
(small T contraction, memHSigma_deflate), NOT a BCF function-space fixed point — so NO τ=0 continuity issue.
G1/G2/G3 bridges + the BCF base are now SUPERSEDED for the live base route.
