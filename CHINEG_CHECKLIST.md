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
