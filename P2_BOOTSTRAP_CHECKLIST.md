# Paper 2 Flux-H¹ Two-Step Parabolic-Smoothing Bootstrap — CHECKLIST

Route: ChatGPT-Pro-verified fractional bootstrap (answers/p2-flux-Hrho-parabolic-smoothing-PRO.md).
σ = ρ = 1/2 fixed.

## Reusable analytic bricks (standalone, coefficient-side)

- [x] **B1 `spectral_multiplier_bound`** — `IntervalSpectralMultiplierBound.lean`.
      ∃ C_θ>0, λ^θ exp(−drλ) ≤ C_θ d^(−θ) r^(−θ), general θ>0. Generalizes proven θ=1.
      Axiom-clean (propext, Classical.choice, Quot.sound).
- [x] **B2 `H^σ` cosine Sobolev scale** — `IntervalHSigmaScale.lean`.
      `hSigmaEnergy σ a = Σ_k (1+λ_k)^σ a_k²`, `MemHSigma`. Axiom-clean.
- [x] **B4 elliptic `H^σ → H^{σ+2}` gain** — `IntervalHSigmaScale.lean`.
      `resolver_memHSigmaPlus2_of_memHSigma`: v_k=g_k/(μ+λ_k), multiplier
      (1+λ)/(μ+λ) ≤ max 1 (1/μ); H^{σ+2} energy ≤ (max 1 (1/μ))² · H^σ energy. Axiom-clean.
- [~] **B3 `bform_L2_flux_to_Hsigma`** — `IntervalBFormHSigmaSmoothing.lean`.
      SCALAR KERNEL DONE (axiom-clean): `weighted_kernel_multiplier_le`
      (multiplier at θ=(σ+1)/2 via B1), `terminal_exponent_lt_one`,
      `integral_terminal_singularity` (∫₀ˢ r^{−p}=s^{1−p}/(1−p)),
      `rate_exponent_eq` (1−(σ+1)/2=(1−σ)/2 ⇒ the s^{(1−σ)/2} rate).
      REMAINING: the tsum×τ-integral Minkowski/Tonelli assembly onto the actual
      `duhamelSpectralCoeff` to land the full ‖·‖_{H^σ} ≤ C M s^{(1−σ)/2}.
- [ ] **B5 `chemotaxisFlux_mem_Hrho`** — 1D Sobolev product/composition
      F=u^m·χ0·(1+v)^{−β}·v_x ∈ H^ρ from u∈H^ρ∩L^∞, v∈H^{ρ+2}.
- [ ] **B6 bootstrap assembly** — STEP1 (F∈L²⇒u∈H^{1/2}) → STEP2 (F∈H^{1/2}) → u∈H¹.

## Terminal wiring (existing repo reduction tree — VERIFIED structure)

`paper2_theorem_1_1_general_chi_via_bform_residual2`  (unconditional given per-datum
   `BFormFluxH1Provider` + `BFormSpectralFrontierResidual2`)
  ⟸ `BFormFluxH1Provider`  ⟸ `BFormFluxH1Constructor`
  ⟸ THREE bridges (IntervalBFormP2FactorH1RepresentativesNew.lean):
    - [ ] **Bridge 1 `P2WeightedRestartCoeffToUFactor`**: weighted-L² restart
          coeffs → IntervalH1Weak of u-slice.  ⟸ `P2RestartRepresentativeIdentity`
          (slice = Σ localRestartCoeff·cosineMode on [0,1]) ⟸
          `P2ConjugateLimitRestartHasSum`.
          *** GENUINE HARD CORE: identify abstract Picard-limit `atTop.limUnder`
          with the explicit restart cosine series.  Currently only closeable
          CIRCULARLY (conjugateLimitRestartHasSum_of_fluxBridge needs the flux
          AC bridge = what u∈H¹ provides).  NON-CIRCULAR route: (a) slice∈L² ⇒
          equals own cosine HilbertBasis series (UNCONDITIONAL, basis complete +
          orthonormal already proven); (b) coefficient identity cosineCoeffs(slice)
          = localRestartCoeff (Picard spectral recursion, flux-bridge-free).
    - [ ] **Bridge 2 `P2ResolverInvDenFactorsFromU`**: u∈H¹ ⇒ resolverGrad∈H¹ +
          invDen∈H¹.  (elliptic gain B4 + 1D composition.)
    - [ ] **Bridge 3 `P2NonC2SourceIdentityBridge`**: product-rule source identity.

## Already PROVEN in repo (reuse)
- `residual2_restartCoeff_weighted_l2`: Σ λ_k |localRestartCoeff|² < ∞ (the H^σ-grade
  weighted data) — Bridge 1's coefficient L² input is ALREADY proven.
- `unitIntervalCosineHeatValue_l2_to_intervalH1Weak`: gradient-energy-summable
  cosine series ⇒ IntervalH1Weak (AC + sine-deriv L²) — the H¹-from-coeffs half.
- cosine HilbertBasis orthonormal + complete (BasisWall).
- `resolver_H2_of_L2` (elliptic L²→H² coefficient identity).

## Scoreboard
Reusable bricks: B1 ✅, B2 ✅, B4 ✅ (3 done); B3 🟡 (scalar kernel done, assembly open);
B5 ⬜, B6 ⬜.
Terminal bridges: 0/3 discharged. paper2_theorem_1_1 still CONDITIONAL on the
three bridges (NOT unconditional yet).
Bridge 1 is the dominant wall = abstract-Picard-limit `atTop.limUnder` ↔ explicit
restart cosine series.  Existing closure is CIRCULAR (needs flux AC bridge).
Non-circular route designed (L² HilbertBasis completeness + flux-bridge-free
coefficient identity) but NOT yet formalized.

Last verified (Jun 21): B1, B2, B4, B3-scalar-kernel all build into oleans
axiom-clean (propext, Classical.choice, Quot.sound) via `lake build`.  Root
ShenWork imports all three new modules.
