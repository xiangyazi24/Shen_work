# DOCTRINE — Chi-Negative Remaining ~15 Atoms

## Goal (one sentence)
Fill the 3 remaining fields of `BFormMildSpectralBootstrapData` (hResolverData, hTimeNhd, hPdeAgreement) to close `CoupledFluxClassicalLocalExistenceResidual` and make Theorem 1.1 χ₀<0 unconditional.

## Architecture (proven, non-negotiable)
```
ConjugateMildSolutionData (PROVED)
  + BFormMildSpectralBootstrapData (4 fields, 1 done)
  → isClassicalSolution_of_conjugateMild_spectral (PROVED, 0 sorry)
  → CoupledFluxClassicalLocalExistenceResidual (wiring)
  → Theorem 1.1 χ₀<0 (existing continuation)
```

## Avenue (a) — Direct bootstrap on the limit (MAIN, oracle-consensus)

Non-circular order (both oracles confirmed):
1. Source coeff CONTINUOUS from hcont+hpos+hbound (FREE from mild data)
2. Per-mode ODE → û_k C¹ via FTC (DELIVERED: IntervalDuhamelCoeffFTC.lean)
3. Reconstruct ∂_t u from summable û'_k (needs ℓ¹ ladder envelopes)
4. Chain rule → source C¹ → DuhamelSourceTimeC1On
5. Fill 3 bootstrap fields → done

### Concrete atom list (dependency order):

**Phase A — source coefficient continuity:**
- A1: `sourceCoeff_continuousOn_logistic` — logistic source coeffs continuous in time
- A2: `sourceCoeff_continuousOn_chemDiv` — chemDiv source coeffs continuous in time

**Phase B — per-mode ODE → u_t:**
- B1: `mildCoeff_restart_identity` — coefficient-level Duhamel (Fubini swap)
- B2: `conjugate_timeDerivative_of_mode_ode` — reconstruct ∂_t u from mode ODE + ℓ¹ envelope

**Phase C — source TimeC1On:**
- C1: `logisticSource_duhamelSourceTimeC1On` — logistic source time-C¹
- C2: `resolver_timeRegular_of_timeRegular` — v_t, v_xt from u_t via Green
- C3: `chemDivSource_duhamelSourceTimeC1On` — chemDiv source time-C¹ (long pole)
- C4: Use existing `bFormSource_duhamelSourceTimeC1On` combiner

**Phase D — fill bootstrap fields:**
- D1: `hTimeNhd_of_bFormSourceWitness`
- D2: `hPdeAgreement_of_bFormSourceWitness` (needs ℓ¹ summability + Fourier data)
- D3: `hResolverData_of_sourceTimeC1`

**Phase E — final wiring:**
- E1: Assemble `BFormMildSpectralBootstrapData`
- E2: Wire to `CoupledFluxClassicalLocalExistenceResidual`

### Warning (Fable R4):
The chem branch C3 needs Σ k³ E(k) < ∞ for ∂_t u_x. This requires the ℓ¹ 
ladder to produce E(k) ≲ k^{-4-ε} (5th pass or sharpened 4th). Pass 4's 
k^{-4+ε} is borderline-insufficient.

## Avenue (b) — Weaker chem interface (fallback)

If C3 (chemDiv TimeC1On) is too expensive, try: define adot_chem(t,k) = 
cosCoeff(∂_x F_t(t), k) where F_t uses only L¹ norm of ∂_x F_t (no k-factor).
This avoids the k³ summability gate but needs F_t ∈ L¹ proved differently.

## Avenue (c) — Re-plumb Task 322 combiner (compatibility route)

If direct bootstrap stalls, re-plumb `conjugatePicardLimit_bFormSource_timeC1On_of_logistic_and_chemDivResidual` by constructing the ChemDivSolutionRegularityResidual from the ladder output. More expensive but uses existing wiring.

## Terminal conditions
- Success: `CoupledFluxClassicalLocalExistenceResidual` closed, 0 sorry
- Failure: a field of `BFormMildSpectralBootstrapData` proved unsatisfiable (contradicts mild data structure)
- Soft-stop: 3+ concrete attempts on a single atom all fail with documented reasons
