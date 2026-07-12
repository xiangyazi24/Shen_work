# Chi-Negative Closure Roadmap v2 (2026-07-07)

## Architecture (proven)

```
conjugateMildExistenceCore_exists (PROVED)
    ↓
ConjugateMildSolutionData (PROVED: bounded, nonneg, positive, continuous)
    ↓
BFormMildSpectralBootstrapData (4 fields)
    ├── hResolverPos ✅ (IntervalResolverBootstrapFromMild.lean:47)
    ├── hResolverData ⚠️ needs DuhamelSourceTimeC1 witness
    ├── hTimeNhd ⚠️ subset of hPdeAgreement
    └── hPdeAgreement ⚠️ needs ℓ¹ ladder + source identity + Fourier data
    ↓
isClassicalSolution_of_conjugateMild_spectral (PROVED, 0 sorry)
    ↓
localClassicalSolution_of_conjugateMild_spectral (PROVED, 0 sorry)
    ↓
CoupledFluxClassicalLocalExistenceResidual (wiring)
    ↓
theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    (PROVED — existing Lemma 3.1 continuation)
```

## Delivered code (all 0 sorry, axiom-clean)

| File | Lines | Content |
|------|-------|---------|
| IntervalNeumannEllipticGreen.lean | 197 | Green kernel, positivity, L¹ value bound |
| IntervalNeumannEllipticGreenGradient.lean | 174 | Gradient L¹ bound ≤ 1/√μ |
| IntervalBFormMildClassicalBootstrap.lean | 305 | mild → classical bootstrap theorem |
| IntervalResolverBootstrapFromMild.lean | 179 | resolver positivity + partial spectral data |
| **Total** | **855** | |

## The ℓ¹ coefficient ladder (Fable R3)

### Existing infrastructure

- `IntervalCosineCoeffDecay.lean` — C² + Neumann → k^{-2} decay (PROVED)
- `IntervalFullKernelGradientTiling.lean` — gradient heat bound t^{-1/2} (PROVED)
- `IntervalResolverPhysicalC2.lean` — resolver C² from source ℓ¹ (PROVED)
- `IntervalDuhamelSpectralC2FromSourceL1.lean` — Duhamel C² from source ℓ¹ (PROVED)

### Atoms needed for the ladder

| Atom | Status | Purpose |
|------|--------|---------|
| C² + Neumann → k^{-2} decay | ✅ EXISTS | pass 1-2 source coefficient bound |
| C¹ + Neumann → k^{-1} decay | 🔄 Codex running | pass 1 finer estimate |
| Hölder → k^{-θ} decay | 🔄 Codex running | pass 3 composition transfer |
| Green kernel bounds | ✅ DELIVERED | elliptic gain v̂ ≲ û^γ/(μ+λ) |
| Positivity floor u ≥ c > 0 on windows | ⏳ TODO | composition u^γ smoothness |

### The four restart passes

| Pass | Input | Mechanism | Output | Depends on |
|------|-------|-----------|--------|------------|
| 1 | û bounded (mild data) | Duhamel ∫ √λ e^{-λr} dr ≤ λ^{-1/2} | û ≲ k^{-1} | gradient heat bound |
| 2 | û ≲ k^{-1} | convolution + Duhamel | û ≲ k^{-2} log k | C¹ decay atom |
| 3 | u ∈ C^{0,θ} → u^γ Hölder | Hölder→decay → elliptic → Duhamel | û ≲ k^{-3+ε} | Hölder atom + pos floor |
| 4 | u ∈ C^{1,θ} | same chain | û ≲ k^{-4+ε} | C¹ decay + elliptic |

### After pass 4

- Σ λ_k |û_k| < ∞ → spatial C² (spectral M-test)
- Per-mode ODE û'_k = -λ_k û_k + ĝ_k → time C¹
- Together → DuhamelSourceTimeC1 witness
- → fills hPdeAgreement, hTimeNhd, hResolverData
- → BFormMildSpectralBootstrapData complete
- → IsPaper2ClassicalSolution (already proved)
- → CoupledFluxClassicalLocalExistenceResidual (wiring)
- → Theorem 1.1 χ₀<0 DONE

## Dependency graph

```
[Green kernel] ✅
[C² decay] ✅
[gradient heat] ✅
     ↓
[C¹ decay atom] 🔄 ─→ [Pass 1] ─→ [Pass 2]
[Hölder decay atom] 🔄 ─→ [Pass 3 requires pos floor]
[Pos floor] ⏳ ─────────→ [Pass 3] ─→ [Pass 4]
                                           ↓
                              [DuhamelSourceTimeC1 witness]
                                           ↓
                              [hPdeAgreement + hTimeNhd + hResolverData]
                                           ↓
                              [BFormMildSpectralBootstrapData complete]
                                           ↓
                              isClassicalSolution ✅ → Theorem 1.1 χ₀<0
```

## Fable R4 Refined Plan (2026-07-07)

### Key structural insights (change the plan materially)

1. **DuhamelSourceTimeC1On is weaker than assumed** — derivative needs only ONE
   uniform constant `derivBound`, not summable k-dependent bounds.
2. **Circularity is illusory.** hcont (FREE from mild data) → ĝ_k continuous →
   û_k C¹ (FTC on the restart ODE) → ∂_t u → adot witness. Monotone bootstrap.
3. **Skip tower/limit-passage.** Bootstrap directly on the limit. Task 322's
   limit-passage `hadot_unif` is expensive and unnecessary.
4. **Warning: pass 4's k^{-4+ε} is borderline for chem branch.** Need 5th pass
   or sharpened pass 4 for Σ k³ E(k) < ∞.

### Exact atom sequence (~20 atoms, critical path 9 deep)

**Phase A — mode-level (no ladder needed, ∥ with B):**
- A1 mildCoeff_restart_identity (Fubini swap for coefficient of mild integral)
- A2 sourceCoeff_continuousOn (ĝ_k continuous from hcont+hpos+hbound)
- A3 uCoeff_continuousOn
- A4 duhamelCoeff_C1_of_contSource ← A1,A2 (**CRITICAL: the circularity-breaker**)

**Phase B — ladder packaging (∥ with A):**
- B1 window envelope with Σ k³E(k) < ∞ (5th pass or sharpened 4th)
- B2 source envelope Σ k·F(k) < ∞
- B3 Green transfer: ‖∂_t v‖, ‖∂_t v_x‖ ≤ C‖∂_t u‖

**Phase C — function-level time derivatives (← A4,B1,B2):**
- C1 ∂_t u termwise
- C2 ∂_t u_x termwise (← B1, needs Σ k³ E(k) — the 5th pass gate)
- C3 ∂_t v, ∂_t v_x, ∂_t v_xx (← C1,B3)

**Phase D — logistic branch (∥ with E):**
- D1-D3: chain rule → adot → DuhamelSourceTimeC1On for logistic

**Phase E — chem branch (the long pole):**
- E1-E5: flux time-C¹ → adot → DuhamelSourceTimeC1On for chemDiv

**Phase F — assembly:**
- F1 bFormSource combiner (exists)
- F2-F4: fill remaining bootstrap fields → BFormMildSpectralBootstrapData complete

## Fable R5 Analysis (2026-07-07, final round)

### Critical finding: heat-smoothing bridge is circular
S(ε)u₀ > 0 does NOT imply u(ε) > 0 — the heat floor (~√ε) is same order as
Duhamel perturbation. Don't use heat smoothing for direct PPID upgrade.

### The correct non-circular mechanism (already in repo):
1. **Stampacchia negative-part energy** (Cron2 track) → u ≥ 0 from u₀ ≥ 0
   No floor needed. Files: IntervalBFormCron2NegativePartEnergy/*
2. **Square-heat barrier comparison** → u > 0 a posteriori
   After classical regularity. File: IntervalBFormLinearDriftComparisonRegularDischarge
   Known stall: t=0 semigroup convention (fixable by re-seeding at s > 0)

### Design fork (Xiang's call):
- **(A) Weak PID** (stronger than paper): needs Cron2 track + barrier. ~20 extra lemmas.
- **(B) Strong PPID** (matches paper): existing PPID machinery. Much less work.

### Estimated remaining work (revised)

- Phase A: ~4 atoms (A4 Codex dispatched)
- Phase B: ~3 atoms (transfer atoms Codex running)
- Phase C: ~3 atoms
- Phase D: ~3 atoms
- Phase E: ~5 atoms (critical path)
- Phase F: ~3 atoms
- **Total remaining: ~20 atoms + ~5 ladder pass lemmas ≈ 25-30 lemmas**
