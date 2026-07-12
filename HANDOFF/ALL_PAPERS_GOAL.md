# ALL PAPERS HEADLINE GOAL (2026-07-07)

Xiang's directive: "所有 paper1-3 的 headline theorem lemma 全部 unconditional."

## Paper 2 (current focus)

### Theorem 1.1 χ₀=0
**STATUS: UNCONDITIONAL ✅** (axiom-clean, 0 sorry)

### Theorem 1.1 χ₀<0
**STATUS: CONDITIONAL on 2 standard PDE facts**

Architecture fully wired (V3, ~3000 lines, 0 sorry):
```
weak PID u₀ → uniform core T(M) → conjugatePicardLimit
  → hnonneg (Stampacchia) ⏳
  → hpos (strong max principle) ⏳
  → ConjugateMildSolutionData
  → ℓ¹ ladder 4-pass → source TimeC1On → spectral bootstrap
  → IsPaper2ClassicalSolution
  → CoupledFluxClassicalLocalExistenceResidual
  → Theorem 1.1 χ₀<0
```

Remaining: Stampacchia hnonneg + strong MP hpos (~10-20 lemmas).
Both oracles confirmed mathematically true.

### Theorem 1.1 χ₀≤0 (combined)
Once χ₀<0 is done: split on `p.χ₀ = 0 ∨ p.χ₀ < 0` and apply the
corresponding branch. This is trivial wiring (the chi-nonpositive headline
at `IntervalDomainChiNonposHeadline.lean` already does this split).

### Theorem 1.2 (0<m≤1, β≥1)
**STATUS: REFUTED (abstract) + MISSING (interval)**
See ROADMAP.md: requires Cor 2.1/Prop 2.5/energy frontiers.
The Lᵖ mountain — avenue C in the original roadmap.

### Theorem 1.3 (regimes i-iv)
**STATUS: REFUTED + MISSING**
Same uninhabited frontiers as 1.2.

## Paper 1 (WaveLemma42/per-step Rothe)

### Headline: `b1_chiNeg_existence_paper_clean_of_cubeApproxData`
**STATUS: assembles cleanly, ONLY `hprodAll` open**

`hprodAll` = per-step Rothe producer. Construction = truncated fixed-source
box Schauder. Route A+ (exponential-rate) was in flight (Tasks W7-W9).

### Key remaining for Paper 1:
- Close the A+ box (weighted-Hölder + exp left-rate) 
- `boxCubeData` (B.4) — finite-net Schauder witness
- Wire `of_truncated_sourceBox → paperRotheStepProducer_of_routeA_greenCore → hprodAll`

## Paper 3

### Headline: `Paper3MainlineTargets`
**STATUS: statement-complete, build-clean (0 sorry), CONDITIONAL on ~6 PDE floors**

Floors:
- P3.1 global existence
- P3.2 uniform persistence (Thm 2.1)
- P3.3 stability dichotomy (Thm 2.2)
- P3.4 sectorial decay
- P3.5 compactness
- P3.6 global stability (Thm 2.3-2.5)
- P3.7 small threshold tails

Same depth as Paper 1's per-step.

## Oracle Assessment (Fable + ChatGPT dual-confirmed, 2026-07-07)

### Paper 1 CRITICAL: b1_chiNeg_existence_final is VACUOUS
- hpos and hlim_neg are unsatisfiable (u≡0 is in the trap)
- Correct headline: Route-A paramCore (WaveLemma42ParamCore.lean:135)
- Big open block: step+tail Rothe continuous-dependence (no mechanism yet)
- hprinciple (Schauder): DONE unconditionally
- Priority: (1) per-step producer contact residuals, (2) step/tail, (3) hsmp/hconv

### Paper 3: 6 named PDE residuals
- Inherits Paper 2's χ₀<0 floor → finish Paper 2 first
- Recent progress: carried conditions reduced ~14 → 6 irreducible
- Deep ends: sectorial orbit + moment-to-uniform
- Thm 2.2 linear dichotomy: UNCONDITIONAL

## Priority order (oracle-confirmed)

1. **Paper 2 Thm 1.1 χ₀<0** — 5 precise Lean obligations remaining
2. **Paper 1 Route-A paramCore** — step/tail is the big open block
3. **Paper 2 Thm 1.2/1.3** — the Lᵖ mountain
4. **Paper 3 existence core** — 6 named PDE residuals
5. **Paper 3 deep ends** — sectorial + moment-to-uniform
