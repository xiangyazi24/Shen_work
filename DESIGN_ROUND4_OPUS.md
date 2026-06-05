# DESIGN_ROUND4_OPUS.md — Opus Response to Codex Round 3 (R1-R6)

**Goal**: converge to a consensus gap list.

---

## R1: One-sided α theorem may not fit old two-sided interfaces

### Codex's concern

Current logistic Lipschitz is two-sided (`|u| ≤ M`). A one-sided replacement
(`u ∈ [0, M]`) for α > 0 may not fit interfaces that quantify over `|u| ≤ M`.

### Verdict: **AGREE — real but containable, not a showstopper**

The concern is valid. `Real.rpow` for negative real bases with non-integer
exponents produces junk values (or requires the `1 ≤ p` branch). A one-sided
theorem on `[0, M]` uses `0 ≤ u → u ^ α = u ^ α` cleanly, but callers
phrased as `|u| ≤ M` need adjustment.

**Containment strategy**: provide BOTH theorems:
- Keep existing `intervalLogisticReaction_lipschitz_on_bounded` (α ≥ 1, two-sided)
- Add `intervalLogisticReaction_lipschitz_on_nonneg_bounded` (α > 0, one-sided)

The Picard iteration already carries `hnonneg` for all iterates, so it can call
the one-sided version. Older scaffolds (`IntervalCoupledBallEstimates`) that
use two-sided form keep working with the old theorem (under α ≥ 1).

**Effort**: ~50-80 lines for the new theorem + adapter. No interface-wide rewrite.

**Showstopper?** No.

---

## R2: Spatial C2 induction does not imply source time-C1

### Codex's concern

`PicardIterateHasC2Slices` gives spatial C2 of u_n(t) for each t, but
`DuhamelSourceTimeC1` for the total source needs time derivatives of cosine
coefficients. Spatial C2 alone does not give time-C1.

### Verdict: **AGREE — this is the most important correction in Round 3**

Codex is right. The current induction predicate is:

```
PicardIterateHasC2Slices = ∀ t, ContDiffOn ℝ 2 (lift(u_n t)) [0,1] + Neumann
```

This is purely spatial. For `DuhamelSourceTimeC1` of the source `F_n(s, ·)`, we need:

```
HasDerivAt (fun r => cosineCoeffs(F_n(r, ·)) k) (adot r k) r
```

which requires `∂_s F_n(s, x)` to exist, i.e., `∂_s u_n(s, x)` must exist.

**However, this is NOT a showstopper — the time derivative is DERIVABLE.**

For the Picard iterates, time differentiability follows from the Picard map
structure:

```
u_{n+1}(t, x) = S(t)u₀(x) + ∫₀ᵗ S(t-s) L(u_n(s))(x) ds + chemotaxis
```

The time derivative of each term:
1. `∂_t S(t)u₀ = ΔS(t)u₀` — exists from `unitIntervalCosineHeatValue_hasDerivAt_time`
2. `∂_t ∫₀ᵗ S(t-s) L(u_n(s)) ds = L(u_n(t)) + ∫₀ᵗ ΔS(t-s) L(u_n(s)) ds`
   — exists from `duhamelIntegrand_hasDerivAt` (in IntervalDuhamelClosedC2.lean)
3. Chemotaxis gradient term: similar structure

So the iterate n+1 IS time-differentiable, with time derivative computable from
the iterate n's source + the semigroup Laplacian. This is a THEOREM to prove,
not an obstruction.

**Action**: strengthen the induction predicate to include time differentiability:

```lean
structure PicardIterateRegularity (p : CM2Params) (u₀ : ...) (T : ℝ) (n : ℕ) where
  spatialC2 : PicardIterateHasC2Slices p u₀ T n
  timeDeriv : ∀ t ∈ (0, T), ∀ x, HasDerivAt (fun s => picardIter p u₀ n s x) (...) t
  timeDerivContinuous : ContinuousOn (∂_t u_n) ((0,T) × [0,1])
```

Base case: the semigroup has time derivative = Laplacian (from cosine series).
Induction step: the Picard map's time derivative exists from Duhamel differentiation.

**Effort**: ~200-300 lines for the time-differentiability induction.

**Showstopper?** No — it's a genuine additional induction layer but the
mathematical content is standard (differentiate the Duhamel integral in time).

---

## R3: Resolver time differentiability absent

### Codex's concern

Total-source time-C1 requires `t ↦ R(u_n(t))` and `t ↦ ∂_x R(u_n(t))` to be
differentiable in t. Current resolver estimates are spatial, not temporal.

### Verdict: **AGREE — genuine gap, but solvable from existing infrastructure**

The resolver R(u) is defined spectrally: its cosine coefficients are algebraic
functions of the source coefficients `cosineCoeffs(ν · u^γ)`. Specifically:

```
R̂_k(u) = ν · ĉ_k(u^γ) / (μ + (kπ)²)
```

For time differentiability along `u_n(t)`:

```
∂_t R̂_k(u_n(t)) = ν / (μ + (kπ)²) · ∂_t ĉ_k(u_n(t)^γ)
```

And `∂_t ĉ_k(u_n(t)^γ)` involves the chain rule:

```
∂_t [u_n(t)^γ](x) = γ · u_n(t,x)^{γ-1} · ∂_t u_n(t,x)
```

then Leibniz interchange for the cosine coefficient integral.

All of this works IF:
- u_n has time derivative (from R2 above — solvable)
- u_n is positive (from Picard positivity — exists)
- γ ≥ 1 so u^{γ-1} is bounded on [0, M] (from γ ≥ 1 hypothesis — exists)

The spectral division by `(μ + (kπ)²)` actually IMPROVES summability (more decay),
so the resolver coefficients are BETTER behaved than the source coefficients.

**Effort**: ~100-150 lines. The chain:
1. `HasDerivAt (fun t => u_n(t,x)^γ) (γ·u_n(t,x)^{γ-1}·∂_t u_n(t,x)) t`
   — from `HasDerivAt.rpow_const` + chain rule
2. Leibniz for `∂_t ĉ_k(u_n(t)^γ)` — from `cosineCoeffs_hasDerivAt_of_smooth_param`
3. Algebraic: `∂_t R̂_k = divider · ∂_t source_k`

**Showstopper?** No.

---

## R4: Endpoint restart at T₀ not available

### Codex's concern

`IsPaper2ClassicalSolution` is on open time `(0, T₀)`, so the solution at T₀
itself is not accessible. Restart-before-end plus gluing is needed.

### Verdict: **AGREE — genuine formal issue, standard PDE handling**

The solution lives on `(0, T₀)`, not `[0, T₀]`. We cannot evaluate u(T₀).
The restart must use u(τ) for some τ < T₀.

The approach:
1. From a-priori bounds: `|u(t, x)| ≤ M` for all `t ∈ (0, T₀)`
2. Choose τ = T₀ − η/2 where η = local lifespan depending only on M
3. u(τ) is continuous, bounded by M, positive (from solution properties at interior time)
4. After G0: u(τ) satisfies `PositiveInitialDatum` (continuous + bounded + positive)
5. Run local existence from u(τ) with lifespan ≥ η
6. The restarted solution extends past T₀ by at least η/2
7. Glue using overlap uniqueness on (τ, T₀)

**Key subtleties in Lean**:
- Must show u(τ) as a function on `intervalDomainPoint` satisfies the initial
  data predicate (continuity from C2, boundedness from a-priori, positivity from
  `D.hpos`)
- The gluing needs `IsPaper2ClassicalSolution` on (0, τ) ∪ (τ, T₀ + η)
  — use overlap uniqueness or locality
- The exported `δ` in `IntervalDomainUniformLocalExistence` must be η/2 or similar

**Effort**: ~200-300 lines for restart + glue.

**Showstopper?** No — standard PDE continuation argument, just verbose in Lean.

---

## R5: G0 changes every proof that treats admissible as boundedness

### Codex's concern

Adding continuity to `initialAdmissible` breaks `.admissible` projections
throughout the codebase. Estimate: 50-150 lines, not 5.

### Verdict: **AGREE — I was wrong about "5 lines"**

After checking the codebase, `.admissible` is used as a boundedness proof in
at least 4-5 files. Each usage needs `.admissible.2` (or a named projection)
after the change.

**Corrected estimate**: 50-100 lines.

The fix:
```lean
-- In BoundedDomainData (or intervalDomain override):
initialAdmissible := fun u₀ => Continuous u₀ ∧ BddAbove (Set.range fun x => |u₀ x|)

-- Projection lemmas:
lemma PositiveInitialDatum.continuous : Continuous u₀ := ...
lemma PositiveInitialDatum.bddAbove : BddAbove (...) := ...
```

Then `s/hu₀.admissible/hu₀.bddAbove/g` (approximately) across callers.

**Showstopper?** No — mechanical.

---

## R6: hposWit and G0 interact

### Codex's concern

After G0, `hposWit` would also need to recover continuity from traces. This
makes standalone `hposWit` even harder.

### Verdict: **AGREE — but this reinforces the "thread hu₀" strategy**

After G0, `PositiveInitialDatum` includes continuity. So `hposWit` claims:
given two solutions with traces converging to u₀, u₀ is continuous.

This IS true (uniform limit of continuous functions is continuous), but
PROVING it in Lean requires extracting continuity from the trace definition.
The proof would be: u(t) is continuous for t > 0, u(t) → u₀ uniformly,
uniform limit of continuous functions is continuous. Mathlib has
`UniformCauchySeqOn.tendsto_uniformOn_range` or `tendstoUniformlyOn_of_...`
but the exact formulation needs care.

**Better route (as agreed in Round 2)**: don't prove standalone `hposWit`.
Instead, thread the original `hu₀ : PositiveInitialDatum` through the
construction. This eliminates the need to recover continuity from traces.

**Effort for threading**: ~100-150 lines of proof-threading through gluing chain.

**Showstopper?** No.

---

## Consensus Gap List

Based on three rounds of adversarial review, here is the converged list:

### Tier 1: Must Do First (Blocking)

| # | Gap | Difficulty | Est. Lines | Risk |
|---|-----|-----------|-----------|------|
| **G0** | Add continuity to `PositiveInitialDatum`, projection lemmas, repair callers | Routine | 50-100 | Low — mechanical |
| **G1** | Export `GradientMildSolutionData` from Picard proof | Wiring | 30-50 | Low |
| **G1a** | One-sided logistic Lipschitz for α > 0 on [0,M] | Medium | 50-80 | Low |

### Tier 2: Core Mathematical Gaps

| # | Gap | Difficulty | Est. Lines | Risk |
|---|-----|-----------|-----------|------|
| **G2** | Gradient→standard Duhamel IBP for full source on [0,1] | **Hard** | 200-400 | High — needs kernel IBP + boundary handling |
| **G3** | Total-source `DuhamelSourceTimeC1` including chemotaxis flux time-C1 | **Hard** | 300-500 | High — needs R2+R3 solved first |
| **G4** | `hpde_u` + full `GradientMildClassicalRegularityFrontierData` (9 fields) | **Hard** | 500-800 | High — central regularity theorem |
| **G5** | Sup-norm semigroup approximate identity (uniform over [0,1]) | Medium | 150-250 | Medium — standard but not present |

### Tier 3: Assembly and Continuation

| # | Gap | Difficulty | Est. Lines | Risk |
|---|-----|-----------|-----------|------|
| **G6** | Thread `hu₀` through gluing to eliminate `hposWit`/`hposLowerWit` | Medium | 100-150 | Low-Medium |
| **G7** | Uniform continuation / `hreach` from local + a-priori bounds | Medium-Hard | 200-300 | Medium — restart-before-end + glue |

### Sub-gaps within Tier 2 (from R2 + R3)

| Sub-gap | Parent | Content |
|---------|--------|---------|
| Time differentiability of Picard iterates | G3 | `∂_t u_{n+1}` from Duhamel differentiation |
| Resolver time differentiability | G3 | `∂_t R(u_n(t))` from chain rule + spectral division |
| Strengthen PicardIterateHasC2Slices | G3 | Add time derivative + continuity to induction predicate |

### Dependency DAG (corrected)

```
G0 (statement fix)
  |
  v
G1a (one-sided logistic Lip) ----+
  |                               |
  v                               |
G1 (export GradientMildSolnData) |
  |                               |
  +---> G5 (initial approach)     |
  |                               |
  +---> G3 (total source time-C1) <-- needs time-diff induction (R2/R3)
  |       |
  |       +---> G2 (gradient→standard IBP)
  |               |
  |               v
  |             HasRestartCosineRepresentations
  |               |
  |               v
  +-----------> G4 (classical regularity frontier)
                  |
                  v
                hlocal
                  |
                  v
                G7 (uniform continuation)
                  |
                  v
                G6 (thread hposWit)
                  |
                  v
              Theorem 1.1
```

Note: G2 and G3 are entangled. The IBP (G2) needs the source to be
well-behaved (from G3), and G3's `DuhamelSourceTimeC1` needs the spectral
agreement (from G2) to close the restart. The resolution: G3 provides
`DuhamelSourceTimeC1` for the total source (from time-differentiability
induction), G2 converts this to the correct spectral representation.

### Total Estimate

| Tier | Lines |
|------|-------|
| Tier 1 (G0, G1, G1a) | 130-230 |
| Tier 2 (G2, G3, G4, G5) | 1150-1950 |
| Tier 3 (G6, G7) | 300-450 |
| **Total** | **1580-2630** |

### What's a Showstopper vs Engineerable

**No showstoppers remain** after G0 (statement fix). Every gap is either:
- Routine wiring (G0, G1, G1a, G6)
- Standard PDE in Lean (G5, G7, R4)
- Hard but well-defined analytic proofs with existing infrastructure (G2, G3, G4)

The hardest pieces: G4 (classical regularity frontier, especially `hpde_u` and
joint time-derivative continuity) and G2+G3 entanglement (gradient→standard IBP
interleaved with total-source time-C1).

Codex's most valuable contribution: identifying R2 (spatial C2 ≠ source time-C1)
as the key risk that my original design underweighted.
