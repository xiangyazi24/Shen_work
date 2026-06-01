# Shen_work — Current Task

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/repos/shen_work && lake build
```

Build green (8387 jobs). 4 sorry total (2 BCF superseded, 2 active).

## Active Sorry

### 1. `IntervalMildPicard.lean:~402` — intervalMildSolution_exists_picard

The main theorem. Needs to construct `MildExistenceData p u₀`.

**Precise remaining steps:**

A. **Add `HasContinuousSlices` to MildExistenceData** — the ball condition
must include spatial continuity because `resolverGrad_sup_le_of_bounded`
(the resolver gradient bound needed for the flux) requires
`ContinuousOn (intervalDomainLift u) (Icc 0 1)`.

B. **Propagate continuity through downstream theorems:**
   - `picardIter_ball` → add continuity induction hypothesis
   - `picardIter_geometric` → add continuity to ball hypothesis
   - `picardLimit_is_mildSolution` → add continuity to hcontract hypothesis
   - `intervalMildSolution_of_data` → pass through

C. **Prove continuity preservation:**
   - `picardIter_continuous_slices`: by induction. Base: `S(t)u₀` is C²
     on [0,1] for t > 0 (from `intervalFullSemigroupProfile_contDiffOn_two_closed`).
     Step: Φ maps spatially-continuous bounded to spatially-smooth (same reason:
     the Duhamel integral of a bounded source via the heat semigroup is smooth).
   - `picardLimit_continuous_slices`: uniform limit of continuous on compact
     is continuous (`TendstoUniformly.continuous`).

D. **Instantiate constants:**
   - C_grad := `heatGradientLinftyLinftyConstant` (fixed)
   - B_G := from `resolverGrad_sup_le_of_bounded` with M
   - C_Q := M * B_G (flux sup bound)
   - L_Q := from `chemFlux_div_lipschitz` (flux Lipschitz)
   - C_L := from `intervalLogisticReaction_lipschitz_on_bounded` (needs α ≥ 1)
   - T := from `exists_small_contraction_time` with A = 2|χ₀|·C_grad·L_Q, B = C_L
   - K := A·√T + B·T < 1
   - M := 2·max(B₀, 1) where B₀ bounds u₀
   - Verify MapsTo: M/2 + |χ₀|·C_grad·2√T·C_Q + T·C_L·M ≤ M (small T)

E. **Discharge integrability:** for spatially-continuous bounded w,
   `intervalDomainLift w` is continuous on [0,1] hence measurable hence
   integrable (via `intervalMeasure_integrable_of_abs_bound`). Spatial
   continuity makes ALL integrability hypotheses trivially dischargeable.

### 2. `IntervalDuhamelIntegrability.lean:~63` — gradient edge case

`gradDuhamel_sup_bound_universal`: case `¬(∀ s, Integrable (q s))` ∧
`IntervalIntegrable (time integrand)`. Edge case — never occurs for
spatially continuous trajectories (which is what the Picard iteration uses).
Can be left as sorry without blocking progress.

## What Is Complete (0 sorry)

- Picard iteration definition
- Geometric Cauchy → pointwise convergence
- Pointwise tail bound (dist_le_tsum)
- Uniform convergence
- Limit is bounded
- **Limit is a fixed point (picardLimit_is_mildSolution)**
- Conditional existence (intervalMildSolution_of_data)
- Ball induction (picardIter_ball)
- Geometric induction (picardIter_geometric)
- Universal value Duhamel bound (valueDuhamel_sup_bound_universal)

## Repository State

- 1761 theorems/lemmas/defs across Paper1/2/3
- Paper2 Theorem 1.1: proved conditional on localExistence (0 sorry)
- From mild solution to localExistence: [A][B][C] regularity + [D] coupled (u,v)
