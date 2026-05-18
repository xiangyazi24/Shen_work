# UNDERSTANDING.md — Shen_work Lean 4 Formalization

## What this project is

Lean 4 formalization of results from Shen's paper on chemotaxis-logistic traveling waves
(arXiv:2605.04401), plus related Chen-Ruau-Shen persistence results (arXiv:2604.02599).

The PDE system (CM):
```
u_t = u_xx − χ(u^m v_x)_x + u(1 − u^α),   x ∈ ℝ
v_xx − v + u^γ = 0
```

## Architecture

### Core layer (Defs.lean)
- `CMParams`: parameters (χ, m, α, γ) with exponent constraints
- `IsClassicalSolution`, `IsGlobalClassicalSolution`: PDE solution predicates
- `IsTravelingWave`, `IsMonotoneTravelingWave`: TW structure
- `Psi`: Green's function Ψ(u) = (λ/2D) ∫ exp(-λ/D |x-y|) u(y) dy
- Main theorems: existence, stability, uniqueness (some sorry'd)

### PDE infrastructure layer
- **HeatSemigroup.lean**: heat kernel, semigroup, L∞ bounds, linearity (`heatSemigroup_sub`),
  `heatKernel_zero`/`heatSemigroup_zero` (t=0 gives kernel=0, semigroup=0)
- **LeibnizRule.lean**: **fully proved** — parametric integral differentiation via
  `hasDerivAt_integral_of_dominated_loc_of_lip`, Lipschitz kernel bound (exp MVT),
  measurability (piecewise). This is the technical core for Ψ derivative bounds.
- **MildSolution.lean**: Duhamel operator, logistic Lipschitz, contraction framework.
  `duhamel_integral_bound` decomposed: pointwise bound (via `heatSemigroup_abs_bound` +
  `heatSemigroup_zero`) → `norm_setIntegral_le_of_norm_le_const` → `L*t*D` bound.
  Integrability via `Measure.integrableOn_of_bounded` + `ae_restrict_mem`.
  Remaining sorrys: `AEStronglyMeasurable` (measurability of parametric integral)
- **ODEExistence.lean**: Picard-Lindelöf for logistic ODE (norm bound + Lipschitz proved)
- **ParabolicMaxPrinciple.lean**: classical comparison principle framework.
  Complete chain: subsolution/supersolution → difference is linear subsolution →
  weak max principle → comparison. ONE core sorry: coercive barrier estimate.
- **TravelingWaveConstruction.lean**: cappedExp approximation + tendsto + monotonicity
- **TravelingWaveODE.lean**: phase space (Fin 4 → ℝ), equilibria E0/E1, Jacobian matrices,
  eigenvector structure, shooting theorem statement.
  `jacobianAtZero_stable_eigenpair` **proved** (simp + ring).
  `jacobianAtOne_unstableVector_eigen` **proved** (simp + (try ring) <;> linear_combination hchar;
  key insight: `first | ring | linear_combination` fails because `first` retries ALL goals per branch;
  `(try ring) <;> linear_combination` correctly closes ring-identity goals first, then applies hchar only to the remaining goal).
  `vectorField_contDiffAt` **proved** (ContinuousLinearMap.proj + contDiffAt_pi + dsimp;
  key: use `dsimp` not `simp only [Matrix.cons_val_...]` to reduce vector indexing after `fin_cases`;
  explicit `contDiffAt_const (c := ...)` annotations needed for Lean to infer constants).
  `localSolutionExists` **proved** (Picard-Lindelöf extraction from picardLindelofData;
  HasDerivWithinAt → HasDerivAt via Icc_mem_nhds).
  `linearization_at_E0` **proved** (fderiv_pi + simp with zero_pow).
  `linearization_at_E1` **proved** (fderiv_pi + simp with one_pow).
  `localSolutionExists` **proved** (Picard-Lindelöf + HasDerivWithinAt → HasDerivAt).
  Remaining sorrys: shooting_theorem (deep — phase plane analysis).

  Key techniques discovered:
  - `(try ring) <;> linear_combination hchar` for mixed ring/hypothesis goals
  - `dsimp` (not simp only [Matrix.cons_val...]) for vector index reduction
  - `contDiffAt_const (c := ...)` for explicit constant annotation
  - `fderiv_pi hdiff` + `ContinuousLinearMap.coe_pi/proj_apply` for componentwise fderiv
  - `continuous_rpow_const.comp_aestronglyMeasurable` for rpow measurability (MildSolution)

### Paper theorem layer
- **ComparisonPrinciple.lean**: rectangle ODE barriers (proved) + PDE comparison (sorry)
- **StabilityUniqueness.lean**: cm_tw_stability (proved), existence_tw_small_pos (proved)
- **TravelingWaves.lean**: existence wrappers
- **Paper3/Defs.lean**: persistence + global stability (deep PDE, sorry)

## Key design decisions

1. **cappedExp is a placeholder**: `min(1, exp(-κx))` satisfies tendsto and positivity
   but NOT the traveling wave ODE. Real TW solutions need phase plane / shooting.

2. **Import cycle constraint**: Defs.lean ← TravelingWaveConstruction.lean, so main
   theorems in Defs can't use cappedExp. Workaround: prove in StabilityUniqueness.lean.

3. **ParabolicMaxPrinciple is self-contained**: uses its own dt/dx/dxx definitions
   (not iteratedDeriv from Defs). Bridge lemma needed to connect.

4. **ContDiff ℝ 2 hypotheses added to cm_tw_stability**: TW solutions are C², but
   `IsTravelingWave` doesn't state this. Added as extra hypotheses.

## Core sorry: coercive_exponential_barrier_estimate

This is THE irreducible analytic step. Everything else in the comparison framework
is proved from it. The proof requires:
- Compactness argument on truncated domain [0,T]×[-R,R]
- Interior maximum characterization (∂_t ≥ 0, ∂_xx ≤ 0)
- Product rule for exp(-λt)*w derivatives
- ε → 0 limiting argument

Proof sketch is in the docstring (6 steps). Formalizing needs Lean infrastructure
for parabolic PDEs on noncompact cylinders (not in Mathlib).

## ChatGPT collaboration

The project uses ChatGPT (Pro Extended Thinking) via bridge for proof assistance:
- Script: `~/repos/chatgpt-bridge/ask-chatgpt.sh`
- Channels: cron-shen, cron-shen1-4 (5 tabs)
- Push mode (default): fire-and-forget, results via tmux inject
- Results: `/tmp/chatgpt-bridge/<task-id>.md`
- Key contributions: exp MVT, cappedExp monotonicity, difference lemma,
  spatiallyConstant supersolution, operator estimate framework

## Mathlib version
- Lean 4.29.1
- Mathlib (latest as of 2026-05)
