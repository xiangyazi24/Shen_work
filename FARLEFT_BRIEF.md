# Codex lane: far-left equilibrium convergence beyond χ<1/2 (left-favorable weighted energy)

## Goal
Produce `UniformCoMovingLeftEquilibriumConvergence c u`
(WholeLineCauchyLeftTailBridge.lean:18) — `∀ ε>0, ∃ R T, ∀ t z, T≤t → z≤−R →
|coMovingPath c u t z − 1| < ε` — for the whole-line critical Cauchy solution
`u = wholeLineCauchyGlobalU p u₀`, for a χ-range STRICTLY LARGER than the
current `χ < 1/2`, ideally the full stable regime (`χγ ≤ 1`). This is the sole
remaining gap in the Theorem-1.2 `hcore` left-tail
(`uniformMovingFrameLeftTailConvergence_of_leftEquilibrium` bridges it).

## Why χ<1/2 is only a TOOL limit, not the truth
- The wave's far-left limit is the EQUILIBRIUM `u≡1`
  (`FrozenStationaryWaveProfile.lim_neg_inf`, Statements.lean:2935).
- The ONLY current far-left tool is the half-line RECTANGLE
  (`uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors`,
  WholeLineChiPosHalfLineRectangle.lean:77), whose gap contracts by factor `2χ`
  (`ChiPosHalfLineRectangleStep.gap_le`) — hence `χ<1/2`. The sharp `χ/(1-χ)`
  variant caps at the same `χ<1/2`.
- The equilibrium `u≡1` is LINEARLY STABLE with spectral gap `−α` for `χγ ≤ 1`
  (`dispersion_le_neg_alpha`, WholeLineChiPosDispersion.lean) — far beyond 1/2.
  So a sharper mechanism should reach `χγ ≤ 1`.

## The mechanism to build
Mirror the hcore weighted-L² dissipation to a LEFT-favorable weight. The hcore
lane proved co-moving weighted-L² decay with weight `e^{2ηz}` (η>0), which
grows at `z→+∞` and controls the far-RIGHT (`u→0`); it DEGENERATES at `z→−∞`,
missing the far-left. For the far-LEFT equilibrium perturbation `w = u − 1`,
use a weight that is non-degenerate / growing as `z→−∞` (e.g. `e^{−2ηz}` or a
two-sided `cosh`-type weight), giving an energy
`E_L(t) = ∫ φ_L(z) |u(t,z+ct) − 1|² dz` that SEES the far left.

Key coefficient bookkeeping (this is the crux — do it honestly):
- Linearizing `u(1−u^α)` at `u=1` gives reaction coefficient `−α` (the gap).
- The moving-frame TRANSPORT term contributes `∓ c η` depending on weight sign;
  with a left-growing weight the transport is DESTABILIZING (`+cη`-type), so the
  reaction gap `α` must dominate it: expect a condition like `α > (transport &
  chemotaxis cross terms)`, with the chemotaxis cross term bounded via the
  resolvent gradient `‖∂ₓ v‖ ≤ K‖u^γ‖` and `u` near 1, contributing a `χγ`
  factor. Track exactly where `χγ` enters and report the achievable threshold.
- Near `u=1` the nonlinear remainder is higher order (`O(w²)`), absorbable.

Reuse: the hcore energy files
(WholeLineWeightedRegularityHCoreEnergyNatural.lean,
...FixedBoundEnergyNatural, ...EnergyEnvelope), `dispersion_le_neg_alpha`,
`frozenElliptic_deriv_abs_le_of_localMoment`, `coMovingPath`, and the localizing
weight files (WholeLineLocalizingWeight*.lean). Prefer building the mirror
energy by analogy to the committed right-weight dissipation.

## Honest-threshold mandate
Determine the ACTUAL χ threshold your estimate achieves. Acceptable outcomes,
in order of value:
1. Full stable regime / `χγ ≤ 1` — closes the window.
2. Any explicit threshold strictly above `1/2` — records real progress + the
   exact obstruction to going further.
3. A rigorous proof that the left-favorable weighted energy CANNOT beat `1/2`
   for a specific reason (e.g. an unbeatable transport-vs-gap sign) — then the
   frontier is genuinely a different mechanism; document it precisely.
Do NOT fake a full-window closure. If a sub-estimate needs a missing Mathlib
object, build it as its own file (no axioms).

## Rules
- 0 sorry / 0 axiom / clean-3 (`[propext, Classical.choice, Quot.sound]`).
- Gate: `lake build ShenWork` (root closure) + `#print axioms` through root.
- New files under `ShenWork/Paper1/`; append imports to `ShenWork.lean`. Do not
  edit committed proofs unless strictly necessary (keep clean-3).
- Commit incrementally on branch `codex/farleft-energy` (isolated worktree).
- No effort cap.

## Endpoint
Produce `UniformCoMovingLeftEquilibriumConvergence c (wholeLineCauchyGlobalU p u₀)`
for the widest χ you can prove, then note whether it suffices to feed
`uniformMovingFrameLeftTailConvergence_of_leftEquilibrium` for the full stable
regime, closing the last hcore gap.
