# Codex Brief — Prop 1.1(2) residual window (χ ≥ 1) via the local-Lp bootstrap

Repo ~/Shen_work (HEAD e05c45b3). Rules: 0 sorry, 0 axiom, NEW files only,
`lake build ShenWork.Paper1.<Module>` green per file, APPEND imports to
ShenWork.lean at the end (a module outside the root closure counts as unverified).
Do NOT commit. Do NOT edit other existing files.

## What is open

`Proposition_1_1_positive_critical_branch` covers `0 < χ < 1` at `α = m+γ−1`;
`Proposition_1_1_positive_supercritical_branch` covers all `χ > 0` when
`α > m+γ−1`. The paper's faithful threshold (see
`Proposition11PositiveErrata.lean`, `paper1PositiveCriticalThreshold`) allows
`χ` up to `min{(2m−1)/(m−1), (m+γ−1)/(γ−1)}`, which exceeds 1. The residual is

  critical exponent, `1 ≤ χ`, `paper1PositiveCriticalThreshold p`.

`MChi = (1/(1−χ))^{1/α}` is not even defined there, so NO constant-ceiling
comparison can reach it. The paper uses a different argument.

## The paper's actual route (arXiv:2605.04401 §3.1, pp.17–20) — follow it

Three stages, ONE fixed exponent (not a Moser exponent chain):
1. a translation-uniform, weighted local `L^p` bound for `u`;
2. a uniform `L^∞` bound for `v_x`;
3. a whole-line heat-semigroup `L^{p/m} → L^∞` bootstrap for `u`.

The admissible exponent `P` satisfies
  `max 1 (max m γ) < P`, `P < m + γ`, `χ (P−1) < P + m − 1`,
and `Proposition11PositiveErrata.lean` already proves
`paper1PositiveCriticalThreshold_iff_exists_admissible_exponent`: the faithful
threshold is EXACTLY the existence of such a `P`. Start by extracting `P` from
that theorem — do not re-derive the threshold.

CRUCIAL: bounded uniformly continuous data need NOT lie in any global `L^p(ℝ)`,
so the functional must be the translation-uniform WEIGHTED moment, not `∫ u^p`.

## Committed foundation to build on

`ShenWork/Paper1/WholeLineLocalizingWeight.lean` provides
`localizingWeight κ x = exp (−κ · regDist x)` with `regDist x = sqrt (1 + x²)`,
and: positivity, `ψ ≤ 1`, `HasDerivAt` with `ψ' = −κ (x / regDist x) ψ`, the
domination `|ψ'| ≤ κ ψ`, the comparison `ψ ≤ exp (−κ|x|)`, and the translate
`localizingWeightAt κ x₀ x = localizingWeight κ (x − x₀)`.
(Define the weight THROUGH `regDist`, as that file does — writing
`Real.sqrt (1+x²)` inline makes it a different atom for `nlinarith`.)

## Deliverables

L1. `WholeLineLocalMoment.lean` — the functional
    `wholeLineLocalLpMoment P κ u t x₀ = ∫ x, (u t x)^P * localizingWeightAt κ x₀ x`
    plus: nonnegativity, finiteness for bounded `u` (dominate by
    `‖u‖^P ∫ ψ`, integrability of `ψ` from the `exp(−κ|x|)` comparison), and
    the translation-uniform envelope predicate
    `UniformlyLocalLpBounded P κ u T K : ∀ t ∈ Ico 0 T, ∀ x₀, moment ≤ K`.
    Also prove the second-derivative domination `|ψ''| ≤ κ' ψ` for an explicit
    `κ'` (needed by the integration-by-parts step) — differentiate
    `ψ' = −κ (x/regDist x) ψ` once more; `|d/dx (x/regDist x)| ≤ 1`.

L2. `WholeLineLocalMomentEnergy.lean` — the weighted energy identity/inequality:
    test the equation with `u^{P−1} ψ`, integrate by parts, and use
    `v_xx = v − u^γ` to convert the chemotaxis term, exactly as the paper does
    on p.17–18. The output should be an inequality of the shape
      `(1/P) d/dt ∫u^P ψ + A ∫ |∂_x u^{P/2}|² ψ ≤ K ∫ u^{P+α} ψ + (lower order)`
    with the `χ(P−1)/(P+m−1)` coefficient made explicit — that coefficient
    being `< 1` is precisely the admissibility of `P`.

L3. `WholeLineLocalMomentBound.lean` — absorb the high power by the weighted
    Gagliardo–Nirenberg / Young step and close the differential inequality to
    get `UniformlyLocalLpBounded`.

L4. `WholeLineChiLargeGradientBound.lean` — stage 2: `‖v_x‖_∞ ≤ C` from the
    resolver representation and the local-`L^p` bound (the kernel `(1/2)e^{−|x−y|}`
    is integrable, so a uniformly-local `L^p` bound on `u^γ` suffices).

L5. `Proposition11PositiveLarge.lean` — stage 3 + capstone: semigroup bootstrap
    to `L^∞`, then the Prop 1.1 conclusion (global existence + eventual
    boundedness) on the residual window, and a combined theorem covering the
    whole faithful threshold.

Land L1 and L2 first and report; they are the load-bearing analysis. If a step
genuinely cannot be done, STOP there, report the exact failing goal, and land
everything before it — do not substitute a weaker statement.
