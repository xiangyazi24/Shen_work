# Codex Brief — P2 Lemma 2.6 Phase A (routine + standard hypotheses)

Repo ~/Shen_work. Rules: 0 sorry, 0 axiom, new files under ShenWork/Paper2/ only.
**Do NOT edit ShenWork.lean** (another lane owns it) — build modules directly by name.
Verify each with `lake build ShenWork.Paper2.<Module>`.

Target: discharge 5 of the 7 frontier hypotheses of
`Lemma_2_6_intervalDomain_of_mass_gradient_frontier` (Paper2/IntervalDomainTheorem11.lean:110)
for the concrete interval-domain solutions. Guide (verified audit): HANDOFF/gpt-Q75-lem26-moser-audit.md.

A1. hu_nonneg: from IsPaper2ClassicalSolution positivity field (le_of_lt).
A2. hpow_int: continuity of x ↦ u(t,x)^pExp on [0,1] ⇒ IntervalIntegrable (compactness route).
A3. hcGrad: define cGrad with a +1 guard ⇒ positivity is algebra.
A4. hMG: instantiate LpMassGradientInterpolationEstimate via the EXISTING interval Agmon /
    interpolation theorem (grep intervalDomain_classicalSolutionPositiveInterpolation and
    CODEX_SPEC_relativeMassGradient.md first — the repo reportedly has this proved; wire, don't rebuild).
    Exponent side condition p+ρ > 1 from the bootstrap p ≥ p₀ > 1.
A5. hmass: mass identity via Neumann flux cancellation (both u_x and v_x vanish at endpoints) +
    Jensen (θ>1): M' ≤ aM − bM^θ ⇒ M ≤ max(M(0), (a/b)^{1/(θ−1)}); Ceta·M^{p+ρ} ≤ Cmass.
    θ=1 case: finite-horizon bound M ≤ M(0)e^{aT} suffices for the hypothesis shape — check the
    exact quantifier in the frontier statement and handle both.

DO NOT attempt hdiss or hgrad (design-level; owner handles the statement fix).
Deliverable: ShenWork/Paper2/IntervalDomainLem26PhaseA.lean (or split files) building green,
#print axioms sections, plus a 10-line report of which existing repo theorems you wired for A4.
