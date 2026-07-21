# Open-research TODO — far-left χ>0 stability past chiStar

Status 2026-07-21. Companion to `INJECTION_PLAN.md` (which has the full derivation
and the refuted naive route). This file is the short action list.

## Settled (do not reopen)
- [x] Far-left Theorem 1.2 at the paper threshold is PROVED, clean-3:
      `wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural`
      (`0<χ<1/2`), sharp sibling `_chi_pos_full_window` (`χ<chiStar`).
- [x] Architecture: buffered half-line KPP-rectangle successor (seed → successor →
      abstract endgame), mirroring the χ≤0 proofs.

## Open frontier: chiStar < χ < (1+√α)²   (=4 at m=γ=α=1)

### O1 — Time-dependent resolver-defect (Bernstein) estimate  [HIGH RISK, the crux]
- [ ] Prove `V(t,z) − q(t,z)^γ ≤ Ω` on each successor slab, with Ω genuinely below
      `M^γ − x^γ`, uniform in t, NON-circular (not assuming the successor's conclusion).
- [ ] Target the c-dependent form `|V−q| ≤ χB(B−A)/(c−χ(B−A))` so the algebra gives
      the `√(c/2)` threshold scaling (INJECTION_PLAN §7).
- [ ] This needs a NEW *parabolic* Bernstein/gradient theorem for the restarted Cauchy
      slices. The committed `crest_gradient_bound` is STEADY + assumes `b≤1`, so it does
      NOT apply (successor slabs have `M>1`). Building the parabolic version is the work.
- [ ] Lemma name to build: `wholeLineChiPos_restart_resolverDefect_le`.

### O2 — Remove the structural χ<1 ceiling
- [ ] `WholeLineCauchyCeilingRegime` is constructed from `hchi_lt : χ<1`
      (WholeLineChiPosHalfLineSuccessor.lean:668). Generalize the ceiling regime.
- [ ] Target-selection monotonicity uses `1−χ>0` (WholeLineChiPosRectangleTargets.lean:62-106).
      Re-derive without that positivity.
- [ ] Only after O1+O2 can `m=γ=α=1` (where chiStar=1) move past χ=1 toward 4.

### O3 — Refactor the comparison interface (mechanical, after O1)
- [ ] `chiPosFloorGapSharp p Ω x := 1 − x^α − χ·x^(m−1)·Ω`; ceiling analogue.
- [ ] New comparison theorem taking `hdefect : V−q^γ ≤ Ω` instead of the fixed ceiling
      `V ≤ Dup`. Rewrites the `hcoupledDiff`/`hsource` one-sided-Lipschitz block.

### O4 — Free small win (independent, low risk)
- [ ] Replace tail charge `tau·G^γ` by exact `tau·(G^γ−M^γ)`
      (`Dup−b^γ = (M^γ−b^γ)+tau(G^γ−M^γ)`, INJECTION_PLAN §6). Local improvement;
      does not move the R→∞ threshold, but tightens finite-R constants.

## Conceptual caveat
`(1+√α)²` is the **linear/temporal** Turing threshold (dispersion σ(k)). That it is the
exact **nonlinear far-left** threshold is a numerical finding, NOT proved. O1–O3 would
push the proved threshold upward; matching 4 exactly is a separate (harder) question.

## Cleanup
- [ ] Delete this session's redundant whole-line exp-barrier files (see INJECTION_PLAN
      "redundant files" list). Keep the crest/oscillation bricks.
