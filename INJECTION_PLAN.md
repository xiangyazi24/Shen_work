# Far-left χ>0 past chiStar — the crest-bound injection plan

## Status (2026-07-21, verified)

- **≤chiStar far-left is DONE** (clean-3, 0 sorry):
  `wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural`
  (WholeLineWeightedRegularityChiPosLeftEquilibriumNatural.lean), `0<χ<1/2` critical;
  sharp `_chi_pos_full_window` covers `χ<chiStar`. Do NOT rebuild.
- Architecture = buffered **half-line KPP-rectangle successor** (mirrors chiNeg/chiZero):
  seed (ChiPosHalfLineSeed) → `exists_next_chiPosHalfLineRectangle`
  (ChiPosHalfLineSuccessor) → abstract endgame
  `uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors`.
  Floor lifted to `L≈1` by the KPP subsolution `chiZeroKPPFloor C L lam → L`
  (Q221: plateau floor alone is a fixed `d<1`; the KPP subsolution is what lifts it).

## Open frontier

`chiStar < χ < (1+√α)² = 4` (true Turing threshold, WholeLineChiPosDispersionSharp).
The rectangle mechanism is exhausted at its wall (chiStar). Need a sharper control
of the chemotaxis defect to push higher.

## The naive injection point — REFUTED (Q227, grounded in code)

`chiPosFloorGap p M x = 1 - x^α - χ·( x^(m-1) · (M^γ - x^γ) )`
(WholeLineChiPosRectangleTargets.lean:24). I thought `(M^γ - x^γ)` was crude and
replaceable by `resolver_oscillation_bound`. **WRONG — non-improving:**
- The current floor proof already uses the TIGHT pointwise bound `V - x^γ ≤ M^γ - x^γ`
  at contact (`hchemResolver`, WholeLineChiPosHalfLineWeightedComparison.lean:427-433,
  via `hresolver : V ≤ Dup`, `Dup ≈ M^γ`).
- `resolver_oscillation_bound` applied to the source `q^γ` gives `|V - q^γ| ≤ M^γ - ell^γ`,
  and since `ell ≤ x`, `M^γ - ell^γ ≥ M^γ - x^γ`. So the oscillation width is LARGER
  (weaker). For m=γ=α=1 with band width 2E it re-gives `2χE < E ⇒ χ < 1/2`. No gain.
- (My error: located the term, never checked the inequality direction. 2nd such retraction.)

## The REAL path (Q227 §5,§7,§8,§9) — genuinely hard, not surgical

Two independent obstructions to reaching `(1+√α)²`:

1. **Need a time-dependent relative-defect bound** `V(t,z) - q(t,z)^γ ≤ Ω` with Ω
   genuinely smaller than `M^γ - x^γ`, uniform on the slab, NON-circular. Then
   `chiPosFloorGapSharp p Ω x := 1 - x^α - χ·x^(m-1)·Ω`, threshold `χ·L^(m-1)·Ω < 1-L^α`.
   The `√(c/2)` scaling IS correct IF a c-dependent dynamic bound `|V-q| ≤ χB(B-A)/(c-χ(B-A))`
   holds on every slice (Q227 §7 algebra: `2Bχ² + 2Eχ < c ⇒ χ→√(c/2)` as E→0).
   BUT the committed `crest_gradient_bound` does NOT supply it: it is a STEADY crest
   estimate assuming `b ≤ 1` (`hb1`), while the successor has time-dependent slices with
   `M > 1`. Needs a NEW parabolic Bernstein/gradient theorem for the restarted orbit —
   the highest-risk build (`wholeLineChiPos_restart_resolverDefect_le`).
2. **χ<1 is structural.** `WholeLineCauchyCeilingRegime` is built from `hchi_lt : χ<1`
   (successor:668), and target monotonicity needs `1-χ>0` (RectangleTargets:62-106).
   At m=γ=α=1 (chiStar=1), reaching 4 requires replacing the ceiling regime AND the
   target-selection algebra too.

**One small real improvement available now** (Q227 §6): replace tail charge `tau·G^γ`
by the exact `tau·(G^γ - M^γ)` (from `Dup - b^γ = (M^γ-b^γ) + tau(G^γ-M^γ)`). Local
gain only; does NOT move the R→∞ threshold.

**Caveat:** `(1+√α)²` is the *linear/temporal* Turing threshold. The repo does NOT
prove it is the exact *nonlinear far-left* threshold. Reaching it is open research,
not a wiring task.

## This session's redundant files (recommend delete, pending Xiang)

Whole-line exp-barrier detour (duplicates done ≤chiStar target + vacuous global-inf
attainment defect, Q214): `WholeLineFarLeftTargetCapstone`, `WholeLineFarLeftDirect`,
`WholeLineParabolicDirect(Upper)`, `WholeLineHstartProducer`, `WholeLineInfSupNormControl`,
`WholeLineParabolicBarrier`, `WholeLineFarLeftAssembly`, `WholeLineScalar*`, `WholeLineExpBarrier*`.
KEEP the crest/oscillation bricks (`WholeLineChiPosCrestGradientBound`,
`WholeLineResolverOscillationBound`, `WholeLineChiPosPointwise*`) — they target >chiStar.

## Tools

- ChatGPT: `python3 ~/.openclaw/workspace/scripts/ask-gpt.py "<question as ARG not stdin>"`
  (auto-picks idle cron1-7). Answers git-drop to /tmp/gpt_Q<N>.md.
- Verify one file: `env LEAN_PATH=$(for d in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do printf "$HOME/Shen_work/.lake/packages/$d/.lake/build/lib/lean:"; done)$HOME/Shen_work/.lake/build/lib/lean ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lean <file>`
- Root gate: `cd ~/Shen_work && lake build ShenWork` (10019 jobs, 0 sorry, 0 axiom).
