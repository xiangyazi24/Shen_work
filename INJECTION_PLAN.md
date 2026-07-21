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

## The injection point (VERIFIED against definitions)

`chiPosFloorGap p M x = 1 - x^α - χ·( x^(m-1) · (M^γ - x^γ) )`
(WholeLineChiPosRectangleTargets.lean:24). The factor `(M^γ - x^γ)` is a **crude**
bound on the resolver aggregation defect `V - x^γ` (V = frozenElliptic p u), using
the full band ceiling `M`. This crudeness caps the threshold at chiStar.

**Tighter tool (already proved, clean-3):**
`resolver_oscillation_bound : |v - u| ≤ b - a` (WholeLineResolverOscillationBound),
and `crest_gradient_bound : ‖u_z‖ ≤ χ b(b-a)/(c - χ(b-a))`
(WholeLineChiPosCrestGradientBound). The oscillation `b-a` is O(1) and much smaller
than the crude `M^γ - x^γ`.

**Plan:** replace `(M^γ - x^γ)` in the successor's subsolution inequality with the
oscillation bound, re-derive the floor gap `≥ 0` condition → new (higher) χ threshold
toward `(1+√α)²`. Reuse the ENTIRE half-line successor scaffold — no parallel route.

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
