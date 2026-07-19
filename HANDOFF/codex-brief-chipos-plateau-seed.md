# Codex Brief — χ>0 persistent plateau floor seed (the FINAL piece of P1 Thm 1.2)

Repo ~/Shen_work (HEAD 6f83faf3). Rules: 0 sorry, 0 axiom, NEW files only,
`lake build ShenWork.Paper1.<Module>` green per file. Do NOT commit. Do NOT edit
existing files (appending import lines to ShenWork.lean at the end is allowed).

## What is already done

`UniformCoMovingLeftEquilibriumConvergence c (wholeLineCauchyGlobalU p u₀)` for
χ>0 now needs ONLY a seed rectangle. Committed and verified:
- abstract layer + endgame: `WholeLineChiPosHalfLineRectangle.lean`
- successor: `exists_next_chiPosHalfLineRectangle`
  (`WholeLineChiPosHalfLineSuccessor.lean`, with Targets and WeightedComparison)
So the remaining obligation is exactly

```
exists_initial_chiPosHalfLineRectangle :
  (p, hregime : StableWaveParameterRegime p, 0 < χ, χ < 1/2, α = m+γ−1,
   wave data hc/hTW/hreg/hstrict/κ₁/htail, weight hroot/hetaCap,
   u₀ with hu₀ : ∀ x, 0 ≤ u₀.1 x, hleft : StrictlyPositiveAtLeft u₀.1,
   hinitial : WeightedL2InitialCloseness eta u₀.1 U)
  → Nonempty (ChiPosHalfLineRectangle p c (wholeLineCauchyGlobalU p u₀))
```

## The route (designed and audited — follow it)

MIRROR the χ<0 chain
`wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_neg_natural`
(`WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:28`), then feed
its output to the χ-FREE extraction lemma
`wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau`
(same file, :219) to obtain `∃ T R d, 0 < d ∧ ∀ t ≥ T, ∀ x ≤ R, d ≤ u t (x+ct)`.

A previous sign audit of that chain (HANDOFF/codex-chipos-sign-audit.md) found:
- NO structural (barrier-shape) dependence on the sign — the profile
  `lowerBarrierPlateau` and the threshold `constantSubsolutionThreshold` are
  written with `|χ|`;
- the ONLY genuine negative-sign steps are TWO discarded resolver-value terms:
  one on the raw tail (`paperWaveOperator_lowerBarrierRaw_nonneg_chiNonpos_scaled`)
  and one on the constant left plateau
  (`paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos`, Statements.lean:7328);
- the repo ALREADY has positive-χ replacements for both:
  * constant ledger at trap height `MChi p`:
    `paperWaveOperator_const_subsolution_nonneg_pos_MChi`
    (`WavePositivePlateauComparison.lean:66`, needs `0 ≤ χ`, `χ < 1/2`,
     `α = m+γ−1`, `0 < d ≤ paper1PositivePlateauFloor p`,
     `InWaveTrapSet κ (MChi p) u`);
  * patched barrier away from the splice:
    `paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away`
    (`WavePositivePlateauComparison.lean:473`), with
    `exists_positivePlateau_D` (:143) choosing `D` for the positive scalar height;
- the ONE mismatch to fix: the negative propagation carries an ARBITRARY common
  trap height `Q ≥ 1`, whereas the positive ledgers are stated at height
  `MChi p`. Since the frozen field scales like `Q^γ`, the constant-left budget
  must be redone at general `Q` — OR the window normalized.

**Normalize, do not re-derive.** After the χ>0 ceiling burn-in the solution
satisfies `u ≤ MChi p + r` for any prescribed `r > 0` eventually
(`wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos`, committed). So run the
plateau propagation on a window where the trap height is exactly `MChi p`
(absorb the `r`-slack by starting the propagation late enough and shrinking the
plateau height), which is precisely the regime of the positive ledgers.

## Deliverables

S1. `WholeLineChiPosPlateauWindow.lean` — the normalization: from the committed
    limsup, produce a restart time `T₀` and the statement that every restarted
    segment datum lies in `InWaveTrapSet κ (MChi p) ·` (or whatever exact trap
    predicate the positive ledgers consume). State clearly which trap predicate
    you land, and prove it.

S2. `WholeLineChiPosPlateauPersistence.lean` — the χ>0 mirror of the persistence
    theorem, using the positive ledgers in place of the two discarded-term
    lemmas. Everything else in the χ<0 chain (profile, thresholds, seed choice,
    one-window comparison, propagation induction) should carry over with `|χ|`
    already in place; the sign audit lists each site.

S3. `WholeLineChiPosHalfLineSeed.lean` — `exists_initial_chiPosHalfLineRectangle`:
    apply the χ-free extraction lemma to S2 to get `d > 0` on a co-moving left
    half-line; take `M₀ := MChi p + r` from the burn-in; then SHRINK the floor to
    `ell₀ := min d (a value with 0 < chiPosFloorGap p M₀ ell₀)` and check the
    ceiling margin `0 < chiPosCeilingGap p ell₀ M₀` (true for `M₀ > MChi`; the
    model computation is in `WholeLineChiPosRectangleWitness.lean`). Assemble the
    `ChiPosHalfLineRectangle`.

S4. Then land the capstone in a fourth file:
    `wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural`
    = `uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors` applied to
    S3's seed and the committed successor.

If a step genuinely cannot be mirrored, STOP at that step, report exactly which
lemma fails and why (with the failing goal), and land everything before it.
Do not substitute a weaker statement silently.
