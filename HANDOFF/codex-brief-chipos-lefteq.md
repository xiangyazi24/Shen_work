# Codex Brief — χ>0 Left Equilibrium Convergence (P1 Thm 1.2 final gap)

Repo: ~/Shen_work (warm .lake build current through HEAD 7ea4d1db). Lean 4, lake build works.
Rules: 0 sorry, 0 axiom, no native_decide. New files only — do NOT edit existing files
except adding imports to ShenWork.lean at the very end if you create new modules.
Verify each new file with `lake build ShenWork.Paper1.<Module>` before claiming done.

## Context

ONE theorem closes Paper 1 Theorem 1.2 full:
`wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural`
(mirror of the χ<0 version in
`ShenWork/Paper1/WholeLineWeightedRegularityChiNegLeftEquilibriumNatural.lean`).

Already available for χ>0 (all 0-sorry, built):
- `wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos` + `wholeLineCauchyGlobal_le_chiPosCeiling_of_chi_pos`
  (ShenWork/Paper1/WholeLineCauchyChiPosLongTimeBound.lean; needs hχ_pos, hχ_lt : χ<1, halpha : α = m+γ-1, ceiling regime)
- `wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural`
  (WholeLineWeightedRegularityWeightedConvergenceChiPosNatural.lean)
- `wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus` (χ-general, takes WholeLineCauchyCeilingRegime)
- `StableWaveParameterRegime.toWholeLineCauchyCeilingRegime` (WholeLineCauchyGlobalBounds.lean:42)
  — note: positive branch of StableWaveParameterRegime is exactly (0 ≤ χ ∧ χ < chiStar ∧ α = m+γ-1),
  so halpha and χ<1 should be extractable from hregime + hchi_pos (VERIFY chiStar ≤ 1 or find the lemma).
- `eventually_coMovingPath_close_on_Icc_of_weightedL2_of_spatialModulus` (buffer closeness, χ-general)
- MChi p = (1/(1-χ))^(1/α) > 1 for χ>0 (Statements.lean:9340)

## Task 1 (RECON — report, no code): χ-sign audit of the two blockers

(a) `wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_neg_natural`
    (WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean) and its upstream chain
    (lower barriers, `constantSubsolutionThreshold p.χ`, plateau seed files).
(b) `leftHalfLine_ge_chiNegKPPFloor_of_buffer`
    (WholeLineWeightedRegularityChiNegBufferedHalfLineComparisonNatural.lean:478) and the
    KPP floor infrastructure (`chiNegKPPFloorRate`, `chiZeroKPPFloor`).

For each: list EVERY use of `hchi : p.χ ≤ 0` / `p.χ < 0` down the transitive proof chain, and
classify: (i) cosmetic (-χ = |χ| rewriting, generalizes verbatim to |χ|), (ii) one-sided sign
exploitation (the resolver term χ·u^m·(frozenElliptic u − u^γ) discarded by sign), or
(iii) structural (barrier shape depends on sign). Write the audit to
HANDOFF/codex-chipos-sign-audit.md with file:line citations.

## Task 2 (MECHANICAL — implement): χ>0 global range bound

New file ShenWork/Paper1/WholeLineCauchyChiPosRangeBound.lean:

theorem wholeLineCauchyGlobal_le_max_of_chi_pos
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (halpha : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤ max (MChi p) ‖u₀‖

Proof route: C := max (MChi p) ‖u₀‖, apply `wholeLineCauchyGlobal_le_chiPosCeiling_of_chi_pos`,
then `wholeLineCauchyChiPosCeiling_le` (line 59 of WholeLineCauchyChiPosLongTimeBound.lean)
bounds ceiling ≤ C when MChi ≤ C. Also add the convenience form with
M := max (max 1 ‖u₀‖) (MChi p) if that eases later use. `#print axioms` section at the end.

## Task 3 (DESIGN PROPOSAL — no implementation): χ>0 two-sided buffered comparison

For χ>0 the single-sided KPP floor breaks: the resolver term hurts BOTH directions
(lower floor when frozenElliptic > u^γ, upper ceiling when frozenElliptic < u^γ), and the
upper bound available is only limsup ≤ MChi > 1, but we must reach u → 1.

Design the concrete route: two-sided squeeze on the left half-line where floor ℓₙ ↑ 1 and
ceiling Mₙ ↓ 1 feed each other through the resolver kernel split
(mass inside buffer where u ≈ U ≈ 1, exponential tail e^{-R} outside), with contraction
guaranteed by χ < chiStar. Write exact inequality chains, the defect budgets
(mirror of H = |χ|·M^m·(e^{-R}/2)·M^γ < C(1−L^α)), the iteration scheme as a Lean-inductable
statement, and which existing lemmas carry over. Check the source paper if present in the repo
(look for *.pdf / paper notes under HANDOFF/ or docs/) for how §5 handles the χ>0 left tail.
Write to HANDOFF/codex-chipos-squeeze-design.md.

## Deliverables
1. HANDOFF/codex-chipos-sign-audit.md (Task 1)
2. ShenWork/Paper1/WholeLineCauchyChiPosRangeBound.lean building green (Task 2), imported in ShenWork.lean
3. HANDOFF/codex-chipos-squeeze-design.md (Task 3)
Commit NOTHING — leave working tree changes for review.
