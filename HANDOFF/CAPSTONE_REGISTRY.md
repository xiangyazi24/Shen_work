# Capstone Registry — every axiom-clean headline theorem (2026-07-17)

All theorems below depend only on `[propext, Classical.choice, Quot.sound]`.
0 sorry, 0 custom axiom across the entire project.

## Paper 1 (Traveling Waves)

| Theorem | Capstone identifier | File:Line | Status |
|---|---|---|---|
| Thm 1.1 (FULL) | `Theorem_1_1.unconditional` | Paper1/Theorem1_1Unconditional.lean:12 | UNCONDITIONAL |
| Thm 1.2 χ≤0 | `paper1_Theorem_1_2_chi_nonpos_paperDatum` | Paper1/WholeLineWeightedRegularityChiNonposHeadlineNatural.lean:22 | UNCONDITIONAL |
| Thm 1.2 χ<0 | `paper1_Theorem_1_2_chi_neg_paperDatum` | Paper1/WholeLineWeightedRegularityChiNonposHeadlineNatural.lean:68 | UNCONDITIONAL |
| Thm 1.2 full | `paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4` | Paper1/Theorem12Corrected.lean:222 | χ>0: TWO adapters remain (Q5314) — see Henry infrastructure below |
| Prop 1.1 χ≤0 | `Proposition_1_1_negative_branch` | Paper1/WholeLineCauchyLongTimeBound.lean:741 | UNCONDITIONAL |
| Prop 1.2 χ≤0 | `Proposition_1_2_negative_branch` | Paper1/Proposition12NegativeBranch.lean:21 | UNCONDITIONAL |
| **Prop 1.2 χ>0 critical (NEW 07-19)** | `Proposition_1_2_positive_branch_critical` | Paper1/Proposition12PositiveBranchCritical.lean:32 | UNCONDITIONAL on 0<χ<1/2, α=m+γ−1, ceiling regime, UniformlyPositive datum. Non-vacuity witness: WholeLineChiPosRectangleWitness.lean. Since the ceiling regime was weakened to χ<1 (07-19), this now covers the paper's ENTIRE critical χ<1/2 range — the earlier chiStar scope caveat is closed. |
| **Prop 1.1 χ>0 critical (NEW 07-19)** | `Proposition_1_1_positive_critical_branch` | Paper1/Proposition11PositiveCritical.lean:31 | UNCONDITIONAL on 0<χ<1, α=m+γ−1. Global nonneg solution + range bound + UniformEventuallyBounded + UniformLimsupLe MChi. FAITHFUL PARTIAL: residual window 1 ≤ χ < faithful threshold inhabited (proved); MChi is undefined there, so it needs the paper's local-Lp route. |
| Refutation Thm 1.2 a>0,b=0 | `not_Theorem_1_2_intervalDomain_when_a_pos_b_zero` | Paper2/IntervalDomainTheorem12Refutation.lean:162 | UNCONDITIONAL |

## Paper 2 (Bounded Domain Existence)

| Theorem | Capstone identifier | File:Line | Status |
|---|---|---|---|
| Thm 1.1 χ=0 | `intervalDomain_theorem_1_1_chiZero_unconditional_tightLedger` | Paper2/IntervalDomainChiZeroTightUnconditional.lean:61 | UNCONDITIONAL |
| Thm 1.1 χ<0 | `paper2_chiNeg_unconditional` | Paper2/IntervalChiNegHeadline.lean:42 | UNCONDITIONAL |
| Thm 1.1 χ≤0 | `paper2_chiNonpos` | Paper2/IntervalChiNegHeadline.lean:50 | UNCONDITIONAL (a>0, b>0, α≥1, γ≥1) |
| Thm 1.2 positive-critical | `Theorem_1_2_intervalDomain_positive_critical_branch_unconditional` | Paper2/IntervalDomainTheorem12PositiveCriticalAllExponents.lean:270 | UNCONDITIONAL |
| Corrected Thm 1.2 | `correctedTheorem12_intervalDomainM` | Paper2/IntervalDomainMTheorem12Headline.lean:109 | UNCONDITIONAL |
| Thm 1.3 general-m | `correctedTheorem13_intervalDomainM` | Paper2/IntervalDomainTheorem13CorrectedHeadline.lean:143 | UNCONDITIONAL |
| Corrected Prop 1.1 | `correctedProposition_1_1_intervalDomainM` | Paper2/IntervalDomainMMaximalContinuationAlternative.lean:374 | UNCONDITIONAL |
| Prop 2.2 | `intervalDomain_Proposition_2_2` | Paper2/IntervalDomainWeightedGradientEstimate.lean:827 | UNCONDITIONAL |
| Prop 2.4 | `intervalDomain_Proposition_2_4` | Paper2/IntervalDomainMass.lean:888 | UNCONDITIONAL |
| Prop 2.5 | `Proposition_2_5_intervalDomainM_of_restarted_affine_general` | Paper2/IntervalDomainMRestartedLpLinfGeneral.lean:494 | UNCONDITIONAL (intervalDomainM) |
| Lem 2.6 (practical content) | `Lemma_2_6_intervalDomain_concrete_terminal` | Paper2/IntervalDomainLem26ConcreteTerminal.lean:44 | UNCONDITIONAL for concrete interval-domain classical solutions (terminal windows), via the existing hdiss-free Agmon route. The ABSTRACT `Lemma_2_6` remains conditional on `MoserDissipationDropBefore`, which is proved unsound (over-quantified; explicit counterexample) — do not route new work through it. No committed headline depends on it. |
| Cor 2.1 | `intervalDomain_Corollary_2_1_terminalWindow` | Paper2/IntervalDomainCorollary21.lean:48 | UNCONDITIONAL |

## Paper 3 (Long-Time Dynamics)

| Theorem | Capstone identifier | File:Line | Status |
|---|---|---|---|
| Thm 2.1 corrected (4-part) | `Theorem_2_1_corrected_intervalDomainM` | Paper3/IntervalDomainTheorem21CorrectedHeadline.lean:30 | UNCONDITIONAL |
| Thm 2.2 general-m (4-branch) | `intervalDomainM_Theorem_2_2_Eventual_concrete_unconditional` | Paper3/IntervalDomainMMinimalFaithfulTheorem22.lean | UNCONDITIONAL |
| Thm 2.3 general-m (FULL) | `intervalDomainM_Theorem_2_3_EventualGlobalStability` | Paper3/IntervalDomainMTheorem23Eventual.lean:208 | UNCONDITIONAL |
| Thm 2.4 general-m (4-branch, zero-hyp) | `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula` | Paper3/IntervalDomainMTheorem24Eventual.lean:85 | UNCONDITIONAL |
| Thm 2.5 (m=1 faithful) | `intervalDomain_Theorem_2_5_EventualGlobalStabilityFormula` | Paper3/IntervalDomainTheorem25Eventual.lean:16 | UNCONDITIONAL |
| Prop 1.2 χ≤0 | `proposition_1_2_intervalDomain_chiNonpos` | Paper3/IntervalDomainP31EventualSupBound.lean:235 | UNCONDITIONAL (a>0, b>0) |
| Prop 1.3 corrected | `correctedProposition13_intervalDomainM` | Paper3/IntervalDomainRecalledPropositionsPositive.lean:41 | UNCONDITIONAL |
| Prop 1.4 | `intervalDomain_Proposition_1_4_unconditional` | Paper3/IntervalDomainRecalledProposition14.lean:46 | UNCONDITIONAL |
| Refutation Thm 2.5 all-time | `not_intervalDomain_Theorem_2_5_original_allTime` | Paper3/IntervalDomainSectorialCorrectedObstruction.lean:421 | UNCONDITIONAL |
| Refutation Thm 2.5 stability-cond | `not_intervalDomain_Theorem_2_5_of_stabilityCondition` | Paper3/IntervalDomainSectorialCorrectedObstruction.lean:353 | UNCONDITIONAL |

## Henry Semigroup Infrastructure (Codex GPT-5.6 sol, July 15-16)

The χ≤0 branch of P1 Thm 1.2 is fully UNCONDITIONAL — the entire Henry-cited regularity chain was built from scratch:

**What was built (76k lines, 212 files in WeightedRegularity chain):**
- Weighted L² heat semigroup law and differentiation (`WholeLineWeightedRegularityL2Semigroup.lean`, 2730 lines)
- Raw difference-quotient (DQ) PDE one-step inequality and Henry window closure (32 RawDQ files)
- Volterra scalar recurrences and singular profile bounds
- Short-window Henry closure via automatic window selection (`target_norm_bound_of_restart_henry_on_fixed_window`)
- Global energy differentiability at positive times (`wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_natural`)
- Exact-weight H⁰ propagation from initial weighted L² closeness
- Tail-start Grönwall to exponential energy decay
- Full χ<0 weighted convergence (`wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_neg_natural`)
- Left-equilibrium dynamics for χ<0 (`wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_neg_natural`)
- Full χ≤0 uniform moving-frame convergence (`wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural`)

**What was built for χ>0 (July 17, three-piece mirror pattern):**
1. ✅ Q5314 adapter 1: `paper5WeightedEnergy_hasDerivAt_and_deriv_le_of_exactGeneratorWindow_local` — paired HasDerivAt + inequality from local window (commit `173a3d9d`)
2. ✅ χ>0 global energy inequality: `wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_chi_pos_natural` — takes `StableWaveParameterRegime`, `0 < p.χ`, and `htarget : ∀ x, u(t,x) ≤ M`
3. ✅ χ>0 global slice H⁰: `wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness` — integrability of weighted L2 error at any positive time
4. ✅ χ>0 global differentiability: `wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_chi_pos_natural` — differentiability of weighted energy at positive times
5. ✅ Spatial modulus — already χ-general (takes `WholeLineCauchyCeilingRegime`)

**FUNDAMENTAL GAP for χ>0: eventual pointwise limsup bound — IN PROGRESS**
The slab maximum principle is DONE (commit `8158948b`):
- `wholeLineSlab_le_chiPosCeiling_of_positive_resolver_pde`: u ≤ MChi+(C-MChi)*exp(-αt) on any time slab
- Supersolution property via Bernoulli inequality for rpow
- Effective reaction Lipschitz infrastructure

Remaining to close the gap (being built):
- Segment Ico/Icc propagation (mirror χ≤0 pattern)
- Global induction chain across segments
- `wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos`: UniformLimsupLe MChi

Once closed, this unblocks:
- Eventual energy dissipation for χ>0
- Q5314 adapter 2 (integrable seed at time after eventual M ceiling)
- Weighted L2 convergence for χ>0
- Left equilibrium convergence for χ>0
- P1 Thm 1.2 full, Thm 1.3 full, Prop 1.2 χ>0

**Supporting infrastructure (34k lines Wiener, 101k lines PDE):**
- Wiener weighted-ℓ¹ algebra (the χ₀<0 hQuant engine)
- Heat kernel gradient estimates (`HeatKernelGradientEstimates.lean`, 3435 lines)
- Interval coupled classical ball estimates (5406 lines)
- Moser iteration infrastructure (energy continuity + integrated closure, 5572 lines)

## Summary

- **UNCONDITIONAL headlines**: 25+ across all three papers
- **NEAR-CLOSABLE (χ>0 PDE gap)**: P1 Thm 1.2 full — slab principle DONE, segment chain in progress
- **CONDITIONAL (frontier data)**: P2 Lem 2.6 (Moser frontier)
- **Refutations**: 3 (P1 Thm 1.2 a>0/b=0, P3 Thm 2.5 all-time, P3 sup-C¹ obstruction)
- **Total sorry/axiom in project**: 0 / 0
- **Scale**: 774,736 lines of Lean, 2009 files, 9882 build jobs, 0 errors


## χ>0 (positive-sensitivity) layer — added 2026-07-19

Scalar engine (Paper1/WholeLineChiPosSqueezeAlgebra.lean, all clean-3):
`chiPos_squeeze_gap_step` (gap contracts by 2χ), `_sharp` (ratio χ/(1−χ)),
`chiPos_squeeze_gap_step_of_le` (paper's full exponent hypothesis m+γ−1 ≤ α),
`affine_recurrence_iterate_le`, `abs_sub_one_le_rpow_gap`, `rpow_gap_mono_exponent`.

Whole-line critical chain: WholeLineChiPosRectangleSqueeze.lean (rounds),
WholeLineChiPosRectangleTargets.lean (margins), WholeLineChiPosWeightedResolverComparisonNatural.lean
(b^m-weighted contact — the constant-defect form fails at small floors when m=1).

Supercritical chain (NO smallness on χ, only d = α−(m+γ−1) > 0):
WholeLineChiPosSupercriticalAtoms.lean (tangent inequality generalized from
`rpow_bernoulli`'s 2≤n to 1≤n), WholeLineChiPosSupercriticalCeiling.lean
(parameter-ceiling barrier + supersolution + one-sided Lipschitz),
WholeLineChiPosSupercriticalLongTimeBound.lean (slab → segments → limsup).

Buffered half-line layer (for the front problem's left equilibrium, avenue in progress):
WholeLineHalfLineResolverUpperNatural.lean, WholeLineChiPosTargetCeilingNatural.lean,
WholeLineChiPosBufferedComparisonNatural.lean, WholeLineChiPosHalfLineRectangle.lean
(structure + endgame delivering UniformCoMovingLeftEquilibriumConvergence).
REMAINING: the buffered successor construction (kernel-tail defect τ = e^{−R}/2).

ERRATA (ours, not the paper's) — Paper1/Proposition11PositiveErrata.lean:
`Proposition_1_1`'s positive-critical threshold mis-transcribes the source
((2m−1)/(m−1) became (m+γ−1)/(2m−1)) and is vacuous at γ=1 under Lean's x/0=0.
Faithful division-free encoding `paper1PositiveCriticalThreshold` landed, proved
equivalent to the paper's ratio form (m,γ>1) AND to the existence of an
admissible local-Lp exponent of §3.1 — which is where the threshold comes from.

Also added 07-19: Prop 1.1 supercritical branch
(`Proposition_1_1_positive_supercritical_branch`) and the combined
`Proposition_1_1_positive_branches_of_regime` (paper's (1.10) on both branches).

Ceiling-regime weakening (07-19): `WholeLineCauchyCeilingRegime`'s critical case
went from `χ < chiStar` to `χ < 1`. Evidence: all four sites in the repo that
destructure that branch used chiStar only to extract χ<1. Producers unaffected
(chiStar_le_one). Verified by a full root build + axiom prints through
`import ShenWork`.

OPEN, recorded (not claimed): (i) Thm 1.2 for χ∈[1/2,χ*) — the paper's left-tail
step cites its own Prop 1.2(2), proved only for χ<1/2; no linear instability, no
bifurcation, no known counterexample (dispersion audit), so plausibly true but
unproved. (ii) Prop 1.1 critical window 1 ≤ χ < faithful threshold — MChi is
undefined there; needs the paper's local-Lp iteration. (iii) The χ>0 front
left-equilibrium (buffered successor construction) — the last piece of P1 Thm 1.2
for positive sensitivity.
