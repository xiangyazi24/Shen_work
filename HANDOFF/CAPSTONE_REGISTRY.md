# Capstone Registry — every axiom-clean headline theorem (2026-07-17)

All theorems below depend only on `[propext, Classical.choice, Quot.sound]`.
0 sorry, 0 custom axiom across the entire project.

## Paper 1 (Traveling Waves)

| Theorem | Capstone identifier | File:Line | Status |
|---|---|---|---|
| Thm 1.1 (FULL) | `Theorem_1_1.unconditional` | Paper1/Theorem1_1Unconditional.lean:12 | UNCONDITIONAL |
| Thm 1.2 χ≤0 | `paper1_Theorem_1_2_chi_nonpos_paperDatum` | Paper1/WholeLineWeightedRegularityChiNonposHeadlineNatural.lean:22 | UNCONDITIONAL |
| Thm 1.2 χ<0 | `paper1_Theorem_1_2_chi_neg_paperDatum` | Paper1/WholeLineWeightedRegularityChiNonposHeadlineNatural.lean:68 | UNCONDITIONAL |
| Thm 1.2 full | `paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4` | Paper1/Theorem12Corrected.lean:222 | CONDITIONAL on Henry semigroup |
| Prop 1.1 χ≤0 | `Proposition_1_1_negative_branch` | Paper1/WholeLineCauchyLongTimeBound.lean:741 | UNCONDITIONAL |
| Prop 1.2 χ≤0 | `Proposition_1_2_negative_branch` | Paper1/Proposition12NegativeBranch.lean:21 | UNCONDITIONAL |
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
| Lem 2.6 | `Lemma_2_6_intervalDomain_of_mass_gradient_frontier` | Paper2/IntervalDomainTheorem11.lean:110 | CONDITIONAL on frontier |
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

## Summary

- **UNCONDITIONAL headlines**: 25+ across all three papers
- **CONDITIONAL (Henry semigroup only)**: P1 Thm 1.2 full (χ>0)
- **CONDITIONAL (frontier data)**: P2 Lem 2.6 (Moser frontier)
- **Refutations**: 3 (P1 Thm 1.2 a>0/b=0, P3 Thm 2.5 all-time, P3 sup-C¹ obstruction)
- **Total sorry/axiom in project**: 0 / 0
