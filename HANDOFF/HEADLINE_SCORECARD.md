# Headline scorecard — independent adversarial audit (2026-07-12→13). Reconstructed after a shared-tree reset wiped the WIP.

## ⚠ PROJECT-WIDE SCOPE: the ENTIRE ShenWork formalization is on the **N=1 interval domain [0,1] Neumann** (all
`intervalDomain`/`intervalDomainM`). Every FAITHFUL headline below is faithful to the paper's theorem **restricted to 1D**;
the general-N versions are NOT formalized (open frontier). Report as "Thm X (1D)", never "Thm X". Errata found (3):
Thm1.2 a>0/b=0; Thm2.2 (2.12); Thm1.3 case-(iv) q_*>2−2m — all safe (strengthen/refute, never over-claim).

## ★ FAITHFUL HEADLINES (1D) — each verified BOTH gates: own axiom-clean remote build + independent non-vacuity/faithfulness audit
| Headline | Capstone | Notes |
|---|---|---|
| **Paper1 Thm 1.1 (FULL)** | `Theorem_1_1.unconditional` (Theorem1_1Unconditional.lean) | both sign branches, hypothesis-free; positive branch genuine Schauder–Tychonoff (refuted Route-A not in closure); non-vacuity witness satisfiable (chiStar=1>1/4). ENTIRE PAPER1 MAIN THEOREM. |
| **Paper2 Thm 1.1 χ=0** | `intervalDomain_theorem_1_1_chiZero_unconditional` | real term-mode local existence; scope α,γ≥1. |
| **Paper2 Thm 1.1 χ<0** | `paper2_chiNeg_unconditional` (IntervalChiNegHeadline.lean, ns IntervalChiNegAssembly) | genuine Banach local existence + direct Duhamel to real pde_u; scope α,γ≥1. **诈尸-cleaned** (was 125 files/6 versions → 1 clean headline). |
| **Paper2 Thm 1.2 positive-critical** | `Theorem_1_2_intervalDomain_positive_critical_branch_unconditional` | all α,γ>0; guard a=0∨b>0; real Picard/Banach. |
| **Paper2 Thm 1.3 general-m** | `correctedTheorem13_intervalDomainM (p)(hN:N=1)` : `CorrectedTheorem_1_3_OneDimensional` | both parts (boundedness ∀m>0 + global m≥1, positive-χ); non-circular boundedness→global; χ₀≤0 covered by Thm 1.1; paper-faithful. |
| Refutation Thm1.2 a>0,b=0 | IntervalDomainTheorem12Refutation | REAL, sorry-free (mass-ODE M'=aM). |
| Refutation Paper3 sup-C¹ | IntervalDomainSectorialCorrectedObstruction | REAL, 3 concrete counterexamples. |
| **Paper3 Thm 2.2 eventual** | `intervalDomain_Theorem_2_2_Eventual_positiveLogistic_unconditional` (+_concrete, +positiveEventual_branch) | hexist DISCHARGED by linear-spectral producer; non-circular (linear gap + local existence + open-interval Henry X^σ barrier + gluing; no stability output consumed). |
| **Paper3 Thm 2.3 general-m (FULL)** | `intervalDomainM_Theorem_2_3_EventualGlobalStability (p)` (IntervalDomainMTheorem23Eventual.lean) | UNCONDITIONAL (only p). Both branches: nonminimal (rectangle global attractor → eventual C1) + minimal χ₀≤0 (signal gap + heat bridge + Gronwall → uniform sup → basin entry → C1). Commit 1897737a, clean-3. |

## ✅ Henry a-priori engine — DONE + VERIFIED, DO NOT RESTART (anti-zombie)
The whole-line weighted-L² regularity / **Henry tower** (20+ `WholeLineWeightedRegularity*` files, incl. the hard
singular-kernel `(r-a)^{-1/2}` self-improving Volterra engine
`target_norm_bound_of_restart_henry_on_fixed_window`, `Paper1/WholeLineWeightedRegularityRawDQTargetHenry.lean:37`)
is **fully closed (every file sorry=0)** and **load-bearing** — it sits in the 483-module import closure of the
clean-3-verified χ≤0 headline `paper1_Theorem_1_2_chi_nonpos_paperDatum`
(`Paper1/WholeLineWeightedRegularityChiNonposHeadlineNatural.lean:22`; independent #print axioms =
`[propext, Classical.choice, Quot.sound]`, 8730 jobs). It is the a-priori foundation making the **P1 χ≤0
stability** (Thm 1.2 co-moving weighted-L² + uniform-frame stability) and **Thm 1.3 uniqueness** UNCONDITIONAL.
**This line is COMPLETE — do NOT re-open, re-derive, or rebuild it as a frontier.** (verified this session 2026-07-16.)

## ✅ Verified this session (2026-07-16, three-gate: source scan + independent remote #print axioms clean-3 + Explore faithfulness)
- **Paper3 Thm 2.1 corrected (persistence, 4-part)** `Theorem_2_1_corrected_intervalDomainM (p)` (Paper3/IntervalDomainTheorem21CorrectedHeadline.lean:30) — UNCONDITIONAL, clean-3 (8987 jobs). Two faithful defect-fixes (Part1 reaction guard w/ a=0<b counterexample; Part4 mass on positive-time orbit). Q4946 contact-small ceiling wired in.
- **Paper2 Corrected Prop 1.1 + Corrected Thm 1.2** (`correctedProposition_1_1_intervalDomainM`, `correctedTheorem12_intervalDomainM`) — UNCONDITIONAL, clean-3. (errata A4 endpoint-tail fix.)
- **Paper3 Thm 2.2 general-m (m>1) FULL 4-branch** `intervalDomainM_Theorem_2_2_Eventual_concrete_unconditional` (IntervalDomainMMinimalFaithfulTheorem22.lean) — UNCONDITIONAL, clean-3 (8967 jobs). 4 branches (positive-logistic stable/unstable + minimal mass-constrained stable/unstable); chiCritical carries uStar^(m+γ-1) (m-dependence faithful to (2.10)); eventual form = errata A6.
- **Paper3 Thm 2.4 general-m (m>1) FULL 4-branch, zero-hyp** `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula (p)` (IntervalDomainMTheorem24Eventual.lean:85; commit a1d56b47) — UNCONDITIONAL (only p, no hm, no carried frontier), clean-3 (independent 9011 jobs). GLOBAL asymptotic stability (∀ positive global bounded solution → UniformConvergesInSup, not local small-data). 4 strong-logistic branches (entropy strong1/2 α+1≥2γ + rectangle strong3/4 α+1≥m+γ+(β≠0)γ / α+1≥m+2γ); chiStrong3/4 carry uStar^(m+γ-1); χ₀≤0 sub-case discharged internally (max-decay + mass→capacity + Hölder-1/2 tail into static coercivity, no fake bridge); gap lemma rpow_mul_gap_le_gap_add proved. eventual form = errata A6/A7.

## STILL OPEN (1D)
- Paper1 **Thm 1.2** (tail asymptotics, Lemma 2.5 + §5) — C3. AT TERMINAL: 0 sorry in Paper1/; χ≤0 unconditional; full conditional only on Henry semigroup (out of Mathlib scope). All 7 errata certified.
- Paper3 **Thm 2.3** general-m: ✅ DONE (commit 1897737a). Thm 2.4 ✅ DONE. Thm 2.5 ✅ DONE (m=1 is paper's own scope).
- Paper2 supporting **Prop 2.2/2.4/2.5, Lemma 2.6, Cor 2.1** (Prop 2.1 ✓ 7b401459, Prop 2.3 ✓ 47771511) — ✅ ALL DONE (all 5 proved, axiom-clean builds; verified 2026-07-17).
- General-N versions of all headlines (the open frontier beyond 1D). Architectural plan: HANDOFF/GENERAL_N_PLAN.md. Abstract `BoundedDomainData` exists; Mathlib gaps (eigenvalues, semigroup, trace, Schauder) are C3.

## AUDIT DISCIPLINE (enforced): every capstone verified against its COMMITTED build (own #print axioms + independent
non-vacuity/faithfulness audit), never the Codex relay. axiom-clean ≠ non-vacuous (§3.3 iron law). Version-suffix in a
capstone name = 诈尸 trigger → halt+consolidate, do not verify the n-th corpse (playbook §防诈尸, memory feedback_anti_zombie_versioning).

## χ<0 诈尸 REFACTOR (2026-07-13, @ dd6521f1): purged 55 dead IntervalChiNeg*/SourceChiNeg* files + de-rooted 32 imports +
de-versioned V6 names → clean + deduped SourceReducedCoreWire cluster. Cold build 9441 jobs green. (My earlier "57 root
sorries" alarm was a grep false-positive from the `No sorry/admit` header comment; real was 1 file, now deleted.)
