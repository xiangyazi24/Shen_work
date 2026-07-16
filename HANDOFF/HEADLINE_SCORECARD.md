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
- **Paper3 Thm 2.2 general-m (m>1) positive-logistic branch** `intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_unconditional` — gate1+gate2 clean-3 (8941 jobs); Explore shape/faithfulness audit in flight. Minimal (a=0,b=0,mass) branch WIP (Fable#3). ⚠ checkpoint: verify the P*M≤1 local-smallness faithfulness at full-headline close.

## STILL OPEN (1D)
- Paper1 **Thm 1.2** (tail asymptotics, Lemma 2.5 + §5) — C3.
- Paper3 **Thm 2.3/2.4/2.5** global stability (ride Thm2.2 producer for χ₀≤0; discharge Paper3Constants/StabilityNorms package fields with genuine analytic proofs on concrete domain — arbitrary-domain obstruction) — C2. (Thm 2.1 ✅ done+verified this session — see above.)
- Paper2 supporting **Prop 2.2/2.4/2.5, Lemma 2.6, Cor 2.1** (Prop 2.1 ✓ 7b401459, Prop 2.3 ✓ 47771511) — C1.
- General-N versions of all headlines (the open frontier beyond 1D).

## AUDIT DISCIPLINE (enforced): every capstone verified against its COMMITTED build (own #print axioms + independent
non-vacuity/faithfulness audit), never the Codex relay. axiom-clean ≠ non-vacuous (§3.3 iron law). Version-suffix in a
capstone name = 诈尸 trigger → halt+consolidate, do not verify the n-th corpse (playbook §防诈尸, memory feedback_anti_zombie_versioning).

## χ<0 诈尸 REFACTOR (2026-07-13, @ dd6521f1): purged 55 dead IntervalChiNeg*/SourceChiNeg* files + de-rooted 32 imports +
de-versioned V6 names → clean + deduped SourceReducedCoreWire cluster. Cold build 9441 jobs green. (My earlier "57 root
sorries" alarm was a grep false-positive from the `No sorry/admit` header comment; real was 1 file, now deleted.)
