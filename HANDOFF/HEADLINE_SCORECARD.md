# Headline scorecard — INDEPENDENT adversarial audit (2026-07-13), playbook §3.2/§3.3 verdicts
| Capstone | Verdict | Input-condition status (file:line) |
|---|---|---|
| Thm 1.2 positive-critical unconditional (Paper2/IntervalDomainTheorem12PositiveCriticalAllExponents:270,284) | FAITHFUL | no smuggle; local existence real Picard/Banach (ConjugateMildExistenceFloorData inhabited). Scope: guard a=0∨b>0. |
| Thm 1.1 χ₀=0 (Paper2/IntervalDomainTheorem11ChiZeroUnconditional:48) | FAITHFUL | real term-mode local existence (chiZeroDatumProviderSupply); scope narrowing α,γ≥1 (paper Thm1.1 is χ₀≤0 — verify faithfulness). |
| Thm 2.2 eventual (Paper3/IntervalDomainFaithfulTheorem22:17,51) | CONDITIONAL-honest | carries hexist = SmallDataGlobalExistence (Statements:3986), the paper's hard-half GLOBAL Cauchy, UNDISCHARGED (no producer; the "producers" repackage abstract fields). Linear dichotomy IS proved; nonlinear rides on assumed existence. Paper3Constants concretely inhabited (NOT vacuous). |
| Thm 1.1 χ₀<0 (Paper2/IntervalDomainThm11ChiNegResidual:199 + _of_picardFrontier_*) | FRAGMENT/CONDITIONAL | carries CoupledFluxClassicalLocalExistenceResidual (undischarged; producers reduce abstract→abstract, never closed). |
| ★FATAL Paper1 Thm 1.1 of_routeAParamData POSITIVE (PositiveRawRouteAAssembly:95,122,129) | VACUOUS/IMPOSTOR | input Paper1PositiveLowerRawCapRouteAParamData is REFUTED in same file (not_...:72). Compiles axiom-clean but proves NOTHING. #print axioms cannot catch — only satisfiability check. |
| Paper1 Thm 1.1 of_negativeRouteAParamData (NegativeRawRouteAAssembly:115) | FRAGMENT/CONDITIONAL | ParamData producible from satisfiable Paper1NegativeRotheAnalyticCore (abstract obligation); positive branch untouched. |
| Refutation a>0,b=0 (IntervalDomainTheorem12Refutation:48,162) | REAL, sorry-free | genuine mass-ODE M'=aM. |
| Refutation Paper3 sup-C¹ (IntervalDomainSectorialCorrectedObstruction:122,176,270) | REAL, sorry-free | 3 concrete counterexamples. |

## CORRECTIONS to my prior over-claims
- "Thm 2.2 closed/FAITHFUL" → WRONG, it's CONDITIONAL-honest on unproven hexist. RETRACTED.
- "whole 3-paper repo 0 sorry, axiom-clean" → WRONG. ~609 sorry tokens repo-wide; IntervalTruncatedPositiveTimeBootstrap
  (6 sorries) + IntervalChiNegV5SelfContained (5) etc. imported by root ShenWork.lean:502/543/544. Capstones sorry-free
  ON-PATH (no sorryAx) but library NOT globally 0-sorry. RETRACTED.
- "Thm 1.1 progressing/axiom-clean" → the POSITIVE routeA branch is VACUOUS (must not count); χ<0 CONDITIONAL; only χ=0 FAITHFUL.

## Genuinely done (survived the attack): Thm 1.2 positive-critical (FAITHFUL), Thm 1.1 χ=0 (FAITHFUL), both refutations.
## Everything else: honest conditional/fragment on the papers' hard-half existence, OR (Paper1 positive) vacuous.
