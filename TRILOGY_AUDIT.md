# Chen–Ruau–Shen trilogy — §3.3 FAITHFULNESS audit summary

Standing goal: complete formalization of all three Chen–Ruau–Shen chemotaxis papers, judged by passing the
playbook §3.3 FAITHFUL audit (no sorry/admit/native_decide/custom axiom; no vacuous conditionals; no carried
unsatisfiable hypotheses; genuine — not fake — counterexamples).

Last audited: 2026-06-20. Method: kernel `#print axioms` on uisai2 built oleans + independent hostile opus
§3.3 audits (default-assume a vacuity/unsatisfiable-hypothesis/fake-counterexample trap).

## Status: ALL THREE PASS §3.3 FAITHFUL (as honestly-CONDITIONAL theorems)

Every headline: sorry-free, kernel axioms = `[propext, Classical.choice, Quot.sound]` (no sorryAx, no custom
axiom), NON-VACUOUS, carried hypotheses SATISFIABLE. Builds: P1 3378 jobs, P2 root 8688 jobs, P3 2706 jobs, all RC=0.

### Paper 2 — bounded-domain boundedness (general χ). FAITHFUL, non-vacuous.
- Headline `paper2_theorem_1_1_general_chi_bformSq_regular`: NON-VACUOUS, axiom-clean.
- CATCH #9 found+fixed: the original carried `Hbridge` asserted an UNSATISFIABLE equality (conjugatePicardLimit =
  truncatedConjugatePicardLimit with DIFFERENT fluxes u·v_x/(1+v)^β vs (u_+)^m). Fixed via the FAITHFUL truncation
  u_+·v_x/(1+v)^β + a real bridge producer. (Also catches #7,#8 earlier.)
- 8 bundle atoms GENUINELY discharged this run (each proof-term-read + hostile-opus-audited + clean-tree-verified):
  truncated_nonneg, semigroup_weak, Hpde, neumann, hpde_v, regularity (genuine but redundant — cleanup TODO),
  hstrip (free params removed, honest super-solution gap), initialTrace. Details in PAPER2_CHECKLIST.md +
  docs/paper2-gradient-map-conjugate-kernel-finding.md.
- CONDITIONAL on: the remaining carried foundational standard-fact atoms (DB/DT Picard existence, Hinf Duhamel
  integrability/source bounds — adversarially confirmed IRREDUCIBLE, hsmall, F1 uniform continuation) — all
  SATISFIABLE standard PDE facts, none vacuous.

### Paper 1 — traveling-wave existence (Schauder/Brouwer). FAITHFUL, non-vacuous.
- Headline `Remark_1_3_2` → `IsRightVanishingTravelingWave` (strict positivity U>0 + full CM traveling-wave ODE +
  right-vanishing + StrictlyPositiveAtLeft): content-bearing, the zero profile FAILS it. Non-vacuous.
- The catch-#9 trap IS present in the codebase (`LocalUniformNontrivialSchauderFixedPointPrinciple` on the bare
  trap is PROVABLY FALSE — refuted by `not_localUniform...bareTrap` via the constant-zero map) — BUT the authors
  found it first, REFUTED it, BANNER-TAGGED the two theorems carrying it as "vacuous audit artifacts" (NOT the
  headline), and route the live headline through the LOWER-PINNED trap (provably excludes zero, provably nonempty).
- Fixed point GENUINELY proved: own Brouwer/Sperner → ε-net → Schauder projection (`inMonotoneWaveTrap_schauderPrinciple`
  unconditional, kernel-clean); strict positivity via a real Grönwall strong-maximum-principle.
- CONDITIONAL on: the deepest analytic frontiers (Rothe/Green-representation cube-approx data, C² bootstrap) carried
  as SATISFIABLE hypotheses; no single numeric producer closes Remark_1_3_2 with zero carried hyps (standard for
  Schauder/Rothe PDE formalizations). Non-vacuous.

### Paper 3 — persistence / critical sensitivity / linear stability. FAITHFUL + genuine counterexamples.
- Spectral headlines FAITHFUL + self-contained + kernel-clean: `paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant`
  (χ* = paperFormula(λ₁) exact), `linearStability_dichotomy_at_mode_one_threshold`. Regime `aαμ ≤ firstNonzero²` is a
  NONEMPTY open region (e.g. a∈[0,π⁴], α=μ=1), not empty/degenerate. Dichotomy exhaustive + non-overlapping (marginal
  gap at σ=0 is mathematically correct, not vacuous).
- Counterexamples GENUINE (not fake): `not_paper2_theorem_1_1_implies_paper3_proposition_1_2` (degenerate-domain witness
  genuinely satisfies IsPaper2ClassicalSolution + violates boundedness), `theorem21Part1Counter_positiveGlobalBounded`
  (u=v=1 genuine equilibrium on inside=univ, PDE actually verified). Correctly scoped as meta-statements about the
  abstract API; honestly documented.
- Persistence Theorem 2.1 CONDITIONAL on `IntervalDomainSectorialMainlineCoreExistence` (sectorial semigroup +
  small-data global existence + uniform persistence) — SATISFIABLE but never-discharged hypothesis bundle (the hard
  Section-4 PDE analysis, carried not proved). NOT vacuous, NOT fake — honest conditionalization; the m<1 vacuous
  variant is transparently self-labelled.

## Honest one-line summary
The trilogy passes §3.3 FAITHFUL: sorry-free, kernel-axiom-clean, non-vacuous headlines, satisfiable carried
hypotheses, genuine counterexamples. All three are CONDITIONAL theorems on satisfiable standard PDE frontiers
(P2: foundational existence/integrability; P1: Rothe/Green cube-approx; P3: sectorial existence) — these are
carried as honest satisfiable hypotheses, not discharged to zero-hypothesis numeric witnesses. Conditional-on-
satisfiable is NOT a §3.3 violation. The catch-#9-style traps that exist in the codebases are refuted/quarantined/
self-labelled, never exploited by the headlines.
