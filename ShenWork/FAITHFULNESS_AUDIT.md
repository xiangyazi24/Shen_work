# Statement-faithfulness audit (2026-06-15) — initial-data positivity bug

Triggered by: Paper2 `Theorem_1_1` was found stating positivity on the OPEN interior
(`PositiveInitialDatum` = `initialAdmissible ∧ ∀x∈D.inside, 0<u₀x`), which admits inf=0 data
(e.g. `x(1−x)`) that the paper EXCLUDES via eq (1.11): `u₀∈C(Ω̄) ∧ inf_Ω u₀ > 0`.
Faithful predicate = `PaperPositiveInitialDatum` = `initialAdmissible ∧ ∃η>0, ∀x, η≤u₀x` (uniform floor).
Defs: Paper2/Statements.lean:277 (weak) and :297 (the fix).

The fix was applied to P2 Theorem_1_1 ONLY and not propagated. Pre-screen of all 28 headline statements:

## 🔴 SAME BUG, must fix (open positivity → PaperPositiveInitialDatum / uniform floor)
- **P2 Theorem_1_2** — Statements.lean:4449, 4455 (existence+boundedness, slow/critical regime)
- **P2 Theorem_1_3** — Statements.lean:4509, 4515 (strong-logistic existence)
- **P3 Proposition_1_2** — Statements.lean:1136 (χ₀≤0,m≥1 global bounded) — Paper3 has NO floor predicate yet
- **P3 Proposition_1_3** — Statements.lean:1319 (strong-logistic global)
- **P3 Proposition_1_4** — Statements.lean:1382 (m=1 global)

## 🟡 Open-vs-closed positivity mismatch, needs paper check (cron P3 check in flight)
- **P3 Theorem_2_1 parts 1-4** (persistence): hypothesis `PositiveGlobalBoundedSolution` positive on open
  `D.inside` (:124) but conclusion bounds `D.infValue` over CLOSED domain (:135). parts :3596/5322/5422/5987.
- **P3 Theorem_2_3/2_4/2_5** (stability): `PositiveGlobalBoundedSolution` (open) → C¹/sup convergence (closed). :6221/6242/6256.
  → likely OK by Neumann strong max principle (interior-positive solution instantly bounded below on
  compact time), but the STATEMENT should match the paper. cron verifying the paper's hypotheses.
- **P3 Theorem_2_2** (local stability): `PositiveInitialDatum` (:6014,6030) BUT co-hyp `SupCloseToConstant … eq.1 δ`
  recovers a floor when δ<eq.1>0 — likely harmless; confirm the proof picks δ<eq.1.
- **P2 Proposition_2_4 / 2_5**: a priori Lᵖ/mass estimates on `PositiveInitialDatum` (:2897,:3007) — floor likely
  irrelevant (conclusion is integral/bound, not a floor). Low priority; verify paper doesn't need inf>0.

## 🟢 Faithful (no action)
- ALL Paper1 headlines: Prop_1_1 (NonnegativeInitialDatum), Prop_1_2 (**`UniformlyPositive`=∃δ>0,∀x δ≤u₀x —
  already the correct floor!**), Theorem_1_1/1_2/1_3 (wave existence/stability/uniqueness on ℝ, no open-interior bug).
  → Paper1 got positivity right; Paper2/Paper3 didn't. Mirror Paper1's `UniformlyPositive` shape.
- P2 Prop_2_1/2_2/2_3 (a priori estimates, no initial positivity).

## NON-bugs (documented design, not faithfulness issues)
- Tautology closers (`*.of_assumed_*_branch := h`): the repo EXPLICITLY tags each "⚠️ IMPOSTOR/TAUTOLOGICAL"
  (e.g. P2:4990, P3:10877) — known interface shims; the headline `def`s are separate + honest.
- Arbitrary `∀ D : BoundedDomainData`: the repo proves `not_forall_<Name>` counterexamples for each — the team
  KNOWS arbitrary D is unfaithful; headlines are meant to be the `intervalDomain` instantiation. (Worth a
  one-line confirmation that the claimed headline is the intervalDomain instance, not the ∀D form.)

## Fix plan
1. [in flight acbefcef] P2 Theorem_1_1: `PaperPositiveInitialDatum` + projection + rewire + floor-preservation.
2. Propagate the SAME fix (once the pattern lands) to P2 Th_1_2/1_3.
3. Add a Paper3 floor predicate (mirror `PaperPositiveInitialDatum`) for P3 Prop_1_2/1_3/1_4.
4. P3 Theorem_2_x: per cron's paper-check, either confirm faithful (Neumann max principle) or fix the open→closed positivity hypothesis.
