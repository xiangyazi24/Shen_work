# Statement-faithfulness audit (2026-06-15) — initial-data positivity bug

## 2026-07-13 — Paper 3 Theorem 2.5 all-time statement refuted and amended

The original target `Theorem_2_5` quantifies one pair of exponential constants
before all bounded positive global solutions and requires its `C¹` estimate at
every `t ≥ 0`.  In the legacy solution API the PDE is imposed only for strict
positive time, `HasInitialMass` reads only `u 0`, and no initial trace constrains
`v 0`.  Therefore the stored chemical slice can be changed arbitrarily at
`t = 0` without changing the PDE orbit or the mass.

`not_intervalDomain_Theorem_2_5_of_stabilityCondition` proves that, whenever
the minimal threshold condition is inhabited, the original all-time target is
false for the concrete interval sectorial norm.  The theorem keeps `u` at its
constant physical equilibrium (hence the mass is exact) and re-anchors only
`v 0` after the proposed uniform prefactor is chosen.
`not_intervalDomain_Theorem_2_5_original_allTime` gives a fully concrete
non-vacuous instance with `χ₀ = 1/4`, all other exponents and elliptic
coefficients equal to one, and a strict first minimal-threshold inequality.
Both obstruction theorems are kernel-clean.

The live faithful replacement is
`intervalDomain_Theorem_2_5_EventualGlobalStabilityFormula`: it uses physical
positive-time mass, orbit-dependent constants, and an orbit-dependent positive
entrance time.  Its two minimal branches are proved, not package projections.

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

## cron PAPER-CHECK verdict (2026-06-15) — the 🟡 P3 cases are REAL gaps
- P3 Prop 1.2/1.3/1.4 initial data = condition (1.8): `u₀∈C(Ω̄) ∧ inf_Ω u₀>0`. Our open `PositiveInitialDatum`
  is TOO WEAK → needs the uniform floor (same fix as P2). CONFIRMED 🔴.
- P3 Theorem 2.1 (persistence) + 2.3/2.4/2.5 (stability): the paper's "positive global classical solution"
  (Def 2.1) means a PER-TIME SPATIAL FLOOR `inf_Ω u(t,·) > 0` for each t∈(0,∞) — NOT pointwise interior
  positivity. Our `PositiveGlobalBoundedSolution` (positivity on open D.inside) is too weak UNLESS paired
  with a proved Neumann strong-max-principle upgrade (open-interior positivity + continuity on Ω̄ ⟹ per-time
  floor on compact time slabs). So either (a) strengthen `PositiveGlobalBoundedSolution` to carry the per-time
  floor, or (b) prove the max-principle upgrade lemma and keep the weak hypothesis. CONFIRMED real gap.
  Note: the persistence CONCLUSION (uniform-in-t lower envelope as t→∞) is what Thm 2.1 PROVES — don't put
  that in the hypothesis; the hypothesis is per-time floor + global + bounded.

## Fix plan (acbefcef DONE for P2 Th_1_1; pattern established)
1. ✅ [acbefcef] P2 Theorem_1_1: `PaperPositiveInitialDatum` (floor) + `.toPositive`/`.floor` + rewire 5 producer
   bridges. χ₀<0 floor obstruction dissolved (chain only needs interior positivity; solution supplies any floor).
   No floor-preservation stall. Full library builds 8671 jobs, χ₀=0 closer axiom-clean. [verify in flight]
2. Propagate `PaperPositiveInitialDatum` (templated) → P2 Theorem_1_2/1_3 + Proposition_1_1.
3. Add Paper3 floor predicate (mirror) → P3 Proposition_1_2/1_3/1_4 (initial data).
4. P3 Theorem_2_1/2_3/2_4/2_5: strengthen `PositiveGlobalBoundedSolution` to the per-time spatial floor
   (or add a Neumann max-principle upgrade lemma). The distinct, solution-level fix.

## RESOLUTION STATUS (2026-06-15)
1. ✅ P2 Theorem_1_1 — fixed + committed (PaperPositiveInitialDatum).
2. 🔧 P2 Theorem_1_2/1_3 + Prop_1_1 — propagation in flight (a029d261).
3. ✅ P3 Proposition_1_2/1_3/1_4 — fixed (ac399cad PART 1, reuse Paper2's PaperPositiveInitialDatum); pending joint verify+commit.
4. ⚠️ P3 Theorem_2_1/2_3/2_4/2_5 (solution-level per-time floor) — DEFERRED, documented in-code note above
   `PositiveGlobalBoundedSolution` (Paper3/Statements.lean:119). REASON (infra-level, cron couldn't see it):
   `BoundedDomainData.Point` is a BARE TYPE (no topology/compactness) and `infValue` is an abstract functional
   with NO axiom `infValue f = ⨅ x, f x`. So the Neumann max-principle upgrade (interior positivity + continuity
   ⟹ per-time floor) is UNPROVABLE from committed facts, and strengthening the def is impossible (`of_global_bounded`
   built from global∧bounded alone can't supply the floor — same gap; 308 refs, 16 producers ripple). AND the floor
   is UNNEEDED: every Th 2.1/2.3/2.4/2.5 proof consumes positivity only POINTWISE (`huv.pos`), never a spatial floor.
   ⟹ no theorem weakened; the faithful fix needs a future PDE-interface upgrade (add a topology/compactness +
   `infValue = ⨅` axiom to `BoundedDomainData`). Tracked, not a fakeable gap.
