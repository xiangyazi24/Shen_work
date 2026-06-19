# Playbook Audit — Shen Trilogy (status as of 2026-06-19)

Run against `formalization-playbook.md` §3.3 (faithfulness audit). Source-of-truth for
per-theorem status: `THEOREM_STATUS.md`; this file is the audit verdict summary.

## Layer 1 — mechanical cleanliness: **PASS (repo-wide)**
Scanned all 606 `.lean` files under `ShenWork/`:
- proof-position `sorry`/`admit`: **0**
- custom `axiom` declarations: **0**
- `native_decide` tactic uses: **0** (158 textual hits are all the "No sorry/admit/native_decide/
  custom axiom" doc-comment headers — 154 + 4 similar, none in proof position)
So no theorem can be faked via `sorryAx` / `ofReduceBool` / `trustCompiler` / a custom axiom.
(Per-headline `#print axioms = [propext, Classical.choice, Quot.sound]` is the campaign invariant,
verified per target as it lands; the absence of forbidden tokens above is the necessary condition.)

## Layer 2 — vacuity: **PASS (conditionals are non-vacuous)**
The three headlines are CONDITIONAL theorems carrying named frontier hypotheses. Those frontiers are
SATISFIABLE (a real wave / a real bounded-domain solution / a real persistent solution exists) — they
are honest reductions to satisfiable analytic statements, NOT vacuous unsatisfiable premises. The
campaign actively discharges them (T6 atom closed, T7e atoms B/C/D/O1 done) — evidence they are real,
not fake. (DOCTRINE.md mandates vacuity-checking each carried hypothesis against the zero function / a
real solution.)

## Layer 3 — completeness / "no carrying the hard content": **PARTIAL — Paper 2 χ₀=0 unconditional; rest conditional**
First unconditional Shen headline landed: Paper 2 Theorem 1.1 at χ₀=0 (986e7d1). The remaining headlines
(Paper 2 general χ≤0, Paper 1 wave, Paper 3 persistence) still carry the paper's hard analytic content as
named frontiers, each actively discharging:
- **Paper 1 — Theorem 1.1 (traveling-wave existence):** the m<2 cusp RESOLVED as a discrete-Rothe artifact;
  the faithful §4.2 parabolic-mild-Schauder engine fully built — **wave bricks 1–17 ALL ✅**, the headline
  `wholeLine_travelingWave_exists` assembled + the constant-barrier energy engine END-TO-END UNCONDITIONAL
  (`wholeLine_constantBarrier_trapping_unconditional`). HONEST CEILING (hostile-audited FAITHFUL, axiom-clean,
  non-vacuous, regression-verified): the wave headline `wholeLine_travelingWave_exists_consolidated` is a
  FAITHFUL CONDITIONAL theorem reducing to **(a) the Schauder fixed-point principle** [genuine Mathlib gap —
  no Brouwer/Schauder in Mathlib; faithful to assume per feedback_no_axiom_escape, NOT the paper's content]
  **+ (b) an 11-field aux-flow parabolic-regularity residual** [spatial/time monotonicity, Duhamel continuity,
  longTime_evolution_eq (= the flow solves eq 4.12), derivative convergence, profile C², T10 left-tail — ALL
  SATISFIABLE properties of a real aux-flow; the load-bearing equicontinuity bound was DISCHARGED via real
  Mathlib Leibniz (intervalIntegral.hasDerivAt_integral_of_dominated)]. To reach unconditional needs (a) a
  separate Brouwer/Schauder Mathlib formalization + (b) the full aux-flow parabolic existence (real PDE theory;
  local existence via Banach done, the regularity discharges banked abstractly). This is the honest ceiling —
  a strong faithful conditional formalization, NOT carrying the paper's hard content as an unsatisfiable hyp.
- **Paper 2 — Theorem 1.1 (boundedness/global existence, interval γ≥1):** **χ₀=0 case now UNCONDITIONAL**
  (`intervalDomain_theorem_1_1_chiZero_unconditional`, commit 986e7d1; non-vacuous since χ₀≤0 holds for 0≤0;
  §3.3 triple-audited FAITHFUL + independent build + axioms clean — the first full unconditional Shen
  headline). General χ≤0 still conditional: `paper2_theorem_1_1_of_frontier` on F1
  (`IntervalDomainUniformLocalExistence`) + hMildLocal (15/15 fields); the gradient-map conjugate-kernel
  faithfulness finding (docs/paper2-gradient-map-conjugate-kernel-finding.md) is the open design decision
  for extending χ₀=0 → all χ≤0. Abstract-domain still open.
- **Paper 3 — Theorems 2.1–2.5 (persistence/stabilization):** linear-stability parts done unconditionally
  (T10: exact χ* threshold, dichotomy); the analytic persistence proofs (uniform persistence, global
  stability) remain package-field assumptions. Built on Paper 2's interface, so gated on Paper 2.

## Verdict
Mechanically clean and non-vacuous, but **not complete**: the trilogy is at honest-conditional stage,
with the genuine remaining work being the carried analytic frontiers — Paper 1's Schauder/antitone
(blocked on the m<2 cusp route decision), Paper 2's F1/F2 existence atoms (T7e/T8, actively built), and
Paper 3's persistence (gated on Paper 2). No faking; reductions are faithful (reduction ≠ discharge is
honestly tracked). To PASS the completeness layer, these frontiers must be discharged.
