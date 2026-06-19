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
- **Paper 1 — Theorem 1.1 (traveling-wave existence):** the m<2 cusp is RESOLVED as a discrete-Rothe
  ARTIFACT (回归原著): the faithful route is the whole-line parabolic-mild-Schauder engine (Shen §4.2), now
  the active architecture (docs/WAVE_ARCHITECTURE.md, source-grounded 17-brick map). avenue-c progress is
  tracked in **docs/PAPER1_AVENUE_C_CHECKLIST.md**: foundation (heat/resolvent/compactness/Schauder/mild
  map) ✅; constant-barrier energy-comparison engine ✅ atoms (timeLeibniz/pdeSubstitution/IBP-no-gap/
  chemotaxisCrossControl) + frontiers, wiring in flight; wave bricks 1/17 ✅ (speed/exponent algebra),
  bricks 2 (exp barriers) & 4 (frozen-signal V_x bound) in flight, bricks 6–12 (differentiated weak-
  comparison monotonicity + long-time map) the open analytic core. Headline still conditional (wave not
  yet unconditional) — but the route is faithful, decided, and discharging atom by atom; no cusp block.
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
