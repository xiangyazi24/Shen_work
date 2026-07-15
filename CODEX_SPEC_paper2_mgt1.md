# CODEX SPEC — Paper 2 χ₀≤0 general-m (m ≥ 1) boundedness + global continuation

## Goal
Close the named residual from commit 934f2f54: Theorem 1.3 (and the Thm 1.2 critical
branch) for χ₀ ≤ 0 and GENERAL m ≥ 1 on `intervalDomainM` — i.e. produce the general-m
analog of the m = 1 chain in `ShenWork/Paper2/IntervalDomainMChiNonposGlobal.lean`:

  boundedness-before-Tmax (general m)  →  reachablePastM_of_bounded (ALREADY general,
  needs only 1 ≤ p.m)  →  reachableArbitrarilyLong  →  global solution + bound.

The single missing producer is the general-m version of `critical_bounded_before_nonpos`
(currently m = 1 only). NO sorry/admit/native_decide/custom axiom.

## Grounding (verify by grep before building — do NOT rebuild existing machinery)
- `critical_bounded_before_nonpos` — find it, read its proof, identify EXACTLY where
  m = 1 is used (likely a linear-diffusion max principle or a p-energy identity
  specialization).
- General-m Moser producer EXISTS: grep `IntervalDomainMRestartedLpLinfGeneral`
  (Prop 2.5, Lᵖ ⇒ L∞ on intervalDomainM, general m).
- The Lᵖ machinery verified in the previous dispatch: terminal-window Corollary 2.1,
  sharp cross-diffusion, critical seed, all-Lᵖ (see ShenWork/Paper2/, grep for the
  terminal-window Cor 2.1 names). For χ₀ ≤ 0 the cross-diffusion sign is favorable —
  check whether the χ₀ ≤ 0 route even needs the ε-Young bootstrap or whether a direct
  comparison/energy argument suffices for general m.
- Paper ground truth (arXiv:2512.14858): Prop 1.1 eq (1.15): for m ≥ 1 finite Tmax
  forces L∞ blow-up (floor collapse excluded via scalar ODE subsolution — the m ≥ 1
  floor lemma). Boundedness for χ₀ ≤ 0: §4.2/§4.3. If the repo already has the m ≥ 1
  no-floor-loss lemma, reuse it (grep floor/Floor/subsolution in Paper2).

## Deliverable
`globalSolution_chiNonpos_m_ge_one` (or the boundedness producer + wiring):
for `p.a = 0 ∨ 0 < p.b`, `p.χ₀ ≤ 0`, `1 ≤ p.m`, every PaperPositiveInitialDatum has a
global classical solution with `IsPaper2Bounded intervalDomainM u`. Then extend
`Theorem_1_3_intervalDomain_chiNonpos_m_one` (IntervalDomainLpHeadline.lean) to a
general-m headline in a NEW file. If a sub-step walls, report the exact goal state,
file:line, and the missing mathematical fact — do not fake, do not weaken.

## Constraints
New files only under ShenWork/Paper2/. Do NOT edit existing files (incl. Statements.lean,
IntervalDomainLpHeadline.lean). No git commands. ≤100 cols. Reuse existing lemmas by
exact grepped name. Remote verification per CODEX_OPS_remote_build.md with
STAGING=/dev/shm/lean/Shen_work-p2lp. #print axioms every headline (expect clean-3),
then remove the directive.
