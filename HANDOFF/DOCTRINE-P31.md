# DOCTRINE — Paper 3 P3.1 (Proposition_1_2 intervalDomain p) — 2026-07-12

## Main goal (one sentence)
Drive Paper 3 P3.1 = `ShenWork.Paper3.Proposition_1_2 intervalDomain p` toward
unconditional (0 sorry / axiom-clean) for the χ₀≤0, 1≤m regime, by discharging
the two undischarged frontier fields of `IntervalDomainPaper3NegativeSensitivityFrontierData p`.

## Ground truth (verified 2026-07-12)
- Target type: `Proposition_1_2 intervalDomain p` (Statements.lean:~1180). Pure
  existential global-bounded-existence; NO semiflow/uniqueness/continuity (Q4436).
- Bridge chain EXISTS & compiles:
  `IntervalDomainPaper3NegativeSensitivityFrontierData p`
    →(intervalDomainPaper3_negativeSensitivityResidual_of_frontierData)→
  `NegativeSensitivityGlobalEventualBound intervalDomain p`
    →(Proposition_1_2_of_negativeSensitivityGlobalEventualBound)→
  `Proposition_1_2 intervalDomain p`.
- χ₀>0 branch: VACUOUS, already discharged
  (`intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos`).
- So the ONLY real content = the two fields for χ₀≤0:
  1. `globalSolution` (χ₀≤0,1≤m ⇒ ∀u₀ ∃ global classical sol + initial trace)
     — DEPENDS ON Codex's Paper 2 χ≤0 existence (χ<0 landing + χ=0 branch).
  2. `eventualSupBound` (**Gap A**: given a global classical sol, ∃T₀ M ∀t≥T₀
     supNorm(u t)≤M) — INDEPENDENT of the existence proof (takes sol as hyp).
- Gaps B (datum class Paper vs Positive) / C (parameter branches) = alignment.

## Avenues (ranked)
- (a) **Gap A — eventualSupBound** [INDEPENDENT of Codex, main grind]. Given a
  global classical solution for χ₀≤0, 1≤m, prove eventual atTop L∞ bound.
  Sub-paths: (a1) reuse Paper 2 Theorem 1.2 `IsPaper2Bounded.of_forall_ge_supNorm_le`
  boundedness machinery if its regime overlaps (m=1 at least); (a2) scalar logistic
  absorbing-set comparison (χ₀≤0 ⇒ chemotaxis non-aggregating ⇒ logistic damping
  gives limsup‖u‖∞ ≤ carrying capacity); (a3) build the absorbing-set estimate fresh.
  Terminal: eventualSupBound proven 0-sorry, OR proof-of-failure (needs specific
  Paper-2-only machinery not yet available → carry as named residual).
- (b) **Scaffold the conditional P3.1 headline** carrying both fields as hypotheses,
  compile green + commit (assemble-early; makes the frontier explicit & durable).
- (c) **Gap B/C alignment** bridges (datum-class widening, parameter-branch coverage)
  — mechanical, dischargeable once globalSolution shape is fixed.
- (d) Fallback: if Gap A is deep, decompose → dispatch sub-lemmas to ChatGPT shen
  tabs / a fresh-context sub-agent, keep driving (b)+(c).

## Do NOT touch (Codex-owned χ<0)
IntervalTruncatedWeakBarrierComparison*, IntervalChemDivSourceWeakH2AssemblyV6,
IntervalUniformConjugateCore, IntervalChiNegV6Assembly, bootstrap files. New P3.1
work goes in NEW files under ShenWork/Paper3/.

## Terminal / fallbacks
Success = `Proposition_1_2 intervalDomain p` reduced to ONLY the globalSolution
field (existence), with eventualSupBound + Gap B/C discharged, cold-built + axiom
gate on a headline. globalSolution then discharges when Codex lands χ<0 + step-0
packaging. If Gap A needs Paper 2 Lᵖ (step-2, not yet done), carry it as the single
named residual and pivot to Gap B/C + scaffolding.

## Build
Single-file: `cd ~/repos/shen_work && env PATH="/Library/TeX/texbin:$PATH" lake env lean <file>`.
NEVER local `lake build`. Cold gate: `REMOTE_BUILD_SERVER=uisai2 bash scripts/remote-build.sh shen_work`.
