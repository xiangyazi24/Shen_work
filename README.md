# Shen_work — a Lean 4 formalization of the chemotaxis–logistic trilogy

A machine-checked (Lean 4 / Mathlib v4.29.1) formalization of the Chen–Ruau–Shen
chemotaxis–logistic papers — the traveling-wave stability paper and the two bounded-domain
papers — together with a body of **beyond-paper** results that push the theorems to their sharp
limits and record the counterexamples that delimit them.

## Integrity gate (verified)

- **0 `sorry`, 0 custom `axiom`, 0 `admit`, 0 `native_decide`** in all tracked Lean sources.
- Every root-imported headline replays with exactly **`[propext, Classical.choice, Quot.sound]`**
  (Lean's classical logic — no `sorryAx`, no `Lean.ofReduceBool`).
- **Root build:** `lake build ShenWork` completes clean (~10,122 jobs).
- **Size:** 2,243 tracked `.lean` files, ~843k lines.

Verify: `lake build ShenWork`, then `#print axioms <headline>` for any theorem below.
(The docstring phrases "No sorry/admit/native_decide" and the word "admissible" are prose, not
tactics — the gate above is the authoritative check.)

## The three papers (formalized headlines)

**Paper 1 — whole-line traveling-wave stability.**
- Thm 1.1: front construction (Schauder / Rothe), producing the traveling wave used downstream.
- Thm 1.2: co-moving stability of the front, **unconditional in the wave** for all sign regimes
  — `paper1_Theorem_1_2_chi_pos_unconditional` (0<χ<min(½,χ*)), `..._chi_zero_...`,
  `..._chi_neg_...`; only the inherent `WeightedL2InitialCloseness` remains.
- Thm 1.3: uniqueness within the regular wave class (`Theorem_1_3_amended_*`); inherent
  hypotheses only.
- Prop 1.1: global Cauchy existence + a-priori bounds, **fully unconditional**
  (`paper1_Proposition_1_1_unconditional : Proposition_1_1`, all χ).
- Prop 1.2, Lemmas 4.1, 5.1–5.3: proved.

**Paper 2 — bounded-interval mild / linear-flux theory.**
- Thm 1.1: `Theorem_1_1 intervalDomain` end-to-end. Thm 1.2: unconditional. Thm 1.3: case-(iv)
  closed for m≥1 (`Theorem_1_3_intervalDomainM_caseIV_with_paperConstants`) and for m<1
  (`Theorem_1_3_intervalDomainM_of_m_lt_one`); the analytic lemma stack (Lem 2.1–2.4, incl.
  full-q semigroup via subordination) is proved. Some printed statements were shown *overstated*
  for the paper's data class and replaced with faithful forms (see `OUTSTANDING_MAP.md`).

**Paper 3 — bounded-interval nonlinear-flux (u^m) theory.**
- Thm 2.1–2.5 eventual stability on `intervalDomainM`, general-m. Thm 2.2/2.3/2.4 and the full
  Thm 2.5 (`intervalDomainM_Theorem_2_5_EventualGlobalStabilityFormula`, both minimal disjuncts)
  proved for **1 ≤ m ≤ 2**, plus the small-sensitivity route for **all m > 1**.

Detailed per-headline status and the correct-the-paper record: `OUTSTANDING_MAP.md`,
`THEOREM_LIST_BY_PAPER.md`.

**Errata.** The formalization proved several printed statements false/overstated for the
papers' own data class (P1 Lem 4.1/4.2, P2 Thm 1.2 guard / Thm 1.3 frontier / Lem 2.6/2.7, P3
all-time-$C^1$ overstatement, Thm 2.1 guard), each refuted in Lean and replaced by a proved
faithful form — see `ERRATA.md`.

## Beyond-paper results — see `research_notes/`

- **`research_notes/FARLEFT_CHI4_RESOLUTION.md`** — the traveling front's far-left stability
  driven to its sharp limit: threshold **χ = 4** (dispersion + entropy coincide), a whole-line
  weighted sharp-entropy engine, a **basin-conditional χ<4 convergence theorem (optimal)**, and
  a **formalized convective-escape counterexample proving unconditional χ<4 is false**.
- **`research_notes/GENERAL_M_STABILITY_RESOLUTION.md`** — Paper 3 Theorem 2.5 for general m:
  stable for `1≤m≤2` and all `m>1` small-χ₀; **false for m ≳ 2.9 large χ₀** (subcritical steady
  pattern). The sharp divider `m_c(U) ≈ 2.9` is a *bifurcation* threshold, cross-validated
  analytically (Lyapunov–Schmidt) and numerically (script alongside).
- **`research_notes/README.md`** — index.

## Follow-on projects (separable)

1. ~~Formalizing the m=3 steady counterexample~~ **DONE** — `minimal_equilibrium_global_stability_false_m3` (`Paper3/MinimalSteadyWACounterexample.lean`), clean-3: `∃χ, 0<χ<χ_lin ∧ ¬(minimal equilibrium globally attracts bounded mass-1 orbits)` for m=3, via amplitude-factored Banach IFT in the repo's Wiener algebra.
2. Discharging the far-left first-order derivative residual — blocked on a parabolic interior
   Schauder theorem absent from Mathlib.

## Layout

`ShenWork/Paper1/`, `ShenWork/Paper2/`, `ShenWork/Paper3/` — the three papers; `ShenWork/PDE/`,
`ShenWork/Wiener/` — shared analytic infrastructure (heat kernels, Wiener/Fourier algebra,
resolvers, Agmon/Moser). `ShenWork.lean` is the root import closure. Planning/audit docs and
`research_notes/` at the top level.
