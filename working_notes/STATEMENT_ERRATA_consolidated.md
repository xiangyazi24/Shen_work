# Consolidated statement errata — Chen–Ruau–Shen chemotaxis trilogy

**Purpose.** This note consolidates the *statement-level* discrepancies found while
formalizing the three papers in Lean 4. Every item below is backed by a machine-checked
Lean theorem that is `sorry`-free and depends only on the standard axioms
`propext, Classical.choice, Quot.sound`. Items are separated into
**A. genuine paper-statement issues** (worth the authors' attention) and
**B. excluded items** (Lean-formalization artifacts that are *not* paper errors — listed
for transparency so the authors know they were checked and ruled out).

For each A-item: *location · what is wrong · counterexample/reason · suggested correction ·
Lean evidence · severity*. Full technical write-ups (with LaTeX) live in the per-theorem
files `working_notes/paper{1,2,3}_*_amendment.{md,tex,pdf}`; this note is the index/summary.

**Papers.**
- **TW** = "Traveling waves for repulsion/attraction chemotaxis with logistic source"
  (arXiv:2605.04401) — repo `ShenWork/Paper1/`.
- **Part I** = "…with signal-dependent sensitivity and a logistic-type source, I:
  Boundedness and global existence" (arXiv:2512.14858) — repo `ShenWork/Paper2/`.
- **Part II** = "…, II: Persistence and stabilization" (arXiv:2604.02599) — repo `ShenWork/Paper3/`.

**Severity legend.**
`GENUINE-FALSE` = the printed conclusion is false on an admissible parameter regime
(needs a hypothesis added). `STATEMENT-FIX` = the conclusion is true after a stated
condition is added or the wording is corrected (the printed form is over-stated /
ill-posed / has a proof gap, but is repairable).

---

## A. Genuine paper-statement issues

### A1 — TW, Theorem 1.2 & 1.3 (nonlinear orbital stability): the stability weight window is over-stated. `STATEMENT-FIX` (+ a genuine local proof gap)

- **Location.** Theorem 1.2 statement and eqs. (1.21)/(1.22); Theorem 1.3 tail hypothesis
  `κ₁ > κ`. Proof steps (5.18),(5.19),(5.23),(5.27),(5.29)–(5.33),(5.35); Lemmas 5.2/5.3.
- **What is wrong.** Seven independent defects in the §5 energy argument. The load-bearing
  ones:
  1. **(5.35) root comparison is in the wrong direction.** With `q(κ)=Aκ+B>0`, `κ` is *not*
     between the two roots of `q`; it lies strictly below the lower perturbed root. The
     energy computation therefore does **not** establish decay for all `η>κ` — the printed
     weight window `κ<η` is over-stated.
  2. **(1.21) uses the wrong spatial coordinate:** it prints the laboratory-frame weight
     `exp(2ηx)`, but §5 estimates the *co-moving* weight; the two differ by `exp(2ηct)`.
  3. **(5.35) exponential sign:** for `λ<0` the text writes `exp(−λt)→0`, but `exp(−λt)`
     grows; the decay factor should be `exp(λt)`.
  4. **(5.18)/(5.19):** two chemotaxis sign errors (the `a_{m+γ}` term and the `b₄z` term).
  5. **(5.27) J₁ Young term drops a `b₁`:** should be `b₁²`, not `b₁`; on the negative-χ
     branch `|χ|` may be arbitrarily large, so the replacement is not an upper bound.
  6. **(5.29)–(5.30) drop an `M^{2(γ−1)}` resolver factor:** on the positive-χ branch
     `M_χ` can exceed 1, so that power is not identically 1.
  7. **Lemma 5.2 is one-sided but (5.23) uses a two-sided bound:** the lemma gives
     `U_x/U ≤ C`, while (5.23) uses `|U_x/U| ≤ C`; for a decreasing wave `U_x/U ≤ 0` the
     negative part is uncontrolled.
- **Correction.** Use the corrected budget `A_χ, B_χ` (carrying `|χ|²B₁²/2` and a common
  resolver factor `K`); the proven weight window is the narrower
  `κ₋ < η < 1/(1+|χ|^{1/6})`; state (1.21) in co-moving form; Theorem 1.3's tail exponent
  should require `κ₁ > κ₋`.
- **Lean evidence** (`ShenWork/Paper1/`): `Theorem12RootObstruction.lean`
  (`paper531_kappa_not_between_perturbed_roots`, `paper531_kappa_lt_rootMinus`,
  `paper531_positive_inside_stated_weight_window`,
  `paper531_printed_decay_factor_tendsto_atTop`,
  `paper531_corrected_decay_factor_tendsto_zero`);
  `Theorem12CoordinateAudit.lean` (`laboratoryWeightedL2Energy_eq_exp_mul_coMoving`);
  `Theorem12MeanCoefficients.lean`; `Theorem12WeightedEnergy.lean`;
  `Theorem12LogDerivative.lean` (`abs_waveLogDerivative_le_one_of_barrier_speed`).
  Full note: `working_notes/paper1_theorem12_statement_amendment.{md,tex,pdf}`.
- **Severity.** Mixed. Defects 2–6 are `STATEMENT-FIX`. Defects **1 + 7** leave a genuine
  gap: the printed window `κ<η` is *not* proven by §5 on a sliver just above `κ` (not a
  counterexample, but a real gap absent a new localized-coercivity argument). The
  corrected narrower window is true.

### A2 — Part I, Theorem 1.2: missing `¬(a>0 ∧ b=0)` guard; the mixed branch is false. `GENUINE-FALSE`

- **Location.** Theorem 1.2(1) and (1.2)(2); Remark 1.4(2). Hypotheses read only
  `a,b ≥ 0, β ≥ 1`, which admits the mixed branch `a>0, b=0`.
- **What is wrong.** A counterexample exists on `a>0, b=0`.
- **Counterexample.** The constant-in-space solution `u(t,x)=c·exp(at)`, `v=(ν/μ)u^γ`, has
  all spatial derivatives and the chemotaxis divergence equal to zero and solves `u_t=au`;
  it is a global positive classical solution with `‖u(t)‖_∞ = c·e^{at} → ∞`. Equivalently
  the Neumann mass identity gives `M'(t)=aM(t)`, forcing exponential mass growth when
  `a>0`. So (1) is false on this branch; (2) is already false at `m=1,β=1,χ₀=0`. The §4.2/4.3
  proof relies on Proposition 2.4's mass bound, which only covers `a=b=0` or `a,b>0`.
- **Correction.** Replace the hypothesis by `(a=0) ∨ (b>0)` (i.e. exclude `a>0 ∧ b=0`); or,
  conservatively, `(a=b=0) ∨ (a>0 ∧ b>0)`. Remark 1.4(2) should say both parameters may
  vanish *together*, not arbitrary mixed nonnegatives.
- **Lean evidence.** `ShenWork/Paper2/IntervalDomainTheorem12Refutation.lean`
  (`not_Theorem_1_2_intervalDomain_when_a_pos_b_zero`,
  `not_Theorem_1_2_intervalDomain_of_a_pos_b_zero`). Verified: `¬ Theorem_1_2` on a concrete
  parameter set. Full note: `working_notes/paper2_theorem12_statement_amendment.{md,tex,pdf}`.
- **Severity.** `GENUINE-FALSE` on the `a>0, b=0` regime.

### A3 — Part I, Theorem 1.3, alternative (iv): missing exponent-domain condition. `STATEMENT-FIX` (proof gap)

- **Location.** Theorem 1.3 alternative (iv) (`β ≥ 1/2, α = 2m+γ−2`); §5.4 invokes
  Proposition 2.2.
- **What is wrong.** §5.4 needs `s(P) = (P+α)/γ > 1`, i.e. `P > 2−2m` at the critical
  identity; but the seed exponent `q_* = max{1, Nα/2}` chosen in the proof does not
  guarantee `q_* > 2−2m`. The claim in §5.4 that "this exponent exceeds 1 for all seed
  powers" fails on an uncovered window.
- **Counterexample (parameter wedge).** `N=1, m=1/4, γ=7/2, α=2, β=1`: then `α=2m+γ−2`,
  `q_*=1`, `s(q_*)=6/7 < 1`, and the first disjunct of (1.25) holds automatically (no χ₀
  smallness), yet Prop 2.2 needs `P > 3/2`. The written proof does not reach these params.
- **Correction.** Add to (iv) the condition `max{1, Nα/2} > 2−2m` (in 1-D:
  `max{1, α/2} > 2−2m`). Alternative (iii) (`α=m+γ−1`) does **not** have this gap.
- **Lean evidence.** `ShenWork/Paper2/IntervalDomainTheorem13Critical{Constants,Seed,Threshold,Bootstrap}.lean`
  (`boundedBefore_critical_case_iv_corrected`). Full note:
  `working_notes/paper2_theorem13_case_iv_amendment.{md,tex,pdf}`.
- **Severity.** `STATEMENT-FIX` — a proof gap, not a counterexample to the conclusion; holds
  after adding the condition (whether the wedge is recoverable by another estimate is open).

### A4 — Part I, Proposition 1.1: the finite-horizon alternative should hang on a maximal continuation. `STATEMENT-FIX` (wording)

- **Location.** Proposition 1.1's continuation / maximal-time alternative (cf. (1.14)/(1.15)).
- **What is wrong.** Read literally as "for every finite local horizon `Tmax`, the
  maximal-time alternative (finite-time blow-up or decay-to-zero) holds," the statement is
  false: the positive logistic equilibrium is a classical solution on every finite horizon
  yet neither blows up nor decays. The intended content is the existence of a *distinguished
  maximal continuation* (a finite branch carrying (1.14)/(1.15), or a global branch), not a
  dichotomy asserted for arbitrary finite horizons.
- **Counterexample.** The constant equilibrium `c=(a/b)^{1/α}` (`a,b>0`) refutes "every
  finite local witness satisfies the maximal-time alternative," already on the unit horizon.
- **Correction.** State the alternative on the maximal-continuation carrier: either a finite
  branch carrying (1.14)/(1.15), or a global branch; the finite-`Tmax` dichotomy appears only
  when the reachable horizon is bounded.
- **Lean evidence.** `ShenWork/Paper2/IntervalDomainCorrectedProposition11.lean`
  (`not_legacyFiniteHorizonAlternativeProducer_of_positive_equilibrium`; corrected
  `CorrectedProposition_1_1` / `correctedProposition_1_1_of_standardContinuation_and_gluing`).
- **Severity.** `STATEMENT-FIX` — a wording over-statement at the boundary between "there
  exists a maximal continuation" and "every finite horizon satisfies the dichotomy." Offered
  to the authors to decide whether the printed phrasing needs clarifying.

### A5 — Part II, Theorem 2.1(1) (uniform persistence): missing the `a=0<b` pure-decay regime; the conclusion is false there. `GENUINE-FALSE`

- **Location.** Theorem 2.1 part (1), §4.1 proof. Hypothesis reads only `m ≥ 1` and asserts
  `liminf_{t→∞} inf_x u > 0`, but §4.1 splits only into `a=b=0` and `a>0 ∧ b>0`, omitting the
  admissible `a=0 < b`.
- **What is wrong.** A counterexample exists on `a=0, b>0`.
- **Counterexample.** With `a=0, b>0`, the constant-in-space solution
  `u(t,x)=(c^{−α}+αbt)^{−1/α}`, `v=(ν/μ)u^γ`, solves `u_t=−bu^{1+α}`; it is global, positive,
  and bounded by `c`, yet `lim inf_x u = 0`. Simplest instance
  `α=γ=m=μ=ν=b=1, a=χ₀=0`: `u=v=1/(1+t)`.
- **Correction.** Add to part (1) the split actually used in §4.1: `(a=b=0) ∨ (a>0 ∧ b>0)`.
  The remaining `a>0, b=0` branch makes the persistence hypothesis vacuous (mass `M'=aM`
  grows exponentially, so no global bounded solution exists), so no third branch is needed.
- **Lean evidence.** `ShenWork/Paper3/IntervalDomainPersistencePart1StatementObstruction.lean`
  (`not_Theorem_2_1_part1_intervalDomain_pureDecay`; corrected `Theorem_2_1_part1_corrected`).
  Verified: `¬ Theorem_2_1_part1` with the explicit decaying orbit. Full note:
  `working_notes/paper3_theorem21_statement_amendment.{md,tex,pdf}`.
- **Severity.** `GENUINE-FALSE` on the `a=0<b` regime.

### A6 — Part II, Theorem 2.2(1) (linear stability/instability): the all-time C¹ estimate (2.12) is over-stated. `STATEMENT-FIX`

- **Location.** Theorem 2.2 part (1), third assertion — printed (2.12) — which claims the C¹
  exponential estimate for **all `t ≥ 0` (including `t=0`)** while the initial hypothesis (1.8)
  only requires `u₀ ∈ C(Ω̄)` positive.
- **What is wrong.** Smallness is in `L^∞` but the conclusion is in C¹ and demands `t=0`; the
  two are unrelated at `t=0`. `u₀` may even have `‖u₀−u*‖_{C¹}=∞`, making the `t=0` instance
  meaningless; even for C¹ data, the C¹ norm inside an `L^∞`-ball can be arbitrarily large, so
  no single constant `C` controls `t=0`.
- **Counterexample.** On `(0,1)` with Neumann BC, `u_{0,N}=u*+N^{−1/2}cos(Nπx)`:
  `‖u_{0,N}−u*‖_∞ = N^{−1/2} → 0` (mass exactly `u*` in the minimal model) but
  `‖u_{0,N}−u*‖_{C¹} = N^{1/2}π → ∞`.
- **Correction.** Split the single printed assertion into the two the proof actually gives:
  **(A) strong-norm, all-time** — `X^α`-small (α∈(3/4,1)) ⇒ all-time exponential decay in
  `X^α` (Henry sectorial theory); **(B) `L^∞`-small, eventual** — there is a data-dependent
  `t₀(u₀)>0` such that C¹ exponential decay holds for `t ≥ t₀`. The linear
  stability/instability dichotomy itself is **unaffected and correct**.
- **Side note.** The sufficient stability bound `κ < (√μ + √(aα))²` is a continuous infimum;
  on a bounded Neumann domain the spectrum is discrete, so the sharp stability boundary should
  be governed by the discrete infimum `min_{n≥1} σ_n < 0` (the continuous bound is only
  sufficient and may be strictly stronger).
- **Lean evidence.** `ShenWork/Paper3/Statements.lean`
  (`not_SectorialLocalExponentialRaw_constant_c1Distance`);
  `ShenWork/Paper3/IntervalDomainSectorialCorrectedObstruction.lean` (zero-time obstruction);
  corrected targets `IntervalDomainSpectralSemigroupOrbitBoundEventualEquilibriumWithoutMass`,
  `LocallyExponentiallyStableFromSup`. Full note:
  `working_notes/paper3_theorem22_statement_amendment.{md,tex,pdf}`.
- **Severity.** `STATEMENT-FIX` — true after splitting into A+B; only the printed (2.12) form
  is not well-posed.

### A7 — Part II, Theorem 2.5 (minimal model `a=b=0` stability): the same all-time C¹ over-statement. `STATEMENT-FIX`

- **Location.** Theorem 2.5: one pair of exponential constants is quantified before all
  bounded positive global solutions, and the C¹ estimate is required for all `t ≥ 0`.
- **What is wrong.** Same all-time `t=0` C¹ issue as A6, in the minimal-model + mass-constrained
  version: `L^∞`/mass-small data cannot give a uniform C¹ bound at `t=0`.
- **Correction.** State it in eventual form: orbit-dependent constants + an orbit-dependent
  entry time `t₀`.
- **Lean evidence.** `ShenWork/Paper3/IntervalDomainSectorialCorrectedObstruction.lean`
  (`not_intervalDomain_Theorem_2_5_original_allTime`,
  `not_intervalDomain_Theorem_2_5_of_stabilityCondition`); corrected
  `intervalDomain_Theorem_2_5_EventualGlobalStabilityFormula`. (The Lean refutation also
  layers in a `v₀`-anchoring interface detail — that part is a Lean-interface matter, see B5 —
  but the all-time C¹ over-statement itself is at the paper level.)
- **Severity.** `STATEMENT-FIX` — true in eventual form.

---

## Summary table

| # | Paper | Statement | Issue | Severity |
|---|-------|-----------|-------|----------|
| A1 | TW (2605.04401) | Thm 1.2 / 1.3 | stability weight window `κ<η` over-stated (7 defects; 2 leave a real gap) | STATEMENT-FIX (+gap) |
| A2 | Part I (2512.14858) | Thm 1.2 | missing `¬(a>0∧b=0)` guard; false on that branch | **GENUINE-FALSE** |
| A3 | Part I | Thm 1.3(iv) | missing `max{1,Nα/2}>2−2m` | STATEMENT-FIX (proof gap) |
| A4 | Part I | Prop 1.1 | finite-horizon alternative should hang on maximal continuation | STATEMENT-FIX (wording) |
| A5 | Part II (2604.02599) | Thm 2.1(1) | missing `a=0<b` regime; false there | **GENUINE-FALSE** |
| A6 | Part II | Thm 2.2(1) | all-time C¹ (2.12) over-stated; split into strong-all-time + L∞-eventual | STATEMENT-FIX |
| A7 | Part II | Thm 2.5 | same all-time C¹ over-statement | STATEMENT-FIX |

---

## B. Excluded — Lean-formalization artifacts, NOT paper errors (checked and ruled out)

Listed so the authors know these were examined and deemed *not* paper-level issues.

1. **TW `not_forall_Lemma_2_1`** (Paper1/Statements.lean:971): refutes an *abstract*
   `HeatSemigroupEstimateData` with fake data (`lqNorm=1, lpNorm=0`); the paper's Lemma 2.1 is
   about the *concrete* heat semigroup. Formalization-scaffolding only.
2. **TW Lemma 4.1 / 4.2 / Remark 4.2** (`not_Lemma_4_1`, `not_Lemma_4_2`, `not_Remark_4_2`,
   and the `_force_` variants): all use one degenerate **trap-set** profile
   `lemma41CounterexampleProfile`. This is a formalization-strength issue (the paper's barrier
   lemma holds for the actual strictly-positive constructed wave; the Lean version
   over-quantifies over the whole trap set), not a paper error.
3. **Part I Lemma 2.1–2.4** (`one_not_bounded_by_exp_decay`,
   `inv_not_dominated_by_one_add_inv_sqrt`, IntervalDomainLemma21.lean): scalar facts showing
   the *current Lean undamped H0.1/H0.2 heat-helper route* cannot recover the `exp(−δt)` damping
   and sharp `1+t^{−1/2}` factors by tuning constants alone. The paper's exponential decay comes
   from the equation's built-in damping (the `−u` term) and is sharp and correct; the Lean route
   uses a bare undamped helper. Internal-route boundary, not a paper error.
4. **`not_paper2_theorem_1_1_implies_paper3_proposition_1_2`** (Paper3/Statements.lean:1315):
   an artificial single-point abstract domain shows the finite-`Tmax` bound of Part I Thm 1.1
   does not imply Part II Prop 1.2's eventual boundedness *under the abstract API*. A
   proof-dependency remark (the reduction needs more than the finite-horizon bound), not a
   statement counterexample.
5. **Part II Thm 2.1(4) mass interface & Thm 2.2/2.5 `v₀` re-anchoring**
   (`not_intervalDomain_Theorem_2_1_part4_anyConstants`, etc.): `HasInitialMass`/`InitialTrace`
   constrain only the `t→0⁺` limit, not the stored `u 0`/`v 0` slice, so the zero-time slice can
   be altered. These are documented Lean-interface amendments (correct interface:
   `HasEquilibriumMassOnPositiveTimes`), not paper falsities.
6. **`PositiveInitialDatum` too weak** (FAITHFULNESS_AUDIT trigger): Lean once wrote initial
   positivity as open-interior pointwise positivity (admitting `inf=0`, e.g. `x(1−x)`), while the
   papers' (1.11)/(1.8) require the uniform floor `inf_Ω u₀ > 0`. The **paper hypothesis is
   correct**; the Lean predicate was too weak (now fixed to a uniform floor). TW stated positivity
   correctly via `UniformlyPositive`.
7. **TW Proposition 1.1 "Cauchy solution"** (commit e91d50d5): Lean used strictly-positive
   `IsGlobalCauchySolutionFrom`, while the paper quantifies over arbitrary *nonnegative* BUC data
   (including the zero solution); fixed to `IsGlobalNonnegativeCauchySolutionFrom`. Lean
   definition was too strong; paper correct.
8. **Part II Thm 2.2(nonlinear) / 2.3 / 2.4 for `m>1`** (commits 3f285fb3, 7ce29447): the Lean
   closers currently gate `m=1`, whereas the papers assert `m≥1` and advertise extending the
   Lyapunov-functional method from `m=1` to `m>1`. This is **this formalization's not-yet-covered
   frontier**, not a refutation of the papers' `m≥1` claims.

---

*Maintained as the project's consolidated statement-errata index. New statement-level findings
should be appended here (with a `sorry`-free Lean witness) before forwarding to the authors.*
