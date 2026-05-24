# ShenWork Parallel Task Queue

Updated 2026-05-24 20:00 CT.

Discipline: 0 sorry / 0 axiom; `export PATH="$HOME/.elan/bin:$PATH" && lake build ShenWork` must pass after each commit; `rg -n '\bsorry\b' ShenWork/` before every commit.

Git author: `git -c user.email="xiangyazi24@gmail.com" -c user.name="Xiang Huang"`

---

## Current status

Build: CLEAN (8281 jobs, 0 sorry, 0 axiom, 0 admit).
Axiom audit: only [propext, Classical.choice, Quot.sound].
11-point playbook: ALL PASS.

### Unconditional closures (no parameter restrictions)
- Paper2: Theorem_1_1, Theorem_1_3 (all p, C)
- Paper3: Proposition_1_3, Proposition_1_4, Theorem_2_5 (all p)
- Paper3: Lemma_3_1_proved (all D, p — pure definitional)

### Conditional closures (parameter-restricted)
- Paper2: Theorem_1_2 when_not_a_pos_b_zero (3-of-4; a>0 b=0 genuinely fails)
- Paper3: Proposition_1_2 when_not_a_pos_b_zero (3-of-4; same blocker)

### Vacuous closures (50+ theorems)
- Paper2: Theorem_1_1/1_2/1_3 parameter slices
- Paper3: Theorem_2_1 parts (15+ building blocks + 10+ composites)
- Paper3: Theorem_2_2 (a_zero_b_nonzero, a_nonzero_b_zero)
- Paper3: Theorem_2_3 (a_pos_b_zero, a_zero_b_pos, chi_pos, m_lt_one)
- Paper3: Theorem_2_4 (a_zero, b_zero)
- Paper3: Theorem_2_5 (a_nonzero, b_nonzero, m_ne_one, beta_lt_one)
- Paper3: Proposition_1_2/1_3/1_4 vacuous slices (chi_pos, m_lt_one, etc.)

### Genuinely blocked (needs new infrastructure)
- Theorem_1_2 full: (a>0,b=0) unitPoint ODE unbounded
- Proposition_1_1: FiniteHorizonAlternative false for bounded positive solutions
- Theorem_2_2 full: needs SectorialLocalExponentialRaw
- Theorem_2_3 full: needs ODE uniqueness + PGBS convergence at t=0
- Paper1 Lemma_2_5 full: ExponentialWeight k_dab unbounded
- intervalDomain mirror: needs Gagliardo-Nirenberg-Poincaré

---

## Active slots for codex windows

### Slot U1 — Refute Theorem_1_2 for (a>0, b=0) on unitPointDomain
- **Owner**: Window 11 (shen-codex-2)
- **File**: `ShenWork/Paper2/UnitPointLogisticBridge.lean` ONLY
- **Goal**: Prove `not_Theorem_1_2_unitPointDomain_when_a_pos_b_zero`:
  show that for specific CM2Params with a=1, b=0, m=1, β=1, χ₀=0,
  `Theorem_1_2 unitPointDomain p` is **false**.
- **Approach**: From the PDE on unitPointDomain with b=0:
  `timeDeriv u t () = u t () * a` (since laplacian=0, chemotaxisDiv=0, b=0).
  Any IsPaper2GlobalClassicalSolution satisfying this has u increasing
  (since u > 0 and a > 0). IsPaper2Bounded requires eventual sup-norm bound.
  But u increasing + positive + u'=au implies u(t)() → ∞, contradicting
  bounded. Use Gronwall-type: if u(t₀)() > 0 and u' ≥ au on [t₀,∞),
  then u(t)() ≥ u(t₀)() for all t ≥ t₀, so deriv ≥ a·u(t₀)() > 0 forever,
  giving u(t) ≥ u(t₀)() + a·u(t₀)()·(t-t₀) → ∞.
- **Output**: `theorem not_Theorem_1_2_unitPointDomain_when_a_pos_b_zero`
- **Difficulty**: Medium (real math argument, not vacuous)
- Status: **OPEN — CLAIM NOW**

### Slot U2 — Paper2 Lemma_2_7 on unitPointDomain
- **Owner**: Window 12 (shen-codex-3)
- **File**: `ShenWork/Paper2/Statements.lean` ONLY (add at end before `end`)
- **Goal**: Prove `unitPointDomain.Lemma_2_7` for the unitPointDomain.
  `Lemma_2_7` says: given a Grönwall-type differential inequality for
  Lp norms, conclude LpPowerBoundedBefore. On unitPointDomain,
  `integral f = f ()` and `deriv (integral (|u|^p)) = deriv (|u()|^p)`,
  so the differential inequality becomes a scalar ODE inequality that
  gives a pointwise bound.
- **Approach**: From AbstractLpBootstrapHypothesis get `LpPowerBoundedBefore p0`.
  On unitPointDomain, `|u(t)()|^p0 ≤ C₀`. So `|u(t)()| ≤ C₀^(1/p0)`.
  Then `|u(t)()|^pExp ≤ (C₀^(1/p0))^pExp` for any pExp.
  Actually re-read Lemma_2_7 — it takes a differential inequality as input
  and concludes LpPowerBoundedBefore. The key is the scalar case.
- **Output**: `theorem unitPointDomain.Lemma_2_7 : Lemma_2_7 unitPointDomain`
- **Difficulty**: Medium
- Status: **OPEN — CLAIM NOW**

### Slot U3 — Paper3 Theorem_2_1 composites for a_pos_b_pos slices
- **Owner**: Window 13
- **File**: `ShenWork/Paper3/Statements.lean` ONLY
- **Goal**: Add more Theorem_2_1 full composites for (a>0, b>0) slices.
  Currently `Theorem_2_1_vacuous_when_a_pos_b_pos_chi_nonpos_m_lt_one` exists.
  Add: `Theorem_2_1_when_a_pos_b_pos_chi_nonpos_beta_lt_one`,
  `Theorem_2_1_when_a_pos_b_pos_chi_nonpos_m_ne_one`, etc. using the
  existing building blocks.
- **Building blocks available**: See lines 11299-11464 for all part-level
  vacuous closures. The key new ones from commit 0afd818:
  `part2_vacuous_when_m_ne_one`, `part2_vacuous_when_beta_lt_one`,
  `part3_vacuous_when_beta_lt_one`.
- **Output**: 3-5 new full composites
- **Difficulty**: Easy (just combining building blocks)
- Status: **OPEN — CLAIM NOW**

---

## Rules
1. Edit ONLY your slot's owner file. One writer per file.
2. After each commit: `lake build ShenWork`, `rg '\bsorry\b' ShenWork/`.
3. Git author: `git -c user.email="xiangyazi24@gmail.com" -c user.name="Xiang Huang"`
4. `git diff --check` before every commit.
5. When done, mark Status as `DONE` and take next unclaimed slot.

## Sequencing
- Slots U1/U2/U3 touch disjoint files — safe to run in parallel.
- After each commit, full build required before proceeding.
