# ShenWork Parallel Task Queue

Updated 2026-05-23 (post unitPoint-batch commit f2fe413).
Owner: claim a slot, edit only the files listed in `Touches`, commit + push,
then move on to next unclaimed slot.  If `Touches` overlaps with an in-progress
slot, pick a different one — fail-fast on file conflicts.

Discipline: 0 sorry / 0 axiom; `lake build ShenWork` must pass after each
commit; one slot at a time per session.

---

## Slot pool (claim by editing the `Claimed:` line)

### Slot A — Paper 1 Lemma 2.5 main-chain assembly
- Owner files: `ShenWork/Paper1/Statements.lean` only (around the
  `KernelConvRpowBound`, `weight_ratio_le`, `Psi_deriv_abs_rpow_le_Psi_rpow`
  cluster).
- Goal: prove the FULL `Lemma_2_5` (∀ pExp γ l μ, ∃ C > 0, ∀ u nonneg ψ
  integrable …) by composing the existing pieces.
- Concretely: take `Psi_deriv_abs_rpow_le_Psi_rpow` to get
  `|Ψ'(u^γ)|^p ≤ √l^p · Ψ^p`; apply `lemma_2_5_jensenStep` to get
  `Ψ^p ≤ C · ∫ K_{x-y} (u^γ)^p`; integrate against ψ and use Fubini +
  `ExponentialWeight.weight_ratio_le` to absorb the inner ∫_x K ψ into
  `ψ(y) · 2/(√l − k)`.  Needs `∫ exp(-c|x|) dx = 2/c` (write a small lemma
  if Mathlib doesn’t expose it directly).
- Output: `Lemma_2_5` instance (full quantifier shape) + supporting lemmas.
- Status: **substantially done** as `Lemma_2_5_restricted_psi_class_holds`
  (commit bcf2b3f), plus full chain in `ShenWork/Paper1/Lemma25Helpers.lean`:
  `kernel_weight_integral_le_psi`, `psi_pExp_weighted_le_kernel_weighted`,
  `psi_deriv_pExp_weighted_le`, `psi_deriv_pExp_weighted_le_kernel_weighted`,
  `psi_deriv_pExp_integral_le_kernel_weighted_integral`, `joint_integrand_le`,
  `ExponentialWeight.integrable`, `.kernel_integrable`,
  `joint_kernel_weight_v_integrable`, `kernel_v_psi_double_integral_le`,
  `psi_kernel_v_integral_integrable`,
  `Lemma_2_5_with_explicit_k_via_Fubini_hypothesis`,
  `Lemma_2_5_with_explicit_k` (full Fubini-discharged, `k < √l`),
  `Lemma_2_5_with_explicit_k_unit`, `Lemma_2_5_existential_for_small_k_psi`,
  `Lemma_2_5_explicit_epsilon`, `Lemma_2_5_explicit_epsilon_CMParams`,
  `Lemma_2_5_explicit_epsilon_CMParams_unit`,
  `Lemma_2_5_from_extracted_psi_k_witness`,
  `Lemma_2_5_restricted_psi_class_holds`.

  **Blocker for closing the original `Lemma_2_5` Prop**: the unrestricted
  `ExponentialWeight` admits ψ with arbitrarily large `k_dab` (e.g.,
  smoothed `exp(-α|x|)` with `α` large), so our weight-transfer constant
  `2/(√l − k_ψ)` cannot be uniform in ψ.  Recommend amending the def to
  use `Lemma_2_5_restricted_psi_class` (which adds an explicit `k < √l`
  quantifier and is closed), or extending `ExponentialWeight` with a
  uniform-k field.

### Slot B — Paper 2 IntervalDomain unitPointDomain-style instances
- Owner files: `ShenWork/Paper2/Statements.lean` only.
- Prerequisite: `intervalBoundedDomainData` (already provided in PDE/
  IntervalDomain etc — verify).
- Goal: port the `unitPointDomain.X` cluster to `intervalDomain`:
  start with `intervalDomain.Lemma_3_1` (already exists? see commit cf5eeff),
  then add `intervalDomain.Lemma_4_1`, `intervalDomain.Proposition_2_5`,
  `intervalDomain.Proposition_2_2`, `intervalDomain.Proposition_2_3`,
  `intervalDomain.Proposition_2_4` mirroring the unitPoint proofs.
- Output: each instance closed; commit one per theorem.
- Status: open.  Claimed: ___

### Slot C — Paper 3 Theorem 2.2 stability/instability composites
- Owner files: `ShenWork/Paper3/Statements.lean` only.
- Goal: add MORE `Theorem_2_2_vacuous_when_*` and minimal-only closures so
  arbitrary `(a, b, m, β, χ₀)` parameter slices have a witness.  In
  particular: `Theorem_2_2_vacuous_when_chi_nonpos` (branches 1/2 hold by
  linear stability, branches 3/4 are vacuous if a ≠ 0 or b ≠ 0; needs the
  `Theorem_2_2_linear_stability_chi_nonpos_branch_direct` plumbing).
- Output: 3–6 new full-composite closures.
- Status: open.  Claimed: ___

### Slot D — Heat kernel Lp smoothing on the interval
- Owner files: `ShenWork/PDE/HeatSemigroup.lean` + the cosine-spectrum
  scaffolding (do NOT touch Paper1/2/3 Statements files in this slot).
- Goal: continue commits 213c17a, 94cb86d, 9d5ec05 — close the remaining
  L²→L∞ gradient smoothing constants from the cosine-basis expansion.  Aim
  for explicit constants K(t) of the heat semigroup gradient norm on
  L²([0,1]).
- Status: open.  Claimed: ___

### Slot E — Paper 3 Lemma A.2/A.3/A.4 closures via cosine spectrum
- Owner files: `ShenWork/Paper3/Statements.lean` cosine-spectrum closures
  (separate from Slot C — work in different name regions; verify by
  grepping the file).
- Goal: continue the `Wire cosine spectrum *_closures` chain (commits
  6fa5fdc, e3bd309, etc.) — close the Lemma_A_2/A_3/A_4 raw analogues.
- Status: open.  Claimed: ___

### Slot F — Real Picard / ODE existence for unit-point logistic
- Owner files: NEW file `ShenWork/PDE/UnitPointLogisticODE.lean` (don’t
  edit existing Lean files in this slot).
- Goal: prove the explicit Bernoulli-substitution solution for
  `u' = u(a − b u^α)` on the unit-point domain (a, b > 0): define
  `bernoulliLogisticSolution p u₀ t : ℝ` and prove HasDerivAt at every t,
  positivity, boundedness by max(u₀, (a/b)^(1/α)).  Once available, use it
  to lift `unitPointDomain.Theorem_1_1` to the **non-minimal** branch.
- Status: done by codex-3 (commits cf7a43f, b64fa91, 5f68900, 85865d0 merged).

---

## Window assignments (coordinator: shen-codex / Opus 4.7)

Updated 2026-05-24. Each window picks the slot pre-assigned below; if
the slot is already complete, take the next unclaimed one in the pool.
Owner files are disjoint so no file races.

| Window      | Slot | Owner file                         | Pre-claim status |
| ----------- | ---- | ---------------------------------- | ---------------- |
| shen-codex  | G    | `ShenWork/Paper2/Statements.lean`  | claimed          |
| shen-codex-2| H    | `ShenWork/Paper3/Statements.lean`  | claimed          |
| shen-codex-3| L    | `ShenWork/Paper2/Statements.lean` (no overlap with G — different theorem) | claimed |
| shen-codex-?| I    | `ShenWork/Paper2/Statements.lean` (small, only Lemma_3_1_nonminimal) | next-up |
| shen-codex-?| J    | `ShenWork/Paper1/Statements.lean`  | next-up          |
| shen-codex-?| K    | `ShenWork/Paper3/Statements.lean` (different region from H) | next-up |

Rules:
1. Edit only your slot's owner file. If a file is shared, edit DIFFERENT
   theorems (grep before editing).
2. After each commit: `lake build ShenWork`, `rg '\bsorry\b' ShenWork/`.
3. Local push fails (no GitHub credential) — that's expected, mac-side dm
   pulls and syncs.
4. When your slot closes (or you finish all assigned work), take the next
   unclaimed slot.
5. Mark `Status:` lines done as you go; coordinator (this comment block)
   adds new slots when pool runs low.

## Next-round slot pool (fresh tasks for windows 11/12/13)

### Slot G — Paper 2 `intervalDomain` mirror of unit-point closures
- Owner files: `ShenWork/Paper2/Statements.lean` only (do NOT touch
  `PDE/IntervalDomain.lean` or `IntervalDomainMaxPrinciple.lean`).
- Prerequisites in place: `ShenWork.IntervalDomain.intervalDomain` is a
  `BoundedDomainData` instance; `Lemma_3_1_intervalDomain` is proved
  (line ~3558).  `SupNormAntitoneData` is the renamed interval-side
  parabolic max-principle data.
- Goal: provide `intervalDomain` analogs of `unitPointDomain.{Lemma_4_1,
  Proposition_2_2, Proposition_2_3, Proposition_2_4, Proposition_2_5}`,
  mirroring the unitPoint proofs.  Names like
  `intervalDomain_Lemma_4_1` (avoid project-name collision with Paper3’s
  `unitPointDomain.Lemma_4_1`).
- Output: one commit per theorem, each ≤ ~100 LOC.
- Status: open.  Claimed: ___

### Slot H — Paper 3 `Theorem_2_2` full-composite closures on unit-point
- Owner files: `ShenWork/Paper3/Statements.lean` only.
- Current state (commit dbeaa63): `Theorem_2_2_vacuous_when_a_zero_b_nonzero`
  and `_b_zero` exist plus a minimal-only chi-nonpos composite.
- Goal: add full-composite closures for each remaining `(a, b, χ₀, m)`
  slice where the four branches can be discharged via
  `Theorem_2_2_linear_stability_chi_nonpos_branch_direct` and
  `Theorem_2_2_linear_threshold_branch_direct`, e.g.
  `Theorem_2_2_minimal_only_b_zero`, `Theorem_2_2_when_chi_nonpos_a_zero`,
  etc.
- Output: 3–6 new full-composite closures.
- Status: open.  Claimed: ___

### Slot I — Paper 2 `Lemma_3_1_nonminimal_branch` honest refutation polish
- Owner files: `ShenWork/Paper2/Statements.lean`.
- Already refuted by `not_forall_Lemma_3_1_nonminimal_branch`.  Goal:
  add a `Lemma_3_1_nonminimal_branch_when_a_zero` vacuous closure and any
  parameter-slice provable variants (mirror the `Theorem_2_1_partN_*`
  pattern).  Useful for downstream Paper3 stability composites.
- Output: 2–4 closure lemmas.
- Status: open.  Claimed: ___

### Slot J — Paper 1 `Lemma_2_1` (heat-semigroup `L^p → L^q`) zero-data
  branches and a real bounded-input chain
- Owner files: `ShenWork/Paper1/Statements.lean`.
- Current state: `Lemma_2_1_zero_output_branch`,
  `Lemma_2_1_zero_data` exist; full bound externalized in
  `HeatSemigroupEstimateData`.
- Goal: prove `Lemma_2_1` for the bounded-measurable inputs subclass
  using the existing whole-line heat-kernel `L^1 → L^∞` smoothing and
  derivative-kernel chain in `ShenWork/PDE/HeatSemigroup.lean` plus
  `Defs.lean`.  Should not need new measure-theoretic primitives.
- Output: 1–3 new branch theorems closer to `Lemma_2_1` full statement.
- Status: open.  Claimed: ___

### Slot K — Paper 3 `Lemma_A_6` constants/transport rewrite
- Owner files: `ShenWork/Paper3/Statements.lean`.
- `Lemma_A_6_direct` is closed; the remaining `Lemma_A_2/3/4/5.paper2`
  bridges to Paper 2 semigroup targets can be tightened (e.g., remove
  redundant hypotheses, replace projection accessors by direct
  computations where the Paper 2 zero-output branches already give
  enough).
- Output: 2–4 cleanup commits.
- Status: open.  Claimed: ___

### Slot L — Paper 2 `Theorem_1_1` nonminimal branch via Slot F output
- Owner files: `ShenWork/Paper2/Statements.lean` (Slot F's
  `ShenWork/PDE/UnitPointLogisticODE.lean` is read-only here).
- Slot F's `bernoulliLogisticSolution` and lift theorems give the
  classical solution for `0 < p.a, 0 < p.b` on `unitPointDomain`.
- Goal: drop `_minimal_only` from `unitPointDomain.Theorem_1_1` and
  prove the full theorem on `unitPointDomain` by routing the
  nonminimal branch through Slot F's machinery.  Similar work for
  `Theorem_1_2` and `Theorem_1_3` once F is wired in.
- Output: 1–3 commits closing each `unitPointDomain.Theorem_1_X` fully.
- Status: open.  Claimed: ___

---

## Sequencing notes

- Slots A–F touch disjoint files; safe to run in parallel.
- After each commit, run `lake build ShenWork` and `rg -n '\\bsorry\\b'
  ShenWork/`; only proceed if both clean.
- Push attempts may fail on uisai1 (no GitHub credential); local commits
  are still authoritative.
- If you finish a slot, mark it `Status: done.  Closed by <hash>.` and
  add a new slot at the bottom describing the next reasonable extension.
