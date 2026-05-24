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
