# Shen_work — Current Task for Codex

## Build

```bash
~/.openclaw/workspace/scripts/remote-build.sh shen_work
~/.openclaw/workspace/scripts/remote-build.sh shen_work --file ShenWork/Paper3/Statements.lean
```

NEVER run local `lake build`. Invariant: 0 sorry, BUILD OK.

## Task: Paper3 Theorem 2.3/2.4/2.5 global stability convergence bridges

File: `ShenWork/Paper3/Statements.lean`

### Context

Paper3 Theorems 2.3--2.5 each have two components:
1. **Linear stability** — proved for 2.4 and 2.5 (see `Theorem_2_4_linear_stability_formula_branch_proved`, `Theorem_2_5_linear_stability_formula_branch_proved`, and their first-mode variants)
2. **Global/exponential convergence** — still externalized in package fields

The exponential convergence conclusions route through `MassConstrainedLocallyExponentiallyStableFromSup` and `ExponentialC1Convergence`. These are already assembled for some branches (see e.g. `Theorem_2_2.nonminimal_stability_conclusion_of_Lemma_A_7`, `Theorem_2_2.minimal_exponential_convergence_of_Lemma_A_8`).

### What to add

Build more **formula-level** bridges that bypass the `Paper3Constants` package and state conclusions directly using the explicit threshold formulas and `paperCriticalSensitivity`. These should follow the pattern of the existing `Theorem_2_4_linear_stability_formula_branch` and `Theorem_2_5_linear_stability_formula_branch` but extend to the full stability + convergence conclusions.

#### 1. Theorem 2.3 negative-sensitivity convergence formula bridge

For the negative-sensitivity case (`χ₀ ≤ 0`), the linear stability is trivially satisfied (already proved by `Theorem_2_2_linear_stability_chi_nonpos_branch_proved`). Build a bridge that:
- Takes `χ₀ ≤ 0`, `a > 0`, `b > 0`, Neumann spectrum, and the sectorial local exponential stability conclusion as explicit hypotheses
- Gives both `LinearlyStable` and `MassConstrainedLocallyExponentiallyStableFromSup` for the positive equilibrium

The sectorial stability should be an explicit hypothesis (not from a package) since the analytic proof is still open.

#### 2. Theorem 2.4 full stability formula bridge

Extend `Theorem_2_4_linear_stability_formula_branch` to also conclude `MassConstrainedLocallyExponentiallyStableFromSup`. This should:
- Keep the existing explicit formula threshold hypotheses
- Add an explicit `SectorialLocalExponentialRaw`-style hypothesis for the local exponential part
- Give both linear stability and exponential stability as conclusions

#### 3. Theorem 2.5 full stability formula bridge

Same pattern as (2) but for the minimal model with `a = 0, b = 0, m = 1`.

#### 4. Explicit equilibrium formula simplifications

Add bridge lemmas that simplify the equilibrium formulas for special parameter cases that appear in the paper's examples:
- `positiveEquilibrium_fst_eq_one` when `a = b` (so `(a/b)^(1/α) = 1`)
- `positiveEquilibrium_snd_eq_nu_div_mu` when `a = b` and `γ = 1`
- `minimalEquilibrium_snd_eq_nu_div_mu_mul_uStar` when `γ = 1`

These are algebraic simplifications from the existing definitions that make the threshold formulas more concrete.

### Constraints

- 0 sorry, BUILD OK
- No axioms, no assumption structures
- Follow the naming pattern of existing `_formula_branch` and `_first_mode_branch` theorems
- Add theorems after the existing `Theorem_2_5_linear_stability_first_mode_branch_proved` and before `Theorem_2_2.nonminimal_stability_conclusion_of_Lemma_A_7`
- Keep `#print axioms` checks for any new `_proved` theorems
- Run `rg -n "\bsorry\b" ShenWork --glob '*.lean'` after every edit
