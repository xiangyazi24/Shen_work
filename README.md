# A Lean formalization of the chemotaxis–logistic trilogy

This repository formalizes three papers on parabolic–elliptic chemotaxis models with
logistic sources in Lean 4 and Mathlib. It contains the paper-level results, corrected
versions of several overstated statements, and machine-checked results that sharpen or
delimit the original theorems.

The project is pinned to **Lean 4.30.0 / Mathlib v4.30.0**.

## Source papers

| Part | Paper | Local copy |
|---|---|---|
| 1 | Wenxian Shen, [*Existence, uniqueness, stability, and monotonicity of traveling waves for repulsion/attraction chemotaxis models with logistic type source*](https://arxiv.org/abs/2605.04401) | [`papers/shen-traveling-waves.pdf`](papers/shen-traveling-waves.pdf) |
| 2 | Le Chen, Ian Ruau, and Wenxian Shen, [*Chemotaxis models with signal-dependent sensitivity and a logistic-type source, I: Boundedness and global existence*](https://arxiv.org/abs/2512.14858) | [`papers/chen-ruau-shen-boundedness-global-existence.pdf`](papers/chen-ruau-shen-boundedness-global-existence.pdf) |
| 3 | Le Chen, Ian Ruau, and Wenxian Shen, [*Chemotaxis models with signal-dependent sensitivity and a logistic-type source, II: Persistence and stabilization*](https://arxiv.org/abs/2604.02599) | [`papers/chen-ruau-shen-persistence-stabilization.pdf`](papers/chen-ruau-shen-persistence-stabilization.pdf) |

## Integrity

- The tracked Lean sources contain no `sorry`, custom `axiom`, `admit`, or
  `native_decide`.
- Root-imported headline theorems use exactly the standard classical axioms
  `[propext, Classical.choice, Quot.sound]`; they do not use `sorryAx` or
  `Lean.ofReduceBool`.
- `lake build ShenWork` checks the complete root import closure.

To reproduce the build:

```bash
lake exe cache get
lake build ShenWork
```

The public PDFs are generated directly from the committed LaTeX sources.
With [Tectonic](https://tectonic-typesetting.github.io/), rebuild them from
the repository root with:

```bash
tectonic ERRATA.tex --outdir .
tectonic ERRATA_MATHEMATICAL.tex --outdir .
tectonic research_notes/FARLEFT_CHI4_RESOLUTION.tex --outdir research_notes
tectonic research_notes/FARLEFT_CHI4_MATHEMATICAL.tex --outdir research_notes
tectonic research_notes/GENERAL_M_STABILITY_RESOLUTION.tex --outdir research_notes
tectonic research_notes/GENERAL_M_STABILITY_MATHEMATICAL.tex --outdir research_notes
```

## Formalized results

### Part 1: traveling waves on the whole line

- Theorem 1.1: traveling-front construction by the Schauder and Rothe routes.
- Theorem 1.2: co-moving stability in all sign regimes, with only the inherent
  weighted initial-closeness hypothesis.
- Theorem 1.3: uniqueness within the regular traveling-wave class.
- Proposition 1.1: unconditional global Cauchy existence and a priori bounds for all
  sensitivity signs.
- Proposition 1.2 and Lemmas 2.1–2.5, 4.1, and 5.1–5.3.

The principal stability entry points are
`paper1_Theorem_1_2_chi_pos_unconditional`,
`paper1_Theorem_1_2_chi_zero_unconditional`, and
`paper1_Theorem_1_2_chi_neg_unconditional`.

### Part 2: bounded-interval linear-flux theory

- Theorem 1.1 on `intervalDomain`, end to end.
- The corrected Theorem 1.2, unconditionally.
- Theorem 1.3 case (iv) for every positive diffusion exponent: the
  `m ≥ 1` and `m < 1` branches are both closed.
- The analytic stack behind the headline results, including the full-exponent
  Neumann semigroup estimates obtained by subordination.

Several printed statements require corrected formulations for the paper's data class.
For a standalone mathematical treatment, see
[`ERRATA_MATHEMATICAL.pdf`](ERRATA_MATHEMATICAL.pdf)
([LaTeX source](ERRATA_MATHEMATICAL.tex)). The companion
[`ERRATA.pdf`](ERRATA.pdf) ([source](ERRATA.tex), [index](ERRATA.md))
also records the formalization audit.

### Part 3: bounded-interval nonlinear-flux theory

- Eventual forms of Theorems 2.1–2.5 on `intervalDomainM`.
- The full Theorem 2.5 formula for `1 ≤ m ≤ 2`.
- The small-sensitivity route for every `m > 1`.
- A mechanized `m = 3` subcritical steady-pattern counterexample:
  `minimal_equilibrium_global_stability_false_m3`.

The formalization distinguishes the valid eventual statements from the printed
all-time `C¹` claims, which are too strong for merely continuous initial data.

## Beyond the papers

The [`research_notes/`](research_notes/) directory records two sharp-limit results.
Each has a standalone mathematical edition and a formalization companion:

- Far-left threshold `χ = 4`:
  [`mathematical PDF`](research_notes/FARLEFT_CHI4_MATHEMATICAL.pdf),
  [`formalization PDF`](research_notes/FARLEFT_CHI4_RESOLUTION.pdf), and
  [`summary`](research_notes/FARLEFT_CHI4_RESOLUTION.md).
- General-`m` stability and the exact `m = 3` subcritical steady obstruction:
  [`mathematical PDF`](research_notes/GENERAL_M_STABILITY_MATHEMATICAL.pdf),
  [`formalization PDF`](research_notes/GENERAL_M_STABILITY_RESOLUTION.pdf), and
  [`summary`](research_notes/GENERAL_M_STABILITY_RESOLUTION.md).

## Repository layout

- `ShenWork/Paper1/`, `ShenWork/Paper2/`, `ShenWork/Paper3/`: paper-specific
  formalizations.
- `ShenWork/PDE/`, `ShenWork/Wiener/`: shared analytic infrastructure.
- `ShenWork.lean`: root import closure.
- `ERRATA_MATHEMATICAL.pdf`, `ERRATA_MATHEMATICAL.tex`: standalone mathematical
  errata.
- `ERRATA.pdf`, `ERRATA.tex`, `ERRATA.md`: formalization-aware statement audit
  and public index.
- `research_notes/`: detailed PDF/LaTeX notes and summaries for results beyond the papers.
- `papers/`: the three source papers.
