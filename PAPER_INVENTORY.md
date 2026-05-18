# Paper inventory

This is the working checklist for paper-level formalization.  It is generated
from the root PDFs (`paper1.pdf`, `paper2.pdf`, `paper3.pdf`) and should be kept
in sync with Lean statement targets.

Status labels:

- `proved`: proved from current non-toy Lean definitions.
- `statement target`: represented as a Lean `Prop`/definition target, not proved.
- `partial`: some supporting definitions exist, but the paper item is not fully
  stated.
- `missing`: no Lean statement target yet.
- `remark/doc`: explanatory paper material; formalize only when it carries a
  reusable hypothesis, estimate, or dependency.

## Paper1: traveling waves on the line

Source: `paper1.pdf`, Wenxian Shen, traveling waves for chemotaxis-logistic
systems.

| Paper item | Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Proposition 1.1 | `Paper1.Proposition_1_1` | statement target | Global Cauchy existence and bounds. |
| Proposition 1.2 | `Paper1.Proposition_1_2` | statement target | Stability of `(1,1)`. |
| Theorem 1.1 | `Paper1.Theorem_1_1` | statement target | Traveling-wave existence. |
| Theorem 1.2 | `Paper1.Theorem_1_2` | statement target | Weighted stability of waves. |
| Theorem 1.3 | `Paper1.Theorem_1_3` | statement target | Uniqueness with right-tail normalization. |
| Remarks 1.1--1.5 | none | remark/doc | Mine later for dependencies and parameter regimes. |
| Lemma 2.1 | `HeatSemigroupEstimateData`, `Paper1.Lemma_2_1` | statement target | Semigroup `L^p-L^q` estimates. |
| Lemma 2.2 | `PsiDerivativeFormula`, `Paper1.Lemma_2_2` | statement target | Elliptic resolvent kernel and derivative formula. |
| Lemma 2.3 | `Paper1.Lemma_2_3`, `Paper1.Lemma_2_3_unit_proved` | partial | Unit-parameter derivative bound is proved; general `(λ, μ)` packaging remains. |
| Lemma 2.4 | `Paper1.Lemma_2_4_proved`, `Psi_le_min_const_exp_of_nonneg_le` | proved | Exponential resolvent bound for `Ψ(·;u,1,1)`. |
| Lemma 2.5 | `ExponentialWeight`, `Paper1.Lemma_2_5` | statement target | Weighted `L^p` estimate for `∇Ψ(u^γ)`. |
| Lemma 4.1 | `frozenWaveOperator`, `upperBarrier`, `Paper1.Lemma_4_1` | statement target | Super-solution barrier for frozen moving-frame equation; basic `upperBarrier`, trap-set projection, and trap-set power bounds proved. |
| Lemma 4.2 | `lowerBarrierRaw`, `lowerBarrierPlateau`, `SubsolutionConstants`, `Paper1.Lemma_4_2` | statement target | Sub-solution barriers; raw lower-barrier factorization, derivative formulas/signs, `x_- < x_+`, critical point at `x_+`, positivity, and exponential upper control of raw/plateau lower barriers proved. |
| Remarks 4.1--4.3 | none | remark/doc | Include constants/asymptotics used by later theorem statements. |
| Lemma 5.1 | `MChi`, `HasWaveUpperTailBound`, `Paper1.Lemma_5_1` | statement target | A priori estimates for stationary wave profiles; basic `MChi`, `MChi` power positivity, tail-bound projections, and `U^γ` bounds proved. |
| Lemma 5.2 | `Paper1.Lemma_5_2` | statement target | Estimate for `u_x/u`. |
| Remarks 5.1--5.2 | none | remark/doc | Feed into definition of `cStarStar` and stability constants. |

## Paper2: boundedness and global existence on bounded domains

Source: `paper2.pdf`, Chen-Ruau-Shen Part I.

| Paper item | Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Definition 1.1 | `Paper2.IsPaper2ClassicalSolution` | partial | Abstract domain/operator interface, not instantiated smooth domain. |
| Proposition 1.1 | `Paper2.Proposition_1_1` | statement target | Local existence/blow-up alternative. |
| Theorem 1.1 | `Paper2.Theorem_1_1` | statement target | Negative sensitivity. |
| Theorem 1.2 | `Paper2.Theorem_1_2` | statement target | Weak nonlinear cross diffusion. |
| Theorem 1.3 | `Paper2.Theorem_1_3` | statement target | Strong logistic source. |
| Remarks 1.1--1.7 | none | remark/doc | Useful for proof strategy and parameter comparisons. |
| Lemmas 2.1--2.4 | `SemigroupEstimateData`, `Lemma_2_1`--`Lemma_2_4` | statement target | Abstract semigroup/fractional-power estimate layer. |
| Lemma 2.5 | `Psi_beta`, `Theta_beta`, `Lemma_2_5_proved`, `Psi_beta_pos`, `Psi_beta_lt_one`, `Theta_beta_pos`, `Psi_beta_eq_beta_mul_Theta_beta` | partial | Scalar entropy inequality and basic `Ψβ`/`Θβ` endpoint, positivity, bounds, and relations proved; monotonicity and asymptotic limit of `Ψβ` remain. |
| Lemma 2.6 | `AbstractLpBootstrapHypothesis`, `Lemma_2_6` | statement target | Abstract `L^p` bootstrap target. |
| Corollary 2.1 | `Corollary_2_1` | statement target | Chemotaxis cross-term bootstrap target. |
| Propositions 2.2--2.5 | `Proposition_2_2`--`Proposition_2_5` | statement target | Integral estimates and boundedness criterion; `χβ` positivity, upper-bound, and denominator branch algebra proved. |
| Lemma 2.7 | `Lemma_2_7` | statement target | ODE/integral inequality used in bootstrap. |
| Lemma 3.1 | `Lemma_3_1` | statement target | Negative-sensitivity estimate. |
| Lemma 4.1 | `Lemma_4_1` | statement target | Weak cross-diffusion estimate. |

## Paper3: persistence and stabilization

Source: `paper3.pdf`, Chen-Ruau-Shen Part II.

| Paper item | Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Propositions 1.1--1.4 | `Paper3.Proposition_1_1`--`Paper3.Proposition_1_4` | statement target | Recalled from Part I. |
| Definition 2.1 | `LinearlyStable`, `LinearlyUnstable`, stability predicates | partial | Needs exact spectral-domain API and local exponential stability statement; equilibrium positivity, constant-state algebra, and negative-sensitivity spectral sign lemmas are proved. |
| Theorem 2.1 | `Paper3.Theorem_2_1` | statement target | Uniform persistence. |
| Theorem 2.2 | `Paper3.Theorem_2_2` | statement target | Linear stability/instability; negative-sensitivity `sigma < 0` and linearly-stable corollaries proved for positive equilibria under nonnegative eigenvalues and for minimal equilibria under positive nonzero eigenvalues. |
| Theorem 2.3 | `Paper3.Theorem_2_3` | statement target | Global stability for negative sensitivity. |
| Theorem 2.4 | `Paper3.Theorem_2_4` | statement target | Global stability with strong logistic source. |
| Theorem 2.5 | `Paper3.Theorem_2_5` | statement target | Minimal-model stability. |
| Remarks 2.1--2.4 | none | remark/doc | Threshold comparisons and biological interpretation. |
| Lemma 3.1 | `Paper3.Lemma_3_1` | statement target | Uniform regularity for bounded positive global solutions. |
| Lemma 3.2 | `Paper3.Lemma_3_2` | statement target | Compactness of time translates. |
| Lemma 3.3 | `Paper3.Lemma_3_3` | statement target | Continuity with respect to initial data. |
| Lemma 3.4 | `Paper3.Lemma_3_4` | statement target | Monotonicity of upper envelope from Part I. |
| Lemma 3.5 | `Paper3.Lemma_3_5` | statement target | Eventual upper bound in minimal model. |
| Corollary 5.1 | `Paper3.Corollary_5_1` | statement target | Converts convergence plus linear stability into exponential convergence. |
| Lemma 7.1 | `Paper3.Lemma_7_1` | statement target | Neumann resolvent gradient estimate. |

## Immediate proof candidates

These are small, non-PDE targets worth proving before the next analytic push:

1. Extend Paper3 spectral-domain API: exact Neumann eigenvalue assumptions,
   instability threshold predicates, and local exponential stability packaging.
2. Paper1 speed/decay algebra already has `cStarLower_ge_two` and
   `kappa_pos_of_two_lt`; next small additions should support `Theorem_1_1`.
3. Continue proving Paper1 Lemma 2.2/2.3: unit-parameter Lemma 2.3 and
   Lemma 2.4 are proved; general `(λ, μ)` derivative formula remains.
