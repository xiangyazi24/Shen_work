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
| Theorem 1.2 | `Paper1.Theorem_1_2`, `StableWaveParameterRegime` | statement target | Weighted stability of waves; stable-regime projections `χ < 1` and `Mχ > 0` proved. |
| Theorem 1.3 | `Paper1.Theorem_1_3` | statement target | Uniqueness with right-tail normalization. |
| Remarks 1.1--1.5 | none | remark/doc | Mine later for dependencies and parameter regimes. |
| Lemma 2.1 | `HeatSemigroupEstimateData`, `Paper1.Lemma_2_1` | statement target | Semigroup `L^p-L^q` estimates. |
| Lemma 2.2 | `PsiDerivativeFormula`, `Paper1.Lemma_2_2`, `Paper1.Lemma_2_2_kernel_formula_proved` | partial | Elliptic resolvent kernel formula proved by definition; derivative formula remains. |
| Lemma 2.3 | `Paper1.Lemma_2_3`, `Paper1.Lemma_2_3_unit_proved` | partial | Unit-parameter derivative bound is proved; general `(λ, μ)` packaging remains. |
| Lemma 2.4 | `Paper1.Lemma_2_4_proved`, `Psi_le_min_const_exp_of_nonneg_le` | proved | Exponential resolvent bound for `Ψ(·;u,1,1)`. |
| Lemma 2.5 | `ExponentialWeight`, `Paper1.Lemma_2_5` | statement target | Weighted `L^p` estimate for `∇Ψ(u^γ)`. |
| Lemma 4.1 | `frozenWaveOperator`, `frozenElliptic`, `expDecay`, `upperBarrier`, `InWaveTrapSet`, `WaveTrapSet`, `InMonotoneWaveTrapSet`, `MonotoneWaveTrapSet`, `Paper1.Lemma_4_1` | partial | Super-solution barrier for frozen moving-frame equation; frozen elliptic nonnegativity, smooth exponential branch positivity/monotonicity/limits/derivative/linear-part identities, `upperBarrier` branch/monotonicity/continuity/boundedness/membership and power-bound facts, ordinary/monotone trap-set projection, named trap sets, trap-set monotonicity in `M`, trap-set power bounds, zero-profile membership/nonemptiness, and ordinary/monotone trap-set convexity proved. |
| Lemma 4.2 | `lowerBarrierRaw`, `lowerBarrierPlateau`, `subsolutionK`, `subsolutionDThreshold`, `constantSubsolutionThreshold`, `Paper1.Lemma_4_2` | statement target | Sub-solution barriers; raw lower-barrier factorization, continuity, derivative formulas/signs, right-tail antitonicity, explicit paper constants `K_{M,κ,κ̃,m,γ}`, `D_{M,κ,κ̃,χ,m,γ}`, and `d_{κ,κ̃,D,χ}` represented with positivity lemmas, speed denominator positivity, `x_+` monotonicity in `D`, existence of arbitrarily large `D` making `exp(-κ x_+) ≤ M`, linear-part identities, speed-normalized coefficient negativity/linear-part positivity including the `kappa c` and `cStarLower p < c` specializations, `x_- < x_+`, critical point at `x_+`, positivity, exponential/rpow upper control of raw/plateau lower barriers, plateau `IsCUnifBdd`, plateau antitonicity, ordinary/monotone trap-set membership with bound `exp(-κ x_+)` or any larger `M`, existential ordinary/monotone trap-set membership for `D` above the explicit paper threshold, existence of admissible positive constant subsolutions `d` below the paper threshold, and projections from the paper's `κ̃` range proved. |
| Remarks 4.1--4.3 | none | remark/doc | Include constants/asymptotics used by later theorem statements. |
| Lemma 5.1 | `MChi`, `HasWaveUpperTailBound`, `Paper1.Lemma_5_1` | statement target | A priori estimates for stationary wave profiles; basic `MChi`, `MChi` power positivity, explicit positive-sensitivity `MChi` formula, positive Shen upper-bound conversion to tail/trap-set bounds, tail-bound projections, conversion to ordinary/monotone trap-set membership, and generic/`γ` power bounds proved. |
| Lemma 5.2 | `Paper1.Lemma_5_2` | statement target | Estimate for `u_x/u`. |
| Lemma 5.3 | `Paper1.Lemma_5_3` | statement target | Weighted elliptic perturbation estimates used in the stability energy proof. |
| Remarks 5.1--5.2 | none | remark/doc | Feed into definition of `cStarStar` and stability constants. |

## Paper2: boundedness and global existence on bounded domains

Source: `paper2.pdf`, Chen-Ruau-Shen Part I.

| Paper item | Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Definition 1.1 | `Paper2.IsPaper2ClassicalSolution` | partial | Abstract domain/operator interface, not instantiated smooth domain; basic `positivePart` branch and iff lemmas proved. |
| Proposition 1.1 | `Paper2.Proposition_1_1` | statement target | Local existence/blow-up alternative. |
| Theorem 1.1 | `Paper2.Theorem_1_1`, `IsPaper2BoundedBefore` | statement target | Negative sensitivity; now separates finite-horizon boundedness from the paper's `m ≥ 1` global-existence conclusion. |
| Theorem 1.2 | `Paper2.Theorem_1_2`, `IsPaper2BoundedBefore` | statement target | Weak nonlinear cross diffusion; sublinear branch now states finite-horizon boundedness, while the `m = 1` branch states global boundedness. |
| Theorem 1.3 | `Paper2.Theorem_1_3`, `StrongLogisticCondition`, `IsPaper2BoundedBefore` | statement target | Strong logistic source; boundedness part now uses finite-horizon boundedness and global existence is restricted to `m ≥ 1`; branch constructors, low-dimensional critical-branch constructors, common `β ≥ 0` projection, and unified `α` lower-bound projections for `m ≥ 1` / `m ≤ 1` proved. |
| Remarks 1.1--1.7 | none | remark/doc | Useful for proof strategy and parameter comparisons. |
| Lemmas 2.1--2.4 | `SemigroupEstimateData`, `Lemma_2_1`--`Lemma_2_4` | statement target | Abstract semigroup/fractional-power estimate layer. |
| Lemma 2.5 | `Psi_beta`, `Theta_beta`, `Lemma_2_5_proved`, `Psi_beta_eq_at_inv`, `Psi_beta_pos`, `Psi_beta_lt_one`, `Psi_beta_lt_self`, `Theta_beta_zero`, `Theta_beta_pos_of_nonneg`, `Theta_beta_lt_one`, `Psi_beta_eq_beta_mul_Theta_beta` | partial | Scalar entropy inequality, equality case at `v=1/β`, and basic `Ψβ`/`Θβ` endpoint, positivity, bounds, self-bound, and relations proved; monotonicity and asymptotic limit of `Ψβ` remain. |
| Lemma 2.6 | `AbstractLpBootstrapHypothesis`, `LpBootstrapEnergyInequality`, `Lemma_2_6` | statement target | Abstract `L^p` bootstrap target; dimension is now separate from domain volume, the hypothesis keeps the paper's differential energy inequality shape, and basic hypothesis projections are proved. |
| Corollary 2.1 | `Corollary_2_1`, `CrossDiffusionBootstrapEstimate` | statement target | Chemotaxis cross-term bootstrap target with the paper's small-`ε` cross-diffusion estimate as an explicit hypothesis; pointwise estimate projection is proved. |
| Proposition 2.1 | `Proposition_2_1` | statement target | Fundamental `L^p` estimate for elliptic signal `v` in terms of `u^γ`. |
| Propositions 2.2--2.5 | `Proposition_2_2`--`Proposition_2_5`, `WeightedGradientEstimate`, `WeightedSignalEstimate`, `MassConservedBefore`, `LogisticMassUpperBoundBefore`, `LpPowerBoundedBefore` | statement target | Fundamental weighted `∇v` and signal estimates, mass comparison, and boundedness criteria; Proposition 2.4 now states the paper's mass conservation/upper-bound result and Proposition 2.5 includes the high-exponent `L^p` boundedness hypothesis; estimate projection lemmas, `χβ` positivity, upper-bound, half/sqrt threshold projections, and denominator branch algebra proved. |
| Lemma 2.7 | `Lemma_2_7` | statement target | Integral differential inequality used in bootstrap, with the paper's `d/dt ∫u^p` and damping powers represented explicitly. |
| Lemma 3.1 | `Lemma_3_1`, `SupNormNonincreasingOn` | statement target | Negative-sensitivity upper-envelope monotonicity; corrected from a false global `supNorm ≤ initial supNorm` claim to the paper's conditional monotonicity statement. |
| Lemma 4.1 | `Lemma_4_1` | statement target | Weak cross-diffusion estimate. |

## Paper3: persistence and stabilization

Source: `paper3.pdf`, Chen-Ruau-Shen Part II.

| Paper item | Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Propositions 1.1--1.4 | `Paper3.Proposition_1_1`--`Paper3.Proposition_1_4` | statement target | Recalled from Part I. |
| Definition 2.1 | `LinearlyStable`, `LinearlyUnstable`, `HasNeumannSpectrum`, stability predicates | partial | Neumann spectral API, equilibrium positivity, constant-state/logistic-reaction algebra, stable/unstable incompatibility, and negative-sensitivity spectral sign lemmas are proved; local exponential stability packaging remains. |
| Theorem 2.1 | `Paper3.Theorem_2_1`, `minimalVLowerFormula` | statement target | Uniform persistence; the minimal-model `v` lower bound now uses the paper's explicit Gaussian-lower-bound constant formula rather than an opaque placeholder, with formula positivity projected from positive data. |
| Theorem 2.2 | `Paper3.Theorem_2_2`, `SupCloseToConstant`, `ExponentialC1ConvergenceWith` | statement target | Linear stability/instability with local exponential stability now stated with the paper's small-sup-norm perturbation hypothesis and minimal-model mass constraint; negative-sensitivity `sigma < 0`, linear `σ` decomposition in `χ₀`, positive chemotaxis coefficient, critical-`χ` threshold algebra, and stable/unstable corollaries proved for positive/minimal equilibria under Neumann spectrum hypotheses. |
| Theorem 2.3 | `Paper3.Theorem_2_3`, `ExponentialC1ConvergenceWith` | statement target | Global stability for negative sensitivity; exponential constants are now quantified uniformly over the solution class, matching the paper. |
| Theorem 2.4 | `Paper3.Theorem_2_4`, `NonminimalGlobalStabilityCondition`, `betaTilde`, `chiStrong1Formula`--`chiStrong4Formula`, `chiBarFormula`, `vABLowerFormula`, `ExponentialC1ConvergenceWith` | partial | Global stability with strong logistic source; exact paper threshold formulas `(2.13)`, `(2.15)`--`(2.19)`, named nonminimal stability-condition predicate/constructors/projections, `β̃` range/piecewise facts, Bernoulli weight bound `1 + β̃v ≤ (1+v)^(2β)`, positivity/nonnegativity for `χ**1`--`χ**4`, `\barχ`, and `\underline v_{a,b}` under usable hypotheses, plus `χ**₂/χ**₄ → \barχ` threshold projections proved; exponential constants are quantified uniformly over the solution class. |
| Theorem 2.5 | `Paper3.Theorem_2_5`, `MinimalGlobalStabilityCondition`, `minimalUpperBoundFormula`, `minimalVLowerFormula`, `GammaMinimalFormula`, `chiMinimal1Formula`, `chiMinimal2Formula`, `ExponentialC1ConvergenceWith` | partial | Minimal-model stability; exact auxiliary threshold formulas around `(2.21)`--`(2.22)`, named minimal stability-condition predicate/constructors/projections, positivity lemmas, and `χ_min → χβ` threshold projections proved; exponential constants are quantified uniformly over mass-constrained solutions. |
| Remarks 2.1--2.4 | none | remark/doc | Threshold comparisons and biological interpretation. |
| Lemma 3.1 | `Paper3.Lemma_3_1` | statement target | Uniform regularity for bounded positive global solutions. |
| Lemma 3.2 | `Paper3.Lemma_3_2` | statement target | Compactness of time translates. |
| Lemma 3.3 | `Paper3.Lemma_3_3` | statement target | Continuity with respect to initial data. |
| Lemma 3.4 | `Paper3.Lemma_3_4` | statement target | Monotonicity of upper envelope from Part I. |
| Lemma 3.5 | `Paper3.Lemma_3_5` | statement target | Eventual upper bound in minimal model. |
| Corollary 5.1 | `Paper3.Corollary_5_1` | statement target | Converts convergence plus linear stability into exponential convergence. |
| Lemma 7.1 | `Paper3.Lemma_7_1` | statement target | Neumann resolvent gradient estimate. |
| Lemma A.1 | `Paper3.Lemma_A_1` | statement target | Abstract sectorial linearized stability theorem, specialized to local exponential convergence packaging. |
| Lemmas A.2--A.5 | `Paper3.Lemma_A_2`--`Paper3.Lemma_A_5` | statement target | Appendix semigroup and embedding estimates, linked to the Part I semigroup API. |
| Lemma A.6 | `CAlphaGamma`, `PowerDifferenceInequality`, `Paper3.Lemma_A_6` | statement target | Exact paper constant `C_{α,γ}` and power-difference inequality used in Theorem 2.4; positivity and `C_{α,γ} α / γ^2 ≥ 1` under `2γ ≤ α+1` proved. |
| Lemmas A.7--A.8 | `Paper3.Lemma_A_7`, `Paper3.Lemma_A_8` | statement target | Comparison between explicit global-stability thresholds and the linear critical sensitivity. |

## Immediate proof candidates

These are small, non-PDE targets worth proving before the next analytic push:

1. Extend Paper3 Definition 2.1 around instability threshold predicates and
   local exponential stability packaging.
2. Paper1 speed/decay algebra already has `cStarLower_ge_two`,
   `kappa_pos_of_two_lt`, `kappa_lt_one_of_two_lt`,
   `kappa_add_inv_eq_of_two_lt`, and the corresponding `cStarLower` bridge
   lemmas; next additions should support `Theorem_1_1`.
3. Continue proving Paper1 Lemma 2.2/2.3: unit-parameter Lemma 2.3 and
   Lemma 2.4 are proved; general `(λ, μ)` derivative formula remains.
