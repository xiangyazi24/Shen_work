# UNDERSTANDING.md — Shen_work

## Paper 1 Theorems 1.2--1.3 statement repair (2026-07-13)

The original Section 5 proof has three independently certified statement
defects: the comparison in (5.35) has the wrong direction, (1.21) uses the
laboratory-coordinate weight although the proof works in the moving frame,
and the exponential factor following (5.35) has the wrong sign.  The faithful
global-(5.31) weight interval starts above `paper531RootMinus`, not merely
above `kappa`.  `Theorem_1_2_amended`, its bounded-solution form, and
`Theorem_1_3_amended` now expose an existential `Paper531StabilityBudget` and
use that perturbed lower root.  The uniqueness hypothesis correspondingly
requires the common wave-tail exponent to exceed the perturbed root.

`CoMovingWeightedL2Convergence.of_paper531_energy_inequality` closes the
scalar part in the native coefficient of (5.31): once the PDE calculation
gives `E' <= 2*q(eta)*E`, root-window negativity supplies the positive decay
rate internally.  The fixed-positive-time PDE calculation is now concrete:
the resolver estimates, corrected coefficients, diffusion IBP, drift
cancellation, and corrected quadratic are assembled in
`paper5WeightedEnergy_deriv_le_concrete_of_coreIntegrability`.  Weighted
`H²` integrability automatically supplies the drift product and all four
whole-line endpoint limits; they are no longer independent hypotheses.  The
remaining stability frontiers are the general-data whole-line Cauchy
construction, its positive-time weighted regularity/dominated time
differentiation, and the Step 4 spatial-modulus/left-tail producers.

The general-data Cauchy construction has now started with the actual coupled
nonlinearity, not the older logistic-only `PDE/MildSolution.lean` model.
`WholeLineCauchyLocalExistence.lean` proves on every nonnegative sup strip that
the frozen elliptic resolver gradient and the full divergence-form
chemotaxis flux are uniformly bounded and sup-Lipschitz; it also supplies the
matching logistic-source bounds.  These are the nonlinear inputs for a BUC
fixed point.  The next local-existence layer must use the Gaussian derivative
kernel directly: the existing `deriv_heatSemigroup_*` API assumes global
`L¹`, which excludes bounded nondecaying Cauchy data even though the kernel
derivative convolution is well-defined.  Its time singularity is the
integrable `1 / sqrt(t-s)` factor.

`WholeLineCauchyDuhamel.lean` now supplies that B-form layer, including joint
time-source measurability, domination by the integrable Gaussian-gradient
singularity, and the resulting `sqrt(T)` chemotaxis / `T` reaction difference
bounds.  It also repairs an important pre-existing mild-map mismatch:
`PaperOne.wholeLineHeatOp` has generator `Delta-I`, so its paired reaction
source must be `u + u(1-u^alpha) = u(2-u^alpha)`.  The older
`PaperOne.wholeLineMildMap` pairs `Delta-I` with only `u(1-u^alpha)` and hence
does not encode the stated Cauchy PDE.  New Cauchy work must use the corrected
map.

The original paper defines `C_unif^b(R)` as uniformly continuous and bounded.
The repository's historical `IsCUnifBdd` predicate currently records only
continuity and boundedness, so it is too weak for the uniform initial trace on
the whole line.  The genuine Cauchy producer must expose a faithful BUC datum
predicate instead of silently proving a false sup-norm approximate-identity
claim for arbitrary bounded continuous data.  Independently of that trajectory
space correction, `WholeLineCauchyTruncation.lean` now globalizes both coupled
nonlinearities with `clampIcc`; it provides global sup/Lipschitz estimates and
proves that the truncation disappears on `[0,M]`.

`WholeLineCauchyBUC.lean` now makes that statement correction executable.  It
defines the paper-faithful bounded-uniformly-continuous datum predicate, proves
its compatibility with the historical admissibility predicate, and realizes
BUC as a closed (hence complete) subtype of the bounded-continuous sup-norm
space.  Continuous BUC-valued trajectories on `Icc 0 T` are therefore a real
complete metric space for the forthcoming Banach contraction; their evaluation
is jointly continuous in time and space.

`WholeLineCauchyBUCSources.lean` lifts the two clamp-globalized nonlinearities
to actual self-maps into BUC.  The nontrivial spatial point is now proved:
the elliptic resolver gradient is globally Lipschitz with constant
`2*M^gamma` by its elliptic equation, and the product of bounded uniformly
continuous factors is uniformly continuous.  Thus both flux and corrected
reaction sources are legitimate elements of the complete phase space, not
merely pointwise functions with assumed regularity.

`WholeLineCauchyBUCConvolution.lean` strengthens the existing bounded-
continuous convolution engine: every continuous `L¹` kernel acts as a
Lipschitz self-map of `BUC(ℝ)`, with operator constant `∫|K|`.  The proof
uses the translated representation and the input's uniform spatial modulus,
so it applies equally to the Gaussian value and gradient kernels.  The BUC
phase space is realized as a closed real submodule, hence now carries the
complete normed-vector-space structure needed for Bochner Duhamel integrals.

`WholeLineCauchyBUCHeatContinuity.lean` closes the initial-time topology gap.
The Gaussian first absolute moment, combined with the datum's global uniform
modulus, gives convergence in the actual BUC sup norm.  After totalizing the
positive-time formula by the identity at nonpositive time, both the ordinary
heat flow and the paper's modified flow are strongly continuous at zero.  The
modified-flow proof explicitly restores the `exp (-t)` factor, rather than
silently treating the generator `Δ-I` as the ordinary heat generator.

`WholeLineCauchyBUCHeatPositiveTime.lean` supplies the complementary open-time
regularity needed by Duhamel.  Local Gaussian dominators prove `L¹` time
continuity of both the shifted value kernel and its spatial derivative.  The
kernel/input convolution estimate then yields joint strong continuity of the
value and gradient operators in positive time and in their BUC input.  Thus a
continuous BUC source trajectory produces a continuous BUC-valued Duhamel
integrand away from the terminal diagonal; no pointwise-only measurability
package is being substituted for this fact.

There is a separate fidelity defect in the older Remark 5.1/5.2 block of
`Statements.lean`: the paper fixes `sigma = 1/6` and uses real powers
`|chi|^sigma` and `|chi|^(2*sigma)`, while several repository definitions
currently encode products `|chi|*sigma` and `|chi|^2*sigma`.  Those constants
must not be reused for the corrected stability budgets until repaired.

## Paper 2 Lemma 2.6 / Corollary 2.1 statement repair (2026-07-13)

The raw `Lemma_2_6` interface in `Statements.lean` is deliberately not claimed
as a theorem.  Its whole-open-interval conclusion is false from the two stored
hypotheses alone: a positive Neumann heat flow starting from
`L^p0 \ L^p` data has the uniform seed bound and the exact power-energy
identity, but its `L^p` norm diverges as time tends to zero.  Pointwise `deriv`
data would also be insufficient without the temporal regularity supplied by a
classical solution.  This is a statement defect, not a missing Moser tactic.

The faithful positive-time replacement is
`intervalDomain_abstractLpBootstrap_terminal`.  For a concrete classical
interval solution, the existing power-energy differentiability and the proved
Agmon absorption produce a scalar linear damping inequality.  A first-crossing
argument then yields a uniform power bound on `[s,T)` for every fixed
`0 < s < T` and every finite exponent.  This is exactly what the printed
terminal `limsup` in Corollary 2.1 needs.  The public concrete close is
`intervalDomain_Corollary_2_1_terminalWindow`; it has no generic
`Lemma_2_6` package assumption and prints only the standard three axioms.

ChatGPT audit Q4708 independently confirmed the quantifier split used here:
terminal control should quantify over every positive anchor, while the stronger
whole-time statement requires a bounded initial datum plus an initial-trace
bridge.  The old conditional all-time wrapper remains only as a clearly marked
compatibility theorem; it is not used as evidence for the paper result.

## Paper 2 positive critical bootstrap frontier (2026-07-12)

Commit `28bb65b1` exposes the Q4589 two-mechanism route without conflating
their hypotheses.  `intervalDomain_signalWeightedGradientEstimate_of_classical_explicit`
is the `eta`-named form of Proposition 2.2: it assumes only `1 < q` and
`0 ≤ eta`, with no admissible-range relation between them.  The separate
critical elliptic test remains in `IntervalDomainMCriticalLpSeed` through
`elliptic_multiplier_ibp_identity_eta`, `critical_elliptic_gradient_control`,
and `exists_critical_seed_exponent`; this is where `2 * beta - 1` and the
upper seed threshold enter.

`criticalFiniteSeed_positive_intervalDomain` now transports the faithful
finite seed back to the legacy interval domain as a standalone theorem.  Its
energy proof uses the special `2 * beta - 1` elliptic weight and mass/Ehrling;
it never introduces or absorbs an `u ^ (p + gamma)` term, so it has no
additional `gamma < 2` restriction.  The later branch-specific bootstrap uses
the fixed lower-rung `L^p0` seed through
`produce_AgmonAbsorbedInterpolationBefore_of_classical`; it does not use the
false L1-mass-only or current-energy remainder criticized in Q4595.

The seed alone does not inhabit the literal `hcriticalBootstrap` type, because
that type also contains a `CrossDiffusionBootstrapEstimate` conjunct.
`criticalBootstrapFrontier_positive_intervalDomain` combines the standalone
seed with the Q4589 sharp estimate at `rho = gamma` and realizes the exact
frontier.  The positive critical headline continues to use the stronger direct
finite-power/boundedness route rather than claiming the generic
`Corollary_2_1`: that statement still depends on the generic
`Lemma_2_6 intervalDomain` interface, which is not discharged merely by this
branch instance.  The frontier, direct bounded-before theorem, and positive
critical Theorem 1.2 headline all print only
`[propext, Classical.choice, Quot.sound]`.  A clean-worktree uisai2 root build
completed successfully with 9333 jobs.

Q4596 audited an older branch and correctly identified four gaps in the
generic `Corollary_2_1`/`Proposition_2_5` route.  On current `main`, all four
are closed for the corrected positive-critical branch, but not by pretending
the generic interfaces are solved.  `criticalLpBootstrapEnergyInputs_positive_intervalDomain`
packages the sharp `rho = gamma` energy family;
`critical_integratedMoserFirstCrossingStep_positive_of_seed` exposes the
branch-specific first-crossing step from the fixed seed, bounded datum, and
initial trace.  The physical restarted-Duhamel proof in
`critical_bounded_before_positive` supplies the finite-Lp-to-Linf endpoint
without a pointwise gradient bound, and `critical_bounded_global_positive`
uses a horizon-independent global finite-power bound plus a one-unit moving
window to produce the `atTop` bound.  These direct branch theorems do not use
generic `Lemma_2_6`, generic `Proposition_2_5`, or generic
`IntegratedMoserFirstCrossingStep`.  The remaining upstream inputs of the
headline are Cauchy theory (`hlocal` and `hglobalExtension`), not boundedness.

## Task 323: Truncated positive-time bootstrap — Sobolev ladder (2026-07-08)

File: `ShenWork/Paper2/IntervalTruncatedPositiveTimeBootstrap.lean`

Goal: close the sorry `truncatedPositiveTimeSpectralData_of_existenceData` in
`IntervalTruncatedTestedSpectral.lean`, making Paper 2 Theorem 1.1 unconditional.

Architecture (validated by ChatGPT Q3942 + Q3945):

```
ball bound
  → source O(1) [Level 2: truncatedBFormSourceCoeff_bound_positive_time — DONE]
  → eigenvalue gain → H¹ [truncatedPicardCoeff_h1_positive_time]
  → source ℓ² [truncatedBFormSourceCoeff_l2_positive_time]
  → eigenvalue gain → H² (hidden stronger output)
  → gradient ℓ¹ [truncatedPicardCoeff_grad_l1_positive_time] (Cauchy-Schwarz corollary)
  → source ℓ¹ [truncatedBFormSourceCoeff_summable_positive_time] (two IBPs + H²)
  → eigenvalue gain → eigenvalue-weighted summability [truncatedPicardCoeff_eigenvalue_weighted_summable_positive_time]
```

Key infrastructure wrappers needed (from Q3945):
- `l2_source_to_H2_duhamel`: ℓ² envelope → Σ (λ_k |Duh_k|)² < ∞
- `source_l1_to_eigenvalue_weighted_duhamel`: ℓ¹ envelope → Σ λ_k |Duh_k| < ∞
- Both are thin wrappers around `eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound`

Key IBP facts:
- `kπ · sineInner(F,k) = cosCoeff(F',k)` (first IBP, uses F(0)=F(1)=0)
- `cosCoeff(F',k) = -sineCoeff(F'',k)/(kπ)` (second IBP, sin vanishes at endpoints — no F' boundary needed)
- Logistic: g = f(u), g'(0)=g'(1)=0 (Neumann), two IBPs → O(1/k²) → ℓ¹
- ChemDiv: F'' ∈ L² → sineCoeff(F'') ∈ ℓ² → divided by kπ → ℓ¹ by Cauchy-Schwarz

Level 0 (Lipschitz black box) — Q3948 architecture (validated):
- The naive "continuous → flux W^{1,1}" route is CIRCULAR (continuity alone ≠ BV/Lipschitz)
- Correct route: iterate-level positive-window Lipschitz bootstrap
  1. Operator-level IBP: B_N(t)F = S_N(t)(F') when F(0)=F(1)=0, F∈W^{1,1}
     - Endpoints: `truncatedChemFluxLifted_zero_left/right` already proved
     - This eliminates the 1/(t-s) singularity (reduces to √(t-s) integrable)
  2. Small-window contraction: G_{n+1} ≤ A_win + B_win * G_n with B_win < 1
  3. Uniform iterate Lipschitz → limit Lipschitz (by uniform convergence)
  4. Limit Lipschitz → flux W^{1,∞} → source O(1) via IBP
- Key reusable pieces: `gradDuhamel_sup_bound`, `cosineCoeffs_abs_le_of_continuous_bounded`
- NOT reusable: `TowerInputs` (has hχ0), `G1profile`/`CL` (logistic-only)

Alternative route (Q3949, deeper but heavier):
- Time-weighted H¹ Picard majorant: P_n(T) = sup_{0<t≤T} √t ‖u_n(t)‖_{H¹}
- Closure: P_{n+1}(T) ≤ C₀ + C₁T + C₂√T·P_n(T), small T makes C₂√T < 1
- ℓ² source → gradient ℓ¹ via (t-s)^{-3/4} smoothing (integrable in 1D)
- Does NOT use modewise eigenvalue gain → avoids divergent harmonic series
- Decision: stick with Q3948 Lipschitz approach for current bootstrap file;
  Q3949 route is backup if Lipschitz IBP proves too heavy in Lean

Status: 16 sorries in bootstrap, 0 in gradient window, 0 in IBP.
Previous session closed logistic source + continuousOn; this session closed:
- 3 algebraic sorries (timeDeriv summability + two tested summabilities) via Codex
- `gradDuhamel_shifted_sup_bound` in gradient window (Q3958, now 0 sorry)
- Level 0 limit passage (tendsto_nhds_limUnder + le_of_tendsto, proved inline)

Level 0 decomposed into:
1. `hiter_grad` (sorry L94): uniform iterate gradient bound from window [t/2, t]
   - Needs `TruncatedGradientWindowWiring` instantiation
   - Key missing piece: `hkernel_step` (restarted mild identity infrastructure)
   - Q3955 dispatched but git-drop FAILED; needs re-dispatch or manual proof
2. MVT (sorry L105): gradient bound → Lipschitz via Mean Value Theorem
   - Needs `HasDerivWithinAt` on Icc 0 1 for lifted iterates
   - Infrastructure exists in codebase but assembly non-trivial
3. Limit passage (PROVED): `le_of_tendsto` + `tendsto_nhds_limUnder`

All 16 sorries chain back to L94 (hiter_grad).

Q3960 insight: `negativePartTest_diff_off_countable` (Level 4b) needs STRONGER
positive-time regularity — Lipschitz alone doesn't give HasDerivAt off countable.
Need C¹ or HasDerivAt-off-countable as a new black box. May need to restructure
Level 4b sorry statements.

Role: Codex grinds the individual sorries. I organize ChatGPT answers and coordinate.

## Task 322: Conjugate B-form/logistic source `TimeC1On` producers (2026-07-07)

`IntervalConjugateBFormSourceTimeC1On.lean` adds a direct producer for the
B-form bank's `hsrcBDirect` shape.  It instantiates the existing generic
`ChemDivSolutionRegularityResidual` chain at
`conjugatePicardLimit p u₀ T`, producing the chem-div source
`DuhamelSourceTimeC1On`, then combines it with a carried logistic source
`DuhamelSourceTimeC1On` via `bFormSource_duhamelSourceTimeC1On`.

`IntervalConjugateLogisticLimitSourceTimeC1On.lean` adds the corresponding
limit-passage producer for the logistic half:
`conjLogSourceTimeC1On_limit_of_uniformLimit` applies the committed
`duhamelSourceTimeC1On_of_uniform_limit` theorem to conjugate Picard iterates on
an arbitrary closed window `[lo, hi]`, consuming iterate source packages,
coefficient convergence, derivative uniform convergence, and common summable
source/derivative bounds.

This is not a headline wrapper.  It lowers `hsrcBDirect` to real analytic
frontiers: the conjugate-iterate logistic source tower/uniform-limit data plus
the chem-div regularity residual for the same trajectory.  Q3797 also flagged a
remaining endpoint issue for the canonical window `[0, T]`: since
`conjugatePicardLimit` is defined to be zero at time `0`, using the theorem at
`lo = 0` needs a separate endpoint-compatibility argument.

## Task 321: B-form bank `Hinf` producer (2026-07-07)

`IntervalBFormBankHinfProducer.lean` closes the B-form bank's `Hinf` field from
`ConjugateMildExistenceData`.  It packages the existing
`IntervalBankInfAndLogSrcWiring` iterate bounds/integrability leaves into
`conjugatePicardInfThresholdData_of_picard_bounds`, exposing
`Hinf_of_conjugateMildExistenceData`.

This is a real bank-field producer: it does not touch `hsrcBDirect`,
`hchemIoo`, or any classical-solution output.

## Task 320: Direct On conjugate/B-form `hpde_u` provider (2026-07-07)

`IntervalConjugatePdeUProviderOn.lean` composes the Task319 bank-shaped
`hB_global` producer with Task317's window-local general-chi `hpde_u` producer.
The new direct theorem
`hpde_u_of_conjugatePicardLimit_open_sourceBridgeRepresentativeSubtypeLogisticDataOn`
consumes `DuhamelSourceTimeC1On (bFormSourceCoeffs ...) 0 T` and
`Continuous u₀`, instead of the old global source package and false continuity
of `intervalDomainLift u₀`.

This is still conditional on the real source-bridge side data, logistic/chem
Fourier packages, and especially a producer for the bank's `hsrcBDirect`; it is
not a headline alias.

## Task 319: Bank-shaped B-form global cosine producer (2026-07-07)

`IntervalSourceBridgeOpenRepresentativeOn.lean` adds the core On/constant-init
B-form global cosine route recommended by Q3794.  The new theorem
`intervalConjugateDuhamelMap_cosineSeries_on_constInit` is a genuine proof
variant of the existing conjugate cosine-series assembly: the homogeneous leg
uses the subtype-continuity spectral adapter, and the Duhamel leg uses
`duhamelSpectral_eq_cosineSeries_on` from a `DuhamelSourceTimeC1On` package on
`[0,T]`.

The public producer
`conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticDataOn`
now gives the bank-shaped `hB_global` field from `Continuous u₀` and windowed
B-form source regularity, rather than the old global `DuhamelSourceTimeC1` plus
false `Continuous (intervalDomainLift u₀)` assumption.  This still leaves the
real source-regularity and chem-div representative producers open.

## Task 318: Public restart-coefficient summability producer (2026-07-07)

`IntervalBFormRestartCoeffSummability.lean` extracts the absolute summability of
restart coefficients from bounded initial cosine coefficients plus source
time-regularity.  The main theorem
`localRestartCoeff_abs_summable_of_sourceC1On` is the window-local form; the file
also exposes global and conjugate-Picard B-form corollaries.  This proof is
upstream of the PDE identity: it uses only the homogeneous heat trace summability,
the `DuhamelSourceTimeC1On` envelope, and the triangle inequality.

`IntervalConjugatePdeUProvider.lean` no longer carries
`hB_global_summable` as an external hypothesis.  Its direct conjugate/B-form
`hpde_u` theorem derives that summability internally from the already-assumed
global B-form source `DuhamelSourceTimeC1` and the initial coefficient bound.
This reduces a visible Task316 analytic premise; it does not close the remaining
source/time-C1, source-bridge side-condition, or Fourier-package producers.

## Task 317: Windowed B-form source `hpde_u` producer (2026-07-07)

`IntervalDomainPdeUGeneralChiProviderOn.lean` adds the window-local analogue of
Task311's global B-form source producer:
`Hsource_of_bForm_global_generalChiOn` and
`hpde_u_of_bForm_global_generalChiOn`.  The input source regularity is now
`DuhamelSourceTimeC1On aB 0 T`, matching the banked B-form route, rather than a
global `DuhamelSourceTimeC1 aB`.

The proof derives the missing restart summability from the homogeneous
eigenvalue estimate plus
`duhamelSpectralCoeff_eigenvalue_summable_on`, extracts the restart base
coefficients from the global B-form cosine representation, and shifts the
windowed source package from `[0,T]` to the half-step restart window
`[0,T - t0/2]`.  It then feeds the existing
`hpde_u_of_generalChi_sourceSpectralDataOn` consumer.  This is a genuine input
lowering for Task316/Task311 surfaces, not a headline theorem and not a route
through `GradientMildSolutionData`, `hgradB`, `IsPaper2ClassicalSolution`, or
regularity bootstrap.

## Task 316: Direct conjugate/B-form `hpde_u` provider (2026-07-07)

Q3792 audited the formulation itself: the old `IntervalGradientDuhamelMap`
operator is not the Neumann divergence-source mild formulation for the PDE
source `-χ ∂x Q`.  On the interval, `∂x K_N` and `-∂y K_N` are different kernel
directions, so the correct PDE route should use
`IntervalConjugateDuhamelMap.IntervalConjugateMildSolution` and the B-form
source representation, not a conversion through `GradientMildSolutionData` or
`hgradB`.

`IntervalConjugatePdeUProvider.lean` adds
`hpde_u_of_conjugatePicardLimit_open_sourceBridgeRepresentativeSubtypeLogisticData`.
It composes Task313's endpoint-safe conjugate Picard `hB_global` producer with
Task311's `hpde_u_of_bForm_global_generalChi` consumer.  The source split for
`bFormSourceCoeffs` is definitional; the proof carries the same explicit
source/time-C1, summability, integrability, and Fourier-data hypotheses as the
two honest upstream producers.  This is a core PDE provider for the conjugate
Picard/B-form route, not another headline alias and not an unconditional final
theorem.

## Task 315: Integrated Ktilde identity for gradient mild data (2026-07-06)

`IntervalGradientKtildeDuhamel.lean` adds the positive replacement for the false
`hgradB` route:
`gradientDuhamel_deriv_integral_eq_ktilde_source_integral_of_gradientMildRegularity`.
For `GradientMildSolutionData` plus
`intervalDomainClassicalRegularity D.T D.u (coupledChemicalConcentration p D.u)`,
it integrates the open source-IBP theorem and proves that the gradient Neumann
Duhamel leg equals the Ktilde source-derivative integral.  The proof uses the
existing mild-regularity flux derivative producer and the endpoint-insensitive
continuous representative for `coupledChemDivSourceLift`; no `hpde_u`,
`IsPaper2ClassicalSolution`, or B-kernel conversion is used.

This is still a value/kernel identity, not a local cosine restart package for
`hpde_u_of_generalChi_sourceSpectralDataOn`.  The remaining design problem is
how to connect the mixed sine/cosine source representation from Tasks297-310 to
the PDE producer without reintroducing the false B-kernel bridge.

## Task 314: `hgradB` endpoint obstruction (2026-07-06)

Q3790 audited the exposed `hgradB` input in
`IntervalGradientBFormGlobalCosine.gradientMildSolution_bForm_global_cosine_of_gradB_sourceBridge`
and found it is the wrong operator identity, not just an unproved lemma.  The
gradient mild chemotaxis leg gives the open-kernel/Ktilde source identity
`deriv S_N Q = -∫ Q' Ktilde`; it is not the B-kernel operator
`intervalConjugateKernelOperator` applied to `Q`.

`IntervalGradientBFormGlobalCosineObstruction.lean` records the concrete Lean
consequence: any proof of the current `hgradB` shape would force the B-kernel
Duhamel leg to vanish at both Neumann endpoints.  The gradient side vanishes at
`x = 0,1` by `intervalFullSemigroupOperator_deriv_at_zero_eq_zero` and
`intervalFullSemigroupOperator_deriv_at_one_eq_zero`; the B-kernel side is not
expected to vanish for a general source.  This file is a route-pruning result:
future core work should use the mixed sine/cosine Ktilde source route from
Tasks297-310, not try to discharge `hgradB`.

## Task 313: Subtype-logistic B-kernel source bridge (2026-07-06)

Q3789 pointed out that Task312 only removed the false endpoint-continuity
assumption for `coupledChemDivSourceLift`; the old bridge still asked for
`Continuous (logisticLifted p (u s))`, which is the same zero-extension
continuity hazard for positive endpoint data.  `IntervalSourceBridgeOpenRepresentative`
now also exposes `source_bridge_slice_open_representative_subtypeLogistic` and
`conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticData`.
These use `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont`,
so the logistic leg only requires
`Continuous (intervalLogisticSource p (u s))` on the interval-domain subtype,
while the cosine coefficient bound remains stated for `logisticLifted`.

The older Task312 theorem is left in place as a compatibility API.  The
subtype-logistic version is the paper-faithful endpoint-safe producer to use
for the B-form `hB_global` route.

## Task 312: Endpoint-insensitive B-kernel source bridge (2026-07-06)

`IntervalSourceBridgeOpenRepresentative.lean` removes the remaining false
closed-endpoint source-continuity input from the B-kernel source bridge.  The
new normalized IBP theorem
`cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff_open_integrable` only requires the
derivative representative to be interval-integrable on `[0,1]`.  This lets
`divMode_of_sliceC1_open_representative` prove the divergence-mode identity from
a continuous-on-`Icc` representative that agrees with the literal
`coupledChemDivSourceLift` only on the open interior, using the endpoint-blind
`BankChemSliceFix.cosineCoeffs_congr_on_Ioo`.

The file then exposes `source_bridge_slice_open_representative` and
`conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeData`.  These
are the B-kernel analogues of the Task309/310 representative route: they still
carry honest flux/logistic continuity, coefficient bounds, integrability, and
within-interior derivative data, but they no longer ask for
`Continuous (coupledChemDivSourceLift ...)` on the zero extension.  This is a
core producer toward the Task311 global B-form `Hsource` route, not a headline
alias.

## Task 311: General-chi `hpde_u` source producers (2026-07-06)

`IntervalDomainPdeUGeneralChiProvider.lean` adds
`ShenWork.IntervalDomainPdeUGeneralChi.Hsource_of_bForm_global_generalChi`.
It turns global B-form cosine representation/source/Fourier data into the exact
`Hsource` tuple consumed by
`hpde_u_of_generalChi_sourceSpectralData`, using the restart identity
`bForm_restart_of_global_cosine`, coefficient extraction at `t / 2`, the
global source shift `DuhamelSourceTimeC1.shift_nonneg`, and the endpoint-safe
`ChemDivCosineFourierDataIoo` package.  This producer is upstream of
classical-solution packages: it does not consume `hpde_u`,
`IsPaper2ClassicalSolution`, or regularity bootstrap data.  The same file also
exposes the direct consumer `hpde_u_of_bForm_global_generalChi`.

`IntervalDomainPdeUGeneralChiOn.lean` adds
`ShenWork.IntervalDomainPdeUGeneralChi.hpde_u_of_generalChi_sourceSpectralDataOn`,
the `DuhamelSourceTimeC1On` analogue of the existing general-chi PDE producer
`hpde_u_of_generalChi_sourceSpectralData`.  The new core producer keeps the same
Fourier/logistic/chem-div data at the target time, but it only asks the restart
source coefficients to be `C¹` on a window `[0,W]` containing `t - offset`.
This matches the B-form banked route, whose canonical source regularity is
window-local rather than global, and removes the artificial mismatch between
B-form source data and the general-chi `hpde_u` interface.

`IntervalBFormSpectralProviderDischargeOn.lean` now exposes
`ShenWork.IntervalConjugatePicard.timeDeriv_eq_of_rep_on_public`, a public
wrapper around the already-proved private windowed restart time-derivative
calculation.  No headline alias is claimed here: the remaining work is to
produce either the global B-form data required by
`Hsource_of_bForm_global_generalChi`, or the window-local `Hsource` package
required by `hpde_u_of_generalChi_sourceSpectralDataOn`, from the
B-form/gradient-source route without circularly using a classical PDE package.

## Task 310: Gradient bridge representative for source integration (2026-07-06)

`IntervalGradientSourceBridgeRegularityRepresentative.lean` identifies the
chemotaxis-divergence source representative used by the gradient source bridge.
For a mild-regular solution, the file proves that
`coupledChemDivSourceLift p u` agrees on interior times and points with
`gradientBridgeChemDivWithinRep p u`, and that this representative is
continuous on compact space-time rectangles through the existing
`intervalDomainChemotaxisDiv_continuousOn_Icc_of_mildRegularity` regularity
theorem.

The file also adds
`ShenWork.IntervalMildToLocalExistence.gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData_and_regular`.
This rewrites `gradientMildDuhamelTerms` to the integral of the mixed
logistic-minus-chemotaxis spectral source under the existing
`GradientMildSolutionData` assumptions plus mild regularity.  It is a producer
step toward the B-form/gradient route, not a headline theorem: the remaining
hard work is still to turn these source representatives into the full B-form
source package needed by the negative-chi local existence branch.

## Task 288: Chi-nonpositive B-form headline alias (2026-07-06)

`IntervalDomainChiNonposHeadline.lean` now exposes
`paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_picardLimitFrontier_BForm`.
The zero branch is unconditional; the strict-negative branch consumes only the
Picard-limit restart frontier and weak-positive B-form seed after `p.χ₀ < 0`
has been selected.  The negative branch routes through the committed
`ChiNegResidual.theorem_1_1_intervalDomain_chiNeg_of_picardLimitFrontier_BForm`
bridge from Task285, where the boundary-window min-persistence input is
supplied internally by the chi-nonpositive boundary limit bridge.  This is a
public conditional route surface, not an unconditional chi-negative theorem.

## Task 284: Chi-nonpositive reduced-core-data headline alias (2026-07-06)

`IntervalDomainChiNonposHeadline.lean` now also exposes
`paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_reducedCoreData`.
The zero branch remains the unconditional chi-zero theorem; the strict-negative
branch calls the landed
`ChiNegResidual.theorem_1_1_intervalDomain_chiNeg_of_reducedCoreData`, which
pushes the primitive local-existence residual through resolver estimates plus
`CoupledDuhamelReducedClassicalCore` data.  This is a real narrowing of the
route-facing negative hypothesis, but it is still conditional on supplying
`CoupledFluxResolverReducedCoreData` whenever the strict-negative branch is
entered.

## Task 283: Paper2 chi-nonpositive public headline aliases (2026-07-06)

`IntervalDomainChiNonposHeadline.lean` exposes three public statement-layer
entry points for the current interval-domain chi-nonpositive strict-logistic
theorem surface.  The preferred PDE-level alias consumes only the strict-negative
branch residual
`ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual`; the second exposes
the PPID-typed faithful EWA frontier from Task279; the third exposes the
EWA-free `ChiNegDatumUniformCore` abstract-core split.  In all three aliases the
zero branch is the already unconditional chi-zero theorem, while the
strict-negative branch remains conditional.  This is route exposure, not an
unconditional chi-negative proof.

## Task 282: Chi-nonpositive split via primitive local existence (2026-07-06)

`IntervalDomainTheorem11ChiNonposLocalExistenceSplit.lean` adds the
chi-nonpositive split whose strict-negative branch carries
`ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual`.  This is currently
the most direct PDE-level residual for the negative branch because it avoids the
known all-PPID uniform-floor/Wiener dead routes.  The theorem is still
conditional on producing that local-existence factory whenever `p.χ₀ < 0`; it
does not close the negative branch by itself.

## Task 280: Paper2 top-level chi-zero strict-logistic alias (2026-07-06)

`IntervalDomainChiZeroHeadline.lean` now also exposes
`paper2_theorem_1_1_intervalDomain_chiZero_strictLogistic` directly under the
main `ShenWork.Paper2` namespace.  It is a public statement-layer alias to the
Task277 cone/tower headline, not a new proof route.  The scope remains the
chi-zero interval-domain strict-logistic fragment with `0 < p.a`, `0 < p.b`,
`1 ≤ p.α`, and `1 ≤ p.γ`; it does not claim the general chi-nonpositive theorem
or degenerate logistic parameters.

## Task 279: Chi-nonpositive split via faithful negative frontier (2026-07-06)

`IntervalDomainTheorem11ChiNonposFaithfulSplit.lean` exposes a general
chi-nonpositive interval-domain wrapper whose zero branch uses the proved
`intervalDomain_theorem_1_1_chiZero_unconditional` theorem and whose
strict-negative branch carries only the PPID-typed faithful realization frontier
`ChiNegStrongFaithfulRealizationFrontier`.  This is a route-facing narrowing of
the negative residual from the stronger datum-uniform construction to the
faithful no-`hfp` realization carrier.  It is still conditional on the
strict-negative frontier; it does not prove the negative branch unconditionally.

## Task 277: Route-facing chi-zero headline alias (2026-07-06)

`IntervalDomainChiZeroHeadline.lean` exposes
`paper2_theorem_1_1_chiZero_headline` as the preferred Paper2-facing entry point
for the current chi-zero interval-domain theorem.  The proof is a thin alias to
`IntervalPicardTowerSupply.from_cone_construction`, so it uses the tower/cone
route rather than the old ledger-level or source-spectral surfaces.  This is
still the chi-zero interval-domain fragment under the structural assumptions
`0 < p.a`, `0 < p.b`, `1 ≤ p.α`, and `1 ≤ p.γ`; it is not the general
nonpositive-chi or arbitrary-domain theorem.

## Task 276: Chi-zero hsrc0 fed directly from the narrowed Hres core (2026-07-06)

`IntervalResolverSourceWindowHsrc0FromCore.lean` bridges the existing
`HresWiring.PicardIterateResidualCore` plus the per-iterate coefficient
time-continuity provider into the Task270 hsrc0-only surface by directly reusing
`HresWiring.duhamelSourceBddOn_of_core`.  This avoids duplicating the
field-by-field bootstrap reconstruction: the core's per-window K2 data, Picard
facts, slice continuity, and tower-style `hiter_cont` input are consumed once by
the existing Hres producer, and the result is packaged as
`ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs`.

`IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointHsrc0InputsFrontier.lean`
now adds source and iterate Hres-core/no-Hu surfaces.  These route through the
new direct bridge into the hsrc0/no-Hu frontier and then into the chi-zero
headline wrappers.  This makes the hsrc0/no-Hu frontier consumable directly from
the narrowed core provider (`hFacts`, `hcont_iter`, `Wdata`, and `hiter_cont`)
without carrying Hu or a prebuilt hsrc0 package as explicit sibling fields.

## Task 274: Chi-zero hsrc0 produced from iterate bootstrap inputs (2026-07-06)

`IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs.lean` now exposes
`ResolverSourceWindowHsrc0BootstrapInputs`, a thin interface around the
non-circular iterate-side producer
`IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates`.  The package
carries the per-window iterate coefficient envelope, pointwise iterate-to-limit
source coefficient convergence, and patched-source coefficient time continuity;
the datum-side source bound is derived from `PositiveInitialDatum` through
`IntervalPicardLimitBddHcontP.datum_source_coeff_bound`.  The adapter
`resolverSourceWindowHsrc0Inputs_of_bootstrapInputs` turns those inputs into the
Task270 hsrc0-only resolver-source package, and a convenience adapter feeds the
existing envelope/no-joint package.

`IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointHsrc0InputsFrontier.lean`
adds source and iterate bootstrap/no-Hu surfaces.  These no longer carry the
full-horizon hsrc0 package or the u-side Hu package as explicit sibling fields:
the hsrc0 package is produced from bootstrap inputs, and Hu is reconstructed by
Task273 before routing into the existing chi-zero headline wrappers.  The route
remains conditional on the bootstrap analytic inputs and the pointwise PDE
identity; it is not yet an unconditional theorem.

## Task 273: Chi-zero hsrc0-only route no longer carries Hu separately (2026-07-06)

`IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs.lean` now proves
`timeNeighborhoodSpectralAgreement_of_hsrc0Inputs`: in the `χ₀ = 0` branch, the
same full-horizon bounded patched-source package `hsrc0` reconstructs the
u-side `HasTimeNeighborhoodSpectralAgreement`.  The proof reuses Task270 to get
the canonical `limitCoeff` representation and compact eigenvalue envelope,
derives singleton-window summability and spatial K2 bounds from that envelope,
then feeds the existing `ResolverSpectralAgreementFromK1` producer and converts
the resulting resolver spectral agreement to the time-neighborhood form.

`IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointHsrc0InputsFrontier.lean`
adds source and iterate no-Hu surfaces.  These carry only the source/iterate
package, the hsrc0-only resolver-source input, and the pointwise PDE identity;
the u-side spectral agreement is derived by the new adapter before routing into
the existing hsrc0 headline wrappers.  This is a genuine removal of the sibling
Hu field from the chi-zero hsrc0 route, but the route is still conditional on
per-datum source or iterate data, the PDE identity, and the explicit full-horizon
`hsrc0` package.

## Task 270: Chi-zero hsrc0-only resolver-source inputs (2026-07-06)

`IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs.lean` implements the
Q3723 reduction for the `χ₀ = 0` route.  The new
`ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs` package carries only the
bounded patched-source package
`DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T`.  Its adapter chooses the
canonical Picard-limit coefficient family
`limitCoeff p u₀ D.u`, derives agreement with `D.u` from
`TimeNhdSubtype.limit_lift_eq_cosineSeries_of_subtypeCont_patched`, and derives
compact-window eigenvalue envelopes from
`BddAdapterPatched.eigenvalue_mul_abs_limitCoeff_le_uniform_patched` plus
`windowEigEnv_summable`.  The resulting no-K1 surface is then fed through
Task269 to recover the power-source K1 fields.

`IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointHsrc0InputsFrontier.lean`
routes this hsrc0-only surface through the source and iterate chi-zero headline
wrappers.  This is still not an unconditional headline theorem: the route
remains conditional on per-datum source or iterate data, u-side spectral
agreement, the pointwise PDE identity, and the explicit full-horizon `hsrc0`
package.  Q3723 also confirms that the full horizon `D.T` matters; a shorter
bounded-source package would not fill all interior times.

## Task 269: Chi-zero no-K1 resolver-source envelope surface (2026-07-06)

`IntervalResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs.lean` removes the
explicit power-source K1 fields from the `χ₀ = 0` resolver-source envelope
surface.  The new
`ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs` package carries only the
chosen coefficients `bc`, their agreement with the lifted solution, the
compact-window eigenvalue envelope, and the explicit bounded patched-source
package
`DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T`.  In the adapter
`resolverSourceWindowEnvelopeOnlyNoJointInputs_of_envelopeOnlyNoJointNoK1Inputs`,
the missing power-source K1 fields are filled by the existing
`ResolverPowerK1.powerK1_quadruple_of_subtypeCont`.  The required pointwise
positivity, upper bound, fixed-point identity, K2 bounds, and const-extend
continuity are derived from `D`, the singleton-envelope summability/K2
reducers, and `ConstExtendAdapter`; the initial Fourier bound is derived from
`PositiveInitialDatum`.

`IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointNoK1InputsFrontier.lean`
routes this surface through the `χ₀ = 0` window and iterate headline wrappers.
This is deliberately not exposed as a general `χ₀ ≤ 0` PPID wrapper: the K1
producer consumes `p.χ₀ = 0`.  It is also still conditional on the explicit
`hsrc0` package; Q3721 confirms that neither `GradientMildHalfStepLogisticSourceData`,
`HasTimeNeighborhoodSpectralAgreement`, nor `D.u = picardLimit p u₀ D.T` alone
produces `hsrc0`.

## Task 268: Envelope/no-joint inputs combine two redundant-field reductions (2026-07-06)

`IntervalResolverSourceWindowEnvelopeOnlyNoJointInputs.lean` combines the
no-`hbsum` envelope interface with the no-`hliftCont` source interface.  The new
`ResolverSourceWindowEnvelopeOnlyNoJointInputs` package carries the coefficient
agreement, compact-window envelope, and power-source K1 data, but neither
per-time eigenvalue summability nor lifted joint continuity.  The former is
recovered by `hbsum_of_envelope` on singleton time windows; the latter is
recovered from the already-carried u-side
`HasTimeNeighborhoodSpectralAgreement` via
`RegularityFrontierAssembly.jointSolutionClosed_u_of_spectralAgreement`.

`IntervalDomainPPIDResolverSourceEnvelopeOnlyNoJointInputsFrontier.lean` and
`IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointInputsFrontier.lean` route
this thinner surface through the PPID and `χ₀ = 0` wrappers.  The remaining
conditional producer frontier is now concentrated in faithful non-`χ₀ = 0`
coefficient/agreement data, compact-window eigenvalue envelopes, and the
power-source K1 time-regularity package.

## Task 265: Envelope-only inputs derive eigenvalue summability (2026-07-06)

`IntervalResolverSourceWindowEnvelopeOnlyInputs.lean` removes the redundant
per-time `hbsum` field from the Task264 envelope surface.  The theorem
`hbsum_of_envelope` applies the compact-window envelope to the singleton time
window `[σ, σ]` and uses nonnegative summability comparison to recover
`Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)`.  The adapter
`resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs` feeds the result
back into the Task264 envelope input package, so all spatial K2 and downstream
resolver-source machinery is reused unchanged.

`IntervalDomainPPIDResolverSourceEnvelopeOnlyInputsFrontier.lean` and
`IntervalDomainChiZeroResolverSourceEnvelopeOnlyInputsFrontier.lean` expose the
same PPID and `χ₀ = 0` wrappers on this stricter no-`hbsum` input surface.  This
is still conditional: it removes only a redundant summability field, while the
real producer work remains faithful non-`χ₀ = 0` coefficients/agreement,
compact-window envelopes, joint lift continuity, and power-source K1
time-regularity.

## Task 264: Resolver-source spatial K2 reduced to coefficient envelopes (2026-07-06)

`IntervalResolverSourceWindowEnvelopeInputs.lean` implements the Q3713
reduction.  The new `ResolverSourceWindowEnvelopeInputs` package replaces the
joint-input fields `hG1` and `hG2` by one compact-window eigenvalue envelope
for the chosen coefficients `bc`: a nonnegative summable sequence `E` with
`unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n` uniformly over the window.
Theorems `hG1_of_envelope` and `hG2_of_envelope` use the existing generic
`CompactSliceGradientBounds.grad_series_abs_le` and `grad2_series_abs_le`
helpers, plus the cosine-series derivative transfer and endpoint junk-derivative
lemmas, to manufacture the K2 bounds consumed by Task259.

`IntervalDomainPPIDResolverSourceEnvelopeInputsFrontier.lean` and
`IntervalDomainChiZeroResolverSourceEnvelopeInputsFrontier.lean` wire this
envelope surface into the PPID and `χ₀ = 0` headline wrappers.  This is still a
conditional interface reduction: the real producer work is now concentrated in
faithful representation/eigenvalue-envelope data, joint lift continuity, and
power-source K1 time-regularity.

## Task 263: Chi-zero headline wrappers from joint resolver-source inputs (2026-07-06)

`IntervalDomainChiZeroResolverSourceJointInputsFrontier.lean` adds the
`χ₀ = 0` headline wrappers for the Task259 joint-continuity resolver-source
input surface.  This is wiring only: it routes the chi-zero headline through
the existing primitive-input chi-zero wrapper after converting joint inputs to
Task255 inputs.  It does not add a new producer for the remaining
representation/envelope, spatial K2, or power-source K1 residuals.

## Task 259: PPID resolver-source easy fields reduced to joint continuity (2026-07-06)

`IntervalResolverSourceWindowJointInputs.lean` implements the stricter Q3711
reduction.  The new `ResolverSourceWindowJointInputs` package removes
`hpos`, `Msup`/`hub`, and `hlower` from the Task255 primitive input ledger.
Pointwise positivity is projected from `GradientMildSolutionData.hpos`, the
upper bound from `GradientMildSolutionData.hbound` with `Msup := D.M`, and
the compact lower bound from a joint-continuity input for
`(σ,x) ↦ intervalDomainLift (D.u σ) x` on `(0,D.T) × [0,1]` plus compact
minimization on `[a,b] × [0,1]`.  Thus positivity/upper/lower fields are no
longer opaque resolver-source residuals.

`IntervalDomainPPIDResolverSourceJointInputsFrontier.lean` wires the joint
input package into the PPID source and iterate-source frontier surfaces, then
exposes the corresponding `χ₀ ≤ 0` and `χ₀ < 0` Theorem 1.1 wrappers.  This
still carries the u-side time-neighborhood spectral agreement and `hpde_u`
as sibling fields for the downstream restart/classical route, but they are no
longer used to manufacture the resolver-source lower-bound field.  The
remaining real resolver-source producer frontier is now sharper: faithful
non-`χ₀ = 0` representation/envelope for `D.u`, spatial K2 bounds from that
envelope, and power-source K1 time-regularity.

## Task 257: PPID resolver-source lower bound discharged from u-side spectral continuity (2026-07-06)

`IntervalResolverSourceWindowInputsNoLower.lean` removes the compact
positive lower-bound field from the Task255 resolver-source primitive input
package.  The new `ResolverSourceWindowInputsNoLower` still carries the
global cosine representation, pointwise positivity, compact upper and spatial
K2 bounds, and power-source K1 coefficient time-regularity, but not
`hlower`.  The theorem `compactLower_of_timeNeighborhoodSpectral` derives
that lower bound from `HasTimeNeighborhoodSpectralAgreement D.T D.u` by using
the existing joint continuity theorem
`mildSolution_jointContinuousOn_closed` on `[a,b] × [0,1]`, compact
minimization, and the carried pointwise positivity.

`IntervalDomainPPIDResolverSourceInputsNoLowerFrontier.lean` wires this
no-lower input package into the PPID restart route for both source-data and
iterate-data surfaces, then exposes the corresponding `χ₀ ≤ 0` and `χ₀ < 0`
Theorem 1.1 wrappers.  This is a residual reduction, not a new unconditional
headline theorem: the route still assumes the u-side time-neighborhood
spectral agreement, `hpde_u`, and the remaining resolver-source primitive
fields.  ChatGPT Q3711 independently audits Task255 in the same direction:
`hpos`, compact upper bounds, and compact lower bounds are not the true
non-`χ₀ = 0` analytic frontier; the hard residue is the faithful non-`χ₀`
representation/envelope, spatial K2 from that envelope, and power-source K1
time-regularity.

## Task 255: PPID resolver-source window data lowered to primitive inputs (2026-07-06)

`IntervalResolverSourceWindowInputs.lean` implements the Q3706 generic
reduction.  The new `ResolverSourceWindowInputs` package is a producer-side
ledger for one global cosine representation of `D.u`, pointwise positivity,
compact positive lower bounds, compact upper and spatial K2 bounds, and
power-source K1 coefficient time-regularity for
`ν * intervalDomainLift (D.u σ) ^ γ`.  The theorem
`resolverSourceWindowData_of_inputs` fixes the standard clamp window around
each interior time and uses the already-proved
`ResolverPowerDecay.powerSource_window_uniform_decay` to manufacture the
per-window decay constant required by Task246's `ResolverSourceWindowData`.
Thus the remaining source residual is now the primitive representation,
lower-bound/K2, and power-K1 ledger, not the clamped existential window shape.

`IntervalDomainPPIDResolverSourceInputsFrontier.lean` wires this primitive
input package into the PPID restart route.  It exposes
`PerDatumWindowInputsSourceSpectralFrontier` and the iterate variant, then
reduces their chi-nonpositive and strict-negative Theorem 1.1 wrappers to the
Task246/250 window-source frontier.  This is still a conditional reduction:
Q3706 confirms that the non-`χ₀ = 0` producer for the primitive input fields is
the real analytic frontier, and that downstream objects such as
`GradientMildClassicalFrontierCoreData`, `IsPaper2ClassicalSolution`, `hpde_u`,
or u-side time-neighborhood spectral agreement should not be used circularly to
produce these resolver-source inputs.

## Task 250: PPID resolver-source decay lowered to spatial K2 data (2026-07-06)

`IntervalResolverSourceWindowDecayFrontier.lean` lowers the
`ResolverSourceWindowData` residual one step further on the decay side.  Its
new `ResolverSourceWindowSpatialK1Data` keeps the window cosine
representation, a positive lower bound, an upper bound, spatial G1/G2 bounds,
and the power-source K1 time-derivative data, but no longer carries the
quadratic decay constant for `ν * u^γ` as an input.  The theorem
`windowData_of_spatialK1Data` produces that constant through the already-proved
`ResolverPowerDecay.powerSource_window_uniform_decay`, so this is a genuine
reduction of the resolver-source decay subfield.  The power-source K1
time-derivative package remains an explicit residual.

`IntervalDomainPPIDResolverSourceDecayFrontier.lean` wires this lowered
resolver-source package into the PPID restart-core route.  It exposes
`PerDatumSpatialK1SourceSpectralFrontier` and
`PerDatumIterateSpatialK1SourceSpectralFrontier`, plus chi-nonpositive and
strict-negative PPID Theorem 1.1 wrappers from those surfaces.  This still does
not solve `PicardIterateConvergenceData`, `Hu`, or `hpde_u`; it only removes
the explicit power-source decay fields from Task246's `ResolverSourceWindowData`
surface.

## Task 246: PPID resolver-source witness lowered to window data (2026-07-06)

`IntervalResolverSourceWitnessFrontier.lean` factors out the smallest current
general PPID residual identified by Q3704: the per-time clamped resolver-source
witness.  It defines `ResolverSourceWitness` (the raw witness consumed by
`RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0`)
and the producer-facing `ResolverSourceWindowData`, consisting of local
power-source cosine representation, positivity, quadratic decay, and K1
time-derivative data on a window around each interior time.  The theorem
`resolverSourceWitness_of_windowData` feeds that window data through the
existing soft-clamped resolver-source producer in
`IntervalResolverSourceClampedWitness`, and
`resolverDirectSpectralData_of_windowData` packages it as resolver direct
spectral data.

`IntervalDomainPPIDResolverSourceFrontier.lean` then replaces the raw
resolver-source witness in the PPID source frontier by
`ResolverSourceWindowData`.  It exposes
`PerDatumWindowSourceSpectralFrontier` and
`PerDatumIterateWindowSourceSpectralFrontier`, plus chi-nonpositive and
strict-negative PPID Theorem 1.1 wrappers from these lowered surfaces.  This is
a real residual reduction for the resolver-source field only.  It does not
claim to produce `PicardIterateConvergenceData`,
`HasTimeNeighborhoodSpectralAgreement D.T D.u`, or the pointwise `hpde_u`
identity; Q3704 flags those as larger or route-specific producer tasks.

## Task 245: PPID frontier surface trimmed to consumed restart/core fields (2026-07-06)

`IntervalDomainPPIDRestartCoreFrontier.lean` records smaller per-datum spectral
packages actually consumed by the PPID Picard-limit frontier bridge.  The core
package contains `GradientMildHalfStepLogisticSourceData`, u-side
time-neighborhood spectral agreement, resolver direct spectral data, and the
pointwise PDE identity.  It intentionally omits the sup-norm derivative and
initial-approach fields from `EndToEnd.PerDatumSpectralFrontier`, because those
fields are not used to produce `ConeQuantBridge.PicardLimitRestartFrontier` in
this PPID route.  It also omits resolver strict positivity, which is produced
internally by `IntervalResolverStrictPositivity.mildChemicalConcentration_pos`.

The same file also exposes a source-witness package, replacing resolver direct
spectral data by the per-time clamped resolver-source witness consumed by
`RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0`.
Finally, it exposes an iterate/source package in which the logistic half-step
source data field is produced internally from
`IntervalPicardLimitLogisticSource.PicardIterateConvergenceData`.

The resulting chi-nonpositive and strict-negative PPID Theorem 1.1 wrappers are
conditional on regime assumptions plus this smaller
`PerDatumRestartCoreSpectralFrontier` producer, or the still-smaller
`PerDatumSourceSpectralFrontier` / `PerDatumIterateSourceSpectralFrontier`
producers.  The next analytic task should target one or more of those consumed
fields, rather than the omitted fields.

## Task 244: PPID headline reduced to unified/spectral Picard frontier (2026-07-06)

`IntervalDomainPPIDPicardLimitFrontier.lean` adds the current thinnest PPID
wrappers for the chi-nonpositive and strict-negative Theorem 1.1 route.
After Task243 discharged `ClassicalMinPersistence`, the remaining input was
the threshold-route `ThresholdQuantBridge.PicardRestartFrontier p`.  Task244
first replaces that input by the unified
`ConeQuantBridge.PicardLimitRestartFrontier p`, using the existing
`picardRestartFrontier_of_picardLimitFrontier` bridge.  It then adds spectral
frontier wrappers using
`ConeQuantBridge.picardLimitRestartFrontier_of_spectralFrontier`.

The current PPID headline surface is therefore conditional on regime
assumptions plus the per-datum spectral frontier
`EndToEnd.PerDatumSpectralFrontier` for Picard-limit solution packages.  This is
an honest conditional reduction: `PerDatumSpectralFrontier` has no producer in
the current grep results, and remains the next analytic construction target.

## Task 243: PPID min-persistence discharged for chi nonpositive (2026-07-06)

`IntervalDomainMinPersistChiNonpos.lean` exposes
`MinPersistenceAtoms.classicalMinPersistence_chiNonpos` and `_chiNeg` by
feeding the proved endpoint chemotaxis-divergence boundary-window producer into
`classicalMinPersistence_of_boundary_window_regime`.  It then proves
`PPIDThresholdReachability.theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNonpos`
and `_chiNeg`, discharging the `ClassicalMinPersistence` input left by Task242.
After Task243, the PPID threshold route's remaining construction input is
`ThresholdQuantBridge.PicardRestartFrontier p`.

## Task 242: PPID seed local existence from Picard frontier (2026-07-06)

`IntervalDomainPPIDPicardFrontierSeed.lean` removes the separate PPID seed
local-existence hypothesis from Task241.  A `PaperPositiveInitialDatum` carries
both a per-datum sup bound and a per-datum positive floor, so it belongs to one
threshold class.  Applying
`ThresholdQuantBridge.thresholdQuantitativeLocalExistence_of_picardFrontier`
at that class gives `localExistencePPID_of_picardFrontier`.

The resulting theorem
`PPIDThresholdReachability.theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence`
proves `Theorem_1_1 intervalDomain p` from regime assumptions,
`PicardRestartFrontier p`, and `ClassicalMinPersistence p`.  This is the current
lean PPID threshold route: the all-PPID common-floor residuals are gone, and the
remaining analytic inputs are the restart frontier and min-persistence.

## Task 241: PPID Picard-frontier bridge to Theorem 1.1 (2026-07-06)

`IntervalDomainPPIDPicardFrontierTheorem11.lean` lowers the Task240
`ThresholdQuantitativeLocalExistence` input to the existing
`ThresholdQuantBridge.PicardRestartFrontier` interface via
`thresholdQuantitativeLocalExistence_of_picardFrontier`.  The resulting theorem
`PPIDThresholdReachability.theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence_seed`
proves `Theorem_1_1 intervalDomain p` from regime assumptions,
`PicardRestartFrontier p`, `ClassicalMinPersistence p`, and per-datum PPID seed
local existence.

This is still conditional, but the threshold-local Picard contraction core is no
longer a residual at this layer.  The remaining PPID-route residuals are the
Picard restart frontier, min-persistence, and PPID seed local existence.

## Task 240: PPID threshold/min-persistence bridge to Theorem 1.1 (2026-07-06)

`IntervalDomainPPIDThresholdTheorem11.lean` lifts the Task238 anti-Zeno
reachability result to the PPID quantitative-local interface and then to
`Theorem_1_1 intervalDomain p`.  The key observation is that Task238 gives
solutions on arbitrary target horizons for each fixed PPID datum; choosing
target horizon `1` yields the uniform `δ = 1` quantitative-local package
needed by `StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant`.

The resulting theorem
`PPIDThresholdReachability.theorem_1_1_intervalDomain_of_ppid_threshold_persistence_seed`
is still conditional on the real analytic inputs
`ThresholdQuantitativeLocalExistence p`, `ClassicalMinPersistence p`, and
per-datum PPID seed local existence.  It does not use a common all-PPID
datum floor.

## Task 239: strict-negative uniform-floor dead routes and floorless scalar atom (2026-07-06)

The full-PPID uniform-floor route for strict chi-negative local existence is
now formally dead in the two interfaces that had been feeding the EWA/Wiener
bridge:

- `SourceChiNegUniformBridgeC3Obstruction.not_uniformFlooredC3NeumannData`
  refutes the narrowed C3/Neumann uniform-floor residual.
- `SourceChiNegDatumWienerDataObstruction.not_datumWienerData` refutes the
  monolithic `DatumWienerData` residual directly, using cosine reconstruction
  to transfer the lifting floor back to the constant paper datum.
- `SourceChiNegUniformFloorDead` collects both no-go facts under route-level
  names, so future all-PPID reductions cannot silently route through these
  uninhabited premises.

Q3697 correctly diagnosed the strategic issue: the all-PPID strict-negative
route cannot depend on a common lower floor depending only on a sup bound.
Its suggested faithful-Wiener obstruction is superseded by the stronger
`not_datumWienerData` theorem above.  Its floorless scalar-power atom was
already present as
`IntervalDomainL2UEnergyUniformGammaGeOne.rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma`.
`IntervalRpowLipschitz.rpow_lipschitz_on_Icc_nonneg` is a thin existential
adapter around that existing result for the floor-free fixed-point route.

## Task 151: endpoint chemDiv limits for general chi nonpositive (2026-07-06)

`ShenWork/Paper2/IntervalDomainBoundaryChemDivLimit.lean` discharges the
left/right one-sided chemotaxis-divergence limit residuals introduced by
Task 150.  The proof avoids endpoint ordinary derivatives of zero extensions:
on interior filters it identifies `boundaryChemDivReal` with the H1-route
closed-slab physical representative, takes endpoint limits through that
representative, and bounds the endpoint coefficient by transferring the
interior `v_slice_coeff_bounds` estimate to the closed endpoint.  The public
producers are:

- `MinPersistenceAtoms.boundaryChemDivLeftLimitBound_of_classicalSolution`
- `MinPersistenceAtoms.boundaryChemDivRightLimitBound_of_classicalSolution`
- `MinPersistenceAtoms.boundaryChemDivEndpointLimitBounds_of_classicalSolution`
- `BFormPositiveDatumLocal.boundaryMinPersistenceWindowEndpointBounds_chiNonpos`
- `BFormPositiveDatumLocal.boundaryMinPersistenceWindowBound_chiNonpos`

Verification before banking: targeted module build, root `ShenWork.lean`,
proof-hole/whitespace scans, and clean-3 axiom audits all passed locally.

Task 152 extends the same file with thin base and negative-part B-form headline
wrappers.  These wrappers consume the proved general chi nonpositive window
boundary producer internally, so the full-PID Picard-restart and Picard-limit
B-form routes no longer expose a separate boundary min-persistence residual at
that layer.  They remain conditional on the corresponding B-form local package,
the Picard restart or Picard-limit frontier, and the scalar parameter
assumptions.

Post-Task152 cleanup:
`ShenWork/Paper2/IntervalDomainPicardLimitSpectralFrontier.lean` factors the
chi-zero/cone Picard-limit route one step further:
`EndToEnd.PerDatumSpectralFrontier` supplies both the half-step restart package
and the classical frontier core, hence it discharges
`ConeQuantBridge.PicardLimitRestartFrontier`.  This is deliberately recorded as
a chi-zero/cone bridge, not as a general-chi B-form shortcut, because the
general-chi B-form route uses the restart-cosine interface rather than the
logistic-only half-step source package.

Q3614 route audit: after Task152, the shortest general-chi negative-part
headline still carries only regime assumptions plus
`BFormPositiveLocalFrontier p` and
`ConeQuantBridge.PicardLimitRestartFrontier p`.  The next assumption-reducing
task is therefore a genuine producer for `BFormPositiveLocalFrontier p` (or a
large named subpackage), not another boundary-window wrapper.

Task153 first constructor:
`BFormPositiveDatumLocal.bFormPositiveLocalFrontier_of_localHyp` proves that the
strong `PositiveDatumBFormLocalHyp p` component package produces the
negative-part `BFormPositiveLocalFrontier p`.  The proof constructs
`BFormPositiveClassicalFrontier` directly from `K.route`, `K.regularity`,
`mildChemical_nonneg`, `K.hpde_v`, and `K.neumann`; it does not use final
Theorem 1.1, a quantitative factory, or a paper-positive conversion.  The
downstream headline
`paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_of_localHyp`
feeds the Task152 negative-part Picard-limit route from this base local package.

Task154 PPID strong-path wiring:
`IntervalBFormPositiveDatumPPIDStrongWiring` adds paper-positive quantitative
wrappers for the squared-barrier B-form packages.  These use
`StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant`, so the
quantitative factory is typed over `PaperPositiveInitialDatum`, matching the
actual datum quantifier in `Theorem_1_1`; they do not pretend that the
`Sq`/`SqRegular`/`SqDeepest` packages provide all-positive PID local existence.
Q3619 then identified the datum-faithful negative-part target:
`BFormPaperPositiveLocalFrontier` and
`BFormPositiveDatumLocalSq.bFormPaperPositiveLocalFrontier_of_sqRegular` expose
the `SqRegular` package as a paper-positive negative-part frontier without
claiming the all-positive `BFormPositiveLocalFrontier`.
Task155 adds the same paper-positive negative-part frontier producer for the
base squared-barrier package:
`BFormPositiveDatumLocalSq.bFormPaperPositiveLocalFrontier_of_sq`.  This remains
datum-faithful: it is a PPID frontier producer, not an all-positive PID
producer.
Task156 wires that PPID frontier to the PPID strong path through
`BFormPositiveDatumNegPart.paperPositiveDatum_localExistence_of_BForm` and
`paper2_theorem_1_1_general_chi_bform_paper_negpart_from_ppid_quant`, with
explicit Sq/SqRegular negative-part wrappers in
`IntervalBFormPositiveDatumPPIDStrongWiring`.
Task157 extends the paper-positive negative-part frontier to the deepest
squared-barrier package:
`BFormPositiveDatumLocalSq.bFormPaperPositiveLocalFrontier_of_sqDeepest`.
The `negativePart_zero` field is produced by consuming the existing
`NegativePartEnergyCoreData`/Gronwall route; this wrapper does not remove any
weak-PDE assumptions used to build that energy core.

## L2 Seed Frontier Producer (2026-07-03)

**File: `ShenWork/Paper2/IntervalDomainL2SeedFrontierProducer.lean`** (149 lines, axiom-clean)

Produces `IntervalDomainL2SeedRegularityFrontier T u` from:
- `IsPaper2ClassicalSolution` (have)
- `IntervalDomainPowerEnergyEndpointContinuity u T 2` (still carried)
- `IntervalDomainL2SeedZeroRightDerivative u` (still carried, but downstream never uses t=0)

Unconditionally discharges 2 of 4 frontier fields:
- `derivativeAlignment`: proved via `LpAbsEnergy 2 = 2 * L2HalfEnergy` + `deriv_const_mul_field`
- `initialBound`: trivial (`⟨E(0), E_nonneg, le_refl⟩`)

Also proves helper identities:
- `intervalDomainLpAbsEnergy_two_eq_two_mul_L2HalfEnergy`
- `intervalDomainLpAbsEnergy_two_eq_powerEnergy`
- `intervalDomainLpAbsEnergy_two_nonneg`

### Conditional input landscape (CERawGradResiduals leaf)

| Condition | Nature | Status |
|-----------|--------|--------|
| `boundednessHyp` | parameter (2γ<α, γN<2, 0<b, 0<γ) | correctly carried |
| `closedEnergyTrace` | FTC + endpoint energy continuity | interior PROVED, endpoints CARRIED |
| `rawMoserDrop` | (1/p)d/dt∫u^p + B∫u^p ≥ 0, ∀B≥0 | **UNSATISFIABLE** (formal counterexample at P3MoserDissipationShape.lean:188) |
| `relativeMassGradient` | Sobolev/GN gradient interpolation | PDE frontier |
| `quantitativeEndpoint` | de Giorgi iteration | PDE frontier |

**Critical finding (2026-07-03):** `rawMoserDrop` is provably FALSE. The file
`P3MoserDissipationShape.lean` contains `unitLinearDrop_not_MoserDissipationDropBeforeNonnegB`
which refutes even the weaker `MoserDissipationDropBeforeNonnegB`. With B=0, the condition
demands E'(t) ≥ 0 (energy non-decreasing), which fails for any solution with diffusion.

**The correct shape** is `IntegratedMoserDissipationDropBefore` (same file, line 67):
integrated energy drop over time intervals, NOT pointwise. This IS satisfiable — it
follows from integrating the energy inequality via FTC.

**The fix route already exists** in the codebase:
- `IntegratedMoserDissipationDropBefore` → `IntegratedMoserFirstCrossingStep` (via `P3MoserThresholdPlanProducer.lean:25`)
- `IntegratedMoserFirstCrossingStep` → `Corollary_2_1` + `Proposition_2_5` (via `IntervalDomainMassLpSmoothingIntegratedStepResiduals`, `IntervalDomainMoserLadderAtoms.lean:257`)
- The integrated step residuals produce `to_routeResiduals` identical to the old nonnegB route.

**Action needed:** Build a leaf-level structure analogous to `CERawGradResiduals` but with
`integratedMoserDissipation : IntegratedMoserDissipationDropBefore` replacing `rawMoserDrop`,
and wire it through `IntegratedMoserFirstCrossingStep` → `IntervalDomainMassLpSmoothingIntegratedStepResiduals`.

The `closedEnergyTrace` gap reduces to: endpoint continuity at t=0 (from InitialTrace)
and t=T (from energy identity/regularity).

### Endpoint continuity at t=0 (COMPLETED, 2026-07-03)

**Codex task 2 delivered + verified axiom-clean.** Added 267 lines to `P3MoserEnergyContinuity.lean`:

- `intervalDomain_traceDiff_slice_abs_bddAbove_of_classical` — boundedness of |u(t) - u₀|
- `intervalDomain_initialTrace_pointwise_abs_lt_of_classical` — pointwise control from InitialTrace
- `intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive_classical` — finite-horizon tendsto
- `intervalDomainPowerEnergyContinuousWithinAt_zero_of_initialTrace` — ContinuousWithinAt at t=0 (with explicit `hzeroSlice : u 0 = u₀`)
- `intervalDomainPowerEnergyContinuousWithinAt_zero_withInitialSlice_of_initialTrace` — ContinuousWithinAt for `intervalDomainWithInitialSlice u₀ u` (no `u 0 = u₀` hypothesis needed)

All `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

The `u(0) ≠ u₀` issue is handled correctly: `intervalDomainWithInitialSlice` re-anchors the trajectory by replacing `u(0)` with `u₀`.

### Integrated Moser drop replacement (FILE CREATED, build pending, 2026-07-03)

**File: `ShenWork/Paper3/IntervalDomainIntegratedMoserAssembly.lean`** (151 lines)

New structure `IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals` replaces the
unsatisfiable `rawMoserDrop` with `integratedMoserDissipation : IntegratedMoserDissipationDropBefore`.

Wiring: `to_integratedStepResiduals` converts to `IntervalDomainMassLpSmoothingIntegratedStepResiduals`,
then `to_routeResiduals` chains through to `IntervalDomainMassLpSmoothingRouteResiduals`.

Extra parameter: `classicalRegularity : ... → IntervalDomainIntegratedMoserClassicalRegularityData u T p0`
is needed by `intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData`.

**Status: VERIFIED axiom-clean on uisai2. `[propext, Classical.choice, Quot.sound]`.**

Note: Codex refined imports from the original spec — uses `IntervalDomainMoserLadderAtoms` +
`P3MoserLemmaDischarge` instead of `IntervalDomainActualLinearStatementAssembly`, reducing the
dependency chain.

### Endpoint wiring into assembly chain (COMPLETED, 2026-07-04)

**Codex task 4 delivered + verified.** Added 315 lines to `P3MoserEnergyContinuity.lean`:

- `intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_classical_withInitialSlice` — packages pointwise ContinuousWithinAt for ALL p ≥ p0
- `intervalDomain_powerEnergyEndpointContinuity_withInitialSlice_of_global_classical` — full endpoint continuity (atZero + atRight) for global solutions with re-anchored trajectory

Also added FTC window theorems:
- `intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData` and variants

### Gradient integrability survey (COMPLETED, 2026-07-04)

**Codex task 5 delivered + verified.** New file `P3MoserGradientIntegrability.lean` (251 lines, axiom-clean).

**Key finding: `gradientTimeIntegrable` is IRREDUCIBLE** — cannot be derived from `IsPaper2ClassicalSolution` alone. Missing: closed-time gradient energy continuity `ContinuousOn (t ↦ ∫|∇(u^{p/2})|²) (Icc 0 T)` at the boundary (especially t=0). Classical solution API gives regularity on `Ioo(0,T)` only.

Provides reducers that wire various partial inputs into `IntervalDomainIntegratedMoserClassicalRegularityData`:
- `intervalDomain_classicalRegularityData_of_classical_endpoint_gradientContinuous`
- `intervalDomain_classicalRegularityData_of_global_atZero_gradientContinuous`

### Closed energy partial producer (COMPLETED, 2026-07-04)

**Codex task 6 delivered + verified.** New file `P3MoserClosedEnergyProducer.lean` (241 lines, axiom-clean).

`ClosedEnergyIdentityTracePartialData` discharges from classical solution:
- ✅ `nonnegT` — from T_pos
- ✅ `initial_trace_energy` — via re-anchoring (`intervalDomainWithInitialSlice`)
- ✅ `positiveTimeEnergyHasDerivWithin` — from classical interior regularity
- ✅ `derivativeAlignment` — algebraic identity

`ClosedEnergyIdentityTraceRemainingData` — the irreducible remainder:
- `g` + `g_integrable` + `energy_eq` — FTC representation
- `zeroRightDerivative` — HasDerivWithinAt at t=0

Converter `to_closedEnergyIdentityTraceData` combines partial + remaining into full data.

### FTC infrastructure bridge (COMPLETED, 2026-07-04)

**Codex task 8 delivered + verified.** New file `P3MoserFTCInfrastructure.lean` (142 lines, axiom-clean).

**Key finding:** `g`, `g_integrable`, `energy_eq` discharge from `IntegratedMoserEnergyWindowFTC` specialized at exponent 2:
- `closedEnergyIdentityTraceRemainingData_of_integratedMoserEnergyWindowFTC` — converts existing FTC package
- `closedEnergyIdentityTraceData_withInitialSlice_of_globalPDEInitialData` — full producer for global case

**Only `zeroRightDerivative` remains irreducible** — no existing producer in the codebase.

### Full project build (2026-07-04)

`lake build` on uisai2: **8993 jobs, 852 seconds, BUILD OK.** All new files axiom-clean.

### Moser continuation chain (tasks 25-35, COMPLETED 2026-07-04)

**File: `P3MoserTopLevelAssembly.lean`** (commit ca20192e, axiom-clean, 3600 jobs verified on uisai2)

Top-level wiring theorem:
```
SubintervalAssemblyResidual + PointwiseUniformizationResidual → IsPaper2BoundedBefore
```

The FULL Moser continuation chain (tasks 25-35) is axiom-clean, 0 sorry:
- T25: `ShortTimeBoundedBeforeResidual` (per-t on (0,τ₀)) — UNCONDITIONAL
- T26-27: `ContinuationWiring` — wires assembly + closure residuals
- T28: `FirstCrossingSupremumClosureResidual` — sSup real induction
- T29: `ShortTimeBoundedBefore` — intervalDomain-specific (compact [0,1])
- T30: `ExtensionByContinuityResidual` — joint continuity extension
- T31: `SubintervalMoserInputResidual` — bootstrap input wiring
- T32: `FirstCrossingPointwiseUniformClosureResidual` — conditional on Uniformization
- T33-34: `SubintervalLpPowerBoundResidual` — Lp from pointwise uniform
- T35: Top-level assembly

**Two irreducible residuals:**
1. `SubintervalAssemblyResidual` — the Moser iteration: given energy inequality data at τ, produce L∞ on [0,τ]. This IS the hard PDE theorem (De Giorgi-Nash-Moser bootstrapping from Lp to L∞).
2. `PointwiseUniformizationResidual` — convert per-t bounds (∀ t, ∃ M_t) to uniform (∃ M, ∀ t). Genuinely irreducible: joint continuity on OPEN (0,T) × [0,1] doesn't give uniform bounds (no control at t=0 or t=T). The circularity: Lp seed → assembly → uniform → Lp seed cannot be broken from current hypotheses.

**Analysis of PointwiseUniformizationResidual:** An InitialUniformBound + Assembly approach was explored but fails because the assembly output M(τ) may grow as τ → T (SubintervalAssemblyResidual is a black box). Even with a real induction carrying uniform bounds, the sSup argument gives τ* = T but not a single uniform M across all of (0,T).

**Relationship to PDE assembly (tasks 1-18):** The PDE assembly produces IntegratedMoserFirstCrossingStep (the iteration STEP) from classical regularity + PDE frontier data. SubintervalAssemblyResidual bundles the FULL iteration (step + endpoint + chain + conversion). Proving SubintervalAssemblyResidual from PDE assembly output would require interior-only FTC (available) + resolving the PDE frontiers (zeroRightDerivative, gradientTimeIntegrable — still carried).

### Task 36: SubintervalAssemblyResidual bridge (COMPLETED 2026-07-04)

**File: `P3MoserSubintervalAssemblyBridge.lean`** (commit edb3ac8c, axiom-clean, 3595 jobs)

Reduces SubintervalAssemblyResidual to 4 explicit suppliers:
1. `hstep`: IntegratedMoserFirstCrossingStep supplier (from sol + cross + boot + gap)
2. `hEndpoint`: MoserQuantitativeEndpoint supplier (from sol + cross + boot)
3. `hInitial`: u(0) pointwise bounded (from sol)
4. `hTerminal`: u(τ) pointwise bounded (from sol + sub + τ>0)

### Task 37: Eliminate hTerminal for τ < T (COMPLETED 2026-07-04)

**File: `P3MoserSubintervalAssemblyBridge.lean`** (commit 0e891c57, axiom-clean, 219 lines)

Two new theorems:
- `intervalDomain_terminal_bound_of_classical_strict` — for τ ∈ (0,T), classical regularity gives `∃ M, ∀ x, |u τ x| ≤ M` via `intervalDomain_solution_slice_abs_bound`
- `intervalDomain_subintervalAssemblyResidual_strict_of_step_endpoint_initial` — assembly from 3 suppliers (hstep + hEndpoint + hInitial) when τ < T (no hTerminal needed)

**Impact:** The continuation chain ONLY invokes assembly at τ < T (extension needs room to extend beyond τ). So in practice, SubintervalAssemblyResidual needs only 3 suppliers.

**Full chain now:**
```
IntegratedMoserFirstCrossingStep + Endpoint + Initial
  → SubintervalAssemblyResidual (tasks 36-37, bridge, τ<T)
    + PointwiseUniformizationResidual
      → IsPaper2BoundedBefore (task 35, top assembly)
        → AprioriBound → GlobalExistence
```

### Comprehensive condition audit (2026-07-04)

**4 irreducible PDE frontiers** block the chain from raw data to GlobalExistence:

| # | Frontier | What it does | Where consumed | Can Codex close it? |
|---|----------|-------------|----------------|---------------------|
| 1 | `zeroRightDerivative` | HasDerivWithinAt at t=0 for energy | → ClosedEnergyTrace → FTC → hstep | 🟡 Fix identified (derivWithin), needs gradient-energy continuity at t=0 |
| 2 | `gradientTimeIntegrable` | ∫₀ᵀ‖∇(u^{p/2})‖² dt < ∞ | → ClassicalRegularityData → hstep | ❌ Genuine PDE (monotone convergence from dissipation) |
| 3 | `DyadicMoserEndpointRecurrence` | De Giorgi dyadic iteration data | → MoserQuantitativeEndpoint → hEndpoint | ❌ PDE content (extraction from integrated dissipation) |
| 4 | `PointwiseUniformizationResidual` | per-t bounds → uniform M | independent, needed by top assembly | ❌ Genuinely irreducible (assembly output M(τ) may grow) |

**Conditions that ARE discharged:**
- ✅ `ShortTimeBoundedBeforeResidual` — unconditional (compact [0,1])
- ✅ `ExtensionByContinuityResidual` — unconditional (classical + compact)
- ✅ `hInitial` — from initial data (PositiveInitialDatum + InitialTrace gives bounded u₀)
- ✅ `hTerminal` — from classical regularity when τ < T (task 37)
- ✅ `integratedMoserDissipation` — conditional on FTC + regularity (task 13)
- ✅ `relativeMassGradient` — conditional on IsPaper2BoundedBefore (task 9)
- ✅ `LpBootstrapEnergyInequalityWithGap` — from classical regularity (task 17)

**Dependency graph of irreducible frontiers:**
```
zeroRightDerivative (#1) ←── depends on gradient-energy continuity at t=0
    ↓
ClosedEnergyTrace → FTC ──┐
                           ├──→ hstep (IntegratedMoserFirstCrossingStep)
gradientTimeIntegrable (#2) ┘         ↓
                                      SubintervalAssemblyResidual
DyadicMoserEndpointRecurrence (#3) → hEndpoint ↓
                                      + PointwiseUniformizationResidual (#4)
                                      → IsPaper2BoundedBefore
```

### Updated conditional input landscape (2026-07-04)

| Condition | Status | Cleared by |
|-----------|--------|------------|
| `boundednessHyp` | ✅ parameter | — |
| `closedEnergyTrace.nonnegT` | ✅ | T_pos (task 6) |
| `closedEnergyTrace.initial_trace_energy` | ✅ | re-anchoring (task 6) |
| `closedEnergyTrace.positiveTimeHasDeriv` | ✅ | classical interior (task 6) |
| `closedEnergyTrace.derivativeAlignment` | ✅ | algebraic (task 6) |
| `closedEnergyTrace.g + g_integrable + energy_eq` | ✅ reducible | from IntegratedMoserEnergyWindowFTC@2 (task 8) |
| `closedEnergyTrace.zeroRightDerivative` | ❌ irreducible | no producer exists |
| `classicalRegularity.endpointEnergy.atZero` | ✅ | trace+classical (tasks 2,4) |
| `classicalRegularity.endpointEnergy.atRight` | ✅ (global) | automatic for global solutions (task 4) |
| `classicalRegularity.gradientTimeIntegrable` | ❌ irreducible | needs closed-time gradient continuity (task 5) |
| `integratedMoserDissipation` | ✅ (conditional) | task 13: `P3MoserIntegratedDissipationPDE.lean` — wired via existing `regularEnergy_coeffGap`. Conditional on `IntervalDomainIntegratedMoserClassicalRegularityData` + hgap |
| `relativeMassGradient` | ✅ (conditional) | task 9: `P3MoserRelativeMassGradientProducer.lean` — Agmon+chain-rule. Conditional on `IsPaper2BoundedBefore` |
| `quantitativeEndpoint` | ✅ (conditional) | task 14: `P3MoserQuantitativeEndpointDischarge.lean` — dyadic recurrence + converter. Conditional on `IntegratedMoserDissipationDropBefore` |
| `a_pos`, `chi_nonneg` | ✅ parameter | — |

**Irreducible PDE frontiers — REVISED after dual-oracle synthesis (2026-07-04):**

The 6 nominal frontiers collapse to 3 real work items (oracle consensus):

| # | Frontier | True status | Action |
|---|----------|-------------|--------|
| 1 | `zeroRightDerivative` | **SATISFIABILITY TRAP** — `deriv E 0` is two-sided, junk at t=0. Audit file created: `P3MoserZeroDerivAudit.lean` (211 lines, axiom-clean). Corrected definition `IntervalDomainL2SeedZeroRightDerivativeWithin` uses `derivWithin (Ici 0)`. | Fold into FTC infrastructure; prove via `hasDerivAt_interval_left_endpoint_of_tendsto_deriv` after gradient-energy continuity at t=0 |
| 2 | `gradientTimeIntegrable` | **DERIVED from #3** — monotone convergence: rearrange integrated drop on [t₁,t₂], Y_p bounded, G_p ≥ 0, take t₁→0, t₂→T. NOT independent. | Derive after #3 lands |
| 3 | `integratedMoserDissipation` | **THE CORE PDE ESTIMATE** — assembly from Leibniz + IBP + cross-diffusion bootstrap + FTC. All sub-tools exist. Must track C(p) polynomial growth for #5. | Main Codex task after #4 and #6 |
| 4 | `relativeMassGradient` | **MOSTLY WIRING** — Agmon interpolation PROVED (`IntervalAgmonInterpolation.lean:872`). GN/Young wrappers exist (`UnitIntervalPowerGNYoungForMoser`). Chain-rule identity for cGrad. Jensen for mass-power. | Codex task 9 (running) |
| 5 | `quantitativeEndpoint` | **TERMINAL** — dyadic root tower already proved. Needs polynomial C(p) from #3. Continuity contradiction for Lp→pointwise. | After #3 with tracked constants |
| 6 | `FTCGlobalPDEInitialData` | **COLLAPSES** — `atZero` already proved. True irreducible is `pdeCombinedInitial` (PDE-term integrability near t=0). | Codex task 12 (running) |

**Attack order:** #4 and #6 in parallel (independent) → #3 (core, depends on both) → #2 (derived) → #1 (corrected + proved) → #5 (terminal)

### Task 9: relativeMassGradient (COMPLETED, 2026-07-04)

**File: `P3MoserRelativeMassGradientProducer.lean`** (506 lines, axiom-clean, 294k Codex tokens)

8 theorems, 0 sorry, 0 axiom. Key deliverables:
- `intervalDomain_massGradientInterpolation_of_classical` — sub-component (B), UNCONDITIONAL, uses Agmon
- `intervalDomain_moserMassPowerToCurrentLpLowerOrder_of_classical` — sub-component (D), UNCONDITIONAL
- `intervalDomain_relativeMassGradient_of_classical_boundedBefore` — full 4-tuple, conditional on `IsPaper2BoundedBefore` (uniform sup bound needed for chain-rule components A,C)
- `intervalDomain_relativeMassGradient_components_BD_of_classical` — convenience theorem packaging B+D

**Note on BoundedBefore:** The assembly field `relativeMassGradient` expects the 4-tuple without explicit `BoundedBefore`. Classical solutions on compact [0,1] are bounded before any finite T (continuous u on compact domain). A wiring lemma `IsPaper2ClassicalSolution → IsPaper2BoundedBefore` is needed; should be straightforward.

### Task 10: frontier #1 deriv audit (COMPLETED, 2026-07-04)

**File: `P3MoserZeroDerivAudit.lean`** (211 lines, axiom-clean, 141k Codex tokens)

**CONFIRMED: `IntervalDomainL2SeedZeroRightDerivative` is UNSATISFIABLE by PDE data.**
- `deriv E 0` is Mathlib's two-sided derivative → junk value 0 at t=0
- `intervalDomainWithInitialSlice` only replaces t=0, negative time = raw u(t)
- Consumers pass `hzero` without using its value, BUT upper layer uses `max K (deriv E 0)` → junk

Corrected definition: `IntervalDomainL2SeedZeroRightDerivativeWithin` using `derivWithin (Ici 0) 0`.
Conditional adapter: `to_old_of_deriv_eq` — needs `deriv E 0 = derivWithin E (Ici 0) 0` to convert back.
Producer: `zeroRightDerivativeWithin_withInitialSlice_of_tendsto_deriv` — from interior differentiability + derivative limit.

### Task 13: frontier #3 integratedMoserDissipation (COMPLETED, 2026-07-04)

**File: `P3MoserIntegratedDissipationPDE.lean`** (97 lines, axiom-clean, 248k Codex tokens)

2 theorems, 0 sorry, 0 axiom. Core PDE assembly:
- `intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE` — produces `IntegratedMoserDissipationDropBefore` from classical solution + cross-diffusion bootstrap + Lp bootstrap + WindowFTC + RelativeMoserInterpolationBefore + classicalRegularityData + coefficient gap
- `intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_fact` — convenience fact version

**Architecture:** Pure wiring through existing `intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap`. No new PDE analysis — all heavy lifting was already done.

**Residuals carried:** `IntervalDomainIntegratedMoserClassicalRegularityData` (needs gradient time integrability → task 15 provides this), `hgap: 2 < q * A` (coefficient condition from parameters).

**⚠️ hgap UNSATISFIABLE (discovered 2026-07-04):** The gap condition `∀ q ≥ p0, ∀ A K > 0, 2 < q * A` is universally quantified over ALL positive A. For A = 1/(2q), we get 2 < 1/2. The underlying theorem `higherPowerWindowCoeffFrontier_of_regularEnergy` (IntegratedClosure.lean:789) only uses A,K from `LpBootstrapEnergyInequality` — the universal quantification is an over-strengthening in the `_coeffGap` wrapper. Fix: task 17 writes a v2 with combined `LpBootstrapEnergyInequalityWithGap` that pairs the energy inequality with the gap for the SPECIFIC A.

### Task 14: frontier #5 quantitativeEndpoint (COMPLETED, 2026-07-04)

**File: `P3MoserQuantitativeEndpointDischarge.lean`** (199 lines, axiom-clean, 236k Codex tokens)

5 definitions/theorems, 0 sorry, 0 axiom:
- `DyadicMoserEndpointRecurrence` — structure for dyadic Moser recurrence data
- `intervalDomain_moserQuantitativeEndpoint_of_dyadic_recurrence` — endpoint from recurrence
- `intervalDomain_moserQuantitativeEndpoint_of_integrated_dissipation` — endpoint from integrated dissipation (bridges frontiers #3→#5)
- `IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals` — refined residual structure with both dissipation and endpoint data
- `to_integratedDropResiduals` — converter to `IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals` (the assembly)

### Task 15: frontier #2 gradientIntegrability (COMPLETED, 2026-07-04)

**File: `P3MoserGradientIntegrabilityFromDissipation.lean`** (258 lines, axiom-clean, 218k Codex tokens)

3 definitions/theorems, 0 sorry, 0 axiom:
- `IntervalDomainIntegratedDissipationGradientBoundData` — input data structure for gradient integrability
- `intervalDomain_gradientTimeIntegrable_of_integratedDissipation_boundData` — gradient time integrability from integrated dissipation
- `intervalDomain_classicalRegularityData_of_integratedDissipation_boundData` — **KEY BRIDGE:** produces `IntervalDomainIntegratedMoserClassicalRegularityData` (the residual from task 13) from integrated dissipation bound data

**This closes the circularity gap:** Task 13 needs classicalRegularityData → Task 15 provides it from dissipation → Task 13 provides dissipation. The resolved dependency: classicalRegularityData derives from dissipation bound data, NOT from dissipation itself (no circularity — the bound data is a weaker input).

### Task 12: frontier #6 pdeCombinedInitial (COMPLETED, 2026-07-04)

**File: `P3MoserPDECombinedInitialProducer.lean`** (186 lines, axiom-clean, 244k Codex tokens)

6 theorems. Key chain:
- `IntegratedMoserEnergyDerivativeInitialWindowIntegrability` (INPUT)
  → `IntervalDomainLpWeightedTimeTermInitialWindowIntegrability`
  → `IntervalDomainLpPDECombinedInitialWindowIntegrability` (OUTPUT = pdeCombinedInitial)

Also provides backward bridge from `IntegratedMoserEnergyWindowFTC` → pdeCombinedInitial (useful when FTC comes from non-GlobalPDE source).

**True irreducible:** `IntegratedMoserEnergyDerivativeInitialWindowIntegrability` — integrability of d/dt Y_p near t=0.

**v-gradient finding:** No standalone ‖∂ₓv‖∞ needed. `CrossDiffusionBootstrapEstimate` absorbs v-gradients via resolver bounds (`IntervalDomainCrossDiffusionBootstrap.lean:591`).

### Task 16: assembly filler (COMPLETED, 2026-07-04)

**File: `P3MoserAssemblyFiller.lean`** (151 lines, axiom-clean, 157k Codex tokens)

Wires all frontier producers into `IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals` via the intermediate `IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals` structure.

**6 carried hypotheses (irreducible inputs):**

| # | Hypothesis | Nature | Status |
|---|-----------|--------|--------|
| 1 | `hClosedTrace` | closed energy trace data | ❌ needs zeroRightDerivative (frontier #1) |
| 2 | `hFTC` | IntegratedMoserEnergyWindowFTC | ❌ needs endpoint continuity at t=0 + derivative integrability |
| 3 | `hClassicalRegularity` | gradient regularity data | 🟡 task 15 provides from dissipation bound data |
| 4 | `hBoundedBefore` | IsPaper2BoundedBefore | 🟡 Moser iteration output (has producer in IntegratedClosure) |
| 5 | `hGap` | coefficient gap 2 < q*A | ❌ **UNSATISFIABLE** — task 17 fixing |
| 6 | `hDyadicEndpoint` | dyadic recurrence data | ❌ needs Moser dyadic recurrence data |

**Build verified:** 9004 jobs, 128s, BUILD OK on uisai2. Commit 9bd27ecf.

**Oracle ledger:**

| Round | Fable | ChatGPT | Key insight |
|-------|-------|---------|-------------|
| R1 | 6→3 real items; #1 has deriv/derivWithin trap; #2,#6 corollaries of #3; v-gradient hidden sub-item | 6→4 real items; #6 first; existing GN/Young wrappers for #4; #1 fold into #6 | Agreement: collapse. Fable caught trap; ChatGPT found wrappers |

## Breakthrough: vdEWA_floor_of_evenReal (2026-07-03)

**`SourceVdFloorGeneric.lean`** proves: for ANY `EvenRealEWA U` with
`UniformFloor U δ` (δ > 0) and `0 ≤ p.ν`, we have
`UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ U) 1`.

This is the GENERALIZATION of `vdEWA_center_floor_heat_discharged`
(which only works for `heatEWA u₀E`). The proof uses the same chain:
`realPowEWA_eval` → `slice_smul_realPow_eq_source` →
`evalST_gResolver_eq_resolverSynthesis_all` → `resolverSynthesis_nonneg_all`.
All the building blocks (`sourceFn_continuous`, `sourceFn_nonneg`,
`sourceFn_coeff`, `realSlice_evalST_realizes`) already work for generic
`U : EWA T 1`, not just the heat center.

**Impact: eliminates the Wiener-norm-dependent `hsmall` condition.**

The existing ball-reduction approach (`vdUniformFloor_of_ball` in
`SourceVdFloorDischarge.lean`) bounds `‖vdEWA u − vdEWA center‖ ≤ Lv·ρ`,
giving floor `1 − Lv·ρ`. For large Wiener norms, `Lv·ρ ≥ 1` and the
bound is NEGATIVE (useless). With `vdEWA_floor_of_evenReal`, any
EvenReal ball element with positive u-floor gets floor 1 DIRECTLY —
no ball reduction, no `hsmall`, no Wiener-norm dependence.

**Remaining integration step: EvenReal-restricted Banach fixed point.**

`picardEWA_clean_fixedPoint` quantifies `hVdFloor : ∀ u ∈ ball, ...`
over ALL ball elements. But non-EvenReal ball elements cannot have their
`vdEWA` floor proved (the `realPowEWA_eval` bridge requires EvenReal).
The Picard map PRESERVES EvenReal, and the fixed point IS EvenReal.
Resolution: apply Banach's contraction mapping theorem on the EvenReal
closed ball `{u | EvenRealEWA u} ∩ closedBall(center, ρ)`, which is:
1. Complete (closed subset of a Banach space ∩ closed set)
2. Self-mapped by Picard (EvenReal preservation + ball self-map)
3. Contracted (same contraction constant, with δv = 1 from the new theorem)

This refactoring eliminates `hVdFloor` as a carried hypothesis entirely
and closes the path to unconditional `Theorem_1_1`.

**File: `SourceVdFloorGeneric.lean` — NOT YET BUILT (uisai1/2 down).**

## Assembly: vdFloor → EvenReal ball → unconditional core (2026-07-03)

Five files wire the breakthrough into the headline theorem:

1. **`SourceFixedPointEvenReal.lean`** — `picardEWA_clean_fixedPoint_evenReal`:
   Banach on `B' = closedBall(center, ρ) ∩ {EvenRealEWA}`. Self-map proof
   INLINED (not via `picardEWA_mapsTo`) to avoid the chicken-and-egg.
   Returns `∃ T, hTpos : 0 < T, ∃ u_star ∈ B, EvenRealEWA u_star ∧ fix`.
   **Changed:** now returns `0 < T` (was `0 ≤ T`); uses `hTpos.le` internally.

2. **`SourceReducedCoreWireV6EvenReal.lean`** — `realSlice_reducedCore_of_evenReal`:
   Takes `EvenRealEWA u_star` as GIVEN (not derived from contraction framework).
   **Changed:** floor-lifespan separation — takes `{η : ℝ} (hηpos : 0 < η)
   (hfloor : UniformFloor u_star η)` instead of `(hfloor : UniformFloor u_star T)`.
   The floor η is decoupled from the lifespan T.

3. **`SourceChiNegPerDatumV6.lean`** — `chiNeg_EWA_core_of_datum` (NEW):
   Per-datum wiring combining clean FP + v6. Takes: continuous u₀ with floor δ₀,
   ℓ¹ cosine summability, MemW, coefficient bounds, reconstruction.
   Produces `∃ T, 0 < T, ∃ u_star : EWA T 1, Core p T u₀p (realSlice u_star)`.
   Key: ball floor η = δ₀ - δ₀/2 derived automatically from `uniformFloor_on_ball`.

4. **`IntervalCoupledClassicalCoreRestrict.lean`** — `Core.restrict` (NEW):
   If `Core p T u₀ u` and `0 < δ ≤ T`, then `Core p δ u₀ u`. Each field
   restricts trivially: quantifier restriction + ContinuousOn.mono.
   Also includes `intervalDomainClassicalRegularity_restrict`.

5. **Remaining gap:** Wire into `ChiNegDatumUniformConstructionStrong`
   → `chiNeg_theorem_1_1_of_strong` → `Theorem_1_1 intervalDomain p`.
   See gap analysis below.

**All files NOT YET BUILT (uisai1/2 down).**

## Gap Analysis: Strong Construction → Theorem_1_1 (2026-07-03)

### The forward chain (what exists)

```
ChiNegDatumUniformConstructionStrong p
  → ppid_of_strong      (IntervalDomainTheorem11StrongPath.lean:534)
  → chiNeg_theorem_1_1_ppid (IntervalDomainTheorem11StrongPath.lean:527)
  → Theorem_1_1 intervalDomain p
```

### What `ChiNegDatumUniformConstructionStrong` requires

```lean
∀ M > 0, ∃ δ > 0, ∀ u₀ : PPID, |u₀| ≤ M →
    ∃ u_star : EWA δ 1, Core p δ u₀ (realSlice u_star)
```

The δ must be **UNIFORM** across all PPID datums bounded by M.

### What we have: per-datum existence (chiNeg_EWA_core_of_datum)

```lean
∀ u₀ : PPID (+ Wiener data), ∃ T > 0,
    ∃ u_star : EWA T 1, Core p T u₀p (realSlice u_star)
```

Per-datum T varies per datum. NOT uniform.

### The TWO gaps (reducible to ONE)

**Gap 1: Wiener membership.** `PaperPositiveInitialDatum` = continuous + bounded
+ positive floor. Continuous bounded functions on [0,1] are NOT necessarily in
the Wiener algebra (ℓ¹ cosine coefficients). The per-datum theorem needs:
- `Summable (fun k => |cosineCoeffs u₀ k|)` — ℓ¹ summability
- `MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))` — weighted ℓ¹: ∑(1+k)|c_k| < ∞
- Reconstruction: `u₀p x = ∑' n, c_n * cos(nπx)` — pointwise convergence

**Gap 2: Uniform lifespan.** The clean FP's T depends on the contraction
constants, which depend on the Wiener norm ‖u₀E‖. For PPID datums bounded by M,
the Wiener norm can be arbitrarily large, so T can be arbitrarily small.
To get a uniform δ, I need uniform Wiener norm bounds.

**Gap 2 reduces to Gap 1.** If all PPID datums bounded by M have Wiener
norm ≤ W(M) for some finite W(M), then:
- All contraction constants (L_Q, L_G, M_Q, M_G) are bounded by explicit
  algebraic expressions in W(M), the floor, and p's parameters
- `exists_uniform_EWA_lifespan` (ChiNegUniformLifespan.lean:109) gives
  uniform T* > 0 from these bounds
- `Core.restrict` restricts per-datum Core from [0,T(datum)] to [0,T*]
  (since T(datum) ≥ T* when per-datum constants ≤ bar constants)

### Regularity analysis of the Wiener gap

| Regularity of u₀ | Cosine decay | ∑\|c_k\| | ∑(1+k)\|c_k\| | In WA? |
|---|---|---|---|---|
| Continuous | O(1/log k) worst | may diverge | diverges | NO |
| Lipschitz (W^{1,∞}) | O(1/k) | ∑1/k diverges | diverges | NO |
| H¹ (∑k²\|c_k\|² < ∞) | varies | converges (CS) | may diverge | ℓ¹ only |
| H² (∑k⁴\|c_k\|² < ∞) | O(1/k²) | converges | converges | YES |
| C² + Neumann BC | O(1/k²) | converges | converges | YES |

**Key insight:** If `PaperPositiveInitialDatum` were strengthened to require
C² or H² regularity, the Wiener gap would close. The paper (Shen) assumes
u₀ ∈ W^{2,p}(Ω) (at least H² by Sobolev embedding), not merely continuous.
**This is a design decision for Xiang.**

### The closing plan (once Wiener gap is resolved)

Given a hypothesis `WienerDatumBounds p` providing:
- For each M > 0: uniform Wiener norm bound W(M) and floor bound δm(M)
- For each PPID datum bounded by M: Wiener lifting (continuous u₀ : ℝ → ℝ
  with floor δm, ℓ¹ summability, MemW, reconstruction)

The proof of `ChiNegDatumUniformConstructionStrong p`:
1. Compute uniform contraction constants from (W(M), δm(M), p)
2. Call `exists_uniform_EWA_lifespan` → uniform δ > 0
3. For each datum: write a "prescribed-T" version of the clean FP at δ
   (or: call the existing clean FP getting T ≥ δ, then Core.restrict to δ)
4. Per-datum v6 → Core on [0,δ]

### Alternative: bypass the EWA contraction entirely

The paper's proof uses Galerkin approximation + energy estimates, not
Fourier contraction. This avoids Wiener membership entirely but requires
massive new formalization infrastructure (finite-dimensional ODE systems,
Sobolev spaces, Aubin-Lions compactness). Not viable in this session.

## New files created (2026-07-03, NOT YET BUILT)

| File | Purpose | Sorry |
|------|---------|-------|
| `SourceVdFloorGeneric.lean` | Generic vdFloor for ANY EvenReal + floor | 0 |
| `SourceFixedPointEvenReal.lean` | Clean Banach FP, `0 < T` output | 0 |
| `SourceReducedCoreWireV6EvenReal.lean` | v6 Core, floor η ≠ lifespan T | 0 |
| `SourceChiNegPerDatumV6.lean` | Per-datum Core from clean FP + v6 | 0 |
| `SourceChiNegLocalExistence.lean` | Per-datum local existence → ClassicalSolution | 0 |
| `IntervalCoupledClassicalCoreRestrict.lean` | Core.restrict for time restriction | 0 |
| `IntervalDomainTheorem11CorePath.lean` | EWA-free: UniformCore → Theorem_1_1 | 0 |
| `SourceCleanFPConstants.lean` | Named defs + nonnegativity for FP constants | 0 |
| `SourceFixedPointEvenRealPrescribed.lean` | Prescribed-T clean FP with normBound | 0 |
| `SourceChiNegPerDatumPrescribed.lean` | Per-datum Core at prescribed T | 0 |
| `SourceChiNegUniformBridge.lean` | DatumWienerData → Theorem_1_1 | 0 |
| `SourceChiNegUniformCore.lean` | WienerLifting structure + packaging | 0 |

**TOTAL: 0 sorry across all 12 new files.** (Pending `lake build` verification.)

### Dependency graph (two paths to Theorem_1_1)

```
PATH A (per-datum, ∃ T):
  SourceVdFloorGeneric + SourceFixedPointEvenReal
    → SourceReducedCoreWireV6EvenReal → SourceChiNegPerDatumV6
      → SourceChiNegLocalExistence → (per-datum ClassicalSolution)

PATH B (uniform T*, via prescribed-T FP — ALL 0 SORRY):
  SourceCleanFPConstants (named defs + nonnegativity)
    → SourceFixedPointEvenRealPrescribed (Banach FP at given T)
      → SourceChiNegPerDatumPrescribed (FP + v6 → Core at T)
        → SourceChiNegUniformBridge (DatumWienerData → UniformCore)
          → IntervalDomainTheorem11CorePath (UniformCore → Thm_1_1)
            → theorem_1_1_of_datumWienerData

HYPOTHESIS: DatumWienerData (the Wiener membership gap)
```

### Remaining work to UNCONDITIONAL Theorem_1_1

1. **Build verification** — ALL new files need `lake build` (uisai1/2 down)
2. **Wiener membership gap** — THE sole remaining mathematical hypothesis.
   PPID (continuous + bounded + positive) does NOT guarantee Wiener algebra
   membership. Need either:
   (a) Strengthen `PaperPositiveInitialDatum` to require H² or C² regularity, OR
   (b) Prove that continuous bounded periodic functions with positive floor
       have ℓ¹ cosine coefficients (unlikely without regularity).
   **This is Xiang's design decision.**

## χ₀<0 Discharge Chain — v4 Complete (2026-07-02)

### Per-slice realization frontier: CLOSED by v4

The full per-slice realization frontier (blocker 1 from `SourceChiNegUncondFix.lean`)
is now internalized by `realSlice_reducedCore_wired_v4`. It eliminates 9 hypotheses
from v2 (11 from v1):

| Group | Hypothesis | Method |
|-------|-----------|--------|
| E | hcontChem, h_coeffChem | EWA eval bridge (`realSlice_hchemInv_of_L1ContOn`) |
| F | hlogNE0, hlogNE1 | constExtend surrogate (`realSlice_hlogInv_of_L1ContOn`) |
| G | Hv | L1ContOn Hv chain (`realSlice_Hv_full_of_L1ContOn`) |
| C | hclassReg | Assembly: htimeDeriv + hdecay + Hv + Hvpos → `realSlice_classicalRegularity_of_L1ContOn` |
| — | μc, νc, γc, hμc, Uc | No longer needed (chemInv bypass) |

**Files committed (NOT YET BUILT — uisai1/2 down):**
- `SourceResolverSummabilityDischarge.lean` — Groups E+F bypass theorems
- `ResolverSliceHvWiringL1.lean` — Group G Hv from L1ContOn (81f2c3ee)
- `SourceReducedCoreWireV2.lean` — v3+v4 chains + `slice_hasDerivAt_of_l1` non-private (aa806744)

### Remaining to Theorem_1_1

**Forward chain:** `ChiNegDatumUniformConstructionStrong p` → `chiNeg_theorem_1_1_of_strong` → `Theorem_1_1 intervalDomain p`.

To produce `ChiNegDatumUniformConstructionStrong p`, need to feed ALL
hypotheses of `realSlice_reducedCore_wired_v4` from EWA fixed point + initial datum.

#### v4 Hypothesis Audit (2026-07-03)

| # | Hypothesis | Producer | Status |
|---|-----------|----------|--------|
| **Picard framework** ||||
| 1 | hfix (fixed point identity) | `chiNegStrong_EWA_fixedPoint_of_floor` | LANDED (SourceChiNegUncondFix) |
| 2 | hself (self-map) | same | LANDED |
| 3 | hLipQ (chemFlux Lip) | same | LANDED |
| 4 | hLipG (growth Lip) | same | LANDED |
| 5 | hKnn, hK (contraction rate) | same | LANDED |
| 6 | hmem_star (ball membership) | same | LANDED |
| 7 | hρ', hρ'ρ, hT0 | framework bookkeeping | LANDED |
| **EWA tower inputs** ||||
| 8 | hsumR (ResolverSourceSummable) | `resolverSourceSummable_of_evenReal` | LANDED (SourceResolverSummabilityDischarge:150) |
| 9 | hgrad (gradient summability) | `resolverGradSummable_of_evenReal` | LANDED (SourceResolverSummabilityDischarge:239) |
| 10 | f, hf_cont | `sourceFn_continuous` | LANDED (SourceResolverSummabilityDischarge:347) |
| 11 | hf_nonneg | `sourceFn_nonneg` | LANDED (SourceResolverSummabilityDischarge:365) |
| 12 | hf_coeff | `sourceFn_coeff` | LANDED (SourceResolverSummabilityDischarge:375) |
| 13 | hf2 | `sourceFn_sq_summable` | LANDED (SourceResolverSummabilityDischarge:408) |
| 14 | h_flux_diff | `chemFluxLifted_differentiableAt_of_EWA` | LANDED (SourceResolverSummabilityDischarge:584) |
| 15 | h_src_cont_log | `wLog_continuous_of_floor` | LANDED (SourceResolverSummabilityDischarge:430) |
| **L1ContOn source data** ||||
| 16 | hchem_l1 | `chemDivSourceL1ContOn_of_EWA` | LANDED (SourceL1ContOnBridge:83) |
| 17 | hlog_l1 | `logisticSourceL1ContOn_of_EWA` | LANDED (SourceL1ContOnBridge:112) |
| 18 | hsumE (eigenvalue-ℓ¹) | `fullSourceCoeff_eigenvalueSummable_slab_of_chemReg` | LANDED but needs wiring (SourceFullCoeffSlabSummable:109) — reduces to chemDiv regularity package |
| **Initial datum** ||||
| 19 | u₀E, hδρ, hheat, hu_ball | `chiNegStrong_heatFloor_of_paperDatum` + Picard | LANDED |
| 20 | u₀cos, hu0bd, hsumc, hmem | cosine analysis of PPID datum | FRAMEWORK — standard spectral decomposition |
| 21 | hβpos, hαnn, hμle1 | parameter constraints | from `CM2Params` |
| 22 | hfloorδ, hfloor | `UniformFloor u_star δ'` | derived from Picard ball + heat floor |
| **Initial trace** ||||
| 23 | hrecon (cosine reconstruction) | initial datum cosine expansion | FRAMEWORK |
| 24 | hdefect (ℓ¹ defect summable) | DERIVABLE from hsumE + hsumc | CAN INTERNALIZE |
| 25 | htrace (defect → 0) | DERIVABLE from hsumc + L1ContOn + DCT | CAN INTERNALIZE |

**Summary:** ALL individual producers exist. `hdefect` and `htrace` (rows 24-25)
are NOT independent atoms — both are derivable:
- `hdefect`: `|defect_n| ≤ |fullSourceCoeff n| + |u₀cos n|`, both summable
  (first from `hsumE` via eigenvalue domination, second from `hsumc`)
- `htrace`: three terms all → 0 as t→0: heat term by DCT over `2|u₀cos n|`,
  Duhamel terms by `t · ∑ envelope_n → 0` from L1ContOn envelope

The remaining work is ASSEMBLY — writing the wiring theorem that:
1. Takes PPID datum + Picard fixed point
2. Calls each landed producer with the correct arguments
3. Derives `hdefect` and `htrace` from `hsumE` + `hsumc` + L1ContOn
4. Feeds the assembled hypotheses into `realSlice_reducedCore_wired_v4`
5. Returns `CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)`

This assembly instantiates `ChiNegDatumUniformConstructionStrong`.

**PID/PPID type gap: CLOSED** by `IntervalDomainTheorem11StrongPath.lean`.
The strong path (`chiNeg_theorem_1_1_of_strong`) takes
`ChiNegDatumUniformConstructionStrong p` (PPID) and produces
`Theorem_1_1 intervalDomain p` directly, bypassing the PID umbrella.

**Remaining blocker: Wiener algebra gap (blocker 3, NEW).**
`chiNegStrong_EWA_fixedPoint_of_floor` requires `hsumc : Summable (fun k =>
|cosineCoeffs u₀ k|)` and `hmem : MemW 1 (ofCosineCoeffs ...)` — the initial
datum must be in the Wiener algebra A(T). But `PaperPositiveInitialDatum` for
`intervalDomain` only requires `Continuous u₀ ∧ BddAbove (range |u₀|)` +
uniform floor. Not every continuous function has ℓ¹ summable cosine
coefficients.

Shen's paper assumes C² initial data (automatic Wiener algebra by IBP:
`|ĉₙ| ≤ C/n²` from double integration by parts). Possible resolutions:
  (a) Strengthen `intervalDomain.initialAdmissible` to include C² or Wiener
      algebra membership (changes `Theorem_1_1` statement — stronger hypothesis)
  (b) Approximation: approximate continuous u₀ by Wiener algebra functions,
      get solutions for each, pass to a limit (requires solution stability)
  (c) Use the heat semigroup: `heatEWA u₀E` is automatically in Wiener algebra
      even if u₀ is only continuous (heat kernel smooths). The issue is only
      in the `hrecon` / trace triple — the initial datum reconstruction.

This is a genuine formalization gap, not a wiring issue.

**Progress (2026-07-03):**
- **hdefect + htrace DISCHARGED** (0 sorry) — `SourceInitialTraceDischarge.lean`
  - Part 1: `fullSourceCoeff_sub_eq` (pointwise defect identity)
  - Part 2: `fullSourceCoeff_defect_summable_of_L1ContOn` (hdefect from L1ContOn)
  - Part 3: `fullSourceCoeff_trace_tendsto_of_L1ContOn` (htrace via Tannery DCT)
  - Also: `SourceTraceDefectDerivation.lean` — alternative hdefect via eigenvalue summability
- **v5 auto-assembly WRITTEN** (0 sorry) — `SourceReducedCoreWireV5Auto.lean`
  - `realSlice_reducedCore_wired_v5_auto`: takes only Picard framework + datum + floor,
    auto-derives ALL 15 spectral chain hypotheses, produces `CoupledDuhamelReducedClassicalCore`
  - Eliminates: hsumR, hgrad, f-family, flux/log regularity, L1ContOn, hsumE, hdefect, htrace

**Remaining work:**
1. ~~Resolve blocker 3 (Wiener algebra gap)~~ STILL OPEN (see analysis above)
2. ~~Prove defect/trace atoms from L1ContOn + hsumc~~ DONE
3. ~~Write v5 assembly wiring~~ DONE
4. ~~VdFloor generalization~~ DONE — `vdEWA_floor_of_evenReal` (NOT YET BUILT)
5. **NEW: EvenReal-restricted Banach fixed point** — modify the contraction
   mapping argument to work on `{u | EvenRealEWA u} ∩ closedBall(center, ρ)`.
   This eliminates `hVdFloor` as a carried hypothesis. Key steps:
   - Prove `EvenRealEWA` is a closed condition (limits of EvenReal are EvenReal)
   - Show the EvenReal closed ball is complete (closed subset of complete space)
   - Apply Banach with δv = 1 (from `vdEWA_floor_of_evenReal`)
   Estimated: ~150 lines (copy of `clean_fixedPoint` with the refined ball)
6. **Per-datum assembly** — wire PPID datum + Wiener membership + EvenReal
   fixed point → `CoupledDuhamelReducedClassicalCore` → `ChiNegDatumUniformConstructionStrong`
7. **Uniform Wiener norm bound for restarts** — solution slices at τ > 0 have
   Wiener norms bounded by a function of the initial Wiener norm and T.
   Needed for the UNIFORM construction (same δ for all data with |u₀| ≤ M).
   Restart data ARE in Wiener algebra via `cosineCoeff_summable_of_eigenvalue_summable`.

1. ~~**`hfp` — chemotaxis-inclusive Duhamel identity.**~~ RESOLVED.
   `SourceChiNegFaithful.lean` already implements the hfp-free route via
   `ChiNegDatumUniformConstructionFaithful`. The `LocalExistenceBypass.lean`
   parallel attempt was redundant and deleted.

2. **Continuation/restart factory over weak data.** The umbrella theorem chain
   (`RestartAndGlueWorks` → `IntervalDomainUniformLocalExistence` → multi-layer
   umbrella → `Theorem_1_1`) quantifies internally over `PositiveInitialDatum`
   (PID: positivity on open interior only). The EWA tower produces a factory over
   `PaperPositiveInitialDatum` (PPID: uniform positive floor on closed domain).

   **Mathematical fact:** PID ⊋ PPID. Every restart slice IS PPID (proved in
   `classicalSolution_slice_paperPositiveInitialDatum`), but the PID typing is
   hard-wired through ~8 deep layers of the umbrella. The cascade is too deep
   to refactor without build verification.

   **New theorem (2026-07-02):**
   `classicalSolution_slice_paperPositiveInitialDatum` in
   `IntervalDomainUniformContinuation.lean` — uses compactness of `Icc 0 1` +
   continuity + closed-domain positivity to produce the uniform floor `∃ η > 0,
   ∀ x, η ≤ u τ x`. This is the mathematical KEY that makes the refactor
   possible — every restart slice is PPID, so a PPID-typed factory suffices.

   **Resolution: PPID strong path (2026-07-03).**
   Instead of a deep PID→PPID cascade refactor (8+ files, ~100 changes, no
   build verification), a PURELY ADDITIVE new file was written:

   `IntervalDomainTheorem11StrongPath.lean` (~525 lines) provides:
   - §1: Private sup-norm helpers duplicated from MoserClosure (~60 lines,
     pure real analysis, inaccessible outside their defining file)
   - §2: `restartAndGlueWorks_ppid` — PPID-typed restart and glue. Close copy
     of the PID version with TWO changes: factory takes PPID, overlap
     uniqueness gets `.toPositive`
   - §3: `uniformLocalExistence_ppid` — PPID-typed uniform continuation from
     PPID quantitative local existence + restart + Lemma 3.1 sup-norm bound
   - §4: `reachableArbitrarilyLong_ppid` — PPID-typed iteration to arbitrary
     horizons
   - §5: `Theorem_1_1_intervalDomain_of_ppid_local_and_quant` — DIRECT proof
     of `Theorem_1_1 intervalDomain p` from PPID-typed `hlocal` + `hQuant`,
     bypassing the PID-typed `IntervalDomainGlobalSolutionExists` struct
   - §6: Wire to EWA construction:
     - `ChiNegDatumUniformConstructionPPID` — PPID-typed analogue of
       `ChiNegDatumUniformConstructionFaithful` (returns solutions, not EWA objects)
     - `localExistence_of_ppid_quant` — derives `hlocal` from `hQuant`
       (any PPID datum: extract bound M → apply factory → get solution)
     - `chiNeg_theorem_1_1_ppid` — single-input route: PPID factory → Theorem_1_1
     - `ppid_of_strong` — bridges `ChiNegDatumUniformConstructionStrong` (PPID,
       returns EWA objects) to `ChiNegDatumUniformConstructionPPID` (PPID, returns
       solutions) via the regularity bootstrap
     - `chiNeg_theorem_1_1_of_strong` — **HEADLINE**: Strong PPID construction →
       `Theorem_1_1 intervalDomain p`

   **Key architectural insight:** `ChiNegDatumUniformConstructionFaithful` (PID)
   is **unsatisfiable** from the EWA tower — the Picard engine needs a uniform
   positive floor (`∀ y, η ≤ u₀ y`) that PID data cannot supply. The tower CAN
   fill `ChiNegDatumUniformConstructionStrong` (PPID). This file connects Strong
   directly to `Theorem_1_1`, bypassing the entire PID-typed umbrella chain.

   The complete forward chain is:
   ```
   ChiNegDatumUniformConstructionStrong p  (EWA tower output, PPID)
   → ppid_of_strong                        (regularity bootstrap unwrap)
   → ChiNegDatumUniformConstructionPPID p  (solutions, PPID)
   → localExistence_of_ppid_quant          (hlocal derived from hQuant)
   → reachableArbitrarilyLong_ppid         (PPID iteration)
   → GlobalSolutionGluingFromReachability  (PID via .toPositive, already proved)
   → Theorem_1_1 intervalDomain p          (PPID quantifier matches)
   ```

   No existing files are modified. The PID umbrella chain still exists but is
   dead code for the χ₀<0 track.

   **Status: written, NOT yet built (uisai1/2 down).** Need to build-verify
   before the file is considered landed.

### Key architectural finding

`hcontChem` (chemDiv continuity on `intervalDomainPoint`, including endpoints)
is likely FALSE — the chemDiv lift is discontinuous at {0,1} (confirmed by
`SourceRealizesRecords.lean:184-185`). The existing route
`realSlice_hchemInv_direct` required it via `constExtend_continuous`. The EWA
eval bridge approach avoids this entirely.

## CURRENT STATE (2026-07-02, code-derived)

Authoritative checks from the current tree:
- Proof-hole scan: no proof-level `sorry`, `admit`, `native_decide`, or custom
  `axiom`/`constant` declaration remains under `ShenWork/**/*.lean`.  The
  current proof-level `sorry` scan and the uncommented `admit`/`native_decide`/
  custom-declaration scans all return no hits.
- Last full remote build: after adding the Paper2 structured-Moser and
  actual-atom Proposition 2.5 frontiers, the common-free actual-atom
  Corollary 2.1 / Proposition 2.5 headline route, the mass-gradient reduction
  of the relative-Moser atom, the terminal-endpoint reduction of the
  quantitative endpoint atom, the raw-drop reduction of the nonnegative-B
  Moser dissipation atom, the common-free actual-atom full-statement route
  with explicit or solution-slice-produced a-priori frontiers, the Paper1
  positive upper-contact / Route-A direct remaining-contact refinements, and
  the Paper2/Paper3 integrated-Moser step-consumer closure layer, the
  fixed-interval integrated relative-Moser time-integral bridge, the
  integrated-Moser precrossing/window and high-excursion contradiction
  frontier plumbing, the Paper2 statement-level integrated-step and
  lower/upper split wrappers, and the reusable Paper3/PDE integrated-step and
  lower/upper split mass/Lp/smoothing residual packages,
  `lake build ShenWork` completed successfully on
  `uisai2:/dev/shm/shen_verify`, **8985 jobs**.  Target builds for
  `ShenWork.PDE.P3MoserIntegratedClosure`,
  `ShenWork.PDE.P3MoserActualWiring`, and
  `ShenWork.PDE.IntervalDomainMoserLadderAtoms`,
  `ShenWork.Paper2.IntervalDomainStatementAssembly`, and
  `ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` also completed
  successfully.  The Paper2/Paper3 wrappers and integrated-Moser bridge
  theorems have `#print axioms` output
  `[propext, Classical.choice, Quot.sound]`.
- The 2026-06-28 note below claiming "Paper 2 χ₀<0: 42 sorry" is stale; the
  repo no longer has proof-level `sorry`.
- Current target verification: after wiring the integrated-Moser data frontier
  through `P3MoserRegularityProducer`,
  `IntervalDomainMoserLadderAtoms`, and
  `Paper2.IntervalDomainStatementAssembly`, the remote uisai2 target build
  `lake build ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly` completed successfully
  (3749 jobs).  `P3MoserEnergyContinuity` also builds on uisai2 (3558 jobs).
  The new integrated-Moser wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
  The PDE/Paper3 compatibility-surface cleanup also builds on uisai2 via
  `lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` (8573 jobs).
- The obsolete PDE-level
  `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`
  compatibility package has been removed.  The Paper3 compatibility-named
  lowerAverage/upperDataGap route now converts only to the integrated-step
  actual-linear route; the old PDE converter is no longer a live source
  surface.
- `IntervalDomainMoserLadderAtoms` now exposes direct Corollary 2.1 and
  Proposition 2.5 consumers for
  `IntervalDomainMassLpSmoothingIntegratedMoserResiduals`,
  `IntervalDomainMassLpSmoothingWindowFrontierResiduals`, and
  `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals`.  These are
  additive wrappers through the existing integrated-step route; no new
  mathematical input fields were introduced.
- `Paper3.IntervalDomainActualLinearStatementAssembly` now exposes the properly
  named direct threshold-plan surface
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals`
  and its sectorial / Stability24 / P2-main statement wrappers.  This route
  consumes classical integrated-Moser regularity, integrated dissipation, and
  relative interpolation directly, then converts through the existing
  integrated-step actual-linear route.  The older compatibility-named
  lowerAverage/upperDataGap route remains only as a compatibility surface.
- The same Paper3 actual-linear file now exposes a named regular-energy
  coefficient-gap Stability24/P2-main statement surface:
  `IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData`,
  `IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData`,
  and the no-negative-sensitivity variant.  These are pure wrappers through the
  existing integrated-step Stability24 route; no new analytic fields were
  introduced.  The uisai2 target build
  `lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly`
  completed successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- The FTC-local-data, derivative-window, and derivative-boundary
  regular-energy coefficient-gap Paper3 routes now have direct
  Stability24/P2-main statement surfaces, including
  `IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData`,
  the corresponding P2-main statement packages such as
  `IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData`
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData`,
  and their no-negative-sensitivity variants.  These are pure wrappers through
  the existing FTC-local-data / derivative-window / derivative-boundary facts
  and the regular-energy coefficient-gap Stability24 route; no analytic
  residual fields were added.  The uisai2 target build
  `lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly`
  completed successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- The derivative-boundary regular-energy coefficient-gap route also has a thin
  sup-norm compactness / Stability24 P2-main statement surface:
  `IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryThinFrontierData`,
  `IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryThinP2MainData`,
  and the no-negative-sensitivity variant.  It routes through the existing
  derivative-boundary facts and integrated-step thin route, so it adds no new
  analytic residual fields.  The uisai2 target build
  `lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly`
  completed successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- The four legacy first-crossing shortcut theorems in
  `P3MoserRegularityProducer` that still accepted lower-average / upper-gap
  frontier parameters after their proof bodies had switched to the direct
  threshold-plan route have been removed.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs).
- `P3MoserIntegratedClosure` now exposes
  `intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap`,
  the fixed `theta = 2` wrapper from the regular-energy coefficient-gap route
  to the public `IntegratedMoserDissipationDropBefore` predicate.  The uisai2
  target build `lake build ShenWork.PDE.P3MoserIntegratedClosure
  ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs).
- `P3MoserRegularityProducer` now exposes
  `intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap`,
  an additive direct first-crossing wrapper from classical regularity data,
  strict-time bootstrap energy, window FTC, relative interpolation, and the
  fixed coefficient-gap condition.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrapper prints only
  `[propext, Classical.choice, Quot.sound]`.
- `Paper2.IntervalDomainStatementAssembly` now exposes
  `IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData`, an additive
  Prop-valued statement surface converting classical regularity, window FTC,
  relative interpolation, and the fixed regular-energy coefficient gap into the
  existing integrated-step Proposition 2.5 / Corollary 2.1 route.  The uisai2
  target build `lake build ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- `IntervalDomainMoserLadderAtoms` now exposes
  `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals`, the
  mass/Lp/smoothing residual analogue of the fixed regular-energy
  coefficient-gap route.  It converts to the existing integrated-step residual
  package and therefore to Corollary 2.1, Proposition 2.5, route residuals, and
  the a-priori bound without using the lower/upper high-excursion split.  The
  uisai2 target build `lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- `P3MoserEnergyContinuity` now exposes the local FTC split
  `IntervalDomainIntegratedMoserEnergyWindowFTCLocalData` and the wrapper
  `intervalDomain_integratedMoserEnergyWindowFTC_of_localData`, reducing the
  abstract `IntegratedMoserEnergyWindowFTC` package to endpoint power-energy
  continuity plus derivative-window integrability.  It also exposes
  `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData`, whose
  explicit residuals are the left-endpoint power-energy continuity field and
  combined PDE initial-window integrability.  `IntervalDomainMoserLadderAtoms`
  now exposes
  `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals`,
  replacing the monolithic `energyWindowFTC` field in the regular-energy
  coefficient-gap route by this local FTC data while preserving the existing
  Corollary 2.1 / Proposition 2.5 / route / a-priori consumers.  The uisai2
  target build `lake build ShenWork.PDE.P3MoserEnergyContinuity
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- `Paper2.IntervalDomainStatementAssembly` now exposes
  `IntervalDomainPaper2Prop25RegularEnergyCoeffGapFTCLocalDataFrontierData`,
  the statement-layer analogue of the local-FTC-data coefficient-gap route.
  It converts to the existing regular-energy coefficient-gap Prop 2.5 /
  Corollary 2.1 route and adds direct Proposition 2.5, Corollary 2.1,
  combined Tier-1, and thin section-2 bootstrap target wrappers.  The uisai2
  target build `lake build ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- `Paper3.IntervalDomainActualLinearStatementAssembly` now exposes
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals`
  and
  `IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts`,
  the actual-linear-small compatibility versions of the local-FTC-data
  coefficient-gap route.  They collapse to the existing regular-energy
  coefficient-gap actual-linear residual/facts, then reuse the integrated-step
  and a-priori mainline consumers.  The uisai2 target build
  `lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly`
  completed successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- The regular-energy coefficient-gap route now has a thinner
  derivative-window surface.  `P3MoserRegularityProducer` exposes
  `intervalDomain_firstCrossingStep_of_classicalRegularityData_coeffGap_derivWindow`,
  which builds the energy-window FTC from
  `classicalRegularity.endpointEnergy` plus
  `IntegratedMoserEnergyDerivativeWindowIntegrability`.  The PDE, Paper2, and
  Paper3 statement layers expose the matching
  `...RegularEnergyCoeffGapDerivativeWindow...` residual/frontier/facts
  packages, converting through the local-FTC-data surfaces without duplicating
  endpoint continuity as a separate residual.  This is still conditional on the
  derivative-window integrability frontier.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- The derivative-window route also has a boundary-split surface landed in
  `98b22ba5`: `P3MoserEnergyContinuity` proves the derivative-window
  integrability wrapper from explicit endpoint/boundary data, and the PDE,
  Paper2, and Paper3 layers expose matching
  `...RegularEnergyCoeffGapDerivativeBoundary...` residual/frontier/facts
  packages.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserEnergyContinuity
  ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs), and the new wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
- `P3MoserAgmonDirectRoute` keeps the existing Agmon route conditional on the
  explicit `MoserDissipationDropBeforeNonnegB` frontier.  The no-drop
  Gronwall shortcut is not exported: `AgmonAbsorbedInterpolationBefore` alone
  does not carry closed-time Lp-energy continuity, right-derivative data, an
  initial-energy bound, or the resulting scalar differential inequality at
  each exponent.  The target build
  `lake build ShenWork.PDE.P3MoserAgmonDirectRoute` completed successfully
  (3561 jobs after the stale shortcut removal), and the Agmon bootstrap /
  Proposition 2.5 axiom audits print only
  `[propext, Classical.choice, Quot.sound]`.
- `P3MoserIntegratedClosure` now exposes direct all-exponent and
  finite-horizon boundedness consumers for the high-excursion
  `windowFrontier`, split `lowerUpperFrontiers`, preferred
  `lowerAverageUpperDataGapData`, and legacy `lowerAverageEpsilonData`
  packages.  These are pure wrappers through the existing
  `IntegratedMoserFirstCrossingStep` closure and the quantitative endpoint; no
  new analytic residual fields were introduced.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserIntegratedClosure` completed successfully
  (3557 jobs), and the new consumer axiom audits print only
  `[propext, Classical.choice, Quot.sound]`.
- The same integrated-Moser closure layer now also exposes direct arithmetic
  ladder-chain consumers for the same four frontier/data packages:
  `moser_iteration_chain_of_windowFrontier`,
  `moser_iteration_chain_of_lowerUpperFrontiers`,
  `moser_iteration_chain_of_lowerAverageUpperDataGapData`, and
  `moser_iteration_chain_of_lowerAverageEpsilonData`.  These are pure
  wrappers through `moser_iteration_chain_of_integrated_first_crossing_step`;
  no new analytic residual fields were introduced.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserIntegratedClosure` completed successfully
  (3557 jobs), and the new chain axiom audits print only
  `[propext, Classical.choice, Quot.sound]`.
- `P3MoserIntegratedClosure` also exposes direct data-to-window-frontier
  conversions
  `integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageUpperDataGapData`
  and
  `integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageEpsilonData`;
  the corresponding step consumers now route through these window-frontier
  wrappers.  This is pure interface plumbing for downstream producers, with no
  new analytic residual fields.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserIntegratedClosure` completed successfully
  (3557 jobs), and the new conversion axiom audits print only
  `[propext, Classical.choice, Quot.sound]`.
- `Paper2.IntervalDomainStatementAssembly` now exposes the statement-layer
  preferred lower-average / upper-data-gap route
  `IntervalDomainPaper2Prop25LowerAverageUpperDataGapFrontierData`, converting
  `Nonempty IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` through
  the existing lower/upper split and integrated-step routes.  It adds direct
  Proposition 2.5, Corollary 2.1, combined Tier-1, and thin section-2 target
  wrappers, without restoring the obsolete PDE-level
  `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals` surface.
  The uisai2 target build
  `lake build ShenWork.Paper2.IntervalDomainStatementAssembly` completed
  successfully (3745 jobs), and the new statement wrapper axiom audits print
  only `[propext, Classical.choice, Quot.sound]`.
- New integrated-Moser closure status: `P3MoserIntegratedClosure` has the
  coefficient-gap surplus wrapper
  `integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality_coeffGap`.
  `P3MoserEnergyContinuity` proves strict-window derivative integrability of
  interval-domain Moser energies from classical regularity, identifies positive
  global-time derivatives with the explicit
  `intervalDomainPowerEnergyDerivIntegral`, and reduces full closed-window FTC
  to endpoint energy continuity plus the honest left-endpoint residual
  `IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability`.
  That residual is now further reduced, under global classical positivity, to
  the weighted Lp time-term residual
  `IntervalDomainLpWeightedTimeTermInitialWindowIntegrability`, with direct
  consumer wrappers ending at
  `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm`.
  The weighted residual is further reduced to initial-window integrability of
  the single combined PDE-side scalar profile
  `q * intervalDomainLpDiffusionIntegral q u s -
    q * (params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s) +
    q * intervalDomainLpLogisticIntegral params q u s`, packaged as
  `IntervalDomainLpPDECombinedInitialWindowIntegrability` and consumed by
  `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined`.
  The stronger componentwise entry point is retained: initial-window
  integrability of the three PDE component profiles
  `intervalDomainLpDiffusionIntegral`,
  `intervalDomainLpChemotaxisIntegral`, and
  `intervalDomainLpLogisticIntegral`, packaged as
  `IntervalDomainLpPDETermInitialWindowIntegrability` and consumed by
  `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms`;
  `intervalDomain_lpPDECombinedInitialWindowIntegrability_of_terms` bridges the
  componentwise package to the combined package.  Conversely,
  `intervalDomain_lpPDECombinedInitialWindowIntegrability_of_weightedTimeTerm_initial`
  and `intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial`
  identify the weighted-time and combined-PDE initial residuals under global
  classical regularity, using only positive times.
  A separate positive-left-start/initial-edge split is now exposed by
  `IntervalDomainLpPDETermPositiveStartWindowIntegrability`,
  `IntervalDomainLpPDETermPositiveStartWindowContinuity`, and
  `intervalDomain_lpPDETermClosedWindowIntegrability_of_initial_and_positiveStart`;
  the logistic component of the positive-start continuity package is now
  produced from global classical regularity by
  `intervalDomain_lpLogisticIntegral_continuousOn_positiveStart_of_global_classical`,
  and
  `intervalDomain_lpPDETermPositiveStartWindowContinuity_of_diffusionChemotaxis_global_logistic`
  reduces the remaining positive-start continuity frontier to the diffusion
  and chemotaxis scalar profiles.  The remaining positive-start scalar
  continuity is further reduced by
  `IntervalDomainLpDiffusionChemotaxisPositiveStartIntegrandJointContinuity`
  and
  `intervalDomain_lpPDETermPositiveStartWindowContinuity_of_integrandJoint_global_logistic`
  to joint continuity of the two lifted diffusion/chemotaxis integrands on
  `[a,b] × [0,1]`.  Current APIs still do not produce the initial-edge
  combined PDE-profile integrability from `InitialTrace` or endpoint energy
  continuity alone.

Current headline status:
- Short audit table for the Paper1--Paper3 headline wrappers:

  | area | closed or internally produced | honest residual/frontier inputs | deprecated or no-go route |
  | --- | --- | --- | --- |
  | Paper 1 | Lemma 2.5/Jensen; negative construction upper bound is reduced to the scalar stationary strictness `U 0 < 1` in `ConstructionNegSMPProvider`; positive-branch `ShenUpperBoundPositive` is split through the pure strict-`MChi` barrier wrapper; lower-pinned plateau and raw traps now produce right-tail asymptotics by pure squeeze; the positive upper-barrier interface no-contact is discharged from differentiability/kink avoidance; the strict exponential contact residual is closed on the `p.m * kappa c ≤ 1` subregime; Route-A has an hmk-aware constant-left-plateau residual package that converts to the remaining-contact package; `positiveBranchTailCap` and `kappa_lt_positiveBranchTailCap` close the scalar cap/gap arithmetic; `Paper1PositiveLowerPinnedContactBranchData`, `Paper1PositiveLowerPinnedRawContactBranchData`, `Paper1PositiveLowerPinnedRawSmoothContactBranchData`, `Paper1PositiveLowerPinnedSchauderContactData`, and `Paper1PositiveLowerPinnedCapSchauderContactData` keep the lower-pinned witness through the positive route; `Paper1MainStatementSMPMainlineData`, `Paper1MainStatementStrictBarrierData`, `Paper1MainStatementLowerPinnedContactData`, `Paper1MainStatementLowerPinnedRawContactData`, `Paper1MainStatementLowerPinnedRawSmoothContactData`, `Paper1CombinedStrictBarrierStatementData`, `Paper1CombinedLowerPinnedContactStatementData`, `Paper1CombinedLowerPinnedRawContactStatementData`, and `Paper1CombinedLowerPinnedRawSmoothContactStatementData` are the thinner conditional statement routes | `Paper1MainResultsData`, `Paper1MainlineExistence`, proposition frontiers, Lemma 5.1/5.2 frontiers, positive construction lower-pinned cap Schauder/contact data, smooth-branch no-contact comparison outside the `hmκ` subregime, and fixed-point/stationarity/SMP inputs | tail-asymptotic identity wrappers from bare stationarity remain non-producers; the lower-pinned plateau/raw squeeze route is the active tail producer; `hmκ` is not implied by the base positive hypotheses |
  | Paper 2 | interval-domain Theorem 1.1 for `χ₀ = 0`; `χ₀ = 0` local existence in the local-free routes; Proposition 2.4 in the thin section-2 route; the preferred χ₀=0 headline routes produce Corollary 2.1 and Proposition 2.5 from actual Moser atoms, with mass-gradient, terminal-endpoint, raw-drop, and positive solution-slice variants; `IntervalDomainPaper2Prop25IntegratedMoserFrontierData` exposes the direct threshold-plan statement route from classical regularity, integrated dissipation, relative interpolation, and quantitative endpoint; `IntervalDomainPaper2Prop25IntegratedStepFrontierData` consumes a supplied integrated first-crossing step; `IntervalDomainPaper2Prop25LowerUpperFrontierData` remains the optional lower-average / upper-gap split route; `P3MoserIntegratedClosure` proves the routine Moser chain/all-exponent/endpoint consequences, fixed-interval integrated dissipation / relative-Moser time-integral bounds, precrossing-to-window upper-bound package, and high-excursion contradiction wrapper | finite-horizon alternative, actual Prop25 atoms where not reduced (raw pointwise Moser drop or nonnegative-B Moser dissipation, quantitative endpoint/root tower or terminal pointwise endpoint, mass-gradient relative data), integrated dissipation / relative interpolation / quantitative endpoint production from concrete PDE data, positive solution-slice interpolation or explicit `IntervalDomainPaper2AprioriTargets` for full statements, global extension, bootstrap/eventual-sup fields, and thin section-2 Lemma 2.6/2.7/Proposition 2.2/2.3 fields | routes carrying global `IntervalDomainInterpolation`, refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`; `OldUnitIntervalPowerGNYoungForMoser` is legacy/false for constants and should not feed new Moser routes; raw pointwise Moser drop and terminal endpoint production are still real atoms; the lower/upper split is no longer required for the direct integrated-step route |
  | Paper 3 | actual-linear-small Theorem 2.1 persistence; Proposition 1.3/1.4 can be routed through Paper2 Theorem 1.3/1.2 or Paper2 main targets; terminal pointwise endpoint now has a named quantitative-endpoint bridge; the actual-linear-small mainline has direct integrated-step, direct integrated-Moser, regular-energy coefficient-gap, derivative-window, derivative-boundary, and optional lower/upper split Moser routes; the reusable cores include `IntervalDomainMassLpSmoothingIntegratedStepResiduals`, `IntervalDomainMassLpSmoothingIntegratedMoserResiduals`, `IntervalDomainMassLpSmoothingWindowFrontierResiduals`, and `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals` in `IntervalDomainMoserLadderAtoms`; `IntervalDomainPaper3SupNormCompactnessRegularizationData` removes only the structural `upperEq` field by fixing the sup envelope; `IntervalDomainPaper3NegativeSensitivityFrontierData` decomposes `negativeBound` into global-solution and eventual-sup residuals | `negativeBound` or its decomposed global-solution/eventual-sup frontiers, production of integrated dissipation / relative interpolation / classical integrated-Moser regularity from concrete PDE data, terminal Moser inputs, spectral orbit, continuation/gluing, compactness/regularization, and stability frontiers | Paper2 Theorem 1.1 does not imply Paper3 Proposition 1.2 under the current API; see `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`; do not derive `MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore` from Corollary 2.1 |

  2026-07-05 H1 bypass update: `H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont`
  wires the direct H1 regularity bridge into the scalar differential inequality,
  `intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before`
  uses the existing 1D L2-window bypass with the local H1 start restricted to
  actual times `τ < T`, and
  `intervalDomain_boundedBefore_of_paperPositive_H1supBoundDI_local_before`
  lifts that restricted wrapper through `H1SupBoundDIDataBefore`.  The remaining
  honest carries for this route are still H1 scalar regularity/its
  `u_xx`-plus-derivative-integrability producer, the sup-bound DI data, and the
  restricted local H1 seed; the old unrestricted `τ ∈ Ioc 0 1` local seed should
  not be treated as the active target when `T < 1`.  The `u_xx` L1-continuity
  side now has a no-sorry scalar producer
  `H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore` from strict closed
  slab joint continuity of `liftDeriv2`; the remaining upstream carry is that
  joint continuity, not the L1 continuity argument itself.  The proof is now
  factored through the reusable scalar bound
  `intervalIntegral_norm_sub_le_of_pointwise_bound` and the fixed-slab helper
  `l1_time_continuity_at_of_jointContinuousOn_slab`.  Verified by remote full
  build on uisai2: 9140 jobs, `BUILD OK` (2026-07-05).
  Follow-up producer `IntervalChiNegH1DerivativeIntegrability` reduces the
  scalar derivative-integrability part to an explicit
  `H1IdentityRHSIntegrableBefore` package.  Its primary bounded-before wrapper
  is now
  `intervalDomain_boundedBefore_of_H1identityRHS_integrableRHS_local_before`,
  which consumes `H1IdentityRHSBoundBefore` directly; the
  `H1SupBoundDIDataBefore` wrapper is only a corollary through
  `H1IdentityRHSBoundBefore_of_supBoundDIData`.  It does not yet produce the
  identity/RHS-bound package or the restricted local H1 seed.
  Follow-up producer `IntervalChiNegH1SupBoundDIProducer` removes one
  bookkeeping layer by letting callers state the same pointwise sup-bound data
  with canonical square-root witnesses while keeping explicit
  `taxisX`/`uvxx`/`reactX` functions for the RHS-integrability package.  It
  also provides `H1SupBoundSqrtRHSIntegrableBefore`, a combined frontier package
  where those same functions feed both the sup-bound side and the
  RHS-integrability side.  An existential-only normalizer remains available for
  later pointwise estimates, but this still assumes the physical split estimates
  pointwise, so it is not a proof of the identity/RHS-bound package.
  Follow-up producer `IntervalChiNegH1RHSIntegrabilityProducer` reduces the
  explicit RHS-integrability package to closed-window continuity of the
  assembled RHS, with a component-continuity helper for `lapL2sq`, `taxisX`,
  `uvxx`, and `reactX`.  It does not prove those component continuity facts.
  Follow-up bridge `IntervalChiNegH1Bridge` factors out the shared
  `H1SqrtTermBoundsBefore` estimate package and adds route-specific wrappers
  from the parametric assembly inputs (`hpar`/`hsub`) and the spectral assembly
  inputs (`hParsevalGrad`/`hder`/`hval`) into
  `H1SupBoundSqrtRHSIntegrableBefore`.  This is only record assembly plus calls
  to `H1EnergyIdentity_of_parametric_and_IBP` or `H1EnergyIdentity_of_spectral`;
  it still carries the physical estimates and RHS interval-integrability as
  hypotheses.  The same bridge now also provides
  `H1IdentityRHSComponentsContinuousBefore` plus parametric/spectral
  component-continuity variants, replacing raw RHS interval-integrability by
  closed-window continuity of `lapL2sq`, `taxisX`, `uvxx`, and `reactX`.  This
  keeps strict-slab joint continuity of `liftDeriv2` and the actual physical
  estimates as explicit frontiers at the bridge layer.  The raw
  time-zero H1 continuity input is further reduced in
  `IntervalChiNegH1InitialContinuity`: deleted-right convergence of
  `H1energy u` to `H1InitialEnergy u₀` on `Ioc 0 T`, plus explicit
  zero-slice compatibility `H1energy u 0 = H1InitialEnergy u₀`, produces
  `ContinuousWithinAt (H1energy u) (Ici 0) 0` and the corresponding
  closed-window H1 continuity wrapper.  Positive-time trace data alone still
  does not identify the stored value `u 0`.  The follow-up wiring file
  `IntervalChiNegH1InitialWiring` threads this split endpoint package through
  the scalar-regularity, scalar-DI, and bounded-before H1 routes.  Downstream
  wrappers now carry `H1InitialTraceEnergyTendsto` plus
  `H1InitialEnergyCompatibleAtZero` instead of a raw `hcont0`.  The bridge
  follow-up `IntervalChiNegH1BridgeInitialWiring` does the same for the
  route-specific parametric/spectral H1 bridge packages, including the
  component-continuity variants.  Its current `_before` wrappers no longer
  require a manual restricted local H1 seed: scalar-DI local-start production is
  internal.  They still leave the route packages, strict-slab `liftDeriv2`
  continuity when required by the chosen route, and endpoint trace/compatibility
  as explicit inputs.

  Thus the tree is proof-hole-free, but most `...Data` / `...FrontierData`
  headline wrappers are conditional assembly interfaces, not no-assumption
  paper theorems.
- **Paper 1:** statement targets are still reduced to explicit frontier
  packages.  `Paper1MainResultsData` carries the full Theorem 1.1--1.3
  statement bridge; `Paper1MainlineExistence` carries the B5
  stability/uniqueness mainline.  For the B1 construction wrappers, the
  base-barrier Lipschitz condition is now derived from the Lemma 4.2 parameter
  conditions rather than carried as a separate floor field: current wrappers include
  `b1_chiNeg_existence_paper_clean_autoBar_of_cubeApproxData`,
  `b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData`,
  `b1_chiNeg_existence_paper_min_noBar_of_cubeApproxData`,
  `b1_chiPos_existence_paper_min_noBar_of_cubeApproxData`,
  `b1_chiNeg_existence_paper_min_core_noBar_of_cubeApproxData`,
  `b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData`, and
  `b1_chiNeg_existence_paper_routeA_core_noBar_of_cubeApproxData` /
  `b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData`.
  The Route-A producer residual also has thinner source-box parameter wrappers,
  `b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData` and
  `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData`, which
  replace the monolithic `PaperGreenStepInputRouteACore` input by explicit
  `PerStepBoxParams` / `PerStepBoxZWitness` / Route-A rest / lower-raw aux data.
  The negative construction's upper-bound slot also has a thinner statement
  route: `ConstructionNegSMPProvider` replaces the full carried
  `ShenUpperBoundNegative c U` field by the scalar stationary strictness
  `U 0 < 1` for each produced fixed point.  The wrappers
  `constructionNeg_of_lowerPinnedSchauderData_smp`,
  `constructionNeg_of_provider_smp`,
  `Theorem_1_1.of_constructionNeg_provider_smp`, and the statement-layer
  `paper1_Theorem_1_1_of_constructionNegSMPProvider` then derive the strict
  upper bound from `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple`.
  On the positive construction branch, `ShenUpperBoundPositive` now has the
  pure `MChi` normalization bridge
  `ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi`, and
  `Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch` /
  `Paper1MainStatementStrictBarrierData` expose the upper-bound frontier as
  the stricter analytic comparison
  `∀ x, U x < upperBarrier (kappa c) (MChi p) x`.  The further
  `Paper1PositiveCriticalFrozenStationaryContactBranch` route splits that
  comparison into the non-strict monotone trap bound plus local no-contact
  facts on the constant branch, exponential branch, and interface of the
  nonsmooth upper barrier.  `Paper1PositiveLowerPinnedContactBranchData` keeps
  the produced profile's `InLowerPinnedMonotoneTrap` witness and rate cover, so
  the tail field of the contact branch is discharged by the pure squeeze
  theorem rather than carried.  `Paper1PositiveLowerPinnedSchauderContactData`
  is the corresponding lower-pinned fixed-point route through
  `b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin`
  with `M = MChi p`; despite the name of that reusable theorem, the wrapper is
  sign-agnostic in `p` and the positive assumptions are carried at the
  statement layer.  The scalar branch ceiling is named
  `positiveBranchTailCap`; `kappa_lt_positiveBranchTailCap` proves
  `kappa c < positiveBranchTailCap p c` for `2 < c`, so the cap-specialized
  route `Paper1PositiveLowerPinnedCapSchauderContactData` can set
  `κtilde = positiveBranchTailCap p c` and discharge both the lower-barrier
  gap and rate-cover fields by pure arithmetic.  The current Route-A
  lower-pinned producers expose a raw lower-barrier pin rather than the plateau
  pin, and this is now matched by `Paper1PositiveLowerPinnedRawContactBranchData`
  plus the statement-level `Paper1MainStatementLowerPinnedRawContactData` and
  `Paper1CombinedLowerPinnedRawContactStatementData` routes.  `UpperBarrierContact`
  further splits `PositiveUpperBarrierContactContradictions` into the residual
  `PositiveUpperBarrierSmoothBranchNoContact` plus the closed theorem
  `positiveUpperBarrier_interfaceNoContact_of_regular_stationary`, reusing
  `maxSub_upperBarrier_ne_interface` and the C² regularity frontier.  It also
  proves the exponential-branch operator comparison directly as
  `positiveUpperBarrier_expOperatorCompareAtContact_of_regular_stationary`.
  The surviving smooth residual is now
  `PositiveUpperBarrierRemainingContactResidual`: the generic wrapper still has
  a `no_const_left_plateau` field, but `UpperBarrierContact` proves this field
  from `FrozenStationaryWaveProfile.lim_neg_inf.1` once `0 < p.χ < 1`, via
  `MChi_ne_one_of_chi_pos_lt_one`.  The thinner
  `PositiveUpperBarrierExpStrictContactResidual` therefore leaves only the
  strict exponential superbarrier residual at contact on that profile route.
  `Statements` now proves the strict positive exponential-region operator
  estimate as `frozenWaveOperator_exp_neg_of_chi_nonneg` and
  `frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg`; with the
  standard scalar side condition `p.m * kappa c ≤ 1`, `UpperBarrierContact`
  packages this as
  `positiveUpperBarrier_expStrictSuperAtContact_of_positive_region`,
  `PositiveUpperBarrierConstLeftPlateauResidual.of_profile_chi_pos`,
  `PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion`,
  `PositiveUpperBarrierRemainingContactResidual.of_positive_region_profile_chi_pos`,
  `positiveUpperBarrierSmoothBranchNoContact_of_positive_region_profile_chi_pos`,
  and
  `PositiveUpperBarrierContactContradictions.of_profile_chi_pos_hmk_regularStationary`.
  This `hmκ` condition is a genuine extra scalar frontier, not a consequence of
  the base positive branch hypotheses: the repo contains
  `not_Lemma_4_1_positive_hypotheses_force_m_kappa_le_one`.
  The direct bridge
  `positiveUpperBarrierSmoothBranchNoContact_of_expStrict_profile_chi_pos`
  closes smooth no-contact from this thinner residual, and
  `PositiveUpperBarrierContactContradictions.of_expStrict_profile_chi_pos_regularStationary`
  closes the full contact package once `0 < kappa c` and regular stationary
  data are present.
  The corresponding raw
  smooth-contact and remaining-contact statement routes are
  `Paper1PositiveLowerPinnedRawSmoothContactBranchData`,
  `Paper1MainStatementLowerPinnedRawSmoothContactData`, and
  `Paper1CombinedLowerPinnedRawSmoothContactStatementData`, plus
  `Paper1PositiveLowerPinnedRawRemainingContactBranchData`,
  `Paper1MainStatementLowerPinnedRawRemainingContactData`, and
  `Paper1CombinedLowerPinnedRawRemainingContactStatementData`.  `PositiveRawRouteAAssembly`
  specializes the exact Lemma 4.2 parameter conditions to
  `positiveBranchTailCap` and wires `Paper1PositiveLowerRawCapRouteAParamData`
  / `Paper1PositiveLowerRawCapRouteASmoothParamData` /
  `Paper1PositiveLowerRawCapRouteARemainingParamData` into those raw-contact,
  raw smooth-contact, and remaining-contact interfaces.  On the `hmκ`
  subregime, `Paper1PositiveLowerRawCapRouteAHmkConstParamData` carries only
  `PositiveUpperBarrierConstLeftPlateauResidual` plus the scalar
  `p.m * kappa c ≤ 1`; `paper1_routeARemainingParamData_of_routeAHmkConstParamData`
  converts it back into the existing remaining-contact route, and
  `paper1_positiveRawRemainingContactData_of_routeARemainingParamData` /
  `paper1_positiveRawRemainingContactData_of_routeAHmkConstParamData`
  now wire Route-A remaining-contact and hmk-aware constant-branch data
  directly to `Paper1PositiveLowerPinnedRawRemainingContactBranchData`.
  The statement wrappers
  `paper1_mainStatementTargets_of_routeARemainingParamData`,
  `paper1_mainStatementTargets_of_routeAHmkConstParamData`,
  `paper1_combinedStatementTargets_of_routeARemainingParamData`, and
  `paper1_combinedStatementTargets_of_routeAHmkConstParamData`
  route the same data directly to Paper1 main/combined statement targets.
  Separately,
  `paper1_positiveRawSmoothContactData_of_routeAHmkConstParamData`,
  `paper1_positiveContactBranch_of_routeAHmkConstParamData`, and
  `paper1_positiveStrictBarrierBranch_of_routeAHmkConstParamData` reuse the
  downstream wrappers.  The remaining positive residuals are the
  Route-A/Schauder analytic data themselves: lower-pin preservation by the
  positive map, map/compactness data, stationarity/flat-left inputs, C²
  regularity data, and either the strict exponential superbarrier at contact or
  the scalar `hmκ` plus constant-left-plateau route above.  The
  no-left-plateau input is no longer separate on profile routes with
  `0 < p.χ < 1`.  The right-tail
  asymptotic itself now has
  the pure lower-pinned squeeze producers
  `HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap` and
  `HasWaveRightTailAsymptotic_of_lowerPinnedRawMonotoneTrap`, with
  `lowerPinnedMonotoneTrap_tail_family_for_branch` and
  `lowerPinnedRawMonotoneTrap_tail_family_for_branch` covering the full branch
  interval once the lower-barrier exponent dominates the branch ceiling.
- **Paper 2:** `intervalDomain_theorem_1_1_chiZero_unconditional` proves
  Theorem 1.1 on the interval for χ₀ = 0.  This producer is now wired through
  `IntervalDomainStatementAssembly` as
  `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` and through the
  `χ₀ = 0` main/local+main/statement-target bundles; those routes carry no
  Theorem 1.1 half-step frontier package, though they still carry the
  independent Proposition 1.1 / Theorem 1.2 / Theorem 1.3 frontiers where
  applicable.  The `χ₀ = 0` Proposition 1.1 route now also has thin wrappers
  `IntervalDomainPaper2Proposition11ChiZeroFrontierData`,
  `IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData`, and
  `IntervalDomainPaper2StatementChiZeroThinFrontierData`: these discharge the
  local-existence field from `intervalDomain_localExistence_chiZero_unconditional`,
  so Proposition 1.1 only carries the independent finite-horizon alternative in
  that regime.  The Theorem 1.2/1.3 part of the `χ₀ = 0` route also has a
  thinner interpolation-positive statement route:
  `IntervalDomainPaper2Theorem12And13InterpolationFrontierData`,
  `IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData`,
  `IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData`, and
  `IntervalDomainPaper2StatementChiZeroInterpolationFrontierData`.  These
  wrappers remove the old carried `SemigroupEstimateData` / Lemma 2.1 / Lemma
  2.6 / Lemma 4.1 / Corollary 2.1 theorem fields from the main Theorem 1.2/1.3
  route, replacing them by explicit interpolation, energy, gradient-chain,
  mass-control, power-integrability, branch-bootstrap, and eventual sup-norm
  frontiers.  That interpolation route is not a valid discharge target as it
  stands: the current `IntervalDomainInterpolation` statement is known false
  as literally stated
  (`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`),
  so any package containing it is a vacuous conditional until the statement is
  repaired.  The current preferred χ₀=0 headline and full-statement route
  avoids that false global premise by using
  `IntervalDomainClassicalSolutionPositiveInterpolation`, a solution-slice
  mass-gradient interpolation residual with the positive constant needed by
  Lemma 4.1.  It proves Lemma 4.1 via
  `Lemma_4_1_intervalDomain_of_solution_interpolation_frontier`, drops the
  positive-constant field for Corollary 2.1 via
  `IntervalDomainClassicalSolutionInterpolation_of_positive`, and is exposed
  by
  `IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData`,
  `IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationFrontierData`,
  `IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData`,
  and
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationFrontierData`.
  The same positive solution-slice route now also has H2-source and
  logistic-source main/local+main/full-statement wrappers:
  `IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationFrontierData`
  and
  `IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationFrontierData`
  are the full-statement entry points.  The full-statement routes now also
  have thinner bootstrap variants,
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationBootstrapFrontierData`,
  `IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationBootstrapFrontierData`,
  and
  `IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationBootstrapFrontierData`.
  These replace the carried `IntervalDomainPaper2Corollary21FrontierData`
  field by the smaller `Paper2BootstrapEstimateBranchData`; Corollary 2.1 is
  produced from the nested positive solution-slice common data.  There is now a
  further section-2-thin variant for each of these routes,
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinFrontierData`,
  `IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationSection2ThinFrontierData`,
  and
  `IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationSection2ThinFrontierData`.
  These replace the full `Paper2BootstrapEstimateBranchData` by
  `IntervalDomainPaper2BootstrapEstimateThinFrontierData`, keeping only the
  Lemma 2.6 / Lemma 2.7 / Proposition 2.2 / Proposition 2.3 branch frontiers;
  Proposition 2.4 comes from the proved interval-domain mass estimate
  `intervalDomain_Proposition_2_4`, and Proposition 2.5 comes from the nested
  Theorem 1.2/1.3 data.  This is still conditional, but no longer rests on the
  step-function counterexample premise, including in the full statement-target
  wrappers.  The preferred `χ₀ = 0` positive solution-slice route now also has
  a local-existence-free version,
  `IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData`,
  with main/local/full-statement wrappers ending at
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
  These remove the Theorem 1.2/1.3 `localExistence` field in the `χ₀ = 0`
  route by inserting `intervalDomain_localExistence_chiZero_unconditional`;
  the remaining full-statement residuals are the finite-horizon alternative,
  positive solution-slice interpolation/energy/global-extension/bootstrap and
  eventual sup-bound frontiers, plus the section-2 thin fields.
  The preferred headline-only route for Theorems 1.1--1.3 is now named by the
  common-free actual-atom route
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData`.
  It excludes Proposition 1.1 and section-2 target fields from headline
  accounting, produces both `Corollary_2_1` and `Proposition_2_5` from the
  same actual Moser atom package, and carries no `cGrad` parameter.  The older
  `IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData` and
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomFrontierData`
  remain as compatibility routes through the positive solution-slice common
  data.  Proposition 2.5 itself is split two ways:
  `IntervalDomainPaper2Prop25StructuredMoserFrontierData` exposes the existing
  structured-Moser producer with explicit `pSeq`/`rootBound`, energy,
  dissipation, relative interpolation, power-integrability, and endpoint
  fields; `IntervalDomainPaper2Prop25ActualAtomFrontierData` is the smaller
  preferred route through
  `intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`, carrying only
  nonnegative-B Moser dissipation, relative Moser interpolation, and the
  quantitative endpoint/root-tower producer.  The further
  `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData` route proves
  the relative-Moser atom from
  `intervalDomain_relativeMoserInterpolationBefore_of_massGradient`; its
  inputs are an `LpMassGradientInterpolationEstimate`, the gradient-chain
  comparison, a positive `cGrad`, and
  `MoserMassPowerToCurrentLpLowerOrder`.  It still honestly carries
  nonnegative-B Moser dissipation and the quantitative endpoint.  The
  corresponding thin section-2 wrappers are
  `intervalDomainPaper2_bootstrapEstimateTargets_of_thinStructuredMoserFrontierData`
  and
  `intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData`,
  with
  `intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomMassGradientFrontierData`
  for the mass-gradient relative-Moser route;
  the preferred full-statement wrappers are
  `intervalDomainPaper2_preferredChiZeroStatementTargets_of_structuredMoserFrontierData`
  and
  `intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData`.
  The matching full-statement actual-atom routes are
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomCor21FrontierData`
  and
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientCor21FrontierData`.
  These use the common-free actual-atom path for section 2 and local+main
  theorem accounting, while keeping `IntervalDomainPaper2AprioriTargets` as an
  explicit independent field.  This is intentional: the current actual-atom
  Moser package does not prove Lemma 4.1.  The solution-interpolation variants
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomCor21SolutionInterpolationFrontierData`
  and
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientCor21SolutionInterpolationFrontierData`
  replace that explicit a-priori field by the existing positive solution-slice
  interpolation producer.  The terminal-endpoint mass-gradient route
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData`
  additionally replaces the endpoint `pSeq` / `rootBound` tower atom by one
  terminal `IntervalDomainMoserPointwisePowerControlBefore` estimate and
  rebuilds the old endpoint shape with constant sequences.  The raw-drop
  terminal route
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData`
  and its full-statement counterpart
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomRawDropMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData`
  additionally replace the black-box `MoserDissipationDropBeforeNonnegB`
  field by raw physical pointwise drop data, using the proved bridge
  `moserDissipationDropBeforeNonnegB_of_raw_drop`.  New headline work
  should not use
  `OldUnitIntervalPowerGNYoungForMoser` or the refuted global
  `IntervalDomainInterpolation` premise; the current code also records that
  abstract `MoserDissipationDropBeforeNonnegB` is false on a unit-linear-drop
  counterexample.  The new `P3MoserIntegratedClosure` module now proves the
  routine Moser chain, all-exponent, and quantitative-endpoint consequences
  from a supplied `IntegratedMoserFirstCrossingStep`.  It also packages the
  fixed-interval algebra needed on the faithful integrated route:
  `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`,
  `intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound`,
  `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound`,
  `intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on`,
  `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound`, and
  `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`.
  It also adds the honest precrossing/window layer:
  `IntegratedMoserPrecrossingIntervalData`,
  `integratedMoserPrecrossingIntervalData_of_regular_window`,
  `IntegratedMoserWindowUpperBoundData`, and
  `integratedMoser_windowUpperBoundData_of_precrossing` package regularity,
  energy nonnegativity, a current-exponent Icc bound, integrated dissipation,
  and relative interpolation into a fixed-window upper bound.  The auxiliary
  `IntegratedMoserWindowUpperBoundWitness` exposes the actual `Gbound`/`Ceps`
  witnesses so that a later strict lower-average gap is tied to the same
  fixed-window estimate, not to arbitrary larger witnesses.  The new
  `IntegratedMoserHighExcursionContradictionWindowFrontier` and
  `integratedMoserFirstCrossingStep_of_windowFrontier` then isolate the pure
  contradiction step from a high pointwise excursion to the supplied one-step
  Moser predicate.  The next producer split is now named as well:
  `IntegratedMoserHighExcursionLowerAverageWindowFrontier` is the
  thickness/modulus lower-average frontier, while
  `IntegratedMoserWindowUpperGapWitnessFrontier` is the quantitative
  `eps`/`Ceps` upper-gap frontier.  The preferred strict-gap interface is now
  `IntegratedMoserWindowUpperDataGapFrontier`: it receives the proved
  fixed-window upper-bound data producer and only has to close the gap for one
  selected actual witness, avoiding the older over-strong requirement that the
  same strict gap hold for every possible larger upper-bound witness.
  `integratedMoser_windowUpperBoundData_of_lowerAverageWindow` supplies that
  fixed-window data from regularity, nonnegativity, dissipation, and relative
  interpolation, and
  `integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap` converts the
  new gap chooser to the existing witness frontier.  The older
  `IntegratedMoserWindowUpperGapEpsilonFrontier` remains as a compatibility
  stronger interface via
  `integratedMoserWindowUpperDataGapFrontier_of_epsilonGap`.  Their pure
  assembler is
  `integratedMoserContradictionWindowFrontier_of_lowerAverage_upperGap`.
  These are still fixed-window or conditional frontier interfaces; they do not
  extract a pointwise next-exponent bound from a bare time-integral estimate.
  The remaining faithful hard theorem is the production of those
  high-excursion lower-average and upper-gap frontiers from integrated
  dissipation, relative interpolation, and all-exponent regularity, including
  high-excursion thickness, lower-average estimates, and the remaining
  quantitative epsilon-gap closure.
  The raw pointwise drop and terminal pointwise endpoint are still analytic
  inputs, not derived from the current abstract APIs.
  General
  χ₀ ≤ 0 is not a no-frontier headline yet:
  `paper2_theorem_1_1_general_chi_bform` still explicitly requires `hlocal`
  and `IntervalDomainUniformLocalExistence`.  The B-form
  branch now has `paper2_theorem_1_1_general_chi_bform_from_quant`, which
  replaces the uniform-local-existence input by the quantitative local factory
  `hQuant` via the existing restart/glue/sup-norm continuation machinery; the
  negative-part frontier branch has the analogous
  `paper2_theorem_1_1_general_chi_bform_negpart_from_quant`.  The
  squared-barrier branch now also has
  `paper2_theorem_1_1_general_chi_bformSq_from_quant`, replacing its
  `IntervalDomainUniformLocalExistence` input by the same quantitative factory;
  the banked squared-barrier wrapper
  `paper2_theorem_1_1_general_chi_bformSq_of_banked_from_quant` does the same
  after `positiveDatumBFormLocalHypSq_of_banked`.  The deeper squared-barrier
  branches are also wired to the quantitative factory:
  `paper2_theorem_1_1_general_chi_bformSq_regular_from_quant` and
  `paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_quant`, and the
  concrete-banked variant
  `paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_quant`.  The
  `SqRegular`/`SqDeepest` plumbing uses the banked PDE identity
  `BFormBankedInputs.hpde_u` directly instead of the stale spectral-agreement
  shim `hpde_of_BFormBankedInputs`.  These B-form branches are also wired one
  layer deeper through the threshold/Picard route:
  `*_from_picardFrontier_persistence` wrappers replace `hQuant` by
  `PicardRestartFrontier`, `ClassicalMinPersistence`, and the per-datum
  `hlocal` seed, using the already-proved
  `ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence`.
  These B-form branches additionally have `*_from_picardFrontier_boundary`
  wrappers, which replace `ClassicalMinPersistence` by the named boundary
  min-point derivative residual `BoundaryMinPersistenceBound`, consumed via
  `MinPersistenceAtoms.classicalMinPersistence_of_boundary`.  For the base and
  negative-part full-PID branches, the `*_of_BForm` variants also discharge the
  explicit per-datum `hlocal` seed from the B-form local package itself.  The
  `*_picardLimitFrontier_*_of_BForm` variants for those same two branches also
  replace `PicardRestartFrontier` by the unified Picard-limit residual
  `ConeQuantBridge.PicardLimitRestartFrontier`.  The squared-barrier branches
  have analogous `*_picardLimitFrontier_*` variants for the restart residual,
  but still keep `hlocal`, because their B-form packages currently cover
  `PaperPositiveInitialDatum`, not the full `PositiveInitialDatum` class needed
  by F1.
- **Paper 3:** the generic `Paper3MainlineTargets` and interval-domain
  sectorial endpoints are still assembled from explicit frontier/existence
  packages such as `Paper3MainlineData` and
  `IntervalDomainSectorialMainlineExistence`; these are not yet no-assumption
  PDE constructions.  Newer interval-domain Theorem 2.1 entry points
  `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall`,
  `intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall`, and
  `intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall` consume
  the proved actual-linear-small persistence producer directly, removing the
  explicit `IntervalDomainSectorialTheorem21Persistence` input in the
  `m = 1`, `1 ≤ β`, `0 < χ₀ < a/(μ*Theta_beta (β-1))` subregime.  This does
  not discharge the Theorem 2.2 local-stability package or the general
  sectorial mainline existence package.  The interval-domain mainline and
  statement assembly also now have reduced-analytic entry points
  `IntervalDomainPaper3MainlineReducedAnalyticFrontierData` /
  `IntervalDomainPaper3StatementReducedAnalyticFrontierData`, with wrappers
  `intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierData` and
  `intervalDomain_paper3_statementTargets_of_reducedAnalyticFrontierData`.
  These replace the monolithic
  `IntervalDomainSectorialMainlineCoreExistence` field by
  `IntervalDomainSectorialMainlineReducedAnalyticFacts`, using the existing
  `.to_coreExistence` bridge; small-data Cauchy fields remain explicit, while
  the four persistence fields are reduced to pointwise lower-barrier facts.
  A deeper a-priori route,
  `IntervalDomainPaper3MainlineAprioriFrontierData` /
  `IntervalDomainPaper3StatementAprioriFrontierData`, uses
  `IntervalDomainSectorialMainlineAprioriFacts.to_coreExistence` to replace the
  small-data Cauchy fields by continuation plus mass/Lp/smoothing residuals,
  while keeping the same pointwise lower-barrier persistence facts.  The
  actual-linear-small route is now wired one layer deeper through
  `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts`,
  `IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData`, and
  `IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData` in
  `IntervalDomainActualLinearStatementAssembly`: in the `m = 1`, `1 ≤ β`,
  `0 < χ₀ < a/(μ*Theta_beta (β-1))` subregime it removes the pointwise
  persistence package from the a-priori mainline by inserting
  `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`.  The
  remaining actual-linear-small statement residuals are the spectral orbit
  bound, continuation/gluing, mass/Lp/smoothing route, compactness,
  stability, and Proposition 1.x packages.  The Proposition 1.x package now
  has a Paper2-theorem route,
  `IntervalDomainPaper3Proposition1FromPaper2TheoremsData`, which replaces the
  Paper3 Proposition 1.3 and Proposition 1.4 existence-branch fields by Paper2
  `Theorem_1_3` and `Theorem_1_2`; the remaining proposition inputs on that
  route are the negative-sensitivity bound plus those two Paper2 headline
  theorem inputs.  There is now also a Paper2-main-target route,
  `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData`, backed by the
  generic `Paper3Proposition1FromPaper2MainTargetsData`: it extracts Paper2
  Theorems 1.2/1.3 from `IntervalDomainPaper2MainTheoremTargets`, so Paper3
  Proposition 1.x can depend on the Paper2 headline theorem bundle rather than
  duplicate theorem fields.  A still thinner
  Moser-ladder actual-linear-small route is exposed by
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData`, and
  `IntervalDomainPaper3StatementMoserActualLinearSmallFrontierData`.  This
  route replaces the old mass/Lp/smoothing package by the Moser-ladder atoms
  and derives the old `a_pos` / `chi_nonneg` fields from the actual-linear
  parameter hypotheses; remaining Moser-route inputs are boundedness,
  L²-seed regularity, Moser dissipation, relative Moser interpolation, and the
  quantitative endpoint tower.  A still thinner closed-energy variant is now
  exposed by
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallClosedEnergyFrontierData`:
  it replaces the naked `l2SeedRegularity` field by the existential closed
  integrated-energy trace package
  `P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData`, using the proved
  `l2SeedRegularity_of_closedEnergyIdentityTraceData` bridge.  The energy
  identity itself remains a residual; the seed regularity conversion is no
  longer a residual.  The closed-energy Moser route now has a still thinner
  CEGrad variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData`, and
  `IntervalDomainPaper3StatementMoserActualLinearSmallCEGradFrontierData`.
  This replaces the black-box `relativeMoserInterpolation` field by a
  mass-gradient/lower-order interface (`cGrad` positivity,
  `LpMassGradientInterpolationEstimate`, the gradient-comparison inequality,
  and `MoserMassPowerToCurrentLpLowerOrder`), then uses the proved
  `P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient`
  bridge to recover `RelativeMoserInterpolationBefore`.  Those four CEGrad
  subfields are still analytic residuals; only the conversion from them to
  relative Moser interpolation is discharged.  The route also has a
  CERawGrad variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallCERawGradFrontierData`.
  This further replaces the black-box `moserDissipation` field by the raw
  pointwise nonnegative-`B` drop condition and uses the proved
  `moserDissipationDropBeforeNonnegB_of_raw_drop` bridge to recover
  `MoserDissipationDropBeforeNonnegB`.  The raw drop is still a residual; the
  packaging bridge is proved.  The route now has a CETerminal variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalFrontierData`.
  This replaces the abstract `quantitativeEndpoint` tower field by direct
  existence of one terminal pointwise power-control estimate
  `IntervalDomainMoserPointwisePowerControlBefore`; the proved conversion uses
  constant `pSeq` / `rootBound` sequences to recover
  `IntervalDomainMoserQuantitativeEndpoint`.  The terminal pointwise estimate
  remains a residual; the tower-packaging bridge is proved.  The CETerminal
  residual no longer carries the full `IntervalDomainBoundednessHyp` bundle:
  it carries the two-field `IntervalDomainMoserActualLinearSmallBoundednessCore`
  (`2 * γ < α` and `γ * N < 2`), and the conversion rebuilds
  `IntervalDomainBoundednessHyp` from that core, the wrapper hypothesis
  `0 < b`, and `CM2Params.hγ`.  Thus `0 < b`, `0 < γ`, and the sharp
  threshold branch are no longer duplicate residual fields at this level; the
  two absorption/dimension inequalities remain genuine parameter assumptions.
  The latest CETerminal statement route also has a Paper2-proposition-input wrapper,
  `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2FrontierData`,
  with theorem
  `intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2FrontierData`;
  this leaves the mainline residuals unchanged and removes the duplicate
  Paper3-side Proposition 1.3/1.4 existence branches by consuming Paper2
  Theorems 1.3/1.2 instead.  The CETerminal statement route also has a
  stronger Paper2-main-target wrapper,
  `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData`,
  whose proposition side consumes `IntervalDomainPaper2MainTheoremTargets`;
  this is the preferred bridge once Paper2's interval-domain headline bundle
  is available.  The actual-linear-small route now also has a direct
  integrated-step variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepFrontierData`,
  plus the Paper2-main-target wrapper
  `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData`.
  This route consumes a supplied `IntegratedMoserFirstCrossingStep` and the
  existing quantitative endpoint.  The same surface is now refined by the
  lower-average / upper-gap split route
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData`,
  `IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainData`;
  this consumes `IntegratedMoserFirstCrossingLowerUpperFrontiers` and then
  collapses to the existing integrated-step route.  Its reusable core is now
  `IntervalDomainMassLpSmoothingIntegratedStepResiduals`, which fills
  `IntervalDomainMassLpSmoothingRouteResiduals` directly via
  `intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms` and
  `intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms`; the
  Paper3 local adapter only supplies `l2SeedRegularity` from closed-energy
  trace data.  It
  deliberately does not derive `MoserDissipationDropBeforeNonnegB` or
  `RelativeMoserInterpolationBefore` from `Corollary_2_1`; those would be
  backwards analytic dependencies.  The hard residual is now exposed more
  precisely as production of the high-excursion contradiction-window frontier
  sufficient to obtain the integrated first-crossing step.  That frontier now
  also has a reusable Type-level split surface:
  `IntegratedMoserFirstCrossingLowerUpperFrontiers` and
  `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals` carry the
  cross-exponent lower-average and upper-gap suppliers separately before
  converting to the existing window-frontier and integrated-step routes.

**New threshold-plan route (2026-06-30):**
`P3MoserThresholdPlanProducer.lean` provides a complete alternative pipeline:
`integratedMoserFirstCrossingStep_of_abstract_data` takes regularity + energy
nonnegativity + dissipation drop + relative interpolation + gradient nonneg +
p0≥0 and produces `IntegratedMoserFirstCrossingStep` via the threshold-plan
contradiction argument.  Handles Cq=0 (non-increasing energy) separately.
`intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data` specializes
to `intervalDomain` by supplying gradient nonneg from `sq_nonneg`.
`P3MoserHighExcursionProducer.lean` is now axiom-clean (fixed 2 linarith
failures from integral-notation greedy parsing).  The remaining frontier for
this route is producing `IntegratedMoserFirstCrossingRegularity` from
`IsPaper2ClassicalSolution` (energy continuity via dominated convergence on
the compact interval domain).

Next real work is residual-assumption discharge, not proof-hole removal.  Good
small targets are the remaining Paper1 construction floors
(`hprodAll`/`hstep`/`htail`/stationary/flat/SMP packages), Paper2 general-χ
local/uniform existence inputs, production of
the high-excursion contradiction-window frontier sufficient for
`IntegratedMoserFirstCrossingStep` from integrated dissipation/relative
interpolation/regularity, and Paper3 interval-domain sectorial mainline
existence/persistence packages.

Input-package audit:
- `structure` and `def ... : Prop` packages here are explicit residual
  interfaces, not axioms and not proof holes.  A theorem consuming one of these
  packages is conditional until a producer constructs that package.
- For the integrated Moser route, `IntegratedMoserPrecrossingIntervalData` and
  `IntegratedMoserWindowUpperBoundData` now have proved producers from the
  named regularity/interior-energy-nonnegativity/current-bound/dissipation/
  relative inputs.  The energy-nonnegativity input is no longer a closed-time
  requirement: it is only required at interior times and, for `intervalDomain`,
  is produced from pointwise nonnegativity, `IsPaper2ClassicalSolution`, or
  `IsPaper2GlobalClassicalSolution`.  `IntegratedMoserHighExcursionContradictionWindowFrontier`
  is still the real analytic frontier.  Its lower-average and upper-gap
  subfrontiers are now explicitly split, both at a single exponent and in the
  cross-exponent `IntegratedMoserFirstCrossingLowerUpperFrontiers` package.
  The base-exponent nonnegativity field is now pure arithmetic via
  `p0_nonneg_of_abstractLpBootstrapHypothesis`, and
  `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` is now the
  preferred package collapsing lower-average data plus the upper-data-aware
  strict-gap chooser to the split first-crossing package.  The older
  `IntegratedMoserFirstCrossingLowerAverageEpsilonData` still collapses through
  a compatibility conversion, but is intentionally stronger.  The current code
  still does not derive high-excursion thickness or the quantitative selected
  upper-witness gap closure.
- Some fields are already produced or reduced further by code.  Examples:
  Paper2 χ₀=0 has `intervalDomain_theorem_1_1_chiZero_unconditional`, now
  exposed in the interval-domain statement assembly; the Paper2
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData`
  wrapper produces `Corollary_2_1` and `Proposition_2_5` from the actual
  Moser atom package, and the mass-gradient variant lowers only the
  relative-Moser atom; Paper3 actual-linear-small persistence is produced by
  `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` and now wired
  to statement-level Theorem 2.1 wrappers.
- Other packages are genuine remaining analytic frontiers.  Examples:
  Paper1 `Paper1MainResultsData` / `Paper1MainlineExistence`, Paper2 general-χ
  `PicardLimitRestartFrontier` and `BoundaryMinPersistenceBound`, and Paper3
  reduced sectorial mainline facts / stability packages still require
  construction from PDE analysis before their corresponding headline endpoints
  become no-assumption theorems.

## SUPERSEDED HISTORICAL SNAPSHOT (2026-06-28)

1001+ files, ~393K LOC. Papers 1, 3: 0 sorry. Paper 2 χ₀=0: 0 sorry (UNCONDITIONAL).
Paper 2 χ₀<0: **42 sorry** across 8 files (was 43; hresolver_series filled).

### Architecture decision: DIRECT CUTOFF PATH is critical
Direct cutoff (IntervalHeatResolverJointC2, 5 sorry) bypasses
ResolverLevel0SpectralC2Coeff (DuhamelSourceTimeC2Coeff is 16+ fields, no producer)
and HeatSemigroupHighRegularity (FlooredSourceTimeData hyps are on separate path).

### 2026-06-28 progress:
- **hresolver_series FILLED** (310bc27): cosine reconstruction via coupledChemical_lift_eq_series
- **heatSemigroup_pos_of_pos ADDED** (571ab1d): S(t)u₀ > 0 from u₀ > 0 via lower bound
- Codex grinding heatLevel0_srcTimeCoeff_contDiffAt_two (adding hfloor chain)

### 2026-06-27 night session progress:
- **hfloor hypothesis added** to heatSemigroup_flooredSourceTimeData (heat positivity at t > 0)
- **heatDu_eq_secondValue bridge** — LaplacianValue = SecondValue by ring (definitional bridge)
- **d0 FILLED** (extracted as heatSemigroup_d0, pending build verify):
  - d0(a): heat profile joint continuity → rpow → srcSlice ContinuousOn
  - d0(b): HasDerivWithinAt → HasDerivAt via Icc_mem_nhds + hasDerivAt_srcSlice under floor
  - d0(c): rpow^(γ-1) × heatDu joint continuity from profile + secondValue
- **srcTimeCoeff_iteratedDeriv2 FILLED** (build-verified):
  iteratedDeriv_succ + EventuallyEq.deriv_eq on Ioi 0 + cosS1_hasDerivAt.deriv
- ChatGPT Q1224-Q1231: bridge verification, srcTimeCoeff proof, API discovery

### Learned: where-syntax ⟨⟩ elaboration pitfall
The `where` syntax for structure fields prevents `refine ⟨...⟩` from determining
the expected type when `have`-bindings are present. Fix: extract the proof into a
separate private theorem and call it from the `where` block.

### 2026-06-27 session progress:
- **3E-bdd filled** (b661bcd): intervalDomainLift u₀ bounded from Continuous u₀ on compact
- **3E-nonneg filled** (388ca89): added hu₀_nonneg hypothesis, propagated to callers
- **cutoffResolverTerm_contDiff_two decomposed** (7bb2f45): 4-layer structure —
  srcTimeCoeff ContDiffAt → resolverTimeCoeff ContDiffAt → cutoff global C² → (t,x) C²
  Single remaining sorry: heatLevel0_srcTimeCoeff_contDiffAt_two
- Level0: 7 → 5 sorry (3E-bdd and 3E-nonneg eliminated)
- ChatGPT Q1116-Q1122: resolver C² strategy, eigenvalue summability route, hu₀_nonneg design
- IntervalHeatResolverJointC2.lean: build-verified on uisai2 (axioms: propext/sorryAx/choice/sound)

### Per-sorry status (Level0, 5 remaining):
| Sorry | Line | Route | Status |
|-------|------|-------|--------|
| 1A (secondDeriv uniform bound) | 755 | joint C² on closed slab + compactness | BLOCKED on resolver C² |
| 2A-sup (uniform sup bound) | 893 | smooth representative + compactness | BLOCKED on resolver C² |
| eigenvalue summability | 1086 | depth-2 NeumannTower for ν·(S(r)u₀)^γ | ChatGPT route ready (Q1119) |
| resolver nonneg | 1101 | need S(r)u₀ ≥ 0 → source nonneg → resolver nonneg | needs hu₀_nonneg (same as 3E) |
| 3C+3D+3F (chain rule) | 1253 | direct resolver C² + inner commute | BLOCKED on resolver C² |
| 3G (time-deriv continuity) | 1262 | Level0HeatMixedRepr scaffold | separate path |

### MILESTONE: srcTimeCoeff_contDiffAt FILLED (127dcce, build-verified)
The assembly theorem connecting HasDerivAt×2 + ContinuousAt → ContDiffAt ℝ 2.
Key API: contDiffOn_succ_of_fderivWithin + ContDiffOn.smulRight (with StrongDual) +
smulRight_one_eq_toSpanSingleton + toSpanSingleton_deriv bridge.
IntervalPhysicalSourceTimeC2Concrete: 4 → 3 sorry.
Sub-lemmas (srcTimeCoeff_hasDerivAt, cosS1_hasDerivAt, cosS2_continuousAt) all sorry-free.
Also fixed: pass ContinuousOn (not IntervalIntegrable) to cosineCoeffs_hasDerivAt_of_smooth_param.

### What this session did (8 commits):
1. **F1 upstream weakening** (c2dfd86, e766768): ContinuousOn → IntervalIntegrable
   in 6 structures + consumer + 6 downstream callers. Boundary obstruction resolved.
2. **Architectural fix** (9dd3a4b): eliminated by_cases hτ : 0 < τ (τ ≤ 0 branch
   was mathematically impossible — heat semigroup discontinuous at t=0).
   15 sorry → 5 sorry.
3. **New infrastructure** (cfcb6de, 365db15, be5bf6b, 4a6740e):
   - variation-of-constants identity for localRestartCoeff
   - direct resolver inner commute WITHOUT PhysicalResolverJointC2Data
   - ResolverHasSpectralAgreementC2Coeff assembly (4 sorry)
   - Level0 ChemDivMixedTimeDerivClosedRepr skeleton (for 3G)

### Remaining 5 Level0 sorry:
- **1A** (line ~755): uniform ptwise bound of secondDeriv via joint continuity + compactness
- **2A-sup** (line ~893): uniform sup bound for coupledChemDivSourceLift
- **3A**: IntervalIntegrable from interior smoothness + sup bound (provable, no obstruction)
- **3C+3D+3F** (combined): chain rule HasDerivAt — blocked on resolver joint C² + bridge
- **3G**: time-derivative joint continuity on slab — blocked on mixed repr witnesses

### Root cause resolution status:
1. ~~Resolver C² scope mismatch~~: RESOLVED via Option B — direct cutoff resolver C²
   (IntervalHeatResolverJointC2.lean, 5 sorry, build-verified on uisai2).
   Option A (floor-weakening) also landed (4000f01) as backup.
   Option B infrastructure: variation-of-constants (0 sorry), direct inner commute (0 sorry),
   ResolverLevel0SpectralC2Coeff (assembly skeleton), Level0HeatMixedRepr (3G scaffold).
2. ~~F1 boundary obstruction~~: RESOLVED (ContinuousOn → IntervalIntegrable, 12+ files).
3. ~~τ ≤ 0 impossible branch~~: ELIMINATED (9dd3a4b, 15→5 sorry).

### Current state (end of 2026-06-26 night session):
Level0: **8 sorry** (from 15). Full project build-verified on uisai2 (3640 jobs).
34 commits, 25+ ChatGPT rounds, 10 subagents.

### Per-sorry closure map (Q1090 + Q1102):
- **3C+3D+3F** (chain rule HasDerivAt): CLOSES from direct resolver C² + inner commute
- **3E/positivity**: CLOSES with existing coupledChemical_floor_pos wiring
- **3A** (IntervalIntegrable): FILLED (9566859), 2 sub-sorry remain
- **3G** (time-deriv continuity): via Level0HeatMixedRepr scaffold (Q1102 confirmed no IteratePicardJointC2Data needed)
- **1A** (secondDeriv uniform bound): NEEDS WORK — joint continuity of cosine representative on closed slab
- **2A-sup** (source sup bound): NEEDS WORK — closed-slab source representative

### Next session priorities:
1. Fill 5 analytic sorry in IntervalHeatResolverJointC2.lean (per-term ContDiff + majorant)
2. Wire 3C+3D+3F from direct resolver C² (Q1066 has exact proof body)
3. Wire 3G from Level0HeatMixedRepr (fill 12 sorry for 10 smooth representatives)
4. Close 1A + 2A-sup from joint continuity + compactness

### Remaining 3 Level0 sorry (all blocked on resolver joint C²):
- 1A (line 755): joint pointwise bound of secondDeriv via compactness
- 2A-sup (line 804): uniform sup bound for coupledChemDivSourceLift
- 3A-sub (line 989): per-slab source continuity (upstream ContinuousOn weakening needed)

ALL THREE share the same blocker: resolver joint C² is proved INSIDE
FluxJointC2Hyp (sub-sorry 3C was filled via coupledChemical_jointContDiffAt_two +
PhysicalResolverJointC2Data), but NOT available as a standalone theorem for the
envelope construction.

### ROOT CAUSE: ∀ τ : ℝ scope mismatch (STRUCTURAL)
IterateSourceTimeData.floor requires positivity ∀ t : ℝ, but S(0)=0 (Lean
convention). The PhysicalResolverJointC2Data chain through FlooredSourceTimeData
is UNFILLABLE for the raw heat semigroup.

### NEXT SESSION OPTIONS (pick one):
(A) Weaken IterateSourceTimeData.floor to ∀ t, 0 < t → positivity
    (cross-cutting change across ~11 files, each ~1 line)
(B) Bypass the chain entirely: prove heatResolverJointContDiffAt_two
    DIRECTLY using cutoff approach (same as heatSemigroup_jointContDiffAt_two)
    — needs ContDiff of cutoff resolver term, which needs srcTimeCoeff C²
    for t > 0 (via cosineCoeffs_hasDerivAt_of_smooth_param)
(C) Build a positive-window-only IterateSourceTimeDataOn structure

Option (B) is the most self-contained. The existing cutoff heat semigroup
proof is the template — adapt it for the resolver series.

### 0-sorry infrastructure landed this session:
- IntervalSourceDecayQuantitative: quartic decay + eigenvalue L¹ summability
- IntervalResolverHighRegularity: global resolver positivity (period/even/reflect)
- Level0: slab inclusion (ContinuousWithinAt.mono_of_mem_nhdsWithin)
- Level0: resolver positivity (nonneg source → global nonneg → 1+V > 0)
- Level0: source eigenvalue summability (7-step chain: H2 certs + quartic decay)
- HeatRegularity: cutoff heat series global C² (contDiff_tsum via smoothRightCutoff)
- HeatRegularity: Leibniz main theorem (norm_iteratedFDeriv_mul_le applied + wired)

### Single key blocker: cutoffHeatTerm_iteratedFDeriv_bound (1 sorry)
In IntervalHeatSemigroupHighRegularity.lean. The cutoff approach is LANDED:
smoothRightCutoff kills t < 0, contDiff_tsum gives global C² of cutoff series,
eventual equality gives ContDiffAt at positive times. Only the Leibniz product
rule bound for ‖iteratedFDeriv k (φ·exp·â·cos)‖ remains.
Pattern: cutoffValueTerm_leibniz_bound (IntervalResolverSpectralJointC2CutoffBounds.lean:52)
uses norm_iteratedFDeriv_mul_le (Mathlib Leibniz rule).
Once proved → heatSemigroup_jointContDiffAt_two fully sorry-free →
unlocks sub-sorry 3B → 3C/3D → 2A-core → 1A.

### Sub-sorry with existing producers (found by cron analysis):
- 3F: coupledChemDivFlux_timeBridge_of_physicalJointC2 EXISTS (IntervalChemDivFACCommuteDischarge)
- 3G: chemDivMixedTimeDeriv_jointContinuousOn_closed EXISTS (IntervalChemDivTimeDerivClosed)
  Both need upstream PhysicalResolverJointC2Data → needs PhysicalSourceTimeC2 → needs heat wiring.

### Sub-sorry independent of joint C²:
- 2A-agree: definitional unfolding (coupledChemDivSourceLift_eq_deriv_fluxLift_interior exists)
- 3E: resolver positivity floor (τ > 0: nonneg source → nonneg resolver; τ ≤ 0: degenerate/sorry)

### Paper 2 χ₀<0 sorry breakdown

**IntervalConjugateLevel0BFormSourceOn.lean (4 sorry):**
1. Line 278: Source eigenvalue summability — `Summable (λ_k |sourceCoeff_k|)`.
   Route: depth-2 IBP via `intervalWeakH4Neumann_eigenvalue_L1_summable` (sorry'd
   in IntervalSourceDecayQuantitative.lean, reduces to cosineCoeffs-Laplacian identity).
2. Line 468: L1 uniform bound — joint continuity of deriv²(chemDiv) on [c,T]×[0,1] + compactness.
3. Line 514: Sup bound + per-slice continuity — same joint continuity difficulty.
4. Line 615: CoupledChemDivFluxJointC2Hyp — 5 fields of regularity for heat semigroup trajectory.

**IntervalConjugateBFormSourceTower.lean (5 sorry):** All downstream of Level0.

### Infrastructure built this session (sorry-free, axiom-clean)
- `IntervalResolverHighRegularity.lean`: global resolver nonneg from [0,1] via
  period-2 + even + reflect-one (intervalResolverLiftR_nonneg_of_nonneg_on_Icc),
  plus `0 < 1 + V(x)` wrapper.
- `IntervalConjugateLevel0BFormSourceOn.lean`: slab inclusion fix via
  ContinuousWithinAt.mono_of_mem_nhdsWithin; resolver positivity via nonneg source
  → nonneg resolver on [0,1] → global nonneg by symmetry.
- `IntervalSourceDecayQuantitative.lean`: depth-2 quartic decay + eigenvalue L¹
  summability — FULLY PROVED (0 sorry, axiom-clean, build verified on uisai2).
  `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound`: |c_k| ≤ 2B/(kπ)⁴
  `intervalWeakH4Neumann_eigenvalue_L1_summable`: Summable (λ_k |c_k|)
  Both proved via depth-2 IBP identity cosineCoeffs(f'') = -(kπ)² cosineCoeffs(f).

### FluxJointC2Hyp route (from ChatGPT analysis Q684/Q688)
The shortest path to CoupledChemDivFluxJointC2Hyp for the heat semigroup is:
  Physical source-time-C² data + summability
  → IntervalPhysicalResolverDataConcrete → CoupledChemDivFluxFactorJointC2Inputs
  → coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs → FluxJointC2Hyp
Hardest field: (b) joint C² of uncurried flux (resolver joint C² burden).
Second: (e) time-derivative ContinuousOn (spectral representative on closed slab).

### NeumannTower for source eigenvalue summability (line 278)
Existing tool: IntervalIBPCoeffExtraction.lean has NeumannTower + cosineCoeffs_decay.
Need: build NeumannTower at depth j=2 for ν·u^γ where u = heat semigroup.
Requires: C⁴ of ν·u^γ (chain rule) + depth-2 Neumann BCs (u' and u''' vanish at endpoints).

### Paper 1 (traveling waves): SORRY-FREE, unconditional infrastructure landed.
### Paper 2 χ₀=0: `intervalDomain_theorem_1_1_chiZero_unconditional` — UNCONDITIONAL, axiom-clean.
### Paper 3 (long-time dynamics): SORRY-FREE, linear dichotomy unconditional.

### χ₀ < 0 PRODUCTION FRONTIER
`BFormBankedInputs` fields — all satisfiable, all but 2 have sorry-free producers:
- `huPaper`, `Hinf`, `hsmall`, `MInit`, `haInit`: from existence data + ball estimates
- `hB_global`: from `conjugatePicardLimit_cosineSeries` (sorry-free)
- `hlogCont`, `hlogFourier`: Fields 9/10 from `IntervalBankSourceSliceLeaves` (sorry-free)
- `hchemIoo`: from `IntervalBankChemSliceFix` (sorry-free, replaces false `hchemCont`)
- **`hlogSrc`**: NEEDS PRODUCTION — `DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs ...)`
- **`hchemSrc`**: NEEDS PRODUCTION — `DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs ...)`

Production route for `hlogSrc`/`hchemSrc`:
1. `sourceTimeC1On_succ_of_sourceTimeC1On` (IntervalPicardSourceTimeC1OnRecursion) — GENERIC
2. `duhamelSourceTimeC1On_of_uniform_limit` (IntervalMildPicardLimitRegularityOn) — limit passage
3. Need: K1/K2 properties (representation, G1/G2 bounds, positivity) for `conjugatePicardIter`

---

## HISTORICAL (2026-06-10/11 — kept for reference, superseded by above)

## ⛔ FIDELITY CORRECTION (2026-06-11 ~04:00 — READ FIRST, supersedes all "done"/"unconditional"/"sorry-free" language below)
An independent adversarial audit (HANDOFF/FIDELITY-AUDIT.md) found this campaign
OVERSTATED its results. The honest status:
- What is in Lean is a **FRAGMENT** of the paper's Theorem 1.1: only χ₀=0 (the
  degenerate decoupled slice — NOT a chemotaxis system), N=1 (intervalDomain),
  a,b>0, 1≤α, 1≤γ. Untouched: χ₀<0 (the real case), a=b=0, N≥2, Thms 1.2/1.3.
- It is **CONDITIONAL** on `hsrc0` (TowerConeAnalyticResidual), which is the
  paper's hard analytic content relocated into a hypothesis AND plausibly
  unsatisfiable as typed (the s=0 ℓ¹-envelope t→0 disease). So there is NO
  unconditional result yet, even for the χ₀=0 fragment.
- The "#print axioms = clean" claims below were run on a DIVERGENT remote olean
  tree (/dev/shm/shen_work @ 6d2f95a, dirty), never on a clean f93cbda checkout.
  Clean-tree certification is in progress.
- Genuine positive: the STATEMENT layer is FAITHFUL (non-hollow) — the PDE, both
  equations, Neumann BC, real C² regularity, exact (1.21) bound.
The strong-language sections below describe real engineering progress on the
fragment, but their "done"/"prize"/"unconditional" framing is corrected here.

## ⭐⭐⭐ K1 ENDGAME STATE (2026-06-11 00:4x — engineering log, see FIDELITY CORRECTION above)
The hsrc0 endgame (waves W1a/W1b/W2/W3/W4, commits 085a3ad…7b424e2) built the
COMPLETE satisfiable replacement stack for the per-level source K1 package:
iterate initial approach (hand-written, χ₀=0), patched-coefficient continuity
+ per-level DuhamelSourceBddOn (no t→0 disease), the σ/2-shifted clamped
DuhamelSourceTimeC1 from winAdot data, consumer variants (hbsum/G2/hagree
_of_window/_of_sourceBdd), and assembled tower replacement legs — all
axiom-clean, all σ < T.

W4 verdict (rigorous): **σ = T is genuinely consumed** by three FROZEN
limit-side capstone feeders (IterateWindowC2Data closed-T quantifiers,
henv_iter at s ≤ D.T, hiter_cont at [D.T/2, D.T]), and every hsrc0-free route
is structurally σ < T strict (clamp pad headroom; WindowAdotLegs hi < T).
**TowerConeAnalyticResidual = { hsrc0 } is the honest irreducible minimum**
under the current frozen capstone surface.  Emptying it needs ONE of:
(i) a T-endpoint one-sided DuhamelSourceTimeC1 construction (the soft clamp
structurally cannot reach the endpoint), or (ii) a BddOn→λ-weighted upgrade
lemma, or (iii) unfreezing the capstone feeders to σ < T quantifiers.
Recorded in HANDOFF/k1-wall-plan.md W4 STATUS.

Also this campaign: the hL_cont VACUITY BUG (false zero-extension global
continuity field — residual was unsatisfiable as published) found and fixed
(c09aaca); hG2base + hG1all fake walls demolished by hand (7083684, 8f7987f).

## ⭐⭐ RESIDUAL SHRINK UPDATE (2026-06-10 19:30 — newest)
After the sorry-free capstone (32c8fee), two more residual legs fell — both
previously reported as BLOCKED by agents, both blockers shown ILLUSORY,
both proofs hand-written:
* **hG2base** (7083684, IntervalHomogeneousG2Base.lean): the gate at t := σ
  already forces homWeightBound = 32M/(eπ²σ²) ≤ A₂/σ², and the homogeneous
  slice's true spectral bound M·eigExpWeight σ ≤ 4M/(eπ²σ²) is 8× smaller —
  the gate's A₂ ≥ 64M/(eπ²) head-room was designed for this. No calibration
  hypothesis needed.
* **hG1all** (8f7987f, IntervalPicardG1All.lean): the split machinery's
  ∀ s : ℝ source sup is over-quantified — the Duhamel integrand reads
  s ∈ Ioc 0 t only. The windowed family wSrc satisfies the global sup by
  construction and the same value EqOn by integral congruence; the existing
  interior split + g1_kernel_bound apply verbatim. Bonus infrastructure:
  picardIter_hasJointMeasurability_all, u₀_lift_abs_le. HCone gained the
  cone-returned hlim_ball conjunct (precedent: hub's hball).
**TowerConeAnalyticResidual is now 7 fields: hsrc0, hL_cont, adot,
hadot_deriv, hadot_cont, adotBound, hadot_bound — ALL rooted in per-iterate
source K1 regularity (the project's one genuine remaining analytic wall;
see UNPROVED_TARGETS.md for the documented producer circularity).**
Axioms unchanged: both capstone theorems = [propext, Classical.choice,
Quot.sound].

## ⭐ FINAL STATE (2026-06-10 18:15 — supersedes everything below)
**THE CAPSTONE IS SORRY-FREE.** Commit 32c8fee:
`#print axioms` on BOTH `paper2_theorem_1_1_chiZero_unconditional` and
`paper2_theorem_1_1_chiZero_from_coneSupply` = `[propext, Classical.choice,
Quot.sound]` — NO sorryAx (independently re-verified on uisai2; full build
8547 jobs EXIT 0; md5 local=remote). The `hinterior` circularity (hcontP →
hsliceTC → restart-rep → BddOn → hcontP) was broken on the iterate side:
s-uniform geometric convergence (PicardConvFacts.hgeom) transfers per-iterate
coefficient time-continuity to the limit (IntervalPicardLimitCoeffTimeCont);
hinterior itself proved via the spectral restart series subtraction with the
λ-cancelling Duhamel bound + heat-damped homogeneous sum
(IntervalRestartSeriesLipschitz / IntervalRestartSliceLipschitz). The capstone
gained ONE hypothesis (`IterCoeffTimeContProvider`), discharged inside
`from_coneSupply` from the tower (`hiter_cont_of_tower`) — the acceptance
surface `from_coneSupply` is UNCHANGED. Tower residual
(`TowerConeAnalyticResidual`, the from_coneSupply hypothesis surface) is now
9 fields: hsrc0, hL_cont, hG1all, hG2base, adot(+4 legs). Honest blockers
recorded: hG1all needs a global all-s iterate source sup (truncated-source
rebuild = new analytic content); hG2base needs a homogeneous heat ∂²ₓ estimate
calibrated to the gate budget A₂. Design verdicts in
HANDOFF/chatgpt-hinterior-break-verdict.md.

## START HERE
Read `HANDOFF/CODEX-HANDOFF.md` — the complete execution handoff for the
Tower campaign (environment rules, current state, stage 1/2 plans, verdict
index). Build is REMOTE ONLY (uisai2:/dev/shm/shen_work; local builds are
blocked and would kernel-panic the mini). Acceptance = #print axioms.

## THE CURRENT STATE (one paragraph)
Paper 2 Theorem 1.1 (χ₀ = 0) capstone
`paper2_theorem_1_1_chiZero_unconditional`:
regime constants (χ₀=0, a>0, b>0, α≥1, γ≥1) + HWdata ⟹ Theorem_1_1,
axioms [propext, sorryAx, Classical.choice, Quot.sound]; the single sorryAx
is `hinterior` (IntervalPicardLimitSliceTimeContinuity). HWdata (per-datum
window iterate-C² provider) and hinterior share ONE root: the per-iterate
source-package production tower. The tower is fully designed and externally
audited (HANDOFF/chatgpt-tower-verdict.md); stage 1 (lemma layer, 4 files)
may already be landed by an in-flight agent — CHECK git log/status first.
Tower lands ⟹ both close ⟹ capstone carries regime constants only.

## What the 2026-06-09/10 campaign did (~40h, ~70 commits, all pushed)
Started at 21 sorries, 14 UNSATISFIABLE AS TYPED (global time quantifiers
vs (0,T]-only data; uniform gradient bounds false at t→0 by parabolic
smoothing; no ℓ¹ envelope at s=0 for continuous data; the s=T jump; two
genuine circularities). Dissolved via: C¹ soft clamp + existential clamped
witnesses; weak-chain horizon retype (DuhamelSourceL1ContOn) then the final
DuhamelSourceBddOn patched-family interface; ledger V2 (per-compact K2,
(0,T) K1, shifted fields deleted); K1 proved WITHOUT new analysis (weak
restart identity + per-mode FTC + fixed-split series differentiation);
iterate-side bootstrap breaking the hsrc0 circularity; hybrid weighted C²
(kernel G1 + t²-weighted spectral G2, gate SOLVED explicitly in
IntervalPicardGateSolve); cone _with_gate_data (returns exact hDu,
discharged GateCondition, hcont_iterates, PicardConvFacts, strict iterate
positivity); Hvsrc per-t₀ retype + clamped ν·u^γ witness; hpde_u via the
continuous-surrogate retype; Hvpos proved; capstone narrowed to
HWdata-only via fact-carrying bridges (the hPLF ∀-D route superseded).
Six external design audits (HANDOFF/chatgpt-*-verdict.md); three caught
real errors (the G1 spectral recursion non-closure, a circular k1_quadruple,
the hDu EqOn trap).

## Historical notes below (pre-campaign architecture, mostly still accurate
## for layers 1-2; the Paper2 layer-3 description is superseded by the above)

## Build invariant

```bash
lake build  # 8409 jobs, 0 sorry, 0 admit, 0 custom axiom
```

## Architecture: three layers

### Layer 1: PDE infrastructure (COMPLETE, 0 sorry)
All spectral, semigroup, kernel, Duhamel, resolver, energy, IBP, and
measurability infrastructure is proved. Key files:
- IntervalNeumannFullKernel, IntervalFullKernel*, IntervalDuhamel*
- IntervalResolverPositivity (O1: heat-Laplace nonneg, unconditional)
- IntervalChemFluxLipschitz (glue1+glue2: contraction estimates)
- IntervalGradDuhamelBound (Atom D: gradient sqrt-T estimates)
- IntervalLogisticLipschitz (Atom C: logistic Lipschitz, one-sided α>0)
- IntervalSourceCoefficientTimeC1 (G3: DuhamelSourceTimeC1 algebra)
- IntervalResolverSpatialC2 (G4q: resolver C² + Neumann + weight summability)

### Layer 2: Mild solution + regularity bootstrap (COMPLETE, 0 sorry)
- IntervalMildPicard: Picard iteration → GradientMildSolutionData (mild FP)
- IntervalMildSourceDecay: SourceCoeffQuadraticDecay (unconditional)
- IntervalMildToClassical: all 9 regularity conjuncts (unconditional)
- IntervalMildRegularityBootstrap: half-step restart C² + Neumann
- IntervalSemigroupNeumann: semigroup conjuncts 3/6/7/8/9 + composition
- IntervalMildPicardRegularity: Picard iterate induction (base + step)
- IntervalMildPicardLimitRegularity (G2.5): DuhamelSourceTimeC1 limit passage
- IntervalMildTimeRegularity (G4j): time DifferentiableAt from spectral
- IntervalMildTimeDerivContinuity (G4 fields): HasDerivAt + joint continuity
- IntervalMildFrontierFromSpectral (G4r): closed-slab joint continuity
- IntervalMildRegularityFrontierAssembly: u-side frontier field wiring
- IntervalResolverTimeRegularity: v-side frontier field wiring
- IntervalResolverDirectTimeRegularity (F2): resolver direct time regularity
- IntervalMildSourceDecayHelper: Sobolev chain rule / weak H² Neumann
- IntervalWeakCosineIBP: cosine coefficient decay infrastructure
- IntervalMildToLocalExistence: bridge to localExistence

### Layer 3: Paper-level theorem assembly (NEAR COMPLETE)
- IntervalDomainTheorem11Umbrella: γ≥1 umbrella (hposWit eliminated, G6)
- IntervalDomainThm11Assembly: final wiring, 15/15 frontier fields proved
- IntervalDomainStatementAssembly: Paper2 Thm 1.1/1.2/1.3 targets
- Paper1/Statements, Paper2/Statements, Paper3/Statements

## G0–G7 + G2.5 status (all committed, 0 sorry)

| Gap | Description | Status | Commits |
|-----|-------------|--------|---------|
| G0 | Continuous u₀ in initialAdmissible | ✓ DONE | 5343c18 |
| G1a | One-sided logistic Lipschitz α>0 | ✓ DONE | 5f94ba0 |
| G2a+G2b | Spatial IBP for Duhamel source | ✓ DONE | 5bf3fb5 |
| G2.5 | DuhamelSourceTimeC1 limit passage | ✓ DONE | e5da4dc |
| G3 | Total-source DuhamelSourceTimeC1 | ✓ DONE | b2b4b66+ |
| G4a–G4i | Spectral time derivatives (ODE→series) | ✓ DONE | 355f14d–356dd4e |
| G4j | Time DifferentiableAt of mild solution | ✓ DONE | e138bfa |
| G4k–G4m | Joint continuity (Duhamel+hom+restart) | ✓ DONE | cfa96ab–665367d |
| G4n–G4p | Spectral PDE identity + Laplacian | ✓ DONE | a1ce482–c7db735 |
| G4q | Resolver spatial C² + weight summability | ✓ DONE | 7c0dd7b |
| G4r | Closed-slab joint continuity | ✓ DONE | 8e8b1ae |
| G5 | Uniform S(t)u₀→u₀ for continuous u₀ | ✓ DONE | 809f1ac |
| G6 | PID-gate L² chain + eliminate hposWit | ✓ DONE | 25da5b3+2d8cdcf |
| G7 | ReachableArbitrarilyLong from hlocal+hUniform | ✓ DONE | 625fa56 |
| F2 | Resolver direct time regularity | ✓ DONE | a32f923 |

## Remaining frontier for unconditional Paper 2 Theorem 1.1

### Proved chain (axiom-clean)
```
Picard FP → iterate C² induction → DuhamelSourceTimeC1 limit (G2.5)
→ regularity bootstrap → localExistence
→ γ≥1 umbrella (no hposWit, G6) → L² uniqueness (PID-gated)
→ δ-iteration (G7) → Theorem_1_1
```

### Assembly theorem
```lean
paper2_theorem_1_1_of_frontier:
  hUniform + hMildLocal → Theorem_1_1 intervalDomain p
```

### Regularity frontier data: 15/15 fields proved
- 12 unconditional (u-side time + spatial, v-side spatial, sup-norm)
- 3 from ResolverHasSpectralAgreement (v-side time, constructible from F2)

### Two genuine remaining hypotheses

**F1: IntervalDomainUniformLocalExistence** (textbook continuation δ(M))
- For every M>0, ∃ δ>0 such that any classical solution with |u₀|≤M extends by δ
- Standard PDE (Henry/Amann); requires restart-before-end + overlap glue
- Estimated ~200 lines

**F2 (partially resolved): DuhamelSourceTimeC1 for the Picard limit**
- G2.5 reduces to uniform convergence of iterate source coefficient derivatives
- F2 direct resolver regularity proved (IntervalResolverDirectTimeRegularity)
- Remaining: instantiate the uniform convergence hypothesis from Picard data
- Estimated ~150 lines

## Other paper theorems

### Gap 2: Paper1 Theorem 1.1 (traveling wave existence)
Requires Schauder fixed point on the whole line (not interval domain).
Mathematically hardest gap.

### Gap 3: Paper1 Thm 1.2/1.3 (stability/uniqueness)
Depends on Gap 2.

### Gap 4: Paper2/Paper3 semigroup estimates (Lemma 2.1-2.4)
Mechanical but large. Zero-data branches proved.

## Priority order
1. F1 + F2 instantiation → Paper2 Thm 1.1 unconditional (~350 lines)
2. Gap 4 (semigroup estimates): mechanical
3. Gap 2 (whole-line Schauder): mathematically hardest
4. Gap 3 (weighted stability): depends on Gap 2

## Build
On uisai1: `PATH=$HOME/.elan/bin:$PATH lake build`

## 2026-06-06 night update — hQuant driven to a single shared residual

The "Two genuine remaining hypotheses" section above is STALE. Current map:

### hQuant (uniform δ(M) local existence) — Session B campaign, all green/axiom-clean
- **χ₀ = 0 (cone route, COMPLETE modulo one hypothesis):**
  `ConeQuantBridge.quantitativeLocalExistence_chiZero` — Picard contraction
  AND positivity proved (exponential cone invariance, uniform δ(p,M),
  no inf-threshold). Residual: `PicardLimitRestartFrontier` only.
  End-to-end: `paper2_theorem_1_1_chiZero_of_frontier` (+ hlocal).
- **General χ₀ ≤ 0 (threshold route, conditional):**
  `QuantFromThreshold` + `ThresholdQuantBridge`: hQuant ⟸ proved-δ(M,c)
  threshold Picard + `ClassicalMinPersistence` (min principle, open) +
  `PicardLimitRestartFrontier` + hlocal.
- **Key new infrastructure** (axiom-clean): Chapman–Kolmogorov
  `IntervalSemigroupComposition` (S(s)S(t)=S(s+t) via S1 spectral identity),
  cone atoms (mono/Duhamel-eval/kernel strict positivity), generic
  `gradientMildSolutionData_initialApproach` (hInitialApproach is no longer
  part of any per-datum frontier for continuous data).

### Unified residual
`PicardLimitRestartFrontier p` (ConeQuantBridge): restart source data +
frontier core for every packaged D with `D.u = picardLimit p u₀ D.T`.
One S-construction discharge (Session A's M-line, in flight) closes
hQuant(χ₀=0), the threshold route's Picard half, and hlocal(χ₀=0).

## 2026-06-09 — Thm 1.1 chain compilation green

### Chain status (ContinuousExtension → … → Provider)
Full 7-file chain compiles end-to-end on uisai2 (lake build green):
```
IntervalDomainContinuousExtension (0 sorry)
→ IntervalPicardLimitRestartWeak (0 sorry, eigenvalue summability proved)
→ IntervalDomainConstExtendAdapter (1 sorry: adapter body)
→ IntervalDomainMildLocalChi0 (1 sorry: restartData_of_inputs)
→ IntervalDomainThm11ChiZeroFinal (0 sorry)
→ IntervalDomainLedgerSweep (2 sorry: time-quantified → global adapters)
→ IntervalDomainThm11ChiZeroCoreProvider (17 sorry: analytic estimates)
```

### Key fix: namespace opens for `intervalLogisticSource` / `cosineMode`
Six files needed `open ShenWork.IntervalDomainExistence (intervalLogisticSource)`
and `open ShenWork.CosineSpectrum (cosineMode)`. Without these, all definitions
using these names silently became autoImplicit variables, cascading "Function
expected" errors.

### RestartWeak eigenvalue summability (NEW, 0 sorry)
`summable_eigenvalue_mul_abs_limitCoeff_weak`: proved via FTC envelope
computation + triangle split + `Summable.of_nonneg_of_le`. The proof handles:
`abs_add` → `abs_add_le` rename, `gcongr` → explicit `add_le_add` /
`mul_le_mul_of_nonneg_left`, `continuous_const` domain inference in tactic mode,
`-(t-s)*λ_k` parse order, `neg_zero` in simp set.

### Provider sorry inventory (17 items)
- G1, G2 — gradient/Hessian bound VALUES
- hG1t, hG2t — gradient/Hessian bound PROOFS
- adott family (5) + adotS family (5) — K1 time-C¹ data
- hpde_u, Hvsrc, Hvpos — PDE/resolver residuals
- hsrc0 (×2 in final wiring) — DuhamelSourceL1Cont

### LedgerSweep interface gap — RESOLVED 2026-06-09 night (horizon localization)
See HANDOFF/horizon-localization-design.md + HANDOFF/horizon-retype-status.md.
Landed (all green, 8521 jobs): C¹ soft clamp (IntervalTimeSoftClamp) +
clamped-witness TimeC1 producer (IntervalDomainClampedSourceRepresentation) +
weak-chain horizon retype (DuhamelSourceL1ContOn) + Hu_of_restart_localized
(0 sorry) + ledger V2 (per-compact hG1t/hG2t/hMdott, (0,T) K1, 5 shifted-K1
fields deleted, hsrc0 field) + K2 gradient producers wired + Hvpos proved
(mildChemicalConcentration_pos) + hpde_u producer (IntervalDomainPdeUProducer).

Sorry inventory end of 2026-06-09 (8, all satisfiable types; see
HANDOFF/horizon-retype-status.md header for the live ledger):
- Provider: hsrc0F (BddOn patched-family migration pass; producer is DONE
  0-sorry in IntervalPicardLimitBddProducer), K1 quadruple ×4 (R2 weak spine
  — NOT uniform-convergence/F2 after all; ChatGPT-verified route: weak
  restart identity → c_k' = −λ_k c_k + A_k by FTC → term-wise diff; first
  attempt was circular, fix in flight), Hvsrc
- PdeUWiring: 1 K1 bundle (same data as the quadruple)
- restartData_of_inputs + hasRestartData_of_subtypeCont (restart packaging)
Discharged today beyond the 10-list: Hu_of_reduced (subtype variant),
hpde_u (surrogate retype killed the false lift-continuity field).

### Option A SETBACK (Q1076): floor-weakening alone insufficient
FlooredSourceTimeData's 6 sorry are NOT trivially fillable after weakening:
- d0-d1: need positivity floor (0 < u(t,x)) for rpow chain rule
- zerothBound/laplBound: need UNIFORM bounds ∀ t > 0, but source derivatives
  blow up as t → 0 for merely continuous initial data
NEXT: further weaken zerothBound/laplBound to per-compact-window (∀ t ∈ [c,T]),
or restructure the consumer chain to accept window-local data directly.

## 2026-07-04 — Assembly Filler Residuals: Architecture Map

### Assembly target chain
```
(hsol, hcross, hboot, hinputs, hbdns)
  → IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals  [assembly filler]
    → IntervalDomainMassLpSmoothingRouteResiduals               [global chain]
      → aprioriBound / seedData                                 [existence]
```

### Assembly filler (P3MoserAssemblyFiller.lean) — 7 input hypotheses

| Hypothesis | Status | Notes |
|-----------|--------|-------|
| hbdns (BoundednessHyp) | ✅ parameter | correctly carried |
| hClosedTrace | chains through hFTC + zero-deriv | see below |
| hFTC | conditional on hderivInitial | task 20 produced `P3MoserFTCGlobalProducer.lean` |
| hClassicalRegularity | ✅ discharged | via `intervalDomain_classicalRegularitySupplier_global_withInitialSlice` |
| hBoundedBefore | conditional on crossing step + endpoint | task 21 report in `P3MoserBoundedBeforeProducer.lean` |
| hGap | ❌ must remain carried | coefficient analysis: `2 < pExp * Acoef` FAILS for current coefficients |
| hDyadicEndpoint | open frontier | dyadic Moser iteration construction needed |

### Global assembly wiring (P3MoserAssemblyGlobalWiring.lean, task 19)
Wires assembly filler into global chain: `hinputs → hClassicalRegularity` discharged;
remaining 6 hypotheses forwarded.

### Dependency chain for hClosedTrace
```
hClosedTrace
  ← closedEnergyIdentityTraceData_withInitialSlice_of_globalPDEInitialData
     ← hFTC (IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData)
     ← hzero (IntervalDomainL2SeedZeroRightDerivative) — task 10 ✅
     ← hglobal (IsPaper2GlobalClassicalSolution) — from hinputs
```

### hFTC residual (task 20)
`intervalDomain_assemblyFTC_of_globalInputs` needs:
- `hinputs` (have)
- `hderivInitial : IntegratedMoserEnergyDerivativeInitialWindowIntegrability`
  (new residual — initial-window derivative integrability from PDE data)

### hBoundedBefore residual (task 21)
Cannot be produced from `(hsol, hcross, hboot)` alone. Needs:
- Preferred route: `IntegratedMoserFirstCrossingStep` + quantitative endpoint
- Older route: physical-B dissipation + relative interpolation + endpoint
Both routes need the quantitative endpoint (Moser iteration closure).

### Net carried residuals (as of task 19-21)
1. **hGap** — must remain carried (coefficient regime dependent)
2. **hDyadicEndpoint** — dyadic Moser iteration construction
3. **hderivInitial** — initial-window derivative integrability for FTC
4. **hBoundedBefore sub-residuals** — crossing step + quantitative endpoint
5. **hClosedTrace** — chains through hFTC, so residual = hderivInitial

### Bottom-level PDE residuals (where the wiring bottoms out)

The assembly filler's 7 hypotheses reduce, after tracing all producer chains, to
5 irreducible PDE residuals:

1. **hGap** (`LpBootstrapEnergyInequalityWithGap`) — **CRITICAL BUG CONFIRMED**.
   Current eps = A0/(2*(chiBound+1)) gives pExp*Acoef → 2⁻ for χ₀ ≠ 0.
   For χ₀ ≥ 1, gap `2 < pExp*A` is NEVER satisfiable — all downstream vacuously true.
   FIX: p-dependent eps = A0/(p*(chiBound+1)) gives pExp*Acoef → 4 (Python-verified).
   Task 22 dispatched for the refactor.

2. **PDE initial-time regularity** (`IntervalDomainLpPDETermInitialWindowIntegrability`)
   — integrability of diffusion/chemotaxis/logistic terms near t=0. This is the base
   of the chain: PDETermInitial → PDECombinedInitial → WeightedTimeTerm →
   PowerDerivIntegral → MoserDerivativeInitial → FTC → ClosedTrace.

3. **IntegratedMoserFirstCrossingStep** — Moser crossing step for hBoundedBefore.
   Producer exists in P3MoserRegularityProducer.lean but needs
   `IntegratedMoserDissipationDropBefore` + `RelativeMoserInterpolationBefore`
   (circular with hBoundedBefore).

4. **IntervalDomainMoserQuantitativeEndpoint** — quantitative endpoint for hBoundedBefore.
   Produced from `DyadicMoserEndpointRecurrence` (item 5).

5. **DyadicMoserEndpointRecurrence** — the dyadic Moser iteration construction
   (hDyadicEndpoint). Core construction of the doubling sequence.

Items 3-5 form the Moser iteration closure: crossing → all-Lp-bounded → bounded-before,
with the dyadic iteration (5) feeding the quantitative endpoint (4).

### Codex task ledger (cumulative)

| Task | Frontier | File | Status |
|------|----------|------|--------|
| 9 | relativeMassGradient | P3MoserRelativeMassGradientProducer.lean | ✅ |
| 10 | zeroDeriv audit | P3MoserZeroDerivAudit.lean | ✅ |
| 12 | pdeCombinedInitial | P3MoserPDECombinedInitialProducer.lean | ✅ |
| 13 | integratedDissipation | P3MoserIntegratedDissipationPDE.lean | ✅ |
| 14 | quantitativeEndpoint | P3MoserQuantitativeEndpointDischarge.lean | ✅ |
| 15 | gradientIntegrability | P3MoserGradientIntegrabilityFromDissipation.lean | ✅ |
| 16 | Assembly filler v1 | P3MoserAssemblyFiller.lean | ✅ |
| 17 | Surplus fix | P3MoserIntegratedDissipationPDEv2.lean | ✅ BUILD_OK |
| 18 | Assembly filler v2 | P3MoserAssemblyFiller.lean update | ✅ BUILD_OK |
| 19 | Global assembly wiring | P3MoserAssemblyGlobalWiring.lean | ✅ (build needs lake) |
| 20 | FTC global producer | P3MoserFTCGlobalProducer.lean | ✅ (build needs lake) |
| 21 | BoundedBefore investigation | P3MoserBoundedBeforeProducer.lean | ✅ (report + wiring) |
| 22 | ε refactor for gap | P3MoserEnergyGapRefactor.lean | ✅ axiom-clean (fixes vacuity bug) |
| 23 | Initial-time regularity | P3MoserInitialTimeRegularity.lean | ✅ axiom-clean (18s) |
| 24 | No-bound relative interp | P3MoserRelativeInterpolationNoBound.lean | ✅ axiom-clean (confirms circularity real) |
| 25 | First-crossing continuation | P3MoserFirstCrossingContinuation.lean | ✅ axiom-clean (circularity broken) |
| 26 | Gap wiring | P3MoserGapProducerWiring.lean | ✅ axiom-clean (wires T22 into assembly) |
| 27 | Continuation wiring | P3MoserContinuationWiring.lean | ✅ axiom-clean (replaces circular hBoundedBefore) |
| 28 | Real induction (Residual D) | P3MoserRealInduction.lean | ✅ axiom-clean (5 theorems, 2 sub-residuals) |
| 29 | Short-time bounded (Residual A) | P3MoserShortTimeBounded.lean | ✅ axiom-clean UNCONDITIONAL |
| 30 | Continuity extension (Residual C) | P3MoserContinuityExtension.lean | ✅ axiom-clean UNCONDITIONAL |
| 31 | Subinterval input | P3MoserSubintervalInput.lean | ✅ axiom-clean (2 sub-residuals: τ>0 + Lp uniform) |
| 32 | Real induction closure | P3MoserRealInductionClosure.lean | ✅ axiom-clean (1 sub-residual: uniformization) |
| 33 | Uniformization | P3MoserUniformization.lean | ⏳ dispatched |

### Residual discharge status (post tasks 31-32)

T25's 4 named residuals for breaking the circularity:
| Residual | Status | Discharged by |
|----------|--------|---------------|
| A: ShortTimeBoundedBefore | ✅ UNCONDITIONAL | T29 (compactness of [0,1] + classical regularity) |
| B: SubintervalAssembly | ✅ wired | T27 (continuation wiring) |
| C: ExtensionByContinuity | ✅ UNCONDITIONAL | T30 (time continuity + compactness) |
| D: FirstCrossingSupremumClosure | ✅ conditional → T28+T32 | T32 proves τ*=T by real induction |

T28's sub-residuals:
| Sub-residual | Status | Task |
|-------------|--------|------|
| SubintervalMoserInputResidual | ✅ T31 | conditional on τ>0 + Lp uniform |
| FirstCrossingPointwiseUniformClosureResidual | ✅ T32 | conditional on PointwiseUniformization |

T31-T32 final frontier (3 sub-residuals converging to 1 issue):
| Sub-residual | Status | Nature |
|-------------|--------|--------|
| SubintervalPositiveTimeResidual | ⏳ | interface mismatch: τ ≥ 0 but needs τ > 0 |
| SubintervalLpPowerBoundResidual | ⏳ | uniform Lp bound from per-t bounds |
| PointwiseUniformizationResidual | ⏳ T33 | per-t to uniform L∞ bound |

The last two converge to the SAME core analytic fact: a classical solution with joint
space-time continuity on intervalDomain has uniform bounds on compact time subintervals.
T33 dispatched to investigate and discharge.

### H1 strict-window component continuity (2026-07-05)

Task 58 adds `IntervalChiNegH1LapComponentContinuity.lean`.
It proves that closed-slab joint continuity of `liftDeriv2 u` gives
continuity of `lapL2sq u` on every strict positive-time closed window
`[a,b] ⊂ (0,T)`.

This is a real component-continuity lemma, but it is not an endpoint closure:
the theorem deliberately assumes `0 < a`, matching
`H1LiftDeriv2JointContinuousBefore`. It does not discharge any record field
that requires continuity on windows starting at `a = 0`.

Task 59 adds `IntervalChiNegH1LiftDeriv2Transfer.lean`.
It fixes the next seam shape: to produce
`H1LiftDeriv2JointContinuousBefore`, it is enough to provide a jointly
continuous strict-slab representative `F` and an `EqOn` proof that `F` agrees
with `liftDeriv2 u` on each strict slab. The file also immediately routes this
to `H1UxxL1ContBefore`.

Task 60 extends that seam to the physical PDE RHS shape. It defines
`liftDeriv2PhysicalRHS p u v = u_t + χ₀ chemotaxisDiv - reaction`, proves this
RHS is continuous on any set from continuity of its time / chemotaxis /
reaction components, and packages strict-slab component continuity plus an
explicit `EqOn` proof into both `H1LiftDeriv2JointContinuousBefore` and
`H1UxxL1ContBefore`.

It also proves that an `IsPaper2ClassicalSolution` supplies the time-derivative
and logistic-reaction component continuity on every strict slab. The remaining
upstream inputs for this H1 route are now exactly: strict-slab continuity of
the lifted `chemotaxisDiv` term, and the `EqOn` proof identifying `liftDeriv2`
with the physical RHS on closed spatial slabs. This is still not the
chemotaxis-divergence or endpoint-equality producer.

Task 62 adds the endpoint-insensitive L¹ variant of the same seam. The new
theorem `H1UxxL1ContBefore_of_strictSlab_interior_eq_continuous` runs
`l1_time_continuity_at_of_jointContinuousOn_slab` on a continuous closed-slab
representative `F`, then transfers the spatial interval integral back to
`liftDeriv2` using `intervalIntegral.integral_congr_ae`. Thus the L¹ route only
requires `EqOn` on `Icc a b ×ˢ Ioo 0 1`; endpoint equality at `x = 0,1` is no
longer needed for `H1UxxL1ContBefore`.

The stronger route to `H1LiftDeriv2JointContinuousBefore` still requires closed
spatial endpoint equality. Q3415/Q3417 both flag the literal lifted
`chemotaxisDiv` endpoint as a real zero-extension derivative trap, so the next
honest frontier is a continuous physical representative plus interior equality,
not a silent closed-endpoint congruence.

Task 63 adds the abstract chemotaxis-divergence representative seam inside
`IntervalChiNegH1LiftDeriv2Transfer.lean`. The new RHS
`liftDeriv2PhysicalRHSWithChemRep p u chemRep` replaces the endpoint-bad
literal lifted chemotaxis-divergence term by an arbitrary closed-slab
continuous `chemRep`; `H1UxxL1ContBefore_of_classical_chemRep_eq_physicalRHS_interiorEq`
then combines:
1. closed-slab continuity of `chemRep`,
2. interior equality between actual lifted `chemotaxisDiv` and `chemRep`, and
3. interior equality between `liftDeriv2` and the old physical RHS,
to produce `H1UxxL1ContBefore`.

This is only an interface reduction. It does not construct the concrete
`chemRep`, and it does not claim endpoint continuity/equality for the literal
lifted chemotaxis-divergence term. A concrete representative producer can now
target the two remaining inputs above without touching the L¹ transfer proof.

Task 63 concrete producer adds
`IntervalChiNegH1ChemDivRepresentative.lean`. It defines
`liftChemotaxisDivPhysicalRep p u v`, the product-rule expression
`u_x v_x/(1+v)^β + u(μv-νu^γ)/(1+v)^β - β u v_x^2/(1+v)^(β+1)`,
and proves
`liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution`
from the existing joint continuity of `u`, `v`, `u_x`, `v_x`, and the elliptic
reaction representative for `v_xx`. The file also specializes the abstract seam
to this concrete representative via
`H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_interiorEq` and
`H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_eq_physicalRHS_interiorEq`.
The remaining frontier is the interior product-rule EqOn identifying the
literal lifted `chemotaxisDiv` with this representative; endpoint equality is
still deliberately not claimed.

Task 64 closes that interior product-rule EqOn using the already-proved
resolver representative route rather than reproving the full quotient
calculus.  The file now imports
`IntervalCoupledClassicalBallEstimates` and proves:
- `intervalChemDivRepr_eq_liftChemotaxisDivPhysicalRep_interior`, rewriting
  the resolver factors with `solution_lift_v_deriv_eq_resolverGrad`,
  `solution_v_eq_resolver_pointwise_unconditional`,
  `sourceValue_eq_source`, and
  `intervalNeumannResolverRLap_elliptic_identity`;
- `lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior`, combining
  the literal interval-domain branch with
  `intervalDomainChemotaxisDiv_eq_chemDivRepr_interior`;
- `lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_strictSlab_interior`,
  the strict-slab `EqOn` on `Icc a b ×ˢ Ioo 0 1`.

Together with the physical-RHS PDE EqOn bridge in
`IntervalChiNegH1LiftDeriv2Transfer`
(`liftDeriv2_eq_liftDeriv2PhysicalRHS_strictSlab_interior_of_classicalSolution`
and `H1UxxL1ContBefore_of_classical_chemRep_eq_chem_interiorEq`),
the final wrapper
`H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep` now produces
`H1UxxL1ContBefore u T` directly from `IsPaper2ClassicalSolution`.  The literal
lifted `chemotaxisDiv` endpoint equality is still intentionally not claimed.

Task 65 wires that concrete `H1UxxL1ContBefore` producer into the downstream
H1 scalar-DI / endpoint / bridge wrappers.  New wrappers in
`IntervalChiNegH1DerivativeIntegrability`, `IntervalChiNegH1InitialWiring`, and
`IntervalChiNegH1BridgeInitialWiring` remove the explicit `hUxxL1` parameter
whenever an `IsPaper2ClassicalSolution` is already in scope.  This closes the
H1 `u_xx` carry for these routes; the remaining honest inputs are now the H1
identity/RHS package or component-continuity route package, the split
initial-energy endpoint data, the restricted local H1 seed, and the physical
sqrt-bound estimates.

Task 66 adds the small zero-slice compatibility bridge in
`IntervalChiNegH1InitialContinuity`: `u 0 = u₀` (or pointwise equality of the
stored zero slice) implies `H1InitialEnergyCompatibleAtZero u₀ u` by unfolding
`H1energy` and `H1InitialEnergy`.  This is useful for mild/finite routes that
already carry exact zero-slice equality, but it deliberately does not prove the
deleted-right convergence field `H1InitialTraceEnergyTendsto`; ordinary
`InitialTrace` is only a sup-norm right trace and remains too weak for that H1
energy limit.

Task 67 records the Q3428 audit conclusion in the API: the two H1 endpoint
fields are now bundled as
`IntervalChiNegH1InitialContinuity.H1InitialEndpointData`.  It contains exactly
`H1InitialTraceEnergyTendsto u₀ u T` and
`H1InitialEnergyCompatibleAtZero u₀ u`; it is not a producer of the deleted-right
H1 trace.  `IntervalChiNegH1InitialWiring` and
`IntervalChiNegH1BridgeInitialWiring` add thin `*_initialEndpointData` wrappers
for the scalar-DI, bounded-before, parametric/spectral, and component-continuity
routes by projecting those two fields into the existing
`*_initialTraceEnergy` theorem family.  The hard frontier remains a genuine H1
trace theorem producing `H1InitialTraceEnergyTendsto`.

Task 68 strengthens the positive-time lap component continuity seam without
claiming any time-zero endpoint.  `IntervalChiNegH1LapComponentContinuity` now
has
`lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous` and its
strict-window family version: a closed-slab continuous representative `F` plus
interior `EqOn` with `liftDeriv2 u` implies continuity of
`τ ↦ lapL2sq u τ` on strict positive-time closed windows.  This mirrors the L1
`u_xx` transfer and avoids requiring equality at spatial endpoints.  It still
does not fill the current `H1IdentityRHSComponentsContinuousBefore.lap_cont`
field globally, because that record asks for windows with `0 ≤ a`, including
`a = 0`; the landed theorem only covers `0 < a`.

Task 69 records that `0 < a` / `0 ≤ a` mismatch in the bridge API rather than
silently strengthening the analysis.  Q3431 independently confirms that the
zero-endpoint lap-continuity input is a genuine H2/lap-trace frontier, not a
consequence of `H1InitialEndpointData`, `H1UxxL1ContBefore`, the classical
solution record, or scalar H1 regularity.  `IntervalChiNegH1LapComponentContinuity`
therefore names this explicit frontier as
`H1LapComponentEndpointContinuousBefore` and proves the pure combiner
`lapL2sq_continuousOn_before_of_endpoint_and_strict`.

`IntervalChiNegH1Bridge` now has
`H1IdentityRHSComponentsContinuousStrictBefore`, with all four component fields
quantified over strict positive-time windows, plus constructors that fill the
strict `lap_cont` either from `H1LiftDeriv2JointContinuousBefore` or from a
continuous closed-slab representative plus interior `EqOn`.

For the existing closed-window package
`H1IdentityRHSComponentsContinuousBefore`, Task 69 adds only honest reducers:
`H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict`,
`..._of_liftDeriv2_jointContinuousBefore_and_lap_zero`, and
`..._of_strictSlab_interior_eq_continuous_and_lap_zero`, together with
record-style `..._lapEndpoint` variants.  Each route requires an explicit
zero-starting-window input
`∀ {b}, 0 ≤ b → b < T → ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc 0 b)`.
That endpoint lap-continuity field is not provided by the strict positive-time
producers and should not be confused with `H1InitialEndpointData`, which only
bundles H1 energy trace/compatibility data.

Task 70 discharges the restricted local H1 seed needed by the H1 averaged
route.  `IntervalChiNegH1AverageWiring` now proves
`exists_H1_localSeed_of_scalarDI_before`: from `0 < T` and
`H1ScalarDIOnBefore u T A B` alone, there is a `Ylocal` with
`H1energy u τ ≤ Ylocal` for `τ ∈ (0,1]` and `τ < T`.

Q3432 identified the scalar-DI seed as the next target; Q3433 audited the
endpoint issue.  Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` cannot
be applied directly on `[0, τ]`, because the current scalar-DI record gives the
right-derivative and derivative inequality only for strictly positive times.
The landed proof avoids a new open-left Gronwall lemma: it first bounds
`H1energy` on `[0, T/2]` by compactness and `hDI.hcont`, then applies Mathlib
Gronwall only on `[T/2, τ]` for points beyond that initial compact interval.
Thus no PDE input, bounded-before assumption, or `H1InitialEndpointData` is
needed once `H1ScalarDIOnBefore` is available.

`IntervalChiNegH1AverageWiring` also exposes
`intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_before`, a no-manual
`hlocal` variant of the paper-positive scalar-DI bounded-before wrapper.
`IntervalChiNegH1InitialWiring` adds only a thin
`exists_H1_localSeed_of_scalarDI_initialEndpointData` wrapper for route APIs
that already carry endpoint data; the endpoint bundle is analytically unused by
the seed theorem.

Task 71 performs the route-facing cleanup enabled by Task 70.  The old
`*_local_*` wrappers are retained, but the derivative/RHS/sup-bound/initial H1
routes now also expose no-manual-`hlocal` variants that first produce
`H1ScalarDIOnBefore` and then call
`intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_before`.  The new
wrappers live in:
- `IntervalChiNegH1DerivativeIntegrability`: identity-RHS and sup-bound-DI
  integrable-RHS routes, including classical representative variants.
- `IntervalChiNegH1SupBoundDIProducer`: square-root sup-bound DI/RHS routes.
- `IntervalChiNegH1InitialWiring`: split `initialTraceEnergy` routes and bundled
  `H1InitialEndpointData` routes.

This removes the local H1 seed as a manual route hypothesis for those H1
bounded-before APIs.  It does not discharge the upstream producers for
RHS-integrability, H1 `u_xx` L1 continuity, sup-bound/square-root physical
frontiers, or the Task 69 zero-start lap-continuity seam.

Task 72 propagates the same no-manual-`hlocal` cleanup one layer higher through
`IntervalChiNegH1BridgeInitialWiring`.  Q3435 independently audited the file and
confirmed that the parametric/spectral initial wrappers still had a propagation
gap after Task 71.  The file now retains the old explicit-`hlocal` APIs and adds
sixteen `_before` wrappers mirroring the existing raw-RHS and
component-continuity parametric/spectral families, both for split
`initialTraceEnergy` data and bundled `H1InitialEndpointData`.  Each new wrapper
converts the route-specific package to `H1SupBoundSqrtRHSIntegrableBefore` and
then calls the corresponding Task71 InitialWiring `_before` theorem.

Q3434 separately audited the Task 69 lap endpoint seam and confirmed it remains
a genuine H2/laplacian trace frontier.  Existing committed infrastructure gives
H1 endpoint energy data, positive-time `u_xx` L1 continuity, and strict
positive-time `liftDeriv2` representative continuity/equality, but no theorem
produces `ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc 0 b)` for zero-start
windows.  A minimal future producer should either prove
`ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici 0) 0` plus combine it with
strict-window continuity, or supply a zero-slab continuous representative for
`liftDeriv2` on `[0,b] × [0,1]`.

Task 73 implements the first option as an honest API split, without proving the
new H2 trace fact.  `IntervalChiNegH1LapComponentContinuity` now names the
atomic zero-right frontier as horizon-free `H1LapComponentZeroRightContinuous`
and proves that this frontier plus strict positive-time `lapL2sq` continuity yields
`H1LapComponentEndpointContinuousBefore`.  Two convenience wrappers fill the
strict part from either `H1LiftDeriv2JointContinuousBefore` or a strict-slab
continuous representative of `liftDeriv2`.  The remaining hard analytic input is
now exactly the zero-right `lapL2sq` continuity at `t = 0`, not the local H1
seed or positive-time `u_xx` continuity.  Q3437 confirmed that no committed
producer currently derives this from the existing H1/PDE APIs; it also led to
three additional reducers in the same file.  A zero-start continuous
representative `F` on `[0,b] × [0,1]`, together with interior equality to
`liftDeriv2`, now produces `H1LapComponentZeroRightContinuous`, and a zero-slab
family directly produces `H1LapComponentEndpointContinuousBefore`.  Thus the
next analytic atom is the zero-slab representative/equality itself.

Task 74 packages that remaining atom without touching the physical-RHS/transfer
route.  `IntervalChiNegH1LapComponentContinuity` now has the record
`H1LiftDeriv2ZeroSlabRepresentativeBefore`, whose fields are exactly the
zero-start continuous representative on `[0,b] × [0,1]` and interior equality to
`liftDeriv2`; this record produces both `H1LapComponentEndpointContinuousBefore`
and full closed-window `lapL2sq` continuity.  A small observation was also
formalized: once `H1LapComponentEndpointContinuousBefore` is known, no separate
strict lap-continuity hypothesis is needed to obtain closed-window lap
continuity on `[a,b]`, since `[a,b] ⊆ [0,b]`.  `IntervalChiNegH1Bridge` now has
component-continuity constructors from an endpoint record, from zero-right plus
positive-time `liftDeriv2`, and from zero-slab representative data.  The
remaining proof obligation is still a producer for
`H1LiftDeriv2ZeroSlabRepresentativeBefore`, expected to live in the
physical-RHS/transfer route.

Q3438 then pointed out a weaker route-facing form of the same atom: one
positive-length zero-start slab already implies the zero-right frontier, which
can then be combined with strict positive-time regularity.  Task 74 therefore
also names `H1LiftDeriv2ZeroSlabRepresentative` and the existential
`H1LiftDeriv2HasZeroSlabRepresentative`, with wrappers to
`H1LapComponentZeroRightContinuous`, to endpoint lap continuity using either
`H1LiftDeriv2JointContinuousBefore` or a strict-slab representative, and to the
Bridge component-continuity package.  The analytic producer may now target
either the minimal existential single-slab package or the stronger
before-`T` family package.

Q3439 and Q3442 independently audited the next producer route.  They reject
deriving the zero-time lap frontier from ordinary classical-solution data, H1
endpoint data, or `H1InitialTraceEnergyTendsto`; those would smuggle in H2/lap
trace.  They recommend the same physical-representative pattern used for the
positive-time `u_xx` frontier: construction-level mild/Picard data should
produce a zero-start continuous physical RHS representative, plus interior
equality to `liftDeriv2`.  Task 75 adds only the honest bridge layer in
`IntervalChiNegH1ZeroSlabPhysicalRHS`: a continuous zero-start representative
or the concrete `liftDeriv2PhysicalRHSWithChemRep` component package now
produces `H1LiftDeriv2ZeroSlabRepresentative` /
`H1LiftDeriv2HasZeroSlabRepresentative`, and the before-`T` component wrapper
`H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHS_components`
feeds the stronger endpoint package.  The concrete
`liftChemotaxisDivPhysicalRep` wrappers
`H1LiftDeriv2HasZeroSlabRep_of_chemPhysical_components` and
`H1LiftDeriv2ZeroSlabRepBefore_of_chemPhysical_components` name the exact next
physical target.  No theorem yet produces those zero-start continuity/equality
inputs from the construction data.

Task 77 adds `IntervalChiNegH1PhysicalComponents`, a thin route-facing interface
for the other H1 frontier: one fixed triple of scalar RHS components
`taxisX`/`uvxx`/`reactX` must simultaneously provide pointwise
`H1EnergyIdentity`, the square-root term estimates, and closed-window component
continuity.  The record
`H1PhysicalSplitComponentDataBefore` packages those three facts and immediately
produces `H1SupBoundSqrtDIDataBefore`, `H1IdentityRHSIntegrableBefore`, and
`H1SupBoundSqrtRHSIntegrableBefore`.  This is not a proof of the physical
formulas or estimates; it is a non-vacuous target shape for a future producer.
In particular, the degenerate existential tuple from
`H1EnergyIdentity_of_classicalSolution_and_uxxL1Cont` still does not count as
the physical split, because Task 77 requires the same global component
functions to carry the sqrt estimates and continuity package.

The zero-start physical RHS route still does not have producers from the
existing strict-positive-time classical/mild regularity APIs for the closed
zero-start inputs.  Task 78 therefore adds the explicit frontier record
`H1ZeroStartPhysicalRHSDataBefore` in
`IntervalChiNegH1ZeroSlabPhysicalRHS`: zero-start continuity of `liftTimeDeriv`,
`liftChemotaxisDivPhysicalRep`, and the reaction component, plus interior
equality of `liftDeriv2` with the concrete physical RHS.  The adapter
`H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHSData` feeds this exact
record into the existing zero-slab representative route.  This remains an
honest construction-level target, not a theorem from the current
`IsPaper2ClassicalSolution` API.
Task 78 also isolates the algebraic reaction component:
`logisticReaction_continuousOn_zeroSlab_of_lift_continuous_positive` proves
zero-start reaction continuity from zero-start lift continuity and positivity,
and `H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHS_lift_positive`
uses that helper so the remaining hard fields are the zero-start time
derivative, chem representative, lift continuity/positivity, and interior PDE
equality inputs.

Task 79 continues the same zero-start physical RHS route with
`IntervalChiNegH1ZeroStartComponents`.  The new primitive record
`H1ZeroStartPhysicalPrimitiveDataBefore` asks for zero-start continuity of
`u`, `v`, `u_x`, and `v_x`, positivity/nonnegativity, zero-start
`liftTimeDeriv` continuity, and the endpoint-including interior equality.
The algebraic theorem
`liftChemotaxisDivPhysicalRep_continuousOn_zeroSlab_of_primitives` proves the
concrete chemotaxis-divergence representative continuous on `[0,b] × [0,1]`
from those primitive continuity fields, and
`H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData` feeds the result
through Task 78's physical-RHS data package.  After Task 79, the easy reaction
and chem algebra are no longer frontier fields; the remaining analytic
zero-start obligations are primitive closed-time regularity of
`u`, `v`, `u_x`, `v_x`, `liftTimeDeriv`, positivity/nonnegativity at `t = 0`,
and the interior PDE equality for `liftDeriv2`.

Task 80 opens the honest strict-positive-time/cutoff route in
`IntervalChiNegH1AverageWiring` and `IntervalChiNegH1WindowWiring`.  The new
`H1ScalarDIOnStrictBefore` asks for scalar continuity, derivative
integrability, and right-derivative data only on windows with positive left
endpoint.  It proves `H1_avg_of_scalarDI_strict_before` only for `τ > 1`;
the downstream strict-average window wrappers use the existing local H¹ seed to
cover `τ ≤ 1`.  The route therefore avoids querying continuity/integrability on
the zero-starting window `[0,1]`; the necessary near-zero input is now explicit
as `hlocal : ∀ τ ∈ (0,1], τ < T → H1energy u τ ≤ Ylocal`.

Task 81 implements the narrower route-C adapter suggested by Q3453 in
`IntervalChiNegH1StrictRHSIntegrability`.  Instead of upgrading strict
positive-time component continuity to zero-start `lapL2sq` continuity, the new
`H1IdentityRHSInitialWindowIntegrableBefore` asks only for initial-window
integrability of the assembled H¹ identity RHS.  The adapter
`H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow`
splits windows by left endpoint: strict component continuity handles positive
left endpoints, and the new initial-window integrability field handles the
zero endpoint.  The bounded-before wrapper then reuses the existing
`boundedBefore_of_H1supBoundDI_classicalChemRep_before` route unchanged.

Task 82 mirrors the P3/Moser initial-window pattern at the H¹ level.  The new
`H1EnergyDerivativeInitialWindowIntegrableBefore` is a scalar near-zero input:
`deriv (H1energy u)` is interval-integrable on every zero-starting window before
`T`.  The adapter
`H1IdentityRHSInitialWindowIntegrableBefore_of_deriv_initialWindow` uses the H¹
identity only on `Ioc 0 b` to turn that scalar derivative integrability into
assembled RHS initial-window integrability; the endpoint value at zero is not
used.  This keeps route C away from zero-start `lapL2sq` continuity while giving
future producers a simpler scalar derivative-integrability target.
The reusable congruence lemmas
`H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_uIoc` and
`H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_Ioc` record the reverse
direction from derivative integrability to explicit-RHS integrability.
The direct adapter
`H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_derivInitial` packages
strict component continuity plus this scalar derivative input straight into the
landed `H1IdentityRHSIntegrableBefore` interface.

Task 83 adds the construction-facing producer file
`IntervalChiNegH1InitialDerivativeProducer`, following Q3462.  It keeps two
frontiers separate from the strict RHS bridge:
`H1EnergyDerivativeInitialWindowProxyBefore`, for an integrable proxy agreeing
with `deriv (H1energy u)` on each `Ioc 0 b`, and
`H1EnergyDerivativeInitialWindowMajorantBefore`, for an integrable near-zero
majorant plus a.e. measurability and norm control.  The adapters
`H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy` and
`H1EnergyDerivativeInitialWindowIntegrableBefore_of_majorant` both produce Task
82's scalar derivative-initial input, still without zero-start `lapL2sq`
continuity or downstream bounded-before data.

Task 84 names the concrete physical H¹ RHS scalar triple in
`IntervalChiNegH1PhysicalRHSScalars`.  The pointwise pieces
`H1PhysicalChemTaxisPart`, `H1PhysicalChemUvxxPart`, and
`H1PhysicalLogisticReactionPart` are integrated against `liftDeriv2` to produce
the fixed scalar functions `H1PhysicalTaxisX`, `H1PhysicalUvxxX`, and
`H1PhysicalReactX`; the two chemotaxis pieces recombine algebraically to the
landed `liftChemotaxisDivPhysicalRep`.  The new route record
`H1PhysicalRHSRouteBefore` packages pointwise identity, square-root bounds, and
closed-window component continuity for this exact scalar triple, then feeds it
into Task 77's `H1PhysicalSplitComponentDataBefore` and the existing
sqrt/RHS integrability packages.  This is still an honest target interface:
the analytic component continuity, estimates, and PDE substitution equality
for the physical formulas remain to be produced upstream.

Task 85 standardizes the derivative-window side of route C in
`IntervalChiNegH1DerivativeWindowProducer`.  The new
`H1EnergyDerivativePositiveStartWindowIntegrableBefore` is produced from strict
component continuity plus the pointwise H¹ identity; it only uses windows with
positive left endpoint.  The theorem
`H1EnergyDerivativeWindowIntegrableBefore_of_initial_and_positiveStart` then
combines that positive-start package with Task 82's zero-start scalar input
`H1EnergyDerivativeInitialWindowIntegrableBefore` to recover full
pre-horizon derivative-window integrability.  The scalar regularity adapter
`H1ScalarRegularityBefore_of_uxxL1Cont_componentsStrictBefore_initial` feeds
this split into the existing `H1ScalarRegularityBefore` interface without using
`H1IdentityRHSIntegrableBefore`, bounded-before, or zero-start `lapL2sq`
continuity.

Task 86 adds `IntervalChiNegH1InitialDerivativeFTC` as the source-facing
zero-start H¹ derivative adapter requested by Q3463.  The new
`H1EnergyDerivativeInitialWindowAEProxyBefore` accepts an interval-integrable
proxy whose equality with `deriv (H1energy u)` holds a.e. on each `Ioc 0 b`,
which is the natural output shape of an integrated energy/FTC argument.  It
lowers to Task 83's `H1EnergyDerivativeInitialWindowMajorantBefore` by
a.e. measurability congruence and the trivial norm bound, then to
`H1EnergyDerivativeInitialWindowIntegrableBefore` through the existing majorant
adapter.  The optional `H1EnergyInitialWindowFTCBefore` frontier stores the
actual FTC identity while exposing only its integrable proxy and a.e. derivative
equality to the current route, so this bridge still does not use RHS
integrability, bounded-before, or zero-start `lapL2sq` continuity.

Task 87 adds `IntervalChiNegH1InitialDerivativeRHS`, the reverse initial-window
bridge for independently produced assembled H¹ RHS data.  Given the pointwise
positive-time H¹ identity and
`H1IdentityRHSInitialWindowIntegrableBefore`, the theorem
`H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow` uses
the explicit `H1IdentityRHSValue` as the proxy for `deriv (H1energy u)` on each
`Ioc 0 b`.  The file then lowers this to Task 86's a.e. proxy, Task 83's
majorant, and finally `H1EnergyDerivativeInitialWindowIntegrableBefore`.  This
adapter does not consume the full `H1IdentityRHSIntegrableBefore` package or
bounded-before data; its source hypothesis must still be produced independently
to avoid reintroducing the old circular route.
The same file also adds `H1IdentityRHSInitialWindowMajorantBefore`, a
source-facing near-zero L¹ majorant for the assembled RHS itself.  Its adapter
to `H1IdentityRHSInitialWindowIntegrableBefore` lets future physical estimates
target an RHS majorant directly before crossing into the derivative-proxy route.

Task 88 adds `IntervalChiNegH1PhysicalInitialRHS`, specializing the Task87
near-zero RHS majorant route to the concrete physical scalar triple from Task
84.  The new `H1PhysicalRHSStrictInitialRouteBefore` asks for the pointwise
physical H¹ identity, square-root estimates, strict-positive-time component
continuity, and an assembled physical RHS initial-window majorant.  It produces
the full `H1IdentityRHSIntegrableBefore`, the combined
`H1SupBoundSqrtRHSIntegrableBefore`, the scalar zero-start derivative
integrability input, and a bounded-before wrapper without requiring zero-start
component continuity.  This is still honest route wiring: the analytic physical
majorant, strict component continuity, bounds, and substitution identity remain
upstream producers.

Task 89 adds `IntervalChiNegH1PhysicalScalarContinuity`, a small interface layer
for the Task88 strict component-continuity input.  The file names the three
physical H1 scalar integrands and reuses the existing compact-slab integral
continuity bridge to turn strict-slab joint continuity of each integrand into
`ContinuousOn` facts for `H1PhysicalTaxisX`, `H1PhysicalUvxxX`, and
`H1PhysicalReactX` on every positive-start time window.  With an explicit
strict `lapL2sq` continuity input, or with the existing `liftDeriv2`/strict-slab
representative producers for that lap input, it packages
`H1PhysicalRHSComponentsContinuousStrictBefore`.  Following the Q3472 audit, it
also includes a representative-friendly version: a continuous strict-slab
representative `F` for `liftDeriv2 u`, equality only on the open spatial
interior, and continuity of the three physical non-lap parts are enough to
produce the same component package, avoiding endpoint continuity assumptions on
literal `liftDeriv2`.  It deliberately does not prove the hard joint continuity
of the physical formulas themselves, nor the near-zero majorant, square-root
bounds, or substitution identity.

Task 90 follows Q3470 and narrows the physical initial-window majorant frontier
from a global zero-start producer to a local endpoint producer.  In
`IntervalChiNegH1InitialDerivativeRHS`, `H1IdentityRHSZeroWindowMajorantBefore`
asks for one local majorant on `(0, delta]`; strict-positive-time component
continuity then extends this to `H1IdentityRHSInitialWindowMajorantBefore` and
initial-window RHS integrability on every zero-start window before `T`.  The
same file also adds reusable scalar majorant algebra and the pointwise norm
bound `H1IdentityRHSValue_norm_le_scalar_sum`, so termwise scalar estimates can
assemble the H¹ RHS majorant without consuming bounded-before, full RHS
integrability, or derivative integrability.

`IntervalChiNegH1PhysicalInitialRHS` now specializes the zero-window interface
to the physical scalar triple.  `H1PhysicalRHSAdditiveScalarZeroMajorantsBefore`
requires local scalar majorants for the lap, taxis, uvxx, and reaction terms on
one common zero window, and
`H1PhysicalRHSZeroWindowMajorantBefore_of_additiveScalarMajorants` packages them
into the assembled physical RHS zero-window majorant.  With strict physical
component continuity, this yields the global physical initial-window majorant
and the scalar zero-start H¹ derivative-integrability input.  All new Task90
theorems are wired with `#print axioms`; target build shows only
`[propext, Classical.choice, Quot.sound]`.

Task 91 connects the Task89 and Task90 interfaces into the physical strict/initial
route.  `IntervalChiNegH1PhysicalInitialRHS` now has the route constructor
`H1PhysicalRHSStrictInitialRouteBefore_of_additiveScalar_zeroWindow`, which
packages physical identity, square-root bounds, strict component continuity, and
additive local scalar zero-window majorants into
`H1PhysicalRHSStrictInitialRouteBefore`.  `IntervalChiNegH1PhysicalScalarContinuity`
then adds representative-integrand and direct part-continuity versions, so a
continuous strict-slab representative for `liftDeriv2`, continuity of the three
non-lap physical parts, and the additive zero-window scalar majorants assemble
the route without consuming bounded-before, full RHS integrability, or derivative
integrability.  This is route wiring only; the source PDE estimates remain the
continuity producers, additive local scalar majorants, physical identity, and
square-root bounds.

Task 92 makes the zero-window scalar majorant interface more source-friendly.
`IntervalChiNegH1PhysicalInitialRHS` adds
`H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore`, where PDE estimates may
provide nonnegative majorizing functions directly on the common zero window.
The adapter `H1PhysicalRHSAdditiveScalarZeroMajorantsBefore_of_nonneg` rewrites
these nonnegative bounds into the existing norm-majorant interface, and
`H1PhysicalRHSStrictInitialRouteBefore_of_nonnegScalar_zeroWindow` feeds that
into the Task91 route constructor.  `IntervalChiNegH1PhysicalScalarContinuity`
adds representative-integrand and direct part-continuity wrappers consuming the
same nonnegative scalar majorants.  This remains wiring: the hard source
producers are still the local nonnegative scalar bounds, strict-slab
continuity, physical identity, and square-root bounds, not bounded-before,
full RHS integrability, or derivative integrability.

Task 93 moves the zero-window scalar-majorant frontier one step closer to the
usual Cauchy/Young PDE estimates.  `IntervalChiNegH1PhysicalInitialRHS` adds
`H1PhysicalRHSYoungScalarZeroMajorantsBefore`: a shared nonnegative lap
majorant plus three nonnegative product remainders control the physical taxis,
uvxx, and reaction scalars in the form expected after applying Young's
inequality.  The adapter
`H1PhysicalRHSAdditiveNonnegScalarZeroMajorantsBefore_of_young` mechanically
turns these bounds into Task92's nonnegative additive scalar majorants, and
`H1PhysicalRHSStrictInitialRouteBefore_of_youngScalar_zeroWindow` feeds them
into the strict/initial route.  `IntervalChiNegH1PhysicalScalarContinuity` adds
representative and direct strict-slab wrappers for the same Young-style input.
The actual analytic producers are still the component-square estimates and the
raw lap time-integrability data; no downstream bounded-before or RHS
integrability package is used.

Task 94 follows the Q3483 audit and pulls the Young-style frontier down to
primitive component-square data without proving the hard spatial Cauchy/Young
estimates.  `IntervalChiNegH1InitialDerivativeRHS` adds
`H1IdentityRHSValue_aestronglyMeasurable_of_components`, so future source
producers can assemble RHS measurability from the lap, taxis, uvxx, and
reaction scalar measurability fields.  `IntervalChiNegH1PhysicalInitialRHS`
names the square profiles `H1PhysicalTaxisPartSq`,
`H1PhysicalUvxxPartSq`, and `H1PhysicalReactPartSq`, then adds
`H1PhysicalRHSComponentSquareZeroDataBefore`: one common zero-window package
carrying assembled RHS measurability, raw `lapL2sq` integrability, the three
square-profile integrability fields, and the three local Young product
estimates.  The adapter
`H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData`
lowers this package to Task93's Young-style scalar majorants.  The remaining
source obligations are still the actual component measurability, local lap
integrability, square-profile integrability, and scalar-product estimates;
they must not be filled using downstream RHS integrability, derivative
integrability, strict/initial route data, or bounded-before packages.

Task 95 follows the Q3489 audit and starts the source-side spatial
Cauchy/Young layer without touching downstream H1 packages.
`GagliardoNirenberg` now exposes the interval Cauchy-Schwarz tools
`sq_integral_abs_mul_le` and `integral_abs_mul_le_sqrt`, plus the
Young half-square consequences `integral_abs_mul_le_half_sq_sum` and
`norm_integral_mul_le_half_sq_sum`.  The new
`IntervalChiNegH1PhysicalYoungSpatial` file proves the three fixed-time
physical product estimates for `H1PhysicalTaxisX`, `H1PhysicalUvxxX`, and
`H1PhysicalReactX`, then packages explicit source-side zero-window data:
time integrability of `lapL2sq` and the three square profiles, a.e.
spatial square integrability of `liftDeriv2` and each non-lap part, and a.e.
spatial absolute-product integrability.  This lowers to Task94
`H1PhysicalRHSComponentSquareZeroDataBefore`, and then to Task93
`H1PhysicalRHSYoungScalarZeroMajorantsBefore`.  The remaining hard producer is
now precisely the PDE/regularity theorem proving those time and a.e. spatial
integrability fields from primitive zero-start data, local denominator/source
bounds, and resolver estimates; it must not consume full RHS integrability,
derivative integrability, strict/initial route data, or `IsPaper2BoundedBefore`.

Task 96 follows Q3486/Q3487 and removes the strict-positive-time continuity
layer from the physical H¹ strict/initial route.  New file
`IntervalChiNegH1PhysicalClassicalContinuity` proves from
`IsPaper2ClassicalSolution intervalDomain p T u v` that the concrete physical
`liftDeriv2` representative
`liftDeriv2PhysicalRHSWithChemRep p u (liftChemotaxisDivPhysicalRep p u v)` is
continuous on every strict closed slab and agrees with literal `liftDeriv2 u`
on the open spatial interior.  It also proves strict-slab continuity of the
three Task84 non-lap factors
`H1PhysicalChemTaxisPart`, `H1PhysicalChemUvxxPart`, and
`H1PhysicalLogisticReactionPart`, then packages these as
`H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution` and
`H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution`.
Consequently `H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero`
and the component-square variant leave only the physical H¹ identity,
square-root bounds, and Task94 zero-window component-square data as route
frontiers.  This is still not a full headline proof: the physical
identity/substitution, sqrt estimates, and near-zero component-square/lap
integrability estimates remain analytic obligations.

The subsequent 5-round ChatGPT audit (Q3506--Q3519) confirmed that this route
is honestly conditional and should not be named as an unconditional physical
H¹ exit.  The next smallest non-circular step is local to the spatial Young
frontier: `GagliardoNirenberg` now also exposes the ordered helper
`intervalIntegrable_abs_mul_of_sq_integrable_of_aestronglyMeasurable`, which
turns square integrability of two factors plus a.e. strong measurability of
their absolute product into interval integrability of that absolute product.
This closes only a generic measurability/integrability API gap.  It does not
prove `H1PhysicalRHSComponentSquareSpatialYoungDataBefore` from a classical
solution; the time integrability of `lapL2sq` and the three physical square
profiles, RHS measurability, the physical identity, and sqrt bounds remain
open carries.

Task 98 completes the next R5 packaging step without changing that accounting:
`IntervalChiNegH1PhysicalYoungSpatial` now has
`H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_squareData_and_productMeas`.
The theorem keeps the zero-window scalar data explicit: one `δ`, RHS
measurability, time integrability of `lapL2sq` and the three physical square
profiles, a.e. spatial square integrability for the lap and three non-lap
factors, and a.e. strong measurability of the three absolute products.  It only
uses the generic GN helper to produce the three product-integrability fields.
It does not produce product measurability from classical regularity and does
not close any identity, sqrt, or time-integrability frontier.

Task 99 completes the R5 product-measurability producer:
`IntervalChiNegH1PhysicalClassicalContinuity` now has
`H1PhysicalRHSAbsProductsMeasBefore_of_classicalSolution`.  It uses the
strict-slab representative continuity package plus the interior a.e. equality
between literal `liftDeriv2` and the continuous physical RHS representative to
produce the three a.e. strong measurability fields for the absolute products on
`Ioc 0 1`.  This discharges only the product-measurability inputs exposed by
Task 98.  The square-integrability fields, time integrability of `lapL2sq` and
the three physical square profiles, RHS measurability, the physical identity,
and sqrt bounds are still explicit frontiers.

Task 100 removes the spatial part of the square-integrability carry:
`H1PhysicalRHSSpatialSquareIntegrableBefore_of_classicalSolution` now produces
the a.e. spatial square-integrability fields for literal `liftDeriv2` and the
three physical non-lap parts from strict-slab representative continuity.  This
does not produce time integrability of `lapL2sq` or of the physical square
profiles; those remain separate one-dimensional-in-time obligations, alongside
RHS measurability, the physical identity, and sqrt bounds.

Task 101 removes the assembled RHS measurability carry for the physical
component-square route.  Following the Q3533 audit,
`IntervalChiNegH1PhysicalClassicalContinuity` now has the local strict-window
adapter from `ContinuousOn f (Icc a b)` on all positive windows to
`AEStronglyMeasurable f (volume.restrict (Ioc 0 δ))`, and the concrete theorem
`H1PhysicalRHSValue_aestronglyMeasurableBefore_of_classicalSolution`.  It feeds
the four strict physical component-continuity fields into the existing
`H1IdentityRHSValue_aestronglyMeasurable_of_components` combiner.  This is only
RHS measurability: the time integrability of `lapL2sq` and the three physical
square profiles, the physical identity/substitution, and sqrt bounds remain
open frontiers.

Task 102 packages the source-facing spatial Young data down to exactly the
remaining time-integrability carries.  `IntervalChiNegH1PhysicalYoungSpatial`
now has
`H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_squareTimeIntegrable`,
which combines the classical RHS measurability producer, the classical
abs-product measurability producer, and the classical a.e. spatial
square-integrability producer, while keeping explicit assumptions for
`IntervalIntegrable (lapL2sq u)` and the three physical square profiles on
`(0, δ]`.  Thus the component-square zero-window route no longer separately
carries RHS measurability, product measurability, or a.e. spatial
square-integrability.  It still does not prove any of the four time
integrability assumptions, physical identity/substitution, or sqrt bounds.

Task 103 follows the Q3535 time-integrability audit.  The audit confirmed that
strict-positive-time classical continuity cannot imply zero-window time
integrability near `t = 0`; the missing input has to be zero-start analytic
data.  `IntervalChiNegH1PhysicalYoungSpatial` now proves
`H1PhysicalSquareProfilesTimeIntegrableBefore_of_zeroStartPrimitiveData`: from
`H1ZeroStartPhysicalPrimitiveDataBefore` it obtains zero-window
`IntervalIntegrable` data for `lapL2sq u`,
`H1PhysicalTaxisPartSq p u v`, `H1PhysicalUvxxPartSq p u v`, and
`H1PhysicalReactPartSq p u`.  The lap field uses the existing zero-slab
representative route; the three non-lap fields use zero-slab continuity of the
individual physical parts plus the interval-integral continuity helper.  The
new wrapper
`H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_zeroStartPrimitiveData`
then combines classical strict-slab regularity with that zero-start primitive
package to produce the full spatial Young data.  This removes the four
separate time-integrability carries only under `H1ZeroStartPhysicalPrimitiveDataBefore`;
it is not an unconditional headline theorem, and the physical
identity/substitution plus sqrt-bound frontiers remain separate.

Task 104 adds the post-Task103 route wrapper
`H1PhysicalRHSStrictInitialRouteBefore_of_classical_zeroStartPrimitiveData`.
It lowers the Task103 spatial Young data to
`H1PhysicalRHSComponentSquareZeroDataBefore` and then reuses the existing
classical component-square strict/initial route constructor.  The resulting
physical strict/initial route still explicitly assumes
`H1PhysicalRHSIdentityBefore`, `H1PhysicalRHSSqrtBoundsBefore`,
`H1ZeroStartPhysicalPrimitiveDataBefore`, and a positive zero window
`δ < T`.  Thus the route wiring from component-square estimates to the
strict/initial H¹ package is now local, but no new identity, sqrt-bound, or
zero-start primitive producer has been proved.

Task 105 adds the endpoint-data exit wrapper in the new
`IntervalChiNegH1PhysicalExit` file:
`boundedBefore_of_physical_classical_zeroStartPrimitiveData_initialEndpointData_before`.
It composes Task104's physical strict/initial route with
`boundedBefore_of_H1supBoundSqrtRHS_classical_initialEndpointData_before`, and
adds the module to `ShenWork.lean`.  This is still conditional route wiring:
it carries `H1PhysicalRHSIdentityBefore`, `H1PhysicalRHSSqrtBoundsBefore`,
`H1ZeroStartPhysicalPrimitiveDataBefore`, `H1InitialEndpointData`,
`IntervalDomainL2SeedRegularityFrontier`, and the usual initial/boundedness
environment.  Q3537 confirmed that identity, sqrt bounds, and the zero-start
primitive package are not currently derivable from `IsPaper2ClassicalSolution`
by a small wrapper.

Task 106 starts splitting the physical identity frontier into a smaller honest
piece.  The new `IntervalChiNegH1PhysicalIdentityRouteC` file defines
`H1PhysicalRHSRouteCSubstitutionBefore`, the exact equality that rewrites the
Route-C derivative value
`-∫ liftDeriv2 u τ x * liftTimeDeriv u τ x` into
`H1IdentityRHSValue` for the concrete physical scalar triple
`H1PhysicalTaxisX`, `H1PhysicalUvxxX`, and `H1PhysicalReactX`.  It proves
`H1PhysicalRHSIdentityBefore_of_classical_uxxL1Cont_routeCSubstitution`: from a
classical solution, `H1UxxL1ContBefore`, and that exact substitution frontier,
one obtains `H1PhysicalRHSIdentityBefore`.  This does not prove the physical
substitution equality; it isolates it as the remaining identity blocker instead
of carrying the whole physical identity package.

Task 107 closes that isolated Route-C substitution frontier.  In the same
`IntervalChiNegH1PhysicalIdentityRouteC` file,
`H1PhysicalRHSRouteCSubstitutionAt_of_classicalSolution` proves the fixed-time
interval-integral expansion from the classical strict-slab physical RHS
representative, using the interior equality for `liftDeriv2`, the algebraic
split of the chemotaxis divergence into the taxis and `u v_xx` parts, and an
a.e. endpoint congruence on `(0,1]`.  The before-wrapper
`H1PhysicalRHSRouteCSubstitutionBefore_of_classicalSolution` is now
axiom-clean.  Consequently the physical identity blocker is no longer the full
substitution package: it reduces to the already explicit `H1UxxL1ContBefore`
input needed by the finite-difference Route-C derivative producer.  The Q3542
audit separately confirmed that the Young/component-square route does not
prove `H1PhysicalRHSSqrtBoundsBefore`; the sqrt frontier is still a distinct
pointwise estimate package for the taxis, `u v_xx`, and reaction scalar terms.
The zero-start primitive package also remains separate, so this is progress on
the identity route, not an unconditional bounded-before headline.

Task 108 removes the last identity-side carry.  The same Route-C identity file
now proves `H1PhysicalRHSIdentityBefore_of_classicalSolution` by composing the
existing `H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep`
producer with Task107's exact physical substitution theorem.  Thus the
concrete physical H¹ identity is axiom-clean from `IsPaper2ClassicalSolution`
alone.  It should no longer be listed as a remaining physical-H¹ exit blocker.

Task 109 adds the disjoint sqrt-bound reducer in
`IntervalChiNegH1PhysicalSqrtBounds`.  It introduces
`H1PhysicalRHSSqrtPointwiseEstimatesBefore`, an exact named record for the
pointwise estimates still needed by `H1PhysicalRHSSqrtBoundsBefore`, and
`H1PhysicalRHSL2SqrtBoundDataBefore`, a source-facing L² factor package for the
taxis and `u v_xx` non-lap factors plus the explicit reaction bound.  The new
theorems `H1PhysicalRHSSqrtBoundsBefore_of_pointwiseEstimates` and
`H1PhysicalRHSSqrtBoundsBefore_of_L2SqrtBoundData` are axiom-clean reducers:
they prove the current sqrt-bound interface from those explicit estimates via
interval Cauchy-Schwarz and record assembly.  This intentionally does not
derive uniform resolver bounds or the logistic reaction IBP estimate; those are
now the honest remaining analytic inputs for the sqrt frontier.

Task 110 updates the endpoint-data physical exit after Task108.  The new
`boundedBefore_of_physical_classical_zeroStart_identityClosed_before` theorem
in `IntervalChiNegH1PhysicalExit` reuses
`H1PhysicalRHSIdentityBefore_of_classicalSolution`, so the endpoint-data
bounded-before wrapper no longer asks for `H1PhysicalRHSIdentityBefore`
explicitly.  Its route-level carries are now the zero-start primitive package,
the sqrt-bound package, `H1InitialEndpointData`,
`IntervalDomainL2SeedRegularityFrontier`, and the standard
initial/boundedness environment.

Task 111 follows the Q3544 zero-start primitive audit.  The audit found no
source-grounded producer for `H1ZeroStartPhysicalPrimitiveDataBefore` from
`IsPaper2ClassicalSolution`, `InitialTrace`, positivity, or endpoint data:
the strict classical APIs are positive-time only and do not provide
closed-slab data at `t = 0`.  `IntervalChiNegH1ZeroStartComponents` now splits
that large package into
`H1ZeroStartPhysicalPrimitiveContinuityBefore` for closed-slab continuity and
positivity of `u`, `v`, `u_x`, and `v_x`, and
`H1ZeroStartPhysicalPDESeamBefore` for zero-start continuity of `u_t` plus the
endpoint-including interior equality between literal `liftDeriv2` and the
physical RHS representative.  The constructor
`H1ZeroStartPhysicalPrimitiveDataBefore_of_continuity_and_pdeSeam` is
axiom-clean and only reassembles the old package.  This is not a mathematical
closure; it marks the initial-time PDE seam as the real remaining
zero-start blocker.

Task 112 follows the Q3549 PDE-seam audit.  The audit confirms that
`H1ZeroStartPhysicalPDESeamBefore` is not derivable from the current
`IsPaper2ClassicalSolution` record alone: `liftTimeDeriv` continuity and the
PDE equality are only available on strict-positive-time slabs.  The new
`H1ZeroStartPhysicalPDEInitialCompatibilityBefore` record therefore asks only
for the genuine missing zero-time seam data: closed-slab continuity of
`liftTimeDeriv u` on `[0,b] × [0,1]` and the interior PDE trace at `t = 0`.
The constructor
`H1ZeroStartPhysicalPDESeamBefore_of_classicalSolution_initialCompatibility`
then fills the positive-time branch from the existing classical pointwise
`liftDeriv2` equality and chemotaxis representative equality.  This shrinks
the PDE-seam carry, but it is still conditional on explicit initial-time
compatibility.

The Q3547 continuity/sign audit gives the analogous result for the other half
of Task111.  `H1ZeroStartPhysicalPrimitiveContinuityBefore` is also not a
consequence of current classical regularity or `InitialTrace`: the available
joint continuity and positivity APIs are strict-positive-time, while this
frontier includes `t = 0`.  The new p-free
`H1ZeroStartClosedPrimitiveC1SignBefore` record names the exact source-facing
closed-slab data needed for `u`, `v`, `u_x`, `v_x`, `u > 0`, and `v ≥ 0`, and
`H1ZeroStartPhysicalPrimitiveContinuityBefore_of_closedPrimitiveC1Sign` maps it
into the physical continuity subfrontier for any `CM2Params`.  This removes the
irrelevant parameter from the source package but still leaves zero-start
closed-slab primitive regularity/sign as a real construction-level obligation.

Task 113 closes the reaction part of the H¹ physical sqrt-bound route.  The
physical reaction file now supplies `H1PhysicalReactionIBPBoundDataBefore` and
the classical-reaction sqrt-bound producer from classical solution data plus the
scalar cap `p.a ≤ L`.  This discharges the reaction residual only; the taxis and
`u_x v_x` pointwise estimates remain separate source-facing inputs.

Task 114 splits the remaining physical chemotaxis sqrt source terms.  The new
`IntervalChiNegH1PhysicalChemSqrtBounds` layer introduces
`H1PhysicalChemResolverSupBefore` for fixed-before-`T` resolver-gradient,
solution-sup, and physical-core bounds, lowers it to
`H1PhysicalChemFactorBoundsBefore`, and the reaction file now rebuilds the
older full `H1PhysicalRHSSqrtBoundsBefore` from chem-side L²/pointwise data plus
the already-proved reaction IBP package.  This makes the current sqrt frontier
explicit: uniform source constants for the two chemotaxis factors remain, while
the logistic reaction term is no longer a residual.

Task 115 follows the second-round zero-start source audits.  Q3551 confirms that
there is still no general producer for
`H1ZeroStartClosedPrimitiveC1SignBefore`: the raw `conjugatePicardLimit` is
definitionally zero at `t = 0`, so the direct B-form/Picard output cannot prove
the target's `u_pos0` field without a reinitialized trajectory carrying the
actual initial datum at time zero.  `IntervalChiNegH1ZeroStartConstant` records
only the honest constant-solution special case
`H1ZeroStartClosedPrimitiveC1SignBefore_const`, using the existing constant lift
and elliptic-resolver lemmas; it is not a general construction producer.

Q3552 and Q3556 together fence off the other zero-start seam.  Q3552 confirms
that the current P3/Moser/FTC/global-PDE-initial infrastructure gives scalar
initial-window integrability/FTC data, not pointwise closed-time continuity of
`liftTimeDeriv u` or the literal initial PDE trace.  Q3556 confirms that the
mixed chemotaxis-divergence representative layer is also not a full producer:
the capstone `ChemDivMixedTimeDerivClosedRepr` concerns
`coupledChemDivTimeDerivativeLift`, not `liftTimeDeriv u`, while raw
`ChemDivMixedReprWitnessData` can contribute only the `time_cont0` half through
its `Utc` representative.  `IntervalChiNegH1ZeroStartMixedWitness` therefore
adds only `time_cont0_of_mixedWitnessBefore` and the reducer
`H1ZeroStartPhysicalPDEInitialCompatibilityBefore_of_mixed`, with
`eq0Interior` still explicit.

Task 118 follows the Q3560 audit of `eq0Interior`.  The audit confirms that
`IsPaper2ClassicalSolution`, mild/Duhamel construction data, `withInitialSlice`,
P3/Moser scalar initial-window data, B-form identities, and mixed
chem-divergence representatives do not currently produce the pointwise
initial-time PDE trace needed by the zero-start H1 route.  The new
`IntervalChiNegH1ZeroStartInitialTrace` file adds only the honest source-facing
decomposition `H1ZeroStartLiteralUPDETraceWithChemRepBefore`: a literal initial
`u`-PDE trace on the spatial interior plus an initial equality between the
literal chemotaxis divergence lift and `liftChemotaxisDivPhysicalRep`.  The
reducer `eq0Interior_of_initialLiteralUPDETrace_withChemRep` proves the existing
`eq0Interior` target from those two fields without using downstream H1
boundedness/sqrt/zero-start RHS packages.  This is a narrower non-circular
interface, not a general producer; the construction layer still has to supply
the literal initial trace and chem-representative seam.

Task 119 adds the constant-source special case for that trace interface.
`H1ZeroStartLiteralUPDETraceWithChemRepBefore_const` proves the literal initial
PDE trace and chemotaxis-representative seam for constant trajectories
`u ≡ c`, `v ≡ ellipticV p c` whenever the logistic reaction term
`c * (p.a - p.b * c ^ p.α)` is zero.  The equilibrium and zero-reaction
wrappers specialize this to the existing constant solution regimes.  This pairs
with Task115's constant primitive C1/sign producer; it still does not supply a
general B-form/Picard zero-start producer.

Task 122 connects the constant special cases to the old route-facing primitive
frontier.  The new `IntervalChiNegH1ZeroStartConstantPrimitiveData` file adds
the Q3565 safe wrapper
`H1ZeroStartInitializedPrimitiveC1SignSource_of_closedPrimitiveC1Sign`, its
constant specialization, the Q3566 route-facing
`H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_of_reaction_zero`, and
equilibrium/zero-reaction wrappers.  It then combines the constant closed
primitive C1/sign package, the constant initial PDE compatibility package, and
the existing constant classical solution theorems to prove
`H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium` and
`H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction`.  This closes the
older zero-start primitive-data frontier only for the constant equilibrium and
zero-reaction regimes.

The same Task118 commit records Q3559's matching current status for the
primitive C1/sign half.  The
raw B-form/Picard local output cannot be the zero-start trajectory because
`conjugatePicardLimit p u₀ T 0 x` is definitionally `0`; `InitialTrace` only
gives right-time sup-norm convergence, not `u 0 = u₀`, and `patchedSlice` is
only a u-value patch without a v patch or first-spatial-derivative trace.  The
new `IntervalChiNegH1ZeroStartInitializedPrimitive` file therefore adds the
guard package `H1ZeroStartInitializedPrimitiveC1SignSource`, which explicitly
records `u 0 = u₀` and `v 0 = v₀` in addition to the closed-zero-slab primitive
continuity/sign fields.  The reducer
`H1ZeroStartClosedPrimitiveC1SignBefore_of_initializedSource` is only a
projection into the current p-free target; it is a source-interface guard, not
a proof that the general B-form/Picard construction supplies those fields.
Q3565 independently rechecked this after Task118: no non-circular general
producer exists in the audited B-form/Picard, patched-slice, or positive-time
joint-continuity layers.  The missing general source data remain an initialized
`(u,v)` trajectory with actual zero slices and closed-zero-slab value/first
spatial-derivative continuity and signs.

### Dual-oracle R1 synthesis (Fable + ChatGPT, 2026-07-04)

**Fable's key findings:**
- hGap is a fixable coefficient bug (not a permanent residual)
- Vacuity risk: χ₀ ≠ 0 case has ALL downstream theorems vacuously true
- Circularity breakable via first-crossing continuation argument
- Initial-time regularity likely not a frontier (time weight trick or closed-interval)

**ChatGPT's key findings:**
- Agrees hGap unsatisfiable; proposes replacing gap definition with positive-coeff frontier
- Suggests no-bounded-before route for relative interpolation via 1D GN/Young
- Sketches `LocalInitialMoserPDEIntegrability` package for initial-time issue

**Synthesis:**
- ε refactor (Fable's route) is more surgical — define alongside, bridge
- ChatGPT's no-bound interpolation route worth investigating as circularity break
- Both agree initial-time is producible with local regularity data
- Priority: ε refactor → (no-bound interp + initial-time) parallel → dyadic

### Task306 gradient-source integration bridge (2026-07-06)

Task305 closed the per-slice classical gradient-source identity without false
endpoint continuity assumptions.  The next core step is to integrate that
identity over the Duhamel time variable.  `IntervalGradientSourceBridgeIntegrated`
adds the a.e. integrand bridge on `s in (0,t]`, discarding only the endpoint
`s=t` where the heat time `t-s` is zero, and an integrated Duhamel bridge whose
chemotaxis/logistic integrability inputs remain explicit.  This is deliberately
not a headline wrapper and not a direct `hpde_u` producer; it only transports
the verified per-slice identity into the time-integrated mild-map vocabulary.

Task307 removes those two explicit integrability inputs under the standard
bounded/jointly-measurable source surface.  The theorem
`gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_windowBounds`
cuts the chemotaxis flux and logistic source to zero outside `(0,t]`, applies
the existing `IntervalDuhamelIntegrability` value/gradient integrability atoms,
and transfers the result back to the raw sources by `EqOn` on the integration
interval.  The remaining inputs are now measurable/bounded source producers,
not Duhamel integrability itself.

Task308 adds those source certificates for packaged mild data in
`IntervalGradientSourceBridgeSourceCertificates`.  It defines the order-box
constants `gradientBridgeChemFluxBound` and `gradientBridgeLogisticBound`,
proves their nonnegativity and the corresponding window bounds from
`GradientMildSolutionData.hbound/hnonneg/hcont`, and combines the public
chemFlux/logistic joint-measurability atoms with Task307 to prove
`gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData`.
This moves the integrated mixed-source bridge from abstract source inputs to
actual `GradientMildSolutionData`; the remaining real input is still the
classical-solution identification consumed by the per-slice physical bridge.

Task309 removes the `hpde_u` circularity from that remaining input.  Q3784
identified that supplying Task308's `hclassical` through the existing classical
producers would be circular, since those producers consume core data carrying
`hpde_u`.  The new `IntervalGradientSourceBridgeRegularity` file therefore
copies the actual pointwise flux differentiability calculation into
`chemotaxisFlux_hasDerivAt_of_classicalRegularity_nonneg`, whose inputs are
only `intervalDomainClassicalRegularity` and nonnegativity of the chemical
component.  It then proves
`chemFluxLifted_hasDerivWithinAt_coupledChemDivSourceLift_open_of_mildRegularity`
for `GradientMildSolutionData` using closed-C2/Neumann source decay rather than
`IsPaper2ClassicalSolution`.

The same file lifts this to the slice and integrated bridge:
`gradient_source_bridge_slice_open_of_gradientMildRegularity_representative`
and
`gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData_and_regularRepr`.
Thus the source-certificate bridge no longer asks for a full classical solution;
it asks for non-PDE classical regularity plus an endpoint-insensitive continuous
representative for `coupledChemDivSourceLift` on each interior time slice.
Q3785 independently warned that this integrated equality is still a value-level
bridge, not an `hpde_u` producer: true `hpde_u` still requires local restart
coefficient/source time-C1 data as in `IntervalDomainPdeUGeneralChi`.

Task310 discharges Task309's remaining explicit representative input without
returning to `IsPaper2ClassicalSolution`.  The new
`IntervalGradientSourceBridgeRegularityRepresentative` file defines the closed
spatial representative `gradientBridgeChemDivWithinRep` using `derivWithin` on
`[0,1]`; this avoids the false endpoint-continuity demand that an ordinary
global derivative representative would impose on the zero-extended lift.  From
closed-C2/Neumann data in `intervalDomainClassicalRegularity`, positivity of
the mild datum, `mildChemical_nonneg`, and the resolver identities, it proves
continuity on `[0,1]` and equality with `coupledChemDivSourceLift` on `(0,1)`.

The public bridge
`gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData_and_regular`
now needs only `GradientMildSolutionData` plus
`intervalDomainClassicalRegularity D.T D.u (coupledChemicalConcentration p D.u)`
for this source-certificate route.  This is still intentionally a non-PDE
value/integral source bridge; the next core headline work is to feed exact
source coefficient/time-C1 data into the `IntervalDomainPdeUGeneralChi`
`hpde_u` producer, not to add more aliases around this bridge.

### Tasks 311–312: faithful positive-time value continuity (2026-07-10)

Commit `a56f85f7` adds three explicitly classified reductions.  The Picard
uniform-limit module transfers joint continuity of all concrete iterates to
the canonical limit but does not produce the iterate premise.  The generic
Holder bridge proves joint continuity from fixed-space time continuity and a
spatial Holder modulus uniform on each positive-time strip.  The resolver
weighted-series module proves local termwise time differentiation and joint
continuity from mode-uniform coefficient bounds.  Independent hostile audits
passed all three and classified them as reductions, not faithful producers.
The integrated root build passed 9244 jobs.

Commit `ab1e9b3f` closes the first genuinely faithful time-regularity seam.
`conjugateMild_timeSlice_continuousOn_Ioc` proves, directly from the mild
formula, continuity of `t ↦ D.u t x` on `(0,D.T]` for every physical point.
The proof freezes an early integration interval and controls the remaining
chemotaxis and reaction tails by square-root and linear bounds; it uses no
source-TimeC1, restart, classical regularity, or spectral-agreement premise.
`conjugateMild_jointValue_u` combines this with the positive-strip spatial
Holder estimate to give joint continuity of the lifted faithful `u` on
`(0,D.T) × [0,1]`.  Both theorems are clean-3 and an independent hostile audit
classified the time-slice theorem as a faithful fragment.  The root import
build passed 9246 jobs.

This closes only the `u` half of `IntervalClassicalRegularityAtoms.jointValue`.
The `v` half, joint continuity of the physical spatial derivative `u_x`, the
time-derivative fields, and `hpde_u` remain on the active dependency path.

### Task 313: faithful positive-time interior spatial derivative continuity (2026-07-10)

Commit `fb7c8103` adds a parametric mean-value bridge which recovers time
continuity of a spatial derivative from joint continuity of the underlying
values and a spatial Holder modulus uniform in the parameter.  Its faithful
consumer, `conjugateMild_jointSpatialDeriv_interior`, combines Task312's joint
value theorem with the actual positive-time Holder estimate for
`deriv (intervalDomainLift (D.u t))`.  It proves joint continuity on
`(0,D.T) × (0,1)` without assuming derivative time continuity, restart data,
source-TimeC1, classical regularity, or spectral agreement.

The interior restriction is deliberate: the available faithful Holder theorem
is stated only for spatial points in `(0,1)`.  Extending the result to the
closed spatial interval requires a separate endpoint argument using the
genuine Neumann limits and ordinary endpoint derivatives; it is not claimed by
this commit.  A cold hostile audit passed the secant/MVT argument, local-time
gluing, quantifier match, and clean-3 check.  The root import build passed 9248
jobs.

### Task 314: faithful coupled joint value continuity (2026-07-10)

Commit `6474da58` closes both halves of the classical ledger's `jointValue`
field.  `conjugateMild_jointValue_v` first derives continuity in time of every
actual resolver source coefficient from Task312's joint continuity of `u`,
with no coefficient time derivative.  A uniform all-mode bound and the
summable elliptic weights then give joint continuity of the resolver series on
`(0,D.T) × [0,1]`.  The exact physical series identity identifies this series
with `coupledChemicalConcentration p D.u`, including the canonical `nu`,
`gamma`, zero/nonzero-mode normalization, real part, and resolver weight.

`conjugateMild_coupled_jointValue` pairs this with Task312's `u` result.  It
uses no SourceTimeC1, spectral-agreement package, restart theorem, classical
regularity, or time derivative.  A cold hostile audit traced every source and
weight definition and classified it as a faithful fragment.  The root import
build passed 9249 jobs.

### Tasks 315–318: closed spatial traces and direct Duhamel time differentiation (2026-07-10)

Commits `1c557f31` and `9b66114c` close two analytic interfaces needed for a
direct physical-space time derivative.  The first extends the faithful joint
continuity of `u_x` from the open interval to `(0,D.T) × [0,1]` using the
genuine one-sided Neumann limits and the actual ordinary endpoint derivative
values.  The second proves a reusable target-time derivative theorem for a
full Neumann Duhamel leg.  Its old history is handled by dominated convergence,
its late history by the cancellative Holder Hessian estimate, and its moving
endpoint by the uniform source trace and the heat approximate identity.  It
does not require source-TimeC1 or restart data.

Commit `5409b317` applies that theorem to the actual logistic source after a
constant spatial extension, and records the joint-continuity-to-uniform-trace
bridge.  The extension is used only because the generic semigroup theorem asks
for globally continuous spatial slices; it agrees with the literal logistic
source on `[0,1]`, which is the whole support of the interval semigroup.  The
same commit constructs the ordinary-derivative continuous representative
`conjugateMildChemDivJointRep` for the post-IBP chemotaxis source.  It proves
joint continuity on `(0,D.T) × [0,1]`, equality with both the raw flux
derivative and the literal physical chemotaxis divergence on `(0,1)`, a uniform
target-time trace, and positive-strip spatial Holder control.

The crucial hostile-audit finding is that the chemotaxis representative must
not be treated as uniformly bounded down to time zero: the available faithful
bound for `u_x`, hence for the flux derivative, can have an integrable
`t^(-1/2)` singularity.  Commit `50817885` removes this obstruction without a
false bound.  It proves positive-lag target-time differentiation of the
conjugate operator by a half-step semigroup factorisation and then differentiates
a fixed old-history integral using only the original flux's global bound.
Consequently the faithful chemotaxis Duhamel leg can be split at a positive
time: keep the old history in conjugate-kernel form and integrate by parts only
on the late history.  Commit `79b1d99a` also exposes the actual conjugate
Hessian's time integrability, so the two derivative integrals can be recombined
honestly.  All landed interfaces are clean-3; the corresponding root builds
passed through 9255 jobs.  The active remaining seam is the final old/late
chemotaxis `HasDerivAt` assembly, followed by the full `u_t`/literal-PDE and
classical-solution wiring.

### Tasks 319–320: faithful chemotaxis time derivative and literal `u` equation (2026-07-10)

Commit `cb819b4b` closes the actual chemotaxis target-time derivative.  It
splits at `a=t/4`: the old history remains in conjugate-flux form and uses only
the global bound for the original flux, while the late history is integrated
by parts into the continuous physical flux-derivative representative on a
strictly positive strip.  The late trace, Holder bound, and Hessian
integrability are supplied explicitly, and the two histories are recombined
only after the required interval-integrability facts are present.  Thus no
uniform bound for the flux derivative near time zero is assumed.  A hostile
audit classified the result as a faithful actual-leg fragment; the root build
passed 9256 jobs and the theorem is clean-3.

Commit `3e0c13b8` differentiates all three terms of the faithful mild equation
and identifies the resulting generator terms with the genuine second spatial
derivative already proved for the same mild slice.  The chemotaxis trace is
then identified with the literal physical divergence on the open spatial
interval, and the reaction trace with the literal logistic source.  The public
theorem `conjugateMild_intervalDomain_pde_u` now supplies the exact Paper 2
parabolic equation at every positive interior space-time point without a
classical-solution, PDE, restart, spectral-agreement, or source-time-C1
premise.  The root build passed 9257 jobs and the theorem is clean-3.

The next honest seam is closed-domain time regularity.  The same old/late
argument can extend the chemotaxis time derivative to `x in [0,1]`, but its
trace there must remain `conjugateMildChemDivJointRep`, not the ordinary
derivative of the zero-extended flux.  The only missing endpoint input is a
public closed-interval version of the actual conjugate Hessian's time
integrability; the existing closed spatial-continuity proof already contains
the required measurability and common integrable dominator.  Even after this
endpoint derivative is obtained, joint continuity of the full time-derivative
field remains a separate parabolic-regularity obligation and must not be
inferred from pointwise differentiability alone.

### Paper 2 finite-power affine endpoint (2026-07-12)

The concrete interval `Proposition_2_5` endpoint no longer goes through the
Agmon pointwise-gradient route.  For `m=1`, one bounded power
`P > max{1,gamma}` makes the physical chemotaxis flux uniformly bounded in
`L^P`: the elliptic primitive gives a pointwise bound for `v_x` from the same
power, while the remaining factor is `u`.  The genuine conjugate operator has
the short-time mapping rate
`B(t) : L^P -> L∞` with exponent `1/2 + 1/(2P) < 1`.  This is proved by an
`L^P` derivative-kernel mass estimate and the exact factorization
`B(t)=S(t/2)B(t/2)`.

On a fixed restart window, the homogeneous datum is smoothed from `L^P`; it
is never assumed uniformly bounded in `L∞`.  The chemotaxis Duhamel leg is an
affine integral of the constant flux bound.  The logistic leg is compared,
using positivity of the full Neumann semigroup, with its positive linear
part; the damping term is dropped rather than estimated in `L^P`.  The same
estimate produces finite-horizon `IsPaper2BoundedBefore` and, on a moving
half-unit window, the global `atTop` bound.  Consequently this endpoint needs
neither a pointwise-in-time gradient estimate nor `2gamma < alpha`.

### Paper 1 BUC Duhamel contraction (2026-07-14)

The whole-line Cauchy construction now has both nonlinear Duhamel legs as
honest Bochner integrals in the complete space `BUC(R)`.  A rescaling to the
fixed interval `[0,1]`, dominated convergence, and the integrable
`(1-r)^(-1/2)` Gaussian-gradient singularity prove continuity of both legs as
BUC-valued time trajectories.  Their sharp difference estimates assemble into
a globally Lipschitz truncated mild self-map on `C([0,T];BUC(R))`, with
coefficient `O(sqrt T)+O(T)`.  Continuity of that coefficient at zero supplies
a positive contraction window, and Banach's theorem gives a genuine fixed
point with the prescribed BUC initial value.  No invariant ball or assumed
realization package is used.

This is still the globally clamped equation.  The next analytic obligation is
the comparison/positivity argument showing that the fixed point remains in the
physical nonnegative strip (and below a short-time upper barrier), after which
the clamp is inactive and the fixed point solves the original Cauchy system.

The upper half of that strip is now concrete.  The two nonlinear histories
have an explicit `O(sqrt T) + O(T)` displacement from the homogeneous heat
orbit.  Choosing the contraction window small enough makes this displacement
strictly less than one, so the canonical fixed point issued from `u₀` stays
strictly below the clamp ceiling `‖u₀‖ + 1` at every space-time point.  The
remaining clamp-inactivity seam is therefore exactly nonnegativity; uniform
closeness to the initial datum cannot supply it when the datum has zero
infimum.
