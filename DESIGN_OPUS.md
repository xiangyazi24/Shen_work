# DESIGN: From Current State to Unconditional Paper2 Theorem 1.1

**Author**: Claude Opus 4.6 (1M context) — 2026-06-04 session  
**Codebase**: `shen_work`, 0 sorry in proof terms, ~60 `.lean` files

---

## Context

Paper2 Theorem 1.1 (Chen-Ruau-Shen, arXiv:2512.14858):

> For the chemotaxis system on [0,1] with negative sensitivity (chi_0 <= 0),
> positive logistic (a > 0, b > 0), and positive initial data u_0, there exists
> a local classical solution (u,v) with explicit sup-norm bounds; if m >= 1 the
> solution is global.

The top-level Lean theorem
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound`
(IntervalDomainTheorem11Umbrella.lean:867) takes four hypotheses:
`hlocal`, `hreach`, `hposWit`, `hposLowerWit`.

Everything DOWNSTREAM of `hlocal` is unconditionally proved:
- L2 energy inequality (`intervalDomainL2U_energy_diffIneq_bound`)
- Overlap uniqueness (Gronwall from energy certificate)
- Global gluing (`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound`)
- Moser sup-norm iteration (`IntervalDomainMoserClosure` chain)
- Global extension (from regime-conditional uniform bound + continuation)

The **sole frontier** is constructing `hlocal`: local classical existence
for every positive datum.

---

## 1. What We Have (Precise Theorems)

### Layer 1: Picard Iteration -> Mild Solution

| Theorem | File:Line | Signature summary |
|---------|-----------|-------------------|
| `intervalMildSolution_of_data` | IntervalMildPicard:1338 | `MildExistenceData p u0 -> exists T > 0, exists u, IntervalMildSolution p T u0 u` |
| `gradientMildSolutionData_of_data` | IntervalMildPicard:1412 | `MildExistenceData p u0 -> GradientMildSolutionData p u0` |

`GradientMildSolutionData` packages: `T, hT, M, hM, u, hmild, hbound, hnonneg, hpos, hcont, hmeas`.

**Status**: Constructor proved. Input `MildExistenceData` must be instantiated from
PDE parameters (Gap G1).

### Layer 2: Spatial Regularity (Restart Framework)

| Theorem | File:Line | Signature summary |
|---------|-----------|-------------------|
| `restartDuhamelSlice_conjunct7` | IntervalMildRegularityBootstrap:154 | `DuhamelSourceTimeC1 a + bounded a0 + tau>0 + hagree + nonvanishing -> ContDiffOn R 2 on Icc 0 1 + Neumann` |
| `hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData` | :364 | `GradientMildHalfStepRestartData D -> HasRestartCosineRepresentations D.T D.u` |
| `gradientMild_closedC2_neumann_of_restartCosineRepresentations` | :448 | `HasRestartCosineRepresentations -> forall t in (0,T), ContDiffOn R 2 + deriv=0 at 0,1` |

**Status**: Fully proved. Consumes `GradientMildHalfStepRestartData`.

### Layer 3: Logistic Source Regularity (IntervalMildPicardRegularity.lean, 1021 lines)

| Theorem | Line | What it gives |
|---------|------|---------------|
| `logisticSourceFun_intervalWeakH2Neumann` | 257 | globally C2 + positive + Neumann profile -> IntervalWeakH2Neumann for logistic source |
| `logisticSourceFun_cosineCoeff_quadratic_decay` | 271 | H2 Neumann -> abs(c_k) <= C/(k*pi)^2 for k >= 1 |
| `cosineCoeffs_hasDerivAt_of_smooth_param` | 494 | time-Leibniz: jointly smooth param family -> HasDerivAt of cosine coefficients |
| `logisticSourceFun_hasDerivAt_time` | 605 | chain rule: HasDerivAt for logistic(f(sigma)) when f has HasDerivAt |
| `logisticSource_duhamelSourceTimeC1` | 638 | profile (C2+pos+Neumann) + time derivative data -> DuhamelSourceTimeC1 |
| `hasRestartCosineRepresentations_of_gradientMildHalfStepLogisticSourceData` | 750 | logistic source data -> HasRestartCosineRepresentations |
| `logisticSourceFun_cosineCoeffs_zeroth_bound` | 426 | zeroth cosine coefficient bounded from profile bound |

**Status**: Full assembly chain proved. Needs profile instantiation (Gap G3).

### Layer 4: Picard Iterate C2 Induction (IntervalMildPicardRegularity.lean)

| Theorem | Line | What it gives |
|---------|------|---------------|
| `picardIterateHasC2Slices_zero` | 871 | base case: semigroup has C2 slices |
| `picardIterateHasC2Slices_succ` | 950 | `PicardRegularityStepData -> PicardIterateHasC2Slices (n+1)` |
| `picardIterateHasC2Slices_all` | 962 | `(forall n, PicardRegularityStepData n) -> forall n, PicardIterateHasC2Slices n` |
| `picardIter_cosineCoeffs_bound` | 983 | bounded iterate -> bounded cosine coefficients (abs <= 2M) |
| `picardIter_endpoint_ne_zero` | 1007 | positive iterate -> nonvanishing at endpoints |

`PicardRegularityStepData` requires: `source` (DuhamelSourceTimeC1), `hagree`
(spectral agreement on Icc 0 1), `ha0_bound`, `hne0`, `hne1`.

**Status**: Structural induction proved. `PicardRegularityStepData` must be
constructed at each level (Gaps G2, G3).

### Layer 5: Mild -> Classical Bridge

| Theorem | File:Line |
|---------|-----------|
| `localExistence_of_gradientMildSolutionData_of_halfStepLogisticSourceData` | IntervalMildToLocalExistence:764 |

Takes: `GradientMildSolutionData` + `GradientMildHalfStepLogisticSourceData` +
`GradientMildClassicalRegularityFrontierData` + initial approach. Produces:
`exists Tmax > 0, exists u v, IsPaper2ClassicalSolution + InitialTrace`.

**Status**: Bridge proved. Needs frontier data (Gap G4) + initial approach (Gap G5).

### Layer 6: Downstream (All Unconditionally Proved)

- `intervalDomainL2U_energy_diffIneq_bound` -- per-time energy differential inequality
- `IntervalDomainClassicalOverlapL2UEnergyCertificate` -- Gronwall to zero
- `GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound` -- gluing
- `IntervalDomainMoserClosure` chain -- Moser iteration
- `Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound` -- top-level

---

## 2. Gaps G1--G6: Full Description

---

### G1: MildExistenceData Instantiation

**Mathematical content**: Compute Picard contraction parameters
(T, M, K, C_0) from `CM2Params` + `PositiveInitialDatum` so that the
gradient Duhamel map Phi is a contraction on the ball of radius M in
sup-norm, with contraction constant K < 1.

**Existing theorems (in codebase)**:
- `intervalFullSemigroupOperator_Linfty_bound` -- semigroup L-infinity contraction
- `IntervalCoupledBallEstimates.lean` -- pointwise ball estimates for Phi
  including logistic Lipschitz, chemotaxis flux Lipschitz, gradient
  Duhamel L-infinity bound
- `IntervalCoupledClassicalBallEstimates.lean` -- same in classical setting
- `intervalLogisticSource_lipschitz` -- logistic Lipschitz on bounded sets
- `chemFluxLifted_bounded_of_continuous` -- flux bounded from bounded profile

**What's missing**:
- Choose explicit T = T(p, ||u0||) small enough that K(T) < 1
- Choose M = max(2||u0||, some threshold)
- Verify all 14 fields of `MildExistenceData`:
  `hbase_ball`, `hbase_nonneg`, `hbase_cont`, `hmapsTo`, `hmapsTo_nn`,
  `hmapsTo_pos`, `hcont_preserved`, `hcontr`, `hbase_diff`, `hbase_meas`,
  `hmeas_preserved`
- The KEY estimates: `hmapsTo` (ball maps to ball) and `hcontr`
  (contraction) -- both follow from the ball estimates + small T

**Attack route**:
1. Fix M = 2 * sup|u0| + 1 (or any large enough constant)
2. The ball estimates give |Phi(w)(t,x)| <= ||u0|| + T*C_L*M + C_Q*M*sqrt(T)
3. Choose T small enough that ||u0|| + T*C_L*M + C_Q*M*sqrt(T) <= M
4. The contraction estimate gives |Phi(w1)-Phi(w2)| <= (T*L_1 + sqrt(T)*L_2) * ||w1-w2||
5. Choose T small enough that T*L_1 + sqrt(T)*L_2 < 1
6. Wire all 14 fields

**Risk**: The sqrt(T) factor from the gradient chemotaxis bound is the
bottleneck -- it forces T << 1/(L_2^2), not just T << 1/L_1. The existing
ball estimates should already have this factor explicit. Lean engineering
is straightforward but verbose (~300-500 lines).

**Difficulty**: Medium (quantitative, no deep math).

---

### G2: Spectral Agreement (hagree)

**Mathematical content**: For the half-step restart of the Picard iterate
u_{n+1} at time t, show:

    intervalDomainLift(u_{n+1}(t)) on [0,1]
    = sum_k restartDuhamelCoeff(a0, source, t/2, k) * cos(k*pi*x)

where a0_k = cosineCoeffs(lift(u_{n+1}(t/2)))(k) and source encodes the
total PDE source (logistic + chemotaxis divergence).

**Existing theorems**:
- `intervalFullSemigroupOperator_eq_cosineHeatValue_funext` -- S(t)f = cosine heat value on all R
- `duhamelSpectral_eq_cosineSeries` -- integral_0^t unitIntervalCosineHeatValue(t-s)(a s) = sum duhamelSpectralCoeff(a)(t)(n) * cos(n*pi*x)
- `intervalNeumannFullKernel_cosineKernel_identity` -- kernel = cosine series

**What's missing**:
- **Gradient <-> standard Duhamel equivalence on [0,1]**: converting
  `-chi_0 * integral_0^t deriv_x(S(t-s) Q(u(s))) ds` to
  `integral_0^t S(t-s) [-chi_0 * div(Q(u(s)))] ds` on [0,1].
  This is integration by parts in the inner (spatial) integral:
  `integral_0^1 deriv_x(S(t-s)g)(x) * h(x) dx = -integral_0^1 S(t-s)g(x) * h'(x) dx`
  (boundary terms vanish by Neumann BC).
  BUT we need this for the FUNCTION VALUE, not an inner product.
  The actual equivalence: for x in [0,1],
  `deriv_x(integral_0^1 K(t-s,x,y) Q(y) dy) = integral_0^1 deriv_x K(t-s,x,y) Q(y) dy`
  which is differentiation under the integral sign (already available
  from the semigroup C2 smoothness).

  Then the standard Duhamel form
  `integral_0^t S(t-s)(totalSource(s))(x) ds`
  applies `duhamelSpectral_eq_cosineSeries` directly.

- **Restart decomposition**: show `u_{n+1}(t) = S(t/2)(u_{n+1}(t/2)) + integral_{t/2}^t S(t-s)(source(s)) ds` from the Picard map definition. This is algebraic: split the time integral at t/2 and use the semigroup composition law.

**Attack route**:
1. Prove `gradientDuhamel_eq_standardDuhamel_on_Icc` by showing that for x in (0,1), the semigroup applied to the flux's spatial derivative equals the derivative of the semigroup applied to the flux (differentiation under the integral, which follows from the semigroup's global C2).
2. Prove `picardIter_restart_eq` by splitting the Picard map's time integrals at t/2.
3. Apply `intervalFullSemigroupOperator_eq_cosineHeatValue_funext` to the semigroup part.
4. Apply `duhamelSpectral_eq_cosineSeries` (with source DuhamelSourceTimeC1 from G3) to the Duhamel part.
5. Combine into `hagree`.

**Alternative route (bypass gradient<->standard)**:
Work directly with the gradient Duhamel form. The gradient semigroup
`deriv(S(t-s)g)` has its own spectral form (sine modes). Show that the
iterate's cosine coefficients on [0,1] absorb both cosine and sine
contributions and are eigenvalue-summable. This avoids the IBP but
requires a "gradient spectral interchange" theorem.

**Risk**: The gradient<->standard IBP requires that the chemotaxis flux
Q(u_n(s)) and its spatial derivative exist and are well-behaved. This
holds when u_n has C2 slices (induction hypothesis) but the Lean proof
requires careful handling of the semigroup-kernel integral structure.
The alternative route might be cleaner but requires new spectral machinery.

**Difficulty**: Hard (structural, the hardest gap).

---

### G3: Profile Instantiation for DuhamelSourceTimeC1

**Mathematical content**: Instantiate `logisticSource_duhamelSourceTimeC1`
(and similarly for the chemotaxis divergence) with the concrete profile
family arising from the Picard iteration.

For the base case (n=0): profile(sigma, x) = S(delta+sigma)(lift u0)(x),
the heat semigroup evaluated at time delta+sigma.

For the induction step (n>0): profile(sigma, x) needs to be a globally C2
function agreeing with the Picard iterate on [0,1]. The natural choice is
the semigroup applied to the iterate at the half-step:
  profile(sigma, x) = S(sigma)(lift(u_n(t/2)))(x)
which IS globally C2 by `semigroup_contDiff_two`.

**Existing theorems**:
- `semigroup_contDiff_two` -- S(t)f is ContDiff R 2 for t > 0
- `semigroup_logistic_intervalWeakH2Neumann` -- H2 Neumann for logistic of semigroup
- `intervalFullSemigroupOperator_neumann_at_zero/one` -- Neumann BC
- `intervalFullSemigroupOperator_lower_bound` -- lower bound from initial data
- `unitIntervalCosineHeatValue_hasDerivAt_time` -- time derivative of cosine heat value
- `unitIntervalCosineHeatSecondValue_continuous` -- Laplacian is continuous

**What's missing for logistic part**:
- Uniform H2 decay constant C across sigma >= 0: from monotonicity of semigroup spatial derivatives (|d^k/dx^k S(t)f| is decreasing in t for t >= delta > 0)
- Time derivative instantiation: d/d(sigma)[logistic(S(delta+sigma)f0(y))] = logistic'(...) * Laplacian(S(delta+sigma)f0)(y). Need HasDerivAt from `unitIntervalCosineHeatValue_hasDerivAt_time` composed with `logisticSourceFun_hasDerivAt_time`.
- Continuity of derivative coefficients: from joint continuity of Laplacian (exists: `unitIntervalCosineHeatSecondValue_continuous`)
- Uniform derivative bound: |d/d(sigma)[cosineCoeffs(logistic(S(delta+sigma)f0))(n)]| <= M_dot, from bounded Laplacian * bounded logistic' * integral over [0,1].

**What's missing for chemotaxis divergence**:
- C2 of the resolver v = R(u_n) from elliptic regularity (`IntervalEllipticCharacterization.lean`)
- C2 of the flux Q = u * grad(R)/(1+R)^beta by product/quotient rule
- C2 of div(Q) = d/dx[Q] by one more derivative
- H2 Neumann of div(Q) from C2 + Neumann BC
- Time derivative of div(Q) coefficients (deeper chain rule)

**Attack route**:
1. For the semigroup (n=0): instantiate all fields of `GradientMildHalfStepLogisticSourceData` using semigroup properties. The decay constant C comes from the H2 bound at the worst time (sigma=0, t=delta), which is finite and uniform.
2. For n>0: same structure, with the semigroup applied to the iterate at the half-step serving as the globally C2 profile.
3. Chemotaxis divergence: package as a separate `DuhamelSourceTimeC1` contribution and add to the logistic one (DuhamelSourceTimeC1 is closed under addition of coefficient sequences).

**Risk**: The chemotaxis divergence chain is long (C2 of resolver -> C2 of flux -> C2 of divergence). The uniform bounds require tracking constants through multiple composition steps. Elliptic regularity infrastructure exists but may need wrapper lemmas.

**Difficulty**: Medium (mostly wiring, logistic part ~100 lines, chemotaxis ~200 lines).

---

### G4: Classical Regularity Frontier

**Mathematical content**: Fill all 8 fields of
`GradientMildClassicalRegularityFrontierData p D`:

**Existing (3/8 proved from restart-cosine)**:
- `vSpatialInterior` -- from elliptic regularity of resolver
- `vNeumannLimits` -- from cosine-slice regularity
- `vClosedSpatial` -- from restart framework

**Missing (5/8)**:

#### G4a: supnormLogistic / supnormZero
**Math**: sup-norm of u(t) is nonincreasing when ||u(t)|| > (a/b)^{1/alpha} (logistic case) or always (zero case). This is the parabolic maximum principle applied to the PDE: if u achieves its sup at (t0,x0), then d_t u(t0,x0) <= 0 because Laplacian(u) <= 0 at a max and the logistic term is negative when u > (a/b)^{1/alpha}.
**Existing**: `ParabolicMaxPrincipleData` / `UpperEnvelopeMaxPrincipleData` infrastructure. `threshold_persists` helper. `antitoneOn_of_deriv_nonpos` from Mathlib.
**Missing**: Wire the logistic comparison into `IntervalDomainSupNormDerivativeNonposOn`.
**Risk**: Low. Infrastructure matches. ~100-150 lines.

#### G4b: timeSlices
**Math**: For each interior time t in (0,T) and each spatial point x:
- `DifferentiableAt R (fun s => u s x) t` -- the mild solution is differentiable in time
- `DifferentiableAt R (fun s => v s x) t` -- so is the chemical concentration
- `ContinuousOn (fun s => deriv_s u(s,x)) (Ioo 0 T)` -- time derivative is continuous
- Same for v

From the mild equation: u(t,x) = S(t)u0(x) + D(t,x) where D is the Duhamel integral. The semigroup S(t)u0(x) is C-infinity in t for t > 0 (time derivative = Laplacian = second-derivative series). The Duhamel integral D(t,x) = integral_0^t S(t-s)(source(s))(x) ds has time derivative = source(t,x) + integral_0^t d_t[S(t-s)](source(s))(x) ds by Leibniz. Both terms are continuous in t.

**Existing**: `unitIntervalCosineHeatValue_hasDerivAt_time` (semigroup time derivative). `duhamelIntegrand_hasDerivAt` (Duhamel integrand time derivative, in IntervalDuhamelClosedC2.lean).
**Missing**: Combining semigroup + Duhamel time derivatives for the full mild solution. Showing continuity of the combined derivative. For v: elliptic time-derivative from d_t v = d_t R(u) = R'(u) * d_t u.
**Risk**: Medium. The Leibniz rule for the Duhamel integral's time derivative is the key step -- it exists (`duhamelIntegrand_hasDerivAt`) but needs composition with the source regularity.
~200-300 lines.

#### G4c: jointTimeDerivInterior / jointTimeDerivClosed
**Math**: The function (t,x) -> d_t u(t,x) is jointly continuous on (0,T) x (0,1) (interior) and (0,T) x [0,1] (closed spatial).

From d_t u = Laplacian(u) + source: the Laplacian is the second-derivative cosine series (jointly continuous from uniform convergence), and the source is continuous. The closure to [0,1] follows from the cosine-series representation being uniformly convergent on [0,1].

**Existing**: `unitIntervalCosineHeatSecondValue_continuous` (Laplacian is continuous). `cosineCoeffSeries_contDiff_two` (cosine series is C2 hence derivatives are continuous).
**Missing**: Joint continuity of d_t u on the product space. This requires showing that the map (t,x) -> Laplacian(u)(t,x) + source(t,x) is jointly continuous, where both terms are expressed as uniformly convergent cosine series with continuous coefficients.
**Risk**: Medium. The joint continuity of uniformly convergent series of continuous functions is standard but requires explicit bounds.
~200 lines.

#### G4d: jointSolutionClosed
**Math**: (t,x) -> u(t,x) and (t,x) -> v(t,x) are jointly continuous on (0,T) x [0,1].

For u: `HasContinuousSlices` gives time-continuity at each x. `ContDiffOn R 2` gives spatial continuity. Combining gives joint continuity (product of continuous functions on each variable, with uniform estimates).

For v = R(u): from the elliptic resolver's continuous dependence on u.

**Existing**: `D.hcont` (HasContinuousSlices). `gradientMild_contDiffOn_of_restartCosineRepresentations` (spatial C2).
**Missing**: The standard "separately continuous + equicontinuous => jointly continuous" argument. Or: directly from the cosine series representation, which converges uniformly on compact subsets of (0,T) x [0,1].
**Risk**: Low. Standard topology.
~50-100 lines.

**Overall G4 risk**: The timeSlices and jointTimeDeriv fields are the hardest. Total ~500-800 lines.

---

### G5: Initial Approach

**Mathematical content**: The mild solution u(t) approaches the initial datum u0 uniformly as t -> 0+:
  forall epsilon > 0, exists delta > 0, forall t in (0, delta), forall x, |u(t,x) - u0(x)| < epsilon

**Existing theorems**:
- `IntervalSemigroupApproxIdentity.lean` -- S(t)f -> f uniformly as t -> 0 for continuous f
- `intervalFullSemigroupOperator_Linfty_bound` -- |S(t)f| <= ||f||

**What's missing**:
- |u(t,x) - u0(x)| = |S(t)u0(x) + D(t,x) - u0(x)| <= |S(t)u0(x) - u0(x)| + |D(t,x)|
- First term -> 0 by approximate identity
- Second term |D(t,x)| <= integral_0^t |S(t-s)(source(s))(x)| ds <= t * sup|source| -> 0
- Need: the gradient Duhamel map agrees with S(t)u0 + D at (t,x) for the specific mild solution u

**Attack route**:
1. Approximate identity: `S(t)u0 -> u0` uniformly from `IntervalSemigroupApproxIdentity`
2. Duhamel vanishing: `|D(t,x)| <= t * C` from semigroup L-infinity + bounded source
3. Gradient Duhamel vanishing: `|integral ∂_x S Q ds| <= sqrt(t) * C` from gradient L-infinity bound
4. Combine: `|Phi(u0, u)(t,x) - u0(x)| < epsilon` for t < delta

**Risk**: Low. All pieces exist. ~100 lines.

---

### G6: hposWit / hposLowerWit

**Mathematical content**: Book-keeping pass-through. When two classical solutions share initial datum u0, that datum is a `PositiveInitialDatum` and admits a uniform spatial lower bound.

**Existing**: The solutions are constructed FROM `PositiveInitialDatum` in `hlocal`. The witness is the datum itself.

**What's missing**: A trivial closure lemma: if u0 is the datum of a solution constructed via `hlocal`, then u0 is positive (tautological by construction).

**Attack route**: Pattern match on how `hlocal` is invoked; the PositiveInitialDatum is an explicit input.

**Risk**: None. ~20 lines.

---

## 3. Difficulty Classification

### True mathematical difficulties (require non-trivial proofs)
- **G2** (Spectral Agreement): gradient<->standard Duhamel IBP + spectral interchange assembly. Hardest structural gap.
- **G4b** (timeSlices): Time differentiability from PDE representation. Requires Leibniz for Duhamel integral time derivative.
- **G4c** (jointTimeDeriv): Joint continuity of time derivative on product space.
- **G1** (MildExistenceData): Not deep math but substantial quantitative computation.

### Wiring (assembly from existing pieces)
- **G3** (Profile Instantiation): Choose profile, verify hypotheses from semigroup/iterate properties.
- **G4a** (supnorm): Max principle application -- infrastructure exists.
- **G4d** (jointSolutionClosed): Standard separate->joint continuity.
- **G5** (Initial Approach): Approximate identity + Duhamel vanishing.
- **G6** (hposWit): Trivial.

---

## 4. Dependency Order

```
G6 (trivial)          --- independent --------------------------+
                                                                |
G1 (MildExistenceData)                                          |
  |                                                             |
  v                                                             |
GradientMildSolutionData -----------------------------------+   |
  |                                                         |   |
  |  G3 (Profile Instantiation for logistic + chemotaxis)   |   |
  |    |                                                    |   |
  |    v                                                    |   |
  |  DuhamelSourceTimeC1 (total source)                     |   |
  |    |                                                    |   |
  |    |  G2 (Spectral Agreement)                           |   |
  |    |    |                                               |   |
  |    v    v                                               |   |
  |  HasRestartCosineRepresentations --> spatial C2/Neumann  |   |
  |    |                                                    |   |
  |    v                                                    |   |
  |  G4 (Classical Regularity Frontier)                     |   |
  |    |                                                    |   |
  |    v                                                    |   |
  |  IsPaper2ClassicalSolution  <--- G5 (Initial Approach)  |   |
  |    |                                                    |   |
  v    v                                                    v   v
  hlocal ----------------------------------> Theorem 1.1 <-- hposWit
```

**Critical path**: G1 -> G3 -> G2 -> G4 -> G5 -> hlocal -> Theorem 1.1

**Parallelizable**:
- G1 is independent of G2-G5
- G6 is independent of everything
- G4a (supnorm) can be done in parallel with G2
- G5 can be done in parallel with G4

**Recommended attack order**:
1. **G5** (Initial Approach) -- easy, unblocks local existence bridge
2. **G1** (MildExistenceData) -- unblocks everything downstream
3. **G3** (Profile Instantiation) -- connects logistic DuhamelSourceTimeC1 to concrete iterates
4. **G2** (Spectral Agreement) -- hardest structural piece
5. **G4** (Classical Frontier) -- final bridge to IsPaper2ClassicalSolution
6. **G6** (hposWit) -- trivial, do last

---

## 5. Estimated Total Effort

| Gap | Lines | Difficulty | Blocking? |
|-----|-------|-----------|-----------|
| G1 | 300-500 | Medium | Yes -- unblocks GradientMildSolutionData |
| G2 | 200-400 | Hard | Yes -- unblocks HasRestartCosineRepresentations |
| G3 | 100-200 | Easy-Medium | Yes -- connects to DuhamelSourceTimeC1 |
| G4 | 500-800 | Hard | Yes -- 8 fields, some analytically deep |
| G5 | 100 | Easy | Yes -- needed for InitialTrace |
| G6 | 20 | Trivial | No -- last step |
| **Total** | **1200-2000** | | |

The hardest pieces are G2 (spectral agreement / gradient<->standard IBP)
and G4b/c (time regularity from PDE representation).
