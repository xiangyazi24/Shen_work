ANSWER Q4590 5f99545b

# Paper 1 Theorem 1.1, negative branch: the actual construction and the Lean closure DAG

## Executive verdict

The faithful construction is **not a shooting argument**. It is the paper's frozen-profile parabolic construction:

1. fix a trapped antitone profile `q` and solve its elliptic equation for `V_q`;
2. evolve a scalar cross-frozen parabolic equation from the exponential upper barrier;
3. use upper/lower comparison and the sign `χ ≤ 0` to keep every orbit antitone and lower-pinned;
4. take the long-time limit, obtaining a compact continuous map `T(q)`;
5. apply Schauder on the lower-pinned monotone trap;
6. identify a fixed point as a stationary traveling-wave profile.

The right-tail assertion is then a **barrier squeeze**. Linearization identifies the leading root `κ(c)`, but it does **not** by itself produce the full upper endpoint

```text
min ((1+α)κ, mκ+1/2, 1).
```

Those three correction exponents come from the nonlinear reaction, the chemotaxis/elliptic remainder, and the exponential Green kernel in the lower-subsolution calculation.

The dominant analytic core is existence and closed-graph stability of the **non-diagonal frozen Green step**. Spatial monotonicity and the right tail are comparatively short after that core exists. There is also a smaller genuine left-endpoint/root-pinning lemma.

One repo-level warning is load-bearing: the current theorem `whole_line_super_barrier` carries a scalar hypothesis stronger than the paper's negative-branch estimate. With `M = 1` it asks

```text
|χ| (1 + mγκ²) / (1 - γ²κ²) ≤ 1,
```

whereas the paper and `c > cStarLower p` give

```text
|χ| (1 + mγκ²) / (1 - γ²κ²) ≤ 1 + |χ|.
```

The latter is enough because the cross-frozen operator contains the additional favorable term `-|χ| W^(m+γ)`. Thus a paper-faithful relaxation/new wrapper is needed before the current `whole_line_super_barrier` can cover arbitrary `χ ≤ 0` in the headline branch.

---

## 0. Normalization

The exact constants in `ShenWork/Paper1` use the normalized system

```text
u_t = u_xx - χ (u^m v_x)_x + u(1-u^α),
0   = v_xx - v + u^γ.
```

Thus

```text
V_q(x) = frozenElliptic p q x
       = 1/2 ∫_ℝ exp(-|x-y|) q(y)^γ dy.
```

For the physical equation `v_xx-μv+νu^γ=0`, the kernel is

```text
G_μ(x) = (1/(2√μ)) exp(-√μ |x|),
V_q = ν G_μ * q^γ.
```

The architecture is unchanged, but the literal tail cap `1` is the normalized kernel exponent; before spatial rescaling it becomes `√μ`, and the other constants acquire the corresponding powers of `μ,ν`. Therefore the repo's displayed `cStarLower`, `kappa`, and tail window should only be quoted literally in the normalized variables.

---

# 1. The construction

## 1.1 The cross-frozen stationary operator

For a frozen antitone profile `q`, put `V_q := frozenElliptic p q`. The paper does not solve the self-coupled stationary equation immediately. It first uses the cross-frozen scalar operator

```text
A_q(W)
  = W'' + c W'
    - χ m W^(m-1) V_q' W'
    + W (1 - χ W^(m-1) V_q - W^α + χ W^(m+γ-1)).       (1.1)
```

When `q=W=U`, the elliptic equation `V_U'' = V_U-U^γ` gives

```text
-χ m U^(m-1) V_U' U'
-χ U^m V_U
+χ U^(m+γ)
= -χ (U^m V_U')'.
```

Hence `A_U(U)=0` is exactly

```text
U'' + cU' - χ (U^m V_U')' + U(1-U^α) = 0.             (1.2)
```

This cross-frozen choice is important: it avoids differentiating the frozen input `q` in the one-step parabolic maximum-principle argument, yet becomes the desired equation on the diagonal fixed point.

## 1.2 The characteristic root and the speed budget

At `(U,V)=(0,0)`, all chemotaxis terms and the nonlinear part of the reaction are higher order. The linearized profile equation is

```text
U'' + cU' + U = 0.
```

For `U=e^{-λx}` this gives

```text
P_c(λ) := λ²-cλ+1 = 0.                                (1.3)
```

For `c>2`, the two positive roots are

```text
κ(c)    = (c-√(c²-4))/2,
κ_+(c)  = (c+√(c²-4))/2 = κ(c)⁻¹.
```

The repo definition is exactly `kappa c = κ(c)`, and the existing lemmas include

```lean
kappa_pos_of_cStarLower_lt
kappa_lt_one_of_cStarLower_lt
kappa_add_inv_eq_of_cStarLower_lt
kappa_quadratic_eq_zero
```

The negative-branch speed bound is not the linear KPP threshold. Define

```text
Aχ := γ² + γ(m+γ)|χ|
    = γ² + γ²|χ| + mγ|χ|,

f(r) := r + r⁻¹.
```

Then the repo's exact formula is

```text
cStarLower p = max { f(1/m), f(1/√Aχ) }.              (1.4)
```

Because `f` is strictly decreasing on `(0,1]`, `c>cStarLower p` implies

```text
0 < κ < 1,
mκ < 1,
γκ < 1,
Aχ κ² < 1.                                            (1.5)
```

These are the actual reasons for the stronger speed bound: they make the exponential upper barrier and the chemotactic convolution estimates work. The minimal linear speed remains `2`.

## 1.3 The upper barrier

Take

```text
U⁺(x) := min {1, e^{-κx}}.                            (1.6)
```

For a trapped `q`, one has `0≤q≤U⁺≤1`, whence `0≤V_q≤1` and `V_q'≤0`.

On the exponential side, the leading linear terms vanish because `P_c(κ)=0`. For `r:=|χ|=-χ`, the elliptic-kernel calculation in Paper 1, equations (4.3)--(4.6), gives

```text
-r m κ V_q'(x) + r V_q(x)
  ≤ r (1+mγκ²)/(1-γ²κ²) e^{-γκx}.                    (1.7)
```

Using `α≤m+γ-1` and `U⁺=e^{-κx}` on that side,

```text
A_q(e^{-κx})
 ≤ e^{-(1+α)κx}
    [ r (1+mγκ²)/(1-γ²κ²) - (1+r) ].                 (1.8)
```

The last bracket is nonpositive precisely because

```text
Aχ κ² ≤ 1
⇔ r(1+mγκ²) ≤ (1+r)(1-γ²κ²).                         (1.9)
```

On the constant side,

```text
A_q(1) = r(V_q-1) ≤ 0.                               (1.10)
```

The corner is a concave downward corner, so `U⁺` is a weak/viscosity supersolution; equivalently one may approximate it by smooth decreasing supersolutions. The repo has already isolated the corner calculation in `WaveSuperBarrier.lean`.

### Current Lean mismatch

The present `whole_line_super_barrier` assumes, at `M=1`,

```lean
|p.χ| * ((1 + p.m * p.γ * κ^2) / (1 - p.γ^2 * κ^2)) ≤ 1
```

rather than the paper-faithful right side `1+|p.χ|`. The existing assumption is not implied by `cStarLower p<c` when `|χ|` is large. The correct negative-branch lemma should retain the favorable `-|χ|W^(m+γ)` term and use (1.9).

## 1.4 The lower barrier and the lower-pinned trap

Let

```text
B(c,p) := min { (1+α)κ, mκ+1/2, 1 }.                 (1.11)
```

All three entries are strictly larger than `κ`, so `κ<B`. To obtain one profile satisfying the tail assertion for **every** admissible `κ₁`, choose

```text
κ̃ := B(c,p),
```

not a separate `κ̃` depending on `κ₁`.

For `D>0`, define the raw lower function

```text
φraw(x) := e^{-κx} - D e^{-κ̃x}.                     (1.12)
```

Its derivative vanishes at

```text
x₊ = log(D κ̃/κ)/(κ̃-κ),
```

and `φraw(x₊)>0`. Define the plateau version

```text
φ(x) := φraw(x₊),   x≤x₊,
        φraw(x),    x≥x₊.                            (1.13)
```

This is positive, bounded, and antitone. It is the mathematical object represented by the repo's

```lean
lowerBarrierRaw
lowerBarrierPlateau
InLowerPinnedMonotoneTrap
```

The key linear coefficient is

```text
cκ̃-κ̃²-1
 = -(κ̃²-cκ̃+1)
 = (κ̃-κ)(κ⁻¹-κ̃) > 0,                              (1.14)
```

because `κ<κ̃≤1<κ⁻¹`. Thus, on the raw branch,

```text
(∂xx+c∂x+1) φraw
 = D(cκ̃-κ̃²-1)e^{-κ̃x}.                             (1.15)
```

All negative nonlinear remainders have faster decay. The three relevant rates are:

* `(1+α)κ` from `W^(1+α)`;
* the chemotactic rate, uniformly bounded in the paper's three resolver regimes by the cap `mκ+1/2`;
* `1`, the decay exponent of the normalized elliptic Green kernel.

More explicitly:

* if `γκ<1`, then `V_q,V_q'=O(e^{-γκx})`, and the chemotactic remainder is `O(e^{-(m+γ)κx})`; the branch hypothesis `α≤m+γ-1` gives `(1+α)κ≤(m+γ)κ`;
* if `γκ=1`, the convolution has a resonant `x e^{-x}` term, for which the paper uses the safe bound `O(e^{-x/2})`, producing `mκ+1/2`;
* if `γκ>1`, the kernel itself gives rate `1` and the chemotactic term is faster than `mκ+1/2`.

The theorem's negative-speed hypothesis actually forces `γκ<1`, but the paper states the shared lower-barrier lemma with the uniform cap (1.11). For sufficiently large `D`, the positive term (1.15) dominates and `φ` is a subsolution.

The closed convex trap is

```text
K = { q∈C_b(ℝ) : φ≤q≤U⁺ and q is antitone }.         (1.16)
```

The lower pin is essential: it excludes the zero fixed point and later supplies the right-tail squeeze.

## 1.5 Frozen parabolic flow and why `χ≤0` preserves monotonicity

For fixed `q∈K`, solve

```text
z_t = A_q(z),
z(0,x)=U⁺(x).                                           (1.17)
```

Comparison gives

```text
φ ≤ z(t₂,·) ≤ z(t₁,·) ≤ U⁺     for 0≤t₁≤t₂.          (1.18)
```

The middle inequality follows because `U⁺` is a supersolution and the frozen scalar flow is order-preserving:

```text
S_q(t+s)U⁺ = S_q(t)(S_q(s)U⁺) ≤ S_q(t)U⁺.
```

The spatial monotonicity is where the sign of `χ` is decisive. Write `r=-χ≥0`, `V=V_q`, and `w=z_x`. Equation (1.17) is

```text
z_t = z_xx + (c+r m z^(m-1)V')z_x
      + z + r z^m V - z^(α+1) - r z^(m+γ).           (1.19)
```

Differentiation yields

```text
w_t = w_xx + (c+r m z^(m-1)V') w_x
    + r m(m-1) z^(m-2)V' w²
    + [r m z^(m-1)V'' + 1 + r m z^(m-1)V
       -(α+1)z^α-r(m+γ)z^(m+γ-1)] w
    + r z^m V'.                                       (1.20)
```

Since `q` is antitone, so is `q^γ`, and convolution with the positive symmetric kernel preserves order. Equivalently,

```text
V'(x) = 1/2 ∫₀^∞ e^{-s}[q(x+s)^γ-q(x-s)^γ] ds ≤ 0.   (1.21)
```

Therefore both

```text
r m(m-1) z^(m-2)V' w² ≤ 0,
r z^m V' ≤ 0.                                         (1.22)
```

After dropping these favorable terms, `w` satisfies a scalar linear parabolic inequality

```text
w_t ≤ w_xx + a(t,x)w_x+b(t,x)w.                      (1.23)
```

Starting from an antitone approximation of `U⁺`, the maximum principle gives `w≤0`; passing to the corner limit gives that every `z(t,·)` is antitone. This is the precise sense in which negative sensitivity has the “good sign.” It is not merely an informal order assertion about the stationary ODE.

## 1.6 The long-time map and Schauder

By (1.18), the pointwise limit

```text
T(q)(x) := lim_{t→∞} z(t,x;q)                         (1.24)
```

exists and belongs to `K`. Uniform interior parabolic estimates/Green-kernel Lipschitz bounds give equicontinuity on every bounded interval, so the convergence is locally uniform after the standard finite-grid argument.

Equip bounded continuous functions with the local-uniform metric

```text
d(f,g)=Σ_{n≥1} 2^{-n} min(1, ‖f-g‖_{L∞([-n,n])}).    (1.25)
```

Then:

* `T(K)⊆K`;
* `T(K)` is relatively compact in the local-uniform topology;
* `T` is continuous by continuous dependence of `V_q'` and of the frozen Green/parabolic step on `q`.

Schauder gives `U∈K` with `T(U)=U`. Passing to the limit in the frozen equation yields `A_U(U)=0`, hence (1.2).

This is the paper-faithful proof. A shooting proof would turn the nonlocal problem into a coupled four-dimensional/nonlocal boundary-value problem and would still need positivity, order, and both endpoint selections. It is substantially less attractive in Lean.

## 1.7 Endpoints and the full profile

The right endpoint is immediate from `0<U≤e^{-κx}` for large `x`:

```text
U(x)→0,   V_U(x)→0       as x→+∞.                    (1.26)
```

For the left endpoint, antitonicity and boundedness give a limit `L_-∈(0,1]`; the positive plateau lower pin gives `L_->0`. A self-contained root-pinning route is:

1. bounded `U''` plus monotonicity implies `U'(x)→0` as `x→-∞` (a fixed-drop/Barbalat argument);
2. the Green representation gives
   `V_U(x)→L_-^γ` and `V_U'(x)→0`;
3. the flux derivative tends to zero;
4. the stationary equation gives a finite limit
   `U''(x)→-L_-(1-L_-^α)`;
5. a finite nonzero limit of `U''` is incompatible with `U'→0`, hence
   `L_-(1-L_-^α)=0`;
6. `L_->0`, so `L_-=1`.

The paper instead takes translations `U(·+x_n)`, `x_n→-∞`, extracts an entire stationary limit, and identifies the positive constant limit by its stabilization result. Both routes prove

```text
U(x)→1,   V_U(x)→1       as x→-∞.                    (1.27)
```

The repo packages the needed derivative-tail input as `FrozenStationaryFlatAtLeft` and then uses

```lean
InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
```

inside

```lean
b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin
b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin.
```

## 1.8 The strict negative upper bound

The trap gives `U≤min(1,e^{-κx})`. This already implies the paper's strict

```text
U(x)<max(1,e^{-κx})
```

for every `x≠0`. Only `x=0` remains.

A direct proof of `U(0)<1` is short. Assume `U(0)=1`. Then `0` is a global maximum, so `U'(0)=0`, `U''(0)≤0`. Because `U(x)<1` for `x>0` and the Green kernel is strictly positive,

```text
V_U(0)<1.
```

At `0`,

```text
(U^mV_U')' = mU^(m-1)U'V_U' + U^m(V_U-U^γ)
            = V_U(0)-1 < 0.                          (1.28)
```

If `χ<0`, then `-χ (U^mV_U')'<0`; inserting this and `U''(0)≤0` into (1.2) contradicts stationarity. If `χ=0`, the equation is the Fisher--KPP profile ODE; the Cauchy data `U(0)=1`, `U'(0)=0` force `U≡1` by ODE uniqueness, contradicting (1.26).

The repo's mechanical final conversion is

```lean
ShenUpperBoundNegative_of_strictAtZero
ShenUpperBoundNegative_of_stationary_strongMaxPrinciple.
```

---

# 2. The right-tail asymptotic

## 2.1 What linearization proves

The characteristic equation (1.3) proves that the slow admissible exponential is

```text
κ(c)=(c-√(c²-4))/2,
```

and the fast linear mode is `κ(c)⁻¹`. It therefore predicts

```text
U(x) = A e^{-κx} + faster terms.                      (2.1)
```

Translation of the wave changes `A`. The chosen upper/lower barriers fix the phase so that `A=1`.

## 2.2 What produces the theorem's window

Let `κ̃=B(c,p)` as in (1.11). On the right-hand raw branch,

```text
e^{-κx}-D e^{-κ̃x} ≤ U(x) ≤ e^{-κx}.                 (2.2)
```

Divide by `e^{-κx}`:

```text
-D e^{-(κ̃-κ)x}
 ≤ U(x)/e^{-κx}-1
 ≤ 0.                                                 (2.3)
```

For any `κ₁` with `κ<κ₁<κ̃`, multiply by `e^{(κ₁-κ)x}`:

```text
-D e^{-(κ̃-κ₁)x}
 ≤ e^{(κ₁-κ)x}(U(x)/e^{-κx}-1)
 ≤ 0.                                                 (2.4)
```

The left side tends to zero, so the squeeze theorem gives exactly

```lean
HasWaveRightTailAsymptotic c κ₁ U.
```

Thus the theorem's window is

```text
κ(c) < κ₁ < min ((1+α)κ(c), mκ(c)+1/2, 1).           (2.5)
```

It is the exact **proved barrier window**, not a claim that no sharper asymptotic is possible.

The repo has already formalized this squeeze through

```lean
HasWaveRightTailAsymptotic_of_lowerPinnedRawMonotoneTrap
HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
lowerPinnedRawMonotoneTrap_tail_family_for_branch
lowerPinnedMonotoneTrap_tail_family_for_branch.
```

That means the tail is no longer the hard Lean leaf, provided the construction preserves the lower pin and chooses `κ̃` at least the branch cap.

---

# 3. Genuine hard core and a minimal Lean DAG

## 3.1 Difficulty ranking

**Dominant hard core:** construct the non-diagonal frozen Green/Rothe step on the lower-pinned order interval and prove its closed-graph/continuous-dependence properties. This includes truncation removal, whole-line flux integration by parts, source monotonicity and endpoint limits, maximum-principle comparison, and family-uniform convergence.

**Secondary real lemma:** left root-pinning (`FrozenStationaryFlatAtLeft`), unless one imports the paper's translate-limit/stabilization argument.

**Mostly mechanical once the core exists:**

* `U'≤0` and `V_U'≤0`;
* the right-tail asymptotic;
* conversion from the trap upper bound to `ShenUpperBoundNegative`, except for the scalar `U(0)<1` lemma;
* final statement assembly.

## 3.2 Eight-node dependency DAG

### 1. Speed budget and corrected negative superbarrier

Use the existing root algebra

```lean
two_lt_of_cStarLower_lt
kappa_pos_of_cStarLower_lt
kappa_lt_one_of_cStarLower_lt
kappa_add_inv_eq_of_cStarLower_lt
kappa_quadratic_eq_zero
```

and add one small scalar theorem of the shape

```lean
theorem negative_cStar_speed_budget
    (hχ : p.χ ≤ 0) (hc : cStarLower p < c) :
    let κ := kappa c
    0 < κ ∧ κ < 1 ∧ κ * p.m < 1 ∧ p.γ * κ < 1 ∧
      |p.χ| * ((1 + p.m*p.γ*κ^2) / (1-p.γ^2*κ^2)) ≤ 1 + |p.χ|.
```

Then prove a paper-faithful wrapper/relaxation

```lean
whole_line_super_barrier_neg_cStar
```

reusing the regional and corner lemmas in `WaveSuperBarrier.lean`. This repairs the current over-strong `hMbound` surface.

### 2. Lower barrier invariance

Use the existing definitions and elementary facts

```lean
lowerBarrierRaw
lowerBarrierPlateau
lowerBarrierPlateau_pos
```

and prove the Paper 1 Lemma 4.2 producer

```lean
lowerBarrierPlateau_subsolution_neg
```

at `κ̃ = min ((1+p.α)*κ) (min (p.m*κ+1/2) 1)`. Its output should be the lower-orbit invariant consumed by the current Rothe/Schauder route (`RotheOrbitLowerBound` or the corresponding lower-pinned step field).

### 3. The one genuinely hard per-step theorem

The current repo has already isolated the exact remaining object:

```lean
P1StepResidualProvider p c lam M κ Λ u
```

from `IntervalP1StepInputAssembly.lean`; this is a provider of

```lean
RotheFloorOrbitDataResidual p c lam M κ Λ u Z
```

for every admissible old iterate `Z`.

Prove one theorem of the form

```lean
theorem p1StepResidualProvider_neg
    (htrap : InLowerPinnedMonotoneTrap κ M φ u)
    (regime hypotheses ...) :
    P1StepResidualProvider p c lam M κ Λ u.
```

This theorem should consume the already landed pieces

```lean
crossStep_concrete_solution
crossStep_output_of_solution
rotheMaxData_Z
rotheMaxData_barrier
crossFlux_deriv_eq_nondiagonal
crossSource_tendsto_atBot_nondiagonal
crossSource_tendsto_atTop_nondiagonal
```

and discharge the remaining truncation-removal/flux-IBP, source-order, endpoint-sign, and shifted-antitonicity fields. Once it exists, the current assembly is immediate:

```lean
rotheStepInput_of_residualProvider
rotheStepProducer_of_residualProvider
rotheFloorResidual_of_orbitResidual
rotheStepFloor_of_orbitResidual.
```

This node is the main PDE formalization.

### 4. Closed graph and continuity of the orbit map

Prove the family version of the same Green-step estimate:

```lean
RotheSeqStepDependence ...
RotheTailUniform ...
```

or, preferably, the weaker tail uniform only along a locally-uniformly convergent family. The frozen elliptic part is already closed by

```lean
frozenEllipticDerivDependence.
```

Then use the existing epsilon/three assembler

```lean
rotheLimit_dep_of_step_and_tail
rotheContinuousDependence.
```

Analytically, nodes 3 and 4 are one closed-graph theorem viewed at fixed input and varying input; they should be proved together rather than as unrelated projects.

### 5. Compactness and Schauder data

The range compactness side is already largely wireable:

```lean
helly_pointwise_selection
Tmap_compactRange
rotheOrbitData_fromTrap
rotheSchauderData_lowerPinned.
```

The bare monotone-trap Schauder principle is already unconditional:

```lean
inMonotoneWaveTrap_schauderPrinciple.
```

For the lower-pinned trap, add the mechanical specialization

```lean
inLowerPinnedMonotoneTrap_schauderPrinciple
```

by the same projected-cube/partition-of-unity construction, or by a retraction preserving the lower bound. This is topology/bookkeeping, not the PDE hard core.

### 6. Stationarity, left root pin, and profile creation

Use the landed local-uniform limit machinery

```lean
PaperRotheOrbitData.locallyUniform
RotheLimitStationaryData.of_paperRotheOrbitData
frozenWaveOperator_zero_of_paperRotheOrbitData
hstationary_of_paperRotheOrbitData.
```

Supply the direct left-flat/root-pinning lemma

```lean
frozenStationaryFlatAtLeft_of_lowerPinned_stationary
```

using derivative decay plus the Green-resolver tail, or the translation-compactness route. Then call

```lean
b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin.
```

This produces

```lean
∃ U,
  InLowerPinnedMonotoneTrap ... U ∧
  FrozenStationaryWaveProfile p c U.
```

### 7. Monotonicity, strict upper bound, and tail

The two derivative signs are already direct projections:

```lean
constructionNeg_hUmono
constructionNeg_hVmono
frozenElliptic_deriv_nonpos_of_monotone_trap.
```

Prove the small scalar/profile lemma

```lean
stationary_chiNonpos_strictAtZero : U 0 < 1
```

by (1.28), splitting `χ<0` and `χ=0`; then use

```lean
ShenUpperBoundNegative_of_stationary_strongMaxPrinciple.
```

The entire tail family is already obtained from the pin by

```lean
lowerPinnedMonotoneTrap_tail_family_for_branch.
```

### 8. Final branch and headline assembly

Package the result with

```lean
constructionNeg_of_lowerPinnedSchauderData_smp
ConstructionNegSMPProvider
constructionNeg_of_provider_smp
Theorem_1_1.of_constructionNeg_provider_smp.
```

Equivalently, feed the resulting `hneg` directly to

```lean
Theorem_1_1.of_assumed_frozenStationaryProfile_trap_branches
```

or

```lean
Theorem_1_1.of_assumed_frozenStationaryProfile_branches.
```

---

# Bottom line

* **Construction:** frozen parabolic/Green iteration plus lower-pinned Schauder, not shooting.
* **Why `χ≤0` helps:** in the differentiated frozen flow, both the quadratic `w²` term and the forcing term have nonpositive sign because `V_q'≤0`; the same sign also makes the exponential upper barrier work.
* **`κ(c)`:** the smaller root of `λ²-cλ+1=0`; the other root is `κ(c)⁻¹`.
* **`cStarLower`:** a nonlinear barrier threshold `max{f(1/m),f(1/√Aχ)}`, not the linear minimal speed.
* **Tail window:** a nonlinear barrier-remainder window; once the lower pin is preserved, its Lean proof is already a squeeze lemma.
* **Single dominant hard core:** the non-diagonal Green-step residual/closed-graph theorem supplying `P1StepResidualProvider` and continuous dependence. The left root pin is a smaller independent analytic lemma.
* **Immediate repo correction:** relax the negative `whole_line_super_barrier` scalar assumption to the paper-faithful bound with right side `1+|χ|M` (at `M=1`, `1+|χ|`); otherwise `cStarLower p<c` does not discharge the current hypothesis for arbitrary negative sensitivity.
