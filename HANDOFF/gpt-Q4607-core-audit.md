ANSWER Q4607 f72fb381

# Adversarial audit verdict

## Fatal source-control finding

The requested committed artifact is not present on the connector-visible remote branch. I therefore cannot honestly give line numbers or claim that any named theorem has the signature described in the question.

Concrete checks against xiangyazi24/Shen_work, ref chatgpt-scratch:

- Fetching ShenWork/PDE/RestartedMildSmoothing.lean by repository path and ref returns GitHub 404 Not Found.

- Fetching the corresponding GitHub blob URL also returns 404 Not Found.

- Repository code searches for RestartedMildSmoothing, restartedSmoothingKernel, and SuperlinearClosedBallData return no result.

- Comparing the known Q4600 commit 2ab96df38191609dc1b62698126bf54bfe76609d with the current remote chatgpt-scratch ref reports exactly two later commits. Their only changed files are:

```plain text
drops/Q4603-df4f2914.md
drops/Q4606-d0ebf916.md
```

There is no ShenWork/PDE/RestartedMildSmoothing.lean in that comparison.

So the first adversarial conclusion is:

REFUTE the claim that this file is currently committed on the named remote branch.

Consequently, the claim “0 sorry” is not auditable from the repository state. A line-specific audit without the source would be fabrication. What follows is a rigorous audit of the stated interface/design, including concrete counterexamples that any eventual file must survive.

# Executive mathematical verdict

The intended kernel and one-window Bochner estimates are sound in principle, but the design as stated is not yet a shared substrate for both keystones.

The decisive mismatch is the affine exit

```plain text
M ‖w₀‖_Z + Λ₀ K₀(T).
```

That estimate starts from a Z-norm bound on the restart datum. The Paper-2 keystone starts from a uniform finite L^P bound and must produce an L∞ bound after a unit delay. Its late-time homogeneous term must therefore be bounded by a Y → Z smoothing estimate,

```plain text
‖S(1) w(t-1)‖_Z ≤ C ‖w(t-1)‖_Y,
```

not by M ‖w(t-1)‖_Z. This distinction is explicit in drops/Q4603-df4f2914.md: the one-unit version is supposed to use A_P K, while the short first window may use an already available M₀ sup bound.

Also, a finite ν=0 one-window estimate does not by itself glue to a uniform all-time bound. The scalar counterexample below proves this.

# 1. Vacuity and joint satisfiability of the superlinear ball conditions

## Correct small-data geometry

For a mild map

```plain text
F(w)(t) = S(t)w₀ + ∫₀ᵗ S(t-s) N(w(s)) ds
```

assume, schematically,

```plain text
‖S(t)w₀‖_Z ≤ M ‖w₀‖_Z,
‖N(z)‖_Y ≤ Λ ‖z‖_Z^(1+ε),
```

and let K be the relevant convolution mass. On a closed path ball of radius R, the genuine self-map condition is

```plain text
M ρ₀ + K Λ R^(1+ε) ≤ R,                 (SM)
```

where ρ₀ bounds the initial datum. A corresponding contraction condition has the form

```plain text
K L_R < 1,
L_R ≲ Λ R^ε.                              (CT)
```

These conditions are jointly satisfiable. For example, set

```plain text
R = 2 M ρ₀
```

when M>0. Then the homogeneous term uses half the ball budget, and sufficiently small ρ₀ makes both

```plain text
K Λ R^(1+ε) ≤ R/2
```

and (CT) true.

## Concrete unsatisfiable formulation to reject

If SuperlinearClosedBallData uses the same positive number ρ both as the initial-data bound and as the path-ball radius, and asks for

```plain text
M ρ + K Λ ρ^(1+ε) ≤ ρ,
```

then the standard semigroup case M=1, with K>0, Λ>0, ε>0, is impossible for every ρ>0:

```plain text
ρ + K Λ ρ^(1+ε) > ρ.
```

That is a genuine vacuity bug, not merely a non-sharp constant. The implementation must separate initialRadius from ballRadius, or build in a factor such as R = 2Mρ₀.

## File-level status

Because the file is absent, I cannot determine whether its SuperlinearClosedBallData makes the correct separation. The exact field list is the first thing to inspect once the source is actually pushed.

# 2. Enforcement of 0 < θ < 1

## Necessary analytic statement

For

```plain text
K(τ) = C (1 + τ^(-θ)) exp(-ντ),   τ>0,
```

the singular part is locally integrable exactly when

```plain text
θ < 1.
```

For the intended smoothing regimes one also wants 0 < θ. The two concrete specializations satisfy this:

```plain text
P2: θ = 1/2 + 1/(2P),  P>1  ⇒  0<θ<1;
P3: θ = α,             0<α<1.
```

The load-bearing Lean theorem should export integrability, not only a numerical inequality. A safe shape is:

```javascript
theorem restartedSmoothingKernel_intervalIntegrable
    (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    IntervalIntegrable
      (fun τ => restartedSmoothingKernel C θ ν τ)
      volume 0 T
```

and the infinite-time positive-rate version should export Integrable on Set.Ioi 0 or on the whole line after zero-extension.

## Mathlib vacuity trap

This point is especially important in Lean: the Bochner integral is defined to be zero for a non-integrable function. Therefore a theorem of the bare form

```javascript
∫ τ in 0..T, restartedSmoothingKernel C θ ν τ ≤ B
```

can be analytically meaningless if no IntervalIntegrable fact is proved or consumed. At θ=1 or θ=2, the intended improper integral diverges at zero, but a proof may still manipulate Mathlib's totalized integral and obtain a harmless-looking inequality.

Concrete failing instances are

```plain text
θ=1:  ∫₀¹ τ⁻¹ dτ = ∞,
θ=2:  ∫₀¹ τ⁻² dτ = ∞.
```

Thus:

- integral_rpow_neg must require the exponent condition corresponding to -θ > -1, namely θ<1;

- every kernel-mass theorem must either return integrability or take it as an explicit hypothesis;

- bochner_mild_norm_le must not rely only on norm_integral_le_integral_norm without separately establishing integrability of the Duhamel integrand.

## File-level status

No confirmation is possible until the theorem signatures are visible. A merely compiled numerical bound is not enough to pass this audit.

# 3. The ν=0 / ν>0 split and restartGlue

## Correct kernel masses

For ν=0, 0<θ<1, and T≥0, the exact finite-window mass is

```plain text
K₀(T) = C [ T + T^(1-θ)/(1-θ) ].
```

It grows like T for large T; the singular contribution behaves like T^(1-θ) near zero. It is not an all-time constant.

For ν>0, the all-time mass is finite:

```plain text
C ∫₀∞ (1+τ^(-θ))e^(-ντ)dτ
 = C [ 1/ν + Γ(1-θ) ν^(θ-1) ].
```

A gamma-free proof can split at τ=1. For 0<θ<1, one valid crude bound is

```plain text
C [ 1/(1-θ) + 2/ν + 1 ],
```

with many harmless variants. A bound containing only 1/ν + 1/(1-θ) needs separate verification; the tail generally contributes to both the 1 and τ^-θ terms.

## Concrete counterexample to an overstrong restart glue

Take

```plain text
Y = Z = ℝ,
S(t) = id,
ν = 0,
f(t) = 1,
w₀ = 0.
```

For any 0<θ<1, the smoothing inequality

```plain text
|S(τ)y| ≤ (1+τ^-θ)|y|
```

holds for every τ>0. The mild solution is

```plain text
w(t) = ∫₀ᵗ 1 ds = t.
```

Every unit window has finite kernel mass, and

```plain text
w(t) = w(t-1) + 1.
```

Nevertheless,

```plain text
sup_{t≥1} |w(t)| = ∞.
```

Therefore:

A theorem cannot derive a uniform all-time ν=0 bound merely from a uniform finite-window affine estimate and recursive restart.

If restartGlue claims that, it is false unless its hypotheses already contain the conclusion in disguise.

## What the P2 restart actually needs

Paper 2 avoids the counterexample by using a fresh uniform Y bound on every restart slice and a fixed positive smoothing delay:

```plain text
sup_t ‖w(t)‖_Y ≤ K_Y,
‖S(1)w(t-1)‖_Z ≤ C_YZ K_Y.
```

The prior Z norm is not propagated recursively. Each late time is estimated directly from the uniform Y bound on the fresh window [t-1,t].

A correct P2 glue interface therefore needs something like

```javascript
(hY : ∀ t, 0 ≤ t → ‖w t‖_Y ≤ KY)
(hhom : ∀ t, 1 ≤ t → ‖S 1 (w (t-1))‖_Z ≤ CYZ * KY)
```

plus the one-window Duhamel bound. A generic restartGlue that only receives M ‖w(t-1)‖_Z is insufficient.

# 4. Direction and sign of the Bochner mild estimate

The correct chain is

```plain text
‖w(t)‖_Z
≤ ‖S(t)w₀‖_Z
  + ‖∫₀ᵗ S(t-s)f(s) ds‖_Z
≤ ‖S(t)w₀‖_Z
  + ∫₀ᵗ ‖S(t-s)f(s)‖_Z ds
≤ M e^(-νt) ‖w₀‖_Z
  + ∫₀ᵗ K(t-s) ‖f(s)‖_Y ds.
```

For an affine source bound ‖f(s)‖_Y≤Λ₀, this gives

```plain text
‖w(t)‖_Z
≤ M ‖w₀‖_Z + Λ₀ K₀(T)
```

on 0≤t≤T, after dropping exponential factors. The direction is correct provided:

- the Duhamel integrand is Bochner integrable;

- C, M, and Λ₀ are nonnegative where monotone multiplication is used;

- the homogeneous estimate is genuinely a Z→Z estimate;

- the smoothing estimate is genuinely a Y→Z estimate;

- interval orientation and the substitution τ=t-s are handled with 0≤s≤t.

A compiled theorem can still be vacuous if it assumes an impossible norm bound such as ‖S(t)z‖≤M‖z‖ with M<0 on a nontrivial space, or if it carries Duhamel integrability as an unexplained hypothesis. Those hypotheses need a concrete instance audit.

Most importantly, the displayed affine theorem is not the P2 late-time homogeneous estimate: P2 needs Y→Z smoothing of the restart datum. The abstract library should expose both variants:

```javascript
bochner_mild_affine_bound_from_Z_initial
bochner_mild_affine_bound_from_Y_initial_at_positive_delay
```

or accept a direct homogeneous bound H₀ rather than hard-code M‖w₀‖_Z.

# 5. Usability by the two keystones

## P2 affine specialization: refuted for the stated Fable interface

The stated affine exit is under-specified for the P2 endpoint for three independent reasons.

### 5.1 Wrong restart-data norm

The key input is a uniform finite L^P bound (Y), while the desired output is L∞ (Z). Requiring ‖w₀‖_Z assumes the conclusion on each late restart slice.

### 5.2 Two different Duhamel operator families

The value-source leg uses the heat semigroup, while the chemotaxis divergence leg uses the B-form derivative-kernel operator. They have different singular exponents:

```plain text
heat: θ₀ = 1/(2P),
B-form: θ₁ = 1/2 + 1/(2P).
```

A single abstract operator can cover both only if the API permits a product/source-sum operator or separate kernel families and then dominates them on a fixed window. If it insists that every Duhamel leg is the same semigroup S, it does not model the P2 equation.

### 5.3 Restart must be direct, not recursive

As the scalar counterexample shows, ν=0 recursive affine restart is not uniformly bounded. The P2 proof must re-estimate the homogeneous term from the fresh L^P bound on every unit window.

Thus, based on the design stated in Q4607, the claim “usable by P2” is REFUTED unless the absent file contains an additional Y-initial, fixed-delay theorem not listed in the question.

## P3 superlinear specialization: plausible, with two checks

The P3 side has the standard shape N:Z→Y with a locally superlinear remainder. It can instantiate the core if the file provides:

```plain text
‖N(z)‖_Y ≤ Λ ‖z‖_Z^(1+ε),
‖N(z)-N(y)‖_Y ≤ L_R ‖z-y‖_Z,
L_R = O(R^ε),
```

and a complete weighted path space.

Two points remain load-bearing.

### 5.4 Reserved rate versus exact full linear rate

The ordinary easy convolution lemma uses a reserved rate 0<ω<ν:

```plain text
e^(ωt) ∫₀ᵗ Kν(t-s)e^(-ωs) ds
≤ ∫₀∞ C(1+r^-θ)e^(-(ν-ω)r) dr.
```

This yields decay e^-ωt, not necessarily e^-νt. That is fully sufficient for local exponential stability.

Exact e^-νt decay is also possible for a genuinely superlinear forcing, because N(w(s)) decays like e^{-(1+ε)νs}, but it needs a different two-ended convolution estimate. The theorem name weightedConvolution_le_reservedRate suggests the simpler ω<ν route. If fixedPoint advertises exact rate ν while only invoking a reserved-rate lemma, that is a claim mismatch.

### 5.5 Completeness and the actual path metric

fixedPoint must act on a complete space such as bounded continuous paths with a weighted sup norm, or a closed subset thereof. Merely postulating a pointwise family ℝ→Z and a formal sup expression is not enough. The closed ball must be closed in the metric used by ContractingWith.

Because the source is absent, these cannot be confirmed.

# 6. Minimal non-vacuous Lean shape

A structurally sound superlinear package separates the radii and makes integrability explicit:

```javascript
structure SuperlinearClosedBallData where
  C M Λ θ ν ε initialRadius ballRadius : ℝ
  C_nonneg : 0 ≤ C
  M_nonneg : 0 ≤ M
  Λ_nonneg : 0 ≤ Λ
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  nu_pos : 0 < ν
  epsilon_pos : 0 < ε
  initialRadius_nonneg : 0 ≤ initialRadius
  ballRadius_pos : 0 < ballRadius
  homogeneous_budget : M * initialRadius ≤ ballRadius / 2
  nonlinear_budget :
    positiveKernelMass C θ ν * Λ * ballRadius^(1+ε) ≤ ballRadius / 2
  contraction_budget :
    positiveKernelMass C θ ν * localLip Λ ε ballRadius < 1
```

For P2, add a separate one-window interface:

```javascript
theorem bochner_mild_affine_bound_from_Y_initial_at_delay
    (hdelay : 0 < τ₀)
    (hhom : ‖S τ₀ w₀‖_Z ≤ CYZ * ‖w₀‖_Y)
    (hforce : ∀ s ∈ Set.Icc 0 τ₀, ‖f s‖_Y ≤ Λ₀)
    ... :
    ‖w τ₀‖_Z ≤ CYZ * ‖w₀‖_Y + Λ₀ * K₀ τ₀
```

and make restartGlue consume a fresh uniform Y bound rather than recursively consume the previous Z bound.

# Final answer to the five audit questions

1. Vacuity: file-level result unavailable. The standard conditions are satisfiable only when initial and ball radii are separated. Reusing one positive radius with M=1 makes self-mapping impossible.

1. θ<1: must be explicit and accompanied by Integrable/IntervalIntegrable. A bare totalized-integral inequality can be vacuous for θ≥1.

1. Rate split/restart: the kernel split is mathematically as above. A ν=0 one-window bound does not imply a uniform all-time bound; S=id, f=1, w(t)=t is a concrete counterexample. P2 needs fresh Y→Z smoothing on every fixed window.

1. Bochner direction: the intended inequality direction is correct under genuine integrability and nonnegative constants. The listed affine bound uses a Z→Z homogeneous estimate and therefore is not the P2 late-time smoothing bound.

1. Shared usability: refuted for the stated interface. P3 is plausibly supported; P2 is not, unless the missing source contains an unlisted Y-initial positive-delay exit and a non-recursive restart theorem.

# Repository verdict

The honest audit cannot certify or condemn the implementations of mapsTo, contracting, fixedPoint, or restartGlue, because the named source file is not on the named remote branch. The remote source-control claim fails before the Lean proof audit begins. The most important design correction, independently established, is to add the fixed-delay Y→Z homogeneous exit required by Paper 2 and to prevent restartGlue from manufacturing a ν=0 uniform bound from recursive affine windows.