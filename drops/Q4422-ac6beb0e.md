ANSWER Q4422 ac6beb0e

# Definitive verdict

**Both leaves close at the `u ≥ 0` stage. Neither leaf mathematically requires `u > 0`.** The energy-to-Jensen dependency can remain acyclic:

```text
truncated mild solution + positive-time gradient bound
→ weak/variational equation for U
→ negative-part energy gives U ≥ 0
→ low-order elliptic C²/W²,∞ regularity of R[U]
→ bounded g and gₓ
→ squared-heat barrier is a subsolution of the same complete linear operator
→ matched-divergence Stampacchia comparison
→ U ≥ w > 0
→ only now use a positive floor for high-order Nemytskii/spectral work.
```

There are, however, two important implementation corrections.

1. On the U side, do **not** require a pointwise `U_t`, a pointwise `U_xx`, or an a-priori assertion that `(w-U)₊` is an absolutely continuous time-dependent test. The right theorem is the variational/mild-to-weak increment identity in the Gelfand triple `H¹ ⊂ L² ⊂ H⁻¹`, followed by the standard Stampacchia chain rule.
2. On the barrier side, `gₓ` is **not** part of the first-order coefficient `B = -χ₀ g`. It enters the zero-order coefficient

   ```text
   C = c - χ₀ gₓ
   ```

   after the divergence operator is expanded. The old concrete pair

   ```text
   B = -χ₀ g,
   C = c
   ```

   does not describe the same operator and is insufficient.

The current high-order shared file `IntervalMildPositiveTimeRegularityV6.lean` must not be used to discharge the Jensen barrier leaf: its generic `ConjugateMildSolutionData` route uses `S.hpos` and even constructs a positive spatial floor. That is appropriate **after** Jensen, but circular before Jensen. The needed resolver result is much lower order and is valid from bounded continuous nonnegative `U` alone.

---

# 1. Leaf 1: U-side integrated Dirichlet-form identity

## 1.1 Correct functional setting

Fix a compact positive-time window

```text
0 < s < T' ≤ T.
```

Let

```text
H  := L²(0,1),
V  := H¹(0,1),
V* := H⁻¹(0,1).
```

Write the already-nonnegative truncated limit as `U`, and put

```text
Q(r,x) := U(r,x) · g(r,x),
g := Rₓ[U] / (1+R[U])^β,
L(r,x) := U(r,x) · (a-b U(r,x)^α).
```

The weak equation is

```text
U_t = ν U_xx - χ₀ ∂ₓQ + L.
```

On `[s,T']`, the inputs already available before strict positivity give:

```text
U ∈ C([s,T']; L²),
U ∈ L∞(s,T'; H¹),
Q ∈ L∞(s,T'; L²),
L ∈ L∞(s,T'; L²).
```

The `H¹` assertion is supplied by the unconditional positive-time spatial-gradient/Lipschitz estimate for the truncated limit. The `Q` and `L` assertions use only the sup bound, continuity, resolver value/gradient bounds, `U ≥ 0`, and `1+R ≥ 1`. They do not differentiate `U^γ` and do not need a positive floor.

Define, for `φ ∈ V`,

```text
⟨G(r),φ⟩
  := -ν ∫₀¹ Uₓ(r,x) φₓ(x) dx
     + χ₀ ∫₀¹ Q(r,x) φₓ(x) dx
     +     ∫₀¹ L(r,x) φ(x) dx.
```

Then

```text
|⟨G(r),φ⟩|
≤ [ν ‖Uₓ(r)‖₂ + |χ₀| ‖Q(r)‖₂ + ‖L(r)‖₂] ‖φ‖_{H¹}.
```

Consequently

```text
G ∈ L∞(s,T';H⁻¹) ⊂ L²(s,T';H⁻¹) ⊂ L¹(s,T';H⁻¹).
```

Thus the correct conclusion is not merely that a formal `U_t` exists: the mild identity identifies the distributional derivative with `G`, so

```text
U ∈ W¹,²(s,T';H⁻¹) ∩ L²(s,T';H¹).
```

The weaker statement `U_t ∈ L¹(H⁻¹)` is therefore true, but it should be a **consequence**, not an extra classical-regularity hypothesis.

## 1.2 Exact fixed-test increment identity

For every `φ ∈ H¹(0,1)` and `s ≤ t₁ ≤ t₂ ≤ T'`, the target identity is

```text
∫₀¹ (U(t₂,x)-U(t₁,x)) φ(x) dx
 = -ν ∫_{t₁}^{t₂}∫₀¹ Uₓ(r,x) φₓ(x) dx dr
   +χ₀ ∫_{t₁}^{t₂}∫₀¹ Q(r,x) φₓ(x) dx dr
   +    ∫_{t₁}^{t₂}∫₀¹ L(r,x) φ(x) dx dr.
```

This is the precise integrated Dirichlet-form equation needed before the Stampacchia test.

For a time-dependent test `Φ`, the useful product-rule version is

```text
∫ U(t₂) Φ(t₂) - ∫ U(t₁) Φ(t₁)
 = ∫_{t₁}^{t₂}∫ U(r) ∂ᵣΦ(r)
   -ν ∫_{t₁}^{t₂}∫ Uₓ(r) ∂ₓΦ(r)
   +χ₀ ∫_{t₁}^{t₂}∫ Q(r) ∂ₓΦ(r)
   +    ∫_{t₁}^{t₂}∫ L(r) Φ(r),
```

under, for example,

```text
Φ ∈ L∞(t₁,t₂;H¹),
∂ₜΦ ∈ L¹(t₁,t₂;L²).
```

A bounded `V`-valued absolutely continuous test is more than enough.

## 1.3 Do the named mild lemmas suffice?

**Yes, modulo the ordinary `H¹`/source measurability fields just listed.** The proof can be kept entirely at the mild/variational level.

The load-bearing chain is:

```text
backward restart mild identity
+ heat-semigroup endpoint pairing in the Dirichlet form
+ self-adjoint pairing for the ordinary heat leg
+ B-form/conjugate-kernel duality for the divergence leg
+ Fubini on the time triangle
+ the integrable (t-r)^(-1/2) majorant
+ strong L² continuity at the two time endpoints.
```

The relevant committed infrastructure already points in exactly this direction:

- `IntervalNegativePartWeakEnergy.lean` explicitly says that it works with mild right increments and **does not reconstruct a pointwise time derivative**.
- `intervalFullSemigroupOperator_pairing_comm` gives the ordinary heat self-adjoint pairing.
- `intervalConjugateApproxOperator_pairing_comm` gives the corresponding signed conjugate/Dirichlet pairing.
- `deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_of_ac` is the Sobolev-level spatial integration-by-parts bridge for an absolutely continuous test.
- `heatDuhamelDCTDominatingFunction_of_bounds` and `chemotaxisDuhamelDCTDominatingFunction_of_bounds` provide the integrable square-root singularity majorants.
- `truncatedLimit_weakIdentity_of_standardFacts` already shows that the standard heat-Duhamel package, B-form duality, and the fixed-point mild identity produce the direct weak identity without using the spectral bootstrap.

The extra semigroup fact needed in the generic fixed-test theorem is the form-generator endpoint limit

```text
lim_{h→0+} h⁻¹ ⟨(Sν(h)-I)v, φ⟩
  = -ν ∫ vₓ φₓ,
```

for `v,φ ∈ H¹`. This is an `H¹` form identity; it does **not** require `v ∈ H²`. It can be proved spectrally by dominated convergence, using

```text
|(e^{-νλh}-1)/h| ≤ νλ
```

and Cauchy–Schwarz in the weighted cosine coefficients.

## 1.4 The actual hidden pitfall: testing by `z₊`

The only subtlety is not strict positivity; it is the order in which the time-dependent truncation is introduced.

Set

```text
z := w-U.
```

One should not assume in advance that

```text
r ↦ z₊(r)
```

is a bounded absolutely continuous `H¹`-valued test. Instead:

1. prove the variational equation for `z`;
2. note

   ```text
   z ∈ L²(H¹) ∩ W¹,²(H⁻¹),
   ```

   because `w` is smooth and `U` has the regularity above;
3. invoke/prove the Lions–Stampacchia chain rule

   ```text
   ½ ‖z₊(t₂)‖₂² - ½ ‖z₊(t₁)‖₂²
     = ∫_{t₁}^{t₂} ⟨z_t,z₊⟩,
   ```

   together with

   ```text
   ∂ₓz₊ = 1_{z>0} ∂ₓz
   ```

   almost everywhere.

Equivalently, formalize the chain rule by smooth convex approximations to `r ↦ ½(r₊)²`. This avoids any circular assumption that the final test is already time-AC.

Because the positive-time estimates give `U_t ∈ L∞(H⁻¹)` and `U ∈ L∞(H¹)` on a compact window, the standard `L²(V)`/`L²(V*)` hypotheses are comfortably satisfied.

### Leaf-1 verdict

There is **no hidden strict-positivity gap**. The leaf is a genuine but routine mild-to-variational packaging theorem. It must include the positive-time `H¹` bound and source measurability/integrability; the three named semigroup/Fubini mechanisms do not magically manufacture those hypotheses, but those hypotheses are already available independently of `u>0`.

---

# 2. Leaf 2: the `gₓ` bound for the squared-heat barrier

## 2.1 Low-order elliptic regularity needs no positive floor

At a fixed positive time, suppose only

```text
0 ≤ U(x) ≤ M,
U ∈ C([0,1]),
γ ≥ 1.
```

Then

```text
F(x) := ν U(x)^γ
```

is continuous and bounded. The map `r ↦ r^γ` is continuous, indeed locally Lipschitz, on `[0,M]` for every real `γ ≥ 1`. Nothing singular occurs at `r=0` at this order.

For the resolver normalization currently compiled in the repository,

```text
-Rₓₓ + μR = ν U^γ,
Rₓ(0)=Rₓ(1)=0,
```

the one-dimensional Neumann resolvent gives

```text
R ∈ C²([0,1])
```

(and in fact `W²,∞`) with the pointwise identity

```text
Rₓₓ = μR - ν U^γ.
```

Hence

```text
‖Rₓₓ‖∞ ≤ μ ‖R‖∞ + ν M^γ.
```

Using resolver positivity and the maximum-principle bound

```text
0 ≤ R ≤ (ν/μ) M^γ,
```

one obtains the coarse explicit bound

```text
‖Rₓₓ‖∞ ≤ 2ν M^γ.
```

One can sharpen the constant, but no sharp value is needed for comparison.

For the alternative normalization written as

```text
(μ-ν∂ₓₓ)R = ν U^γ,
```

the corresponding identity is

```text
Rₓₓ = (μ/ν)R - U^γ,
```

and the same conclusion follows because `ν>0`.

This uses only continuity and boundedness of `U^γ`. It does **not** use `(U^γ)ₓ`, `(U^γ)ₓₓ`, or a factor `U^{γ-2}`. The latter appears only in high-order Nemytskii estimates and is irrelevant here.

## 2.2 Exact `gₓ` formula and bound

Let

```text
g := Rₓ (1+R)^(-β).
```

Since `R ≥ 0` and `β ≥ 0`,

```text
1+R ≥ 1,
0 < (1+R)^(-β) ≤ 1,
0 < (1+R)^(-β-1) ≤ 1.
```

The product/chain rule gives

```text
gₓ
 = Rₓₓ (1+R)^(-β)
   - β Rₓ² (1+R)^(-β-1).
```

Therefore

```text
‖g‖∞ ≤ ‖Rₓ‖∞,
‖gₓ‖∞ ≤ ‖Rₓₓ‖∞ + β ‖Rₓ‖∞².
```

The resolver-gradient bound for an arbitrary bounded continuous ball element is already part of the weak resolver infrastructure (`IntervalResolverWeakBounds.lean`). Combining it with the low-order second-derivative identity gives the required finite constant.

Time dependence also causes no positivity issue. If

```text
t ↦ U(t) ∈ C([0,1])
```

is continuous on a compact positive-time window, then `t ↦ U(t)^γ` is continuous in sup norm, and the constant-coefficient elliptic resolver is continuous from `C⁰` into `C²` on the interval. Thus `g` and `gₓ` can be taken jointly continuous; for the weak comparison, bounded measurability would already suffice.

## 2.3 Where `gₓ` belongs in the linear operator

The common divergence-form linear operator is

```text
𝓛_g,c[y]
  := ν yₓₓ - χ₀ ∂ₓ(y g) + c y.
```

Expanding only for the smooth barrier gives

```text
𝓛_g,c[y]
 = ν yₓₓ + B yₓ + C y,
```

with the **complete** coefficients

```text
B := -χ₀ g,
C := c - χ₀ gₓ.
```

Thus:

```text
|B| ≤ |χ₀| ‖g‖∞,
-C = -c + χ₀ gₓ
   ≤ ‖c‖∞ + |χ₀| ‖gₓ‖∞.
```

For the squared barrier

```text
w = e^{-Mt}(Sν(t)f)²,
```

the residual is

```text
w_t - νwₓₓ - B wₓ - Cw
 = e^{-Mt}
   [-M h² - 2ν hₓ² - 2B h hₓ - C h²],
```

where `h=Sν(t)f`. Completing the square gives

```text
-2ν hₓ² - 2B h hₓ ≤ B²/(2ν) · h².
```

Hence it suffices to choose

```text
A ≥ ‖B‖∞,
D ≥ sup(-C),
M ≥ A²/(2ν) + D.
```

The committed `squareHeatResidualCore_nonpos_of_bounds` uses the normalization `ν=1`, hence its displayed threshold `A²/2+D`. If the heat diffusion is not normalized, the theorem or its wrapper must carry the factor `1/ν`.

## 2.4 Crucial matched-divergence distinction

The `gₓ` bound is needed to verify the **barrier residual after expansion**. It is not needed in the final `z₊` energy estimate.

If both `w` and `U` satisfy sub/supersolution inequalities for the same complete divergence operator, subtraction gives

```text
z_t - νzₓₓ + χ₀ ∂ₓ(zg) - cz ≤ 0,
z=w-U.
```

Testing with `z₊` gives the drift term

```text
-χ₀ ∫ ∂ₓ(zg) z₊
 = χ₀ ∫ z g ∂ₓz₊,
```

with no interior `gₓU z₊` or `gₓw z₊` term. The boundary term vanishes because the Neumann resolver has

```text
Rₓ(0)=Rₓ(1)=0,
```

hence `g(0)=g(1)=0`.

If a term such as

```text
∫ gₓ U z₊
```

survives, the two equations were not subtracted in the same divergence form. Boundedness of `gₓ` does not repair that mismatch: it would generally produce a forcing term proportional to `∫ U z₊`, not the homogeneous `∫ z₊²` needed for zero-initial Gronwall.

## 2.5 Current repository packaging caveat

The low-order conclusion is mathematically straightforward, but the safest formalization route is important:

- `IntervalResolverWeakBounds.lean` already develops resolver value and gradient bounds for an **arbitrary bounded continuous** ball element, explicitly without a classical-solution hypothesis.
- `IntervalResolverLaplacianBridge.lean` has a strong Laplacian identity, but its main pointwise series theorem is packaged under `SourceCoeffQuadraticDecay`. That is stronger than this leaf needs and can drag in later source regularity.
- `IntervalMildPositiveTimeRegularityV6.lean` obtains high-order slice regularity through a package that uses `S.hpos` and a positive floor. It must not be imported to prove pre-Jensen `gₓ` control.

The clean missing low-order theorem should have approximately this contract:

```text
bounded continuous 0≤u≤M
→ R=intervalNeumannResolverR p u has a C² representative on [0,1]
→ Rₓ(0)=Rₓ(1)=0
→ Rₓₓ = μR-νu^γ on (0,1)
→ ‖Rₓₓ‖∞ ≤ μ‖R‖∞+νM^γ.
```

Prove it from the explicit one-dimensional Neumann Green kernel, or from weak `H²/W²,∞` elliptic regularity followed by the ODE identity. This is a real formalization leaf, but it is **low order, positivity-free, and independent of HSpectral**.

### Leaf-2 verdict

`Rₓₓ` boundedness and hence `gₓ ∈ L∞` are valid already at `U ≥ 0`. No lower bound `U ≥ δ` and no strict positivity are needed. The only danger is accidentally routing through a high-order theorem whose hypotheses already contain `S.hpos`.

---

# 3. Final Stampacchia/Gronwall closure

With the two leaves in place, let `z=w-U`. The common-operator sub/supersolution inequalities give

```text
½ d/dt ‖z₊‖₂²
≤ -ν ‖∂ₓz₊‖₂²
   + χ₀ ∫ z₊ g ∂ₓz₊
   + ∫ c z₊².
```

Young's inequality yields

```text
|χ₀| ‖g‖∞ ∫ z₊ |∂ₓz₊|
≤ (ν/2) ‖∂ₓz₊‖₂²
  + χ₀² ‖g‖∞²/(2ν) ‖z₊‖₂².
```

Hence

```text
½ d/dt ‖z₊‖₂²
≤ -ν/2 ‖∂ₓz₊‖₂²
  + [χ₀² ‖g‖∞²/(2ν) + ‖c‖∞] ‖z₊‖₂².
```

If the restart seed satisfies

```text
w(s) = f² ≤ U(s),
```

then

```text
z₊(s)=0
```

(the stronger equality `z(s)=0` is unnecessary). Gronwall gives

```text
z₊≡0,
w≤U.
```

Since the squared Neumann heat barrier is strictly positive for positive elapsed time,

```text
0 < w(t,x) ≤ U(t,x),
```

so `U>0` follows a posteriori.

---

# 4. Minimal producer interfaces Codex should target

## Leaf 1: variational solution package

The producer should expose, on every compact positive-time window, the following facts for the **same** truncated limit:

```text
U ∈ C(L²),
U ∈ L²(H¹),
U_t ∈ L²(H⁻¹),

∀ φ∈H¹,
  ⟨U(t₂)-U(t₁),φ⟩
   = ∫_{t₁}^{t₂}
       [-ν⟨Uₓ,φₓ⟩ + χ₀⟨Q,φₓ⟩ + ⟨L,φ⟩] dr.
```

It should be produced from the restart mild identity and the committed pairing/Fubini lemmas. Do not put `U_t` or `U_xx` pointwise in the input signature.

Separately prove a generic positive-part chain-rule/comparison theorem for

```text
z ∈ L²(H¹) ∩ W¹,²(H⁻¹).
```

## Leaf 2: low-order resolver coefficient package

For each compact positive-time window, expose constants `G0,G1` with

```text
|g(t,x)| ≤ G0,
|gₓ(t,x)| ≤ G1,
g(t,0)=g(t,1)=0,
```

from only

```text
U continuous,
0≤U≤M,
γ≥1,
μ>0,
ν>0.
```

Then define the complete barrier coefficients

```text
B = -χ₀g,
C = c-χ₀gₓ,
```

and feed their bounds to the squared-heat residual theorem.

---

# Bottom line

**The chain is acyclic and sound.**

- Leaf 1 closes at `U ≥ 0` through mild-to-variational theory; `U_t∈L¹(H⁻¹)` not only holds but can be strengthened to `L²` or `L∞` on compact positive-time windows under the existing uniform gradient/source bounds.
- Leaf 2 closes at `U ≥ 0` because a bounded continuous source `U^γ` gives a low-order `C²/W²,∞` Neumann resolver. Real `γ≥1` causes no singularity at zero at this order.
- Strict positivity is required only later for high-order real-power Nemytskii estimates containing negative powers such as `U^{γ-2}`.
- The two implementation red flags are: do not assume `z₊` is an AC test before proving the Stampacchia chain rule, and do not omit `-χ₀gₓ` from the barrier's zero-order coefficient.