ANSWER Q4586 d4109b14

# Verdict: the proposed route is not Paper 3 Theorem 2.3, and the claimed “single Parseval leaf” is not the right leaf

There are three separate thresholds/routes being conflated.

1. **Paper 3 Theorem 2.3** is the **negative-sensitivity** theorem. Its hypothesis is
   `χ₀ ≤ 0` (with `m ≥ 1`), not `0 < χ₀ < chiBeta`. The paper’s Section 6 proof uses the upper-envelope maximum principle, time-translate compactness, persistence, and an ODE argument for the mass. It does not use the relative entropy proposed in the question.
2. `chiBeta` is the Paper 2 boundedness/global-existence threshold
   ```lean
   def ShenWork.Paper2.chiBeta (p : CM2Params) : ℝ :=
     2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))
   ```
   so on the one-dimensional interval it is
   ```text
   chiBeta = 2(2β-1) / max{2,γ}.
   ```
   It is not the entropy-dissipation threshold for the positive equilibrium.
3. The entropy proof in the paper is part of **Paper 3 Theorem 2.4(i)**. It uses the repo’s
   `chemotaxisEntropyDensity`, and for `m = 1` that density is
   ```text
   h₁(s) = s - u* - u* log(s/u*),
   ```
   not
   ```text
   s log(s/u*) - (s-u*).
   ```
   The corresponding smallness threshold is `chiStrong1Formula`, not `chiBeta`.

The difference between the two entropy orientations is load-bearing:

```text
forward entropy: h''(u) = 1/u
  ⇒ Young remainder = ∫ u (1+v)^(-2β) |v_x|²;

paper/reverse entropy: h₁''(u) = u*/u²
  ⇒ Young remainder = ∫ (1+v)^(-2β) |v_x|².
```

The latter is exactly what the elliptic equation controls. The former introduces the extra factor `u`, and ordinary cosine Parseval does not remove it.

---

# 1. Exact identity for the entropy written in the question

Set

```text
S(v) := (1+v)^(-β),
H(t)  := ∫₀¹ [u log(u/u*) - (u-u*)] dx,
u*    := (a/b)^(1/α),
v*    := (ν/μ)(u*)^γ.
```

Assume `u>0`, sufficient classical regularity to differentiate under the integral, and the homogeneous Neumann conditions `u_x=v_x=0` at `x=0,1`. Since

```text
a = b (u*)^α
```

and

```text
d/ds [s log(s/u*)-(s-u*)] = log(s/u*),
```

the exact identity is

```text
H'(t)
  = - ∫₀¹ |u_x|²/u dx
    + χ₀ ∫₀¹ (1+v)^(-β) u_x v_x dx
    - b ∫₀¹ u log(u/u*) (u^α-(u*)^α) dx.          (1.1)
```

There is no additional factor in the cross term. The `u` in the chemotactic flux cancels the derivative `1/u` of `log u`.

## Derivation

Diffusion:

```text
∫ log(u/u*) u_xx
  = [log(u/u*)u_x]₀¹ - ∫ (u_x/u)u_x
  = -∫ |u_x|²/u.
```

Chemotaxis:

```text
-χ₀ ∫ log(u/u*) ∂ₓ(u S(v) v_x)
  = χ₀ ∫ (u_x/u) u S(v) v_x
  = χ₀ ∫ S(v)u_xv_x.
```

Reaction:

```text
∫ log(u/u*) u(a-bu^α)
  = -b ∫ u log(u/u*) (u^α-(u*)^α).
```

The last integrand is nonnegative because both
`log(s/u*)` and `s^α-(u*)^α` have the sign of `s-u*`.

## Equivalent identity after inserting the elliptic equation

The elliptic equation gives

```text
v_xx = μv - νu^γ.
```

Since `v_x=0` at both endpoints,

```text
∫ S(v)u_xv_x
 = -∫ u ∂ₓ(S(v)v_x)
 = -μ∫ uvS(v)
   +ν∫ u^(γ+1)S(v)
   +β∫ u(1+v)^(-β-1)|v_x|².                    (1.2)
```

Thus (1.1) is equivalently

```text
H'(t)
 = -∫ |u_x|²/u
   +χ₀ν∫ u^(γ+1)(1+v)^(-β)
   -χ₀μ∫ uv(1+v)^(-β)
   +χ₀β∫ u(1+v)^(-β-1)|v_x|²
   -b∫ u log(u/u*)(u^α-(u*)^α).                 (1.3)
```

Identity (1.3) does not yield `chiBeta` either; for positive `χ₀` its terms do not have a uniform favorable sign.

## Lean-shaped identity

A useful new statement is:

```lean
def boltzmannEntropyDensity (uStar s : ℝ) : ℝ :=
  s * Real.log (s / uStar) - (s - uStar)

def intervalBoltzmannEntropy
    (uStar : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => boltzmannEntropyDensity uStar (u t x))

def intervalFisher
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => (intervalDomain.gradNorm (u t) x)^2 / u t x)

def intervalBoltzmannLogisticDissipation
    (uStar alpha : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => u t x * Real.log (u t x / uStar) *
      ((u t x)^alpha - uStar^alpha))

/-- New PDE-calculus leaf: differentiation under the integral plus the two
Neumann integration-by-parts identities. -/
theorem intervalBoltzmannEntropy_hasDerivAt
    (huStar : 0 < uStar)
    (heq : p.a = p.b * uStar ^ p.α)
    (hm : p.m = 1)
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (intervalBoltzmannEntropy uStar u)
      (- intervalFisher u t
       + p.χ₀ * intervalDomain.integral
          (fun x => (1 + v t x)^(-p.β) *
            intervalDomain.spatialDeriv (u t) x *
            intervalDomain.spatialDeriv (v t) x)
       - p.b * intervalBoltzmannLogisticDissipation
          uStar p.α u t)
      t
```

The identifiers `spatialDeriv` above are schematic: in the current interval API the final implementation should use `intervalDomainLift`, `deriv`, and the existing `gradNorm`/classical-regularity bridges. The mathematical target is exact.

---

# 2. Weighted Young and the threshold it actually gives

Let

```text
A(t) := ∫ |u_x|²/u,
E(t) := ∫ u(1+v)^(-2β)|v_x|²,
L(t) := ∫ u log(u/u*)(u^α-(u*)^α).
```

The correct pointwise Young inequality is

```text
|χ₀ u_x(1+v)^(-β)v_x|
 ≤ |u_x|²/(2u)
   + χ₀² u(1+v)^(-2β)|v_x|²/2.
```

If Young is written as

```text
|AB| ≤ A²/(2w) + wB²/2,
```

the choice is `w=u`, not `w=1/u`. Equivalently use

```text
A = u_x/sqrt(u),
B = χ₀ sqrt(u)(1+v)^(-β)v_x.
```

Consequently

```text
H'(t) ≤ -A(t)/2 + χ₀² E(t)/2 - bL(t).           (2.1)
```

This calculation alone has **no `chiBeta` threshold**. To close it one would need a genuinely new estimate of the form

```text
E(t) ≤ C_F A(t) + C_L L(t).                     (2.2)
```

Then (2.1) would give

```text
H'(t)
 ≤ -(1-χ₀²C_F)A(t)/2
   -(b-χ₀²C_L/2)L(t),
```

and the sufficient smallness condition would be

```text
χ₀² C_F < 1,
χ₀² C_L < 2b.                                   (2.3)
```

No existing repo lemma identifies constants in (2.2) that turn (2.3) into
`χ₀ < chiBeta p`. In fact, `chiBeta` does not involve `a`, `b`, `μ`, `ν`, or `u*`, whereas any equilibrium entropy absorption through the logistic term necessarily contains those parameters. That mismatch is a decisive warning that the claimed threshold is from a different theorem.

## Correct combined condition if boundedness is also needed

For a positive-sensitivity theorem starting from initial data, the two logically separate gates are:

```text
χ₀ < chiBeta p
```

for the Paper 2 boundedness/global-existence branch, and

```text
χ₀ < chiStrong1Formula p u* v*
```

for the Paper 3 entropy stability branch described below. Thus the direct combined hypothesis is

```text
0 < χ₀ < min (chiBeta p) (chiStrong1Formula p u* v*),
2γ ≤ α+1,
m = 1,
a,b > 0.
```

For actual Paper 3 Theorem 2.3, the sensitivity hypothesis is instead simply

```text
χ₀ ≤ 0,
```

with no smallness bound.

---

# 3. The paper-correct entropy and exact stability threshold

The repo already defines

```lean
chemotaxisEntropyIntegrand
chemotaxisEntropyDensity
chemotaxisEntropyFunctional
```

in `ShenWork/Paper3/LyapunovFunction.lean`, with

```text
h_m'(s) = 1 - (u*/s)^(2m-1).
```

For `m=1`,

```text
h₁(s) = s-u* - u*log(s/u*).
```

Set

```text
F(t) := ∫₀¹ [u-u* - u*log(u/u*)] dx,
D(t) := ∫₀¹ (u-u*)(u^α-(u*)^α) dx.
```

The exact derivative identity is

```text
F'(t)
 = -u* ∫ |u_x|²/u²
   +χ₀u* ∫ u_xv_x/[u(1+v)^β]
   -bD(t).                                       (3.1)
```

Applying `ab ≤ a²+b²/4` with

```text
a = sqrt(u*) u_x/u,
b = χ₀ sqrt(u*) v_x/(1+v)^β
```

absorbs the whole diffusion term and yields

```text
F'(t)
 ≤ χ₀²u*/4 ∫ |v_x|²/(1+v)^(2β) - bD(t).         (3.2)
```

This is why the paper’s entropy orientation is the correct one: the Young remainder is unweighted in `u`.

## Exact weighted elliptic estimate

Define, exactly as in `ShenWork/Paper3/Statements.lean`,

```lean
def betaTilde (beta : ℝ) : ℝ :=
  positivePart (min 1 (2 * beta - 1))
```

and put

```text
q := betaTilde β,
w := v-v*,
f := u^γ-(u*)^γ.
```

Subtracting the equilibrium equation gives

```text
w_xx - μw + νf = 0,
w_x(0)=w_x(1)=0.
```

Multiply by `w/(1+v)^q` and integrate by parts. The exact identity is

```text
∫ [1+v-q(v-v*)]/(1+v)^(q+1) |v_x|²
 + μ∫ (v-v*)²/(1+v)^q
 = ν∫ (v-v*)(u^γ-(u*)^γ)/(1+v)^q.              (3.3)
```

Using

```text
νwf ≤ μw² + ν²f²/(4μ)
```

inside the common weight gives

```text
∫ [1+v-q(v-v*)]/(1+v)^(q+1) |v_x|²
 ≤ ν²/(4μ) ∫ (u^γ-(u*)^γ)²/(1+v)^q
 ≤ ν²/(4μ) ∫ (u^γ-(u*)^γ)².                    (3.4)
```

The definition of `q` gives the pointwise weight comparison

```text
[1+v-q(v-v*)]/(1+v)^(q+1)
 ≥ (1+qv*)/(1+v)^(2β).                          (3.5)
```

Therefore

```text
∫ |v_x|²/(1+v)^(2β)
 ≤ ν²/[4μ(1+qv*)] ∫ (u^γ-(u*)^γ)².             (3.6)
```

For the requested regime `β≥1`, the existing lemma

```lean
betaTilde_eq_one_of_one_le_beta
```

gives `q=1`, and (3.5) is particularly transparent:

```text
[1+v-(v-v*)]/(1+v)² = (1+v*)/(1+v)²
                    ≥ (1+v*)/(1+v)^(2β).
```

## Power-difference estimate

Under

```text
2γ ≤ α+1,
```

the scalar lemmas in `Statements.lean` involving
`power_difference_normalized_*` and `CAlphaGamma` give the scaled inequality

```text
(u^γ-(u*)^γ)²
 ≤ CAlphaGamma(α,γ) (u*)^(2γ-α-1)
     (u-u*)(u^α-(u*)^α).                        (3.7)
```

The repo’s constant is

```lean
def CAlphaGamma (alpha gamma : ℝ) : ℝ :=
  if alpha < 1 then
    (alpha + 1)^2 / (4 * alpha)
  else if gamma ≤ 1 then
    1
  else
    gamma^2 / (2 * gamma - 1)
```

Combining (3.2), (3.6), and (3.7) yields

```text
F'(t)
 ≤ -κ D(t),                                      (3.8)

κ := b -
  χ₀² ν² CAlphaGamma(α,γ) (u*)^(2γ-α)
    / [16 μ (1+betaTilde(β)v*)].
```

Thus the exact smallness condition for `m=1` is

```text
χ₀² <
  16 b μ (1+betaTilde(β)v*)
    / [ν² CAlphaGamma(α,γ) (u*)^(2γ-α)].        (3.9)
```

Equivalently,

```text
0 < χ₀ < chiStrong1Formula p u* v*,             (3.10)
```

where the repo definition is

```lean
def chiStrong1Formula (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  Real.sqrt
    (p.b *
      (16 * (1 + betaTilde p.β * vStar) * p.μ /
        ((2 * p.m - 1) * p.ν^2 * CAlphaGamma p.α p.γ *
          uStar^(2 * p.γ - p.α + 2 * p.m - 2))))
```

For `m=1` and `β≥1`, this simplifies to

```text
chiStrong1Formula
 = sqrt [16 b μ(1+v*) /
          (ν² CAlphaGamma(α,γ)(u*)^(2γ-α))].    (3.11)
```

This is the threshold used by the entropy route. `ThresholdOrdering.lean` supplies its comparison with the spectral critical sensitivity needed to enter the local exponential-stability theorem.

---

# 4. The Parseval leaf: what is true, and why it does not prove the requested weighted inequality

There is a clean cosine-mode lemma, but it is an **unweighted** resolvent estimate.

Use the orthonormal Neumann basis

```text
e₀(x)=1,
e_n(x)=sqrt(2) cos(nπx),
λ_n=n²π².
```

For

```text
f = u^γ-(u*)^γ,
w = v-v*,
```

the coefficient equation is

```text
(μ+λ_n) ŵ_n = ν f̂_n.
```

Hence Parseval gives the exact identity

```text
∫₀¹ |v_x|² dx
 = ν² Σ_{n≥1} [λ_n/(μ+λ_n)²] |f̂_n|².          (4.1)
```

Define the exact unit-interval modal constant

```text
Cres(μ) := sup_{n≥1} λ_n/(μ+λ_n)².
```

Then

```text
∫ |v_x|²
 ≤ ν² Cres(μ) ∫ |f-mean(f)|²
 ≤ ν² Cres(μ) ∫ |f|².                           (4.2)
```

The scalar inequality

```text
λ/(μ+λ)² ≤ 1/(4μ)
```

is equivalent to `(λ-μ)²≥0`, so

```text
Cres(μ) ≤ 1/(4μ),
```

and therefore

```text
∫ |v_x|² ≤ ν²/(4μ) ∫ (u^γ-(u*)^γ)².            (4.3)
```

A second, Poincaré-style bound is

```text
λ_n/(μ+λ_n)² ≤ 1/(μ+π²),
```

so one may use

```text
Cres(μ) ≤ min {1/(4μ), 1/(μ+π²)}.
```

## Repo machinery for (4.1)

The relevant existing pieces are:

```lean
ShenWork.Paper3.unitIntervalNeumannSpectrum
ShenWork.PDE.intervalNeumannResolverSourceCoeff
ShenWork.PDE.intervalNeumannResolverCoeff
ShenWork.PDE.intervalNeumannResolverCoeff_elliptic
```

in `Statements.lean` and `IntervalNeumannEllipticResolverR.lean`, together with the cosine Parseval infrastructure in `CosineParsevalBridge.lean` and `HeatKernelGradientEstimates.lean`.

A useful exact new endpoint theorem is:

```lean
theorem intervalNeumannResolver_grad_sq_le_source_sq
    {mu nu : ℝ} (hmu : 0 < mu)
    {f w : ℝ → ℝ}
    (hell : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      -deriv (deriv w) x + mu * w x = nu * f x)
    (hN0 : deriv w 0 = 0) (hN1 : deriv w 1 = 0)
    (hreg : /* L² + cosine reconstruction/Parseval hypotheses */) :
    ∫ x in (0 : ℝ)..1, (deriv w x)^2 ≤
      nu^2 / (4 * mu) * ∫ x in (0 : ℝ)..1, (f x)^2
```

Its proof DAG is mechanical:

```text
coefficient elliptic identity
→ derivative Parseval
→ λ/(μ+λ)² ≤ 1/(4μ)
→ source Parseval.
```

## Why Parseval does not give the requested estimate

The term from the forward entropy is

```text
E = ∫ m(x)|v_x|²,
m(x)=u(x)(1+v(x))^(-2β).
```

In coefficient space this is

```text
⟨M_m v_x, v_x⟩,
```

where `M_m` is multiplication by the nonconstant function `m`. Its matrix has entries

```text
∫₀¹ m(x) sin(nπx) sin(kπx) dx,
```

so it is not diagonal. The equality (4.1) therefore cannot be inserted under this weight.

Parseval gives only the conditional corollary

```text
m(x) ≤ M for all x
⇒ E ≤ M ν²/(4μ) ∫(u^γ-(u*)^γ)².                (4.4)
```

That requires an `L∞` bound on `u(1+v)^(-2β)`. If the goal is to obtain boundedness, this is circular. If global boundedness is already assumed, (4.4) is valid but its constant depends on that particular bound and does not yield the paper’s parameter-only stability threshold.

Therefore the requested statement

```text
∫ u(1+v)^(-2β)|v_x|²
 ≤ C(μ,ν,γ,u*) × [existing dissipation]
```

is **not** a one-line consequence of the elliptic equation plus Parseval. It is an additional nonlinear multiplier theorem. No such parameter-only theorem is currently present in the repo, and the paper does not need it. The correct replacement is the weighted elliptic test (3.3)–(3.6), after changing to the paper entropy so that the prefactor `u` disappears.

---

# 5. LaSalle/compactness and the exact convergence conclusion

Assume the corrected dissipation estimate (3.8) with `κ>0`. Since `F≥0`,

```text
κ ∫₀ᵀ D(t) dt ≤ F(0)-F(T) ≤ F(0),
```

so

```text
∫₀^∞ D(t) dt < ∞.                               (5.1)
```

This does **not by itself** imply `D(t)→0`. One needs either uniform continuity of `D` and Barbalat’s lemma, or the time-translate compactness/LaSalle route.

## LaSalle route

Assume every sequence `t_n→∞` has a subsequence such that

```text
u(t_n+·,·) → u∞
v(t_n+·,·) → v∞
```

locally uniformly on bounded time intervals, with enough derivative convergence for the limit to remain an entire classical solution. From (5.1), for every finite interval `[A,B]`,

```text
∫_A^B D∞(s) ds = 0.
```

Continuity and nonnegativity imply `D∞(s)=0` for every `s`. Because `s↦s^α` is strictly increasing on `(0,∞)`,

```text
(u∞-u*)((u∞)^α-(u*)^α)=0
```

pointwise forces

```text
u∞ ≡ u*.
```

The elliptic equation then forces

```text
v∞ ≡ v*.
```

Thus the omega-limit set is the singleton `{(u*,v*)}`, and

```text
‖u(t)-u*‖_∞ → 0.                                (5.2)
```

In repo language, the exact `u` conclusion is

```lean
UniformConvergesInSup intervalDomain u uStar
```

which unfolds to

```lean
Tendsto
  (fun t => intervalDomain.supNorm (fun x => u t x - uStar))
  atTop (𝓝 0).
```

Continuity of the Neumann elliptic resolver gives, from (5.2),

```text
‖v(t)-v*‖_{C¹([0,1])} → 0.                      (5.3)
```

The current repo exposes the compactness/conversion pieces through names such as

```lean
TimeTranslateCompactnessConclusion
MomentConvergenceToUniformRaw
intervalDomain_momentToUniform_of_corollary51
```

and the assembly theorems in `IntervalDomainStabilityChain.lean`. The PDE derivative inequality remains an explicit frontier in `IntervalDomainEnergyDissipation.lean` and `LyapunovFunction.lean`.

## Eventual versus global exponential convergence

The entropy/LaSalle step yields asymptotic convergence, not an exponential rate. Once (5.2) places the orbit inside the local stability ball from Theorem 2.2/Corollary 5.1, there is a time `Tδ` such that

```text
‖u(t)-u*‖_{C¹} + ‖v(t)-v*‖_{C¹}
 ≤ Cδ exp[-λ(t-Tδ)]            for t ≥ Tδ.       (5.4)
```

For one fixed solution, enlarge the constant by `exp(λTδ)` and by the maximum on the compact initial slab `[0,Tδ]`; this rewrites (5.4) as

```lean
ExponentialC1Convergence intervalDomain N u v uStar vStar
```

with a bound for all `t≥0`.

The distinction is important:

- the **rate after entry** can come from the local spectral theorem;
- the **entry time** generally depends on the solution;
- extending the estimate back to `t=0` makes the prefactor solution-dependent unless a uniform entry-time/initial-slab estimate is proved.

`HARDBONE_TODO.md` correctly records this remaining quantifier gap: the current Corollary 5.1 path supplies per-solution exponential constants, whereas the paper-level theorem interface asks for constants uniform over the whole branch.

---

# 6. Dependency-ordered Lean build

## A. Mechanical scalar layer — already mostly present

```text
chemotaxisEntropyIntegrand
chemotaxisEntropyDensity
chemotaxisEntropyDensity_nonneg
chemotaxisEntropyDensity_hasDerivAt
betaTilde
betaTilde_eq_one_of_one_le_beta
CAlphaGamma
power_difference_normalized_*
chiStrong1Formula
```

Add the small closed-form wrapper

```lean
theorem chemotaxisEntropyDensity_one_eq
    (huStar : 0 < uStar) (hs : 0 < s) :
    chemotaxisEntropyDensity 1 uStar s =
      s - uStar - uStar * Real.log (s / uStar)
```

and a scaled `CAlphaGamma` wrapper for (3.7).

## B. First genuine PDE leaf — entropy derivative identity

```lean
theorem intervalDomain_paperEntropy_m1_hasDerivAt
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hm : p.m = 1)
    (heq : p.a = p.b * uStar ^ p.α)
    (huStar : 0 < uStar)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun tau => chemotaxisEntropyFunctional intervalDomain 1 uStar u tau)
      (-uStar * ∫ |u_x|²/u²
       +p.χ₀*uStar * ∫ u_x*v_x/(u*(1+v)^p.β)
       -p.b * ∫ (u-uStar)*(u^p.α-uStar^p.α))
      t
```

This is not yet in the repo. It needs differentiation under the interval integral, chain rules for `log`/real powers on the positive range, and two Neumann integrations by parts.

## C. Second genuine PDE leaf — weighted elliptic estimate

```lean
theorem intervalDomain_weightedSignalGradient_le_powerDifference
    (hmu : 0 < p.μ) (hnu : 0 < p.ν)
    (hbeta : 0 ≤ p.β)
    (huStar : 0 < uStar)
    (hvStar : vStar = p.ν / p.μ * uStar ^ p.γ)
    (helliptic : /* v_xx-μv+νu^γ=0 + Neumann */)
    (hvnonneg : ∀ x, 0 ≤ v x) :
    ∫ |v_x|²/(1+v)^(2*p.β) ≤
      p.ν^2 /
        (4*p.μ*(1 + betaTilde p.β*vStar)) *
      ∫ (u^p.γ-uStar^p.γ)^2
```

Proof: exactly (3.3)–(3.6). This is the correct replacement for the proposed weighted Parseval statement.

## D. Mechanical assembly of dissipation

```lean
theorem intervalDomain_paperEntropySlope_le
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hidentity : /* B */)
    (helliptic : /* C */) :
    entropySlope t ≤
      -(p.b -
        p.χ₀^2 * p.ν^2 * CAlphaGamma p.α p.γ *
          uStar^(2*p.γ-p.α) /
          (16*p.μ*(1+betaTilde p.β*vStar))) *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t)
```

Then

```lean
(hchi : 0 < p.χ₀ ∧ p.χ₀ < chiStrong1Formula p uStar vStar)
```

produces a positive dissipation coefficient.

## E. Existing Lyapunov post-processing

Wire D into the existing packages in `LyapunovFunction.lean`, including

```text
intervalDomain_entropyFunctional_nonneg_antitone_of_positiveGlobalBoundedSolution
intervalDomain_entropyFunctional_lyapunovPackage_of_positiveGlobalBoundedSolution
```

The current versions accept the derivative/dissipation estimate explicitly, which is exactly the right acyclic interface.

## F. Compactness/rigidity

Prove or instantiate:

```lean
TimeTranslateCompactnessConclusion intervalDomain p K u v
```

and the rigidity statement

```lean
theorem thetaDissipation_eq_zero_iff_const
    (hu : ∀ x, 0 < u x)
    (hα : 0 < p.α) :
    chemotaxisThetaDissipation intervalDomain uStar p.α u = 0 ↔
      u = fun _ => uStar
```

Then obtain

```lean
UniformConvergesInSup intervalDomain u uStar.
```

## G. Local exponential upgrade

Use the comparison in `ThresholdOrdering.lean` showing the strong threshold is below the spectral critical sensitivity, then the local sectorial stability/Corollary 5.1 bridge to obtain eventual `C¹` exponential convergence. Rebase it to `t≥0` only after deciding whether the desired constants are per-solution or uniform over all solutions.

---

# Final answer to the four numbered questions

1. **Identity:** (1.1) is exact. The cross-term multiplier is exactly `1`. The elliptically expanded equivalent is (1.3).
2. **Absorption:** weighted Young gives (2.1). It does not produce `chiBeta`; it creates the difficult factor `u(1+v)^(-2β)`. For the paper entropy, the exact threshold is `chiStrong1Formula`, equations (3.9)–(3.11).
3. **“Missing Parseval leaf”:** the true Parseval lemma is the unweighted estimate (4.1)–(4.3), and it is mechanically formalizable from existing cosine-resolver machinery. It does not imply the requested weighted estimate because multiplication by `u(1+v)^(-2β)` couples the modes. The correct PDE leaf is the weighted elliptic test (3.3)–(3.6), after switching to the repo’s entropy.
4. **Convergence:** dissipation plus time-translate compactness and zero-dissipation rigidity gives `UniformConvergesInSup` for `u`, then elliptic continuity gives `C¹` convergence of `v`. Exponential `C¹` convergence is naturally eventual; extending it to all `t≥0` changes the prefactor and exposes the current per-solution-versus-uniform-constant gap.

So the honest build is **not** “three scalar lemmas + one Parseval leaf.” It is two genuine PDE leaves—entropy production and the weighted elliptic test—followed by already-designed Lyapunov/compactness wiring. For actual Paper 3 Theorem 2.3, use the separate `χ₀≤0` maximum-principle/compactness route instead.