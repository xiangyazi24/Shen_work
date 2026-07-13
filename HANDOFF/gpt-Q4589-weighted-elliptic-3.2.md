ANSWER Q4589 c38d07fb

# Verdict

There are two distinct weighted elliptic mechanisms, and keeping them separate is the key fidelity point.

1. The signal-weighted gradient estimate

holds for every q>1 and every \eta\ge0. In the paper this is Proposition 2.2, with

On the interval there is an even cleaner direct proof with the explicit constant

There is no additional admissible-range condition relating q to \eta: q>1 and \eta\ge0 suffice.

1. The critical factor 2\beta-1 and the upper seed restriction

do not arise from Proposition 2.2 itself. They arise from a separate test of the elliptic equation by

because differentiating (1+v)^{-(2\beta-1)} produces exactly

Proposition 2.2 is used afterward, in the all-p bootstrap leg, with its parameter \eta specialized to 2\beta-1. The paper makes exactly this substitution in (4.12).

For the repository: Statements.lean defines

```javascript
def chiBeta (p : CM2Params) : ℝ :=
  2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))
```

and IntervalDomainTheorem12.lean still exposes the critical seed as the explicit hcriticalBootstrap frontier. The lemmas below are the mathematical producer needed to inhabit that field.

# 1. The signal-weighted resolver estimate

Write

Assume v\in C^2([0,1]), v_x(0)=v_x(1)=0, and

## 1.1 Exact one-dimensional multiplier

Use the total derivative

For q>1, the scalar map z\mapsto |z|^{2q-2}z is C^1 and

including at z=0. Hence

The Neumann conditions give F(0)=F(1)=0, so integration yields the exact identity

Now factor

because 1-r+r(q-1)/q=-\eta. Hölder therefore gives

If I_{\eta,q}=0 there is nothing to prove; otherwise divide by

I_{\eta,q}^{(q-1)/q}:

Since y\ge1 and \eta\ge0,

## 1.2 Resolver L^q contraction

The Neumann resolvent is an L^q contraction up to \nu/\mu:

One proof tests the elliptic equation by v^{q-1}; if v may vanish, first use (v+\varepsilon)^{q-1} and let \varepsilon\downarrow0. The resulting inequality is

which gives (2).

Using v_{xx}=\mu v-\nu u^\gamma,

Combining (1) and (3) gives the explicit interval estimate

This is rigorous for every q>1 and \eta\ge0. It uses only u,v\ge0, not a positive floor.

## 1.3 Paper-faithful constant and \Theta_\eta

The paper first proves

and then uses the sharp scalar maximum

(with the continuous value \Theta_0=1) to obtain

Thus the exact paper form is

For Lean on u\ge0, the direct (1+v) multiplier is cleaner because it avoids dividing by v and avoids a separate strict-positivity proof for the resolver.

# 2. How the critical coefficient 2\beta-1 enters the u^p energy

Assume now m=1, \chi_0>0, \beta\ge1, and set

Testing the parabolic equation by u^{p-1} gives

Young gives

## 2.1 Threshold-producing elliptic identity

Put

Multiply v_{xx}-\mu v+\nu u^\gamma=0 by

u^p(1+v)^{-\eta} and integrate. One Neumann integration by parts gives

Since \eta+1=2\beta, the exact identity is

This is the precise location where 2\beta-1 is born: it is the derivative coefficient of the weight (1+v)^{-(2\beta-1)}.

Drop the last, nonpositive term on the right of (6). Applying Young to the first term and using

gives

The coefficient of J_p in (5) can be absorbed through (7) exactly when

which is equivalent to

This is the seed upper bound. It is not an admissibility condition for (\star).

For a completely explicit positive leftover gradient coefficient, any

works after possibly decreasing it to be <1. Consequently there is

A_p\ge0 such that

# 3. How (\star) supplies the all-p cross-diffusion estimate

This is a separate second step, valid for every p>1.

Young first gives, for any \varepsilon>0,

Set

Young with conjugate exponents (p+\gamma)/p and (p+\gamma)/\gamma gives the exact estimate

Apply (\star) with its weight parameter specialized to

because (1+\eta)q=2\beta q, and note that

\gamma q=p+\gamma. Hence

Therefore

This is exactly CrossDiffusionBootstrapEstimate with

not 2\gamma. Thus Corollary 2.1 asks for a seed exponent

On the interval N=1, this is p_0>\max\{1,\gamma/2\}.

# 4. Closing the finite L^{p_0} seed

Choose

For \chi_0>0, this interval is nonempty exactly when

which is precisely chiBeta with N=1.

## 4.1 Exact one-dimensional GNS/Ehrling inequality

For every p>1, every \delta>0, and every positive C^1 function u on [0,1],

A very Lean-friendly direct interval proof avoids fractional L^r spaces. Let

For each x, choose a subinterval J_x\subset[0,1] of length h containing x. Some y\in J_x satisfies u(y)\le M/h. With w=u^{p/2},

Therefore

Integrating and using (p^2/2)h\le\delta proves (14), with the explicit choice

For merely nonnegative u, apply the argument to u+\varepsilon and pass to the limit.

## 4.2 Absorbing scalar ODE

Apply (14) to (9) with

Then

so

If M(t)\le\overline M on the time interval under consideration, Gronwall gives

and hence

This proves the finite-horizon seed required by LpPowerBoundedBefore.

## 4.3 Important finite-horizon versus global distinction

The seed only needs a mass bound on the finite branch:

- if b=0, then M(t)\le M(0)e^{at}, so on every fixed [0,T] one may take \overline M_T=M(0)e^{aT};

- if b>0, Jensen gives

- if a=b=0, mass is conserved.

A genuinely all-time absorbing L^{p_0} bound cannot follow under the bare subcase b=0<a: already at \chi_0=0, a spatially constant solution grows like e^{at}. Thus the mathematics above closes the finite-horizon hcriticalBootstrap. A separate long-time boundedness producer is needed for the all-time conclusion—exactly as IntervalDomainTheorem12.lean separates hcriticalBootstrap from hcriticalGlobalBound.

The logistic sink is helpful when b>0, but it is not the source of the critical threshold and is not needed for the finite seed.

# 5. Paste-ready Lean targets and dependency order

The clean implementation is six lemmas.

## L1. Resolver L^q contraction

```javascript
theorem interval_neumann_resolver_Lq_contraction
    {q μ ν γ : ℝ} {u v : ℝ → ℝ}
    (hq : 1 < q) (hμ : 0 < μ) (hν : 0 ≤ ν)
    (hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ u x)
    (hv : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ v x)
    (hreg : ContDiffOn ℝ 2 v (Set.Icc (0 : ℝ) 1))
    (hneumann : /* one-sided v' 0 = v' 1 = 0 */)
    (hode : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv v) x - μ * v x + ν * (u x) ^ γ = 0) :
    (∫ x in (0 : ℝ)..1, (v x) ^ q) ^ (1 / q) ≤
      (ν / μ) * (∫ x in (0 : ℝ)..1, (u x) ^ (γ * q)) ^ (1 / q)
```

A semigroup/resolvent-contraction proof is easier than formalizing the regularized test.

## L2. Signal-weighted gradient estimate

```javascript
theorem interval_signalWeighted_resolver_gradient
    {q η μ ν γ : ℝ} {u v : ℝ → ℝ}
    (hq : 1 < q) (hη : 0 ≤ η)
    (hμ : 0 < μ) (hν : 0 ≤ ν)
    /* nonnegativity, C², Neumann, resolver ODE */ :
    ∫ x in (0 : ℝ)..1,
        |deriv v x| ^ (2 * q) / (1 + v x) ^ ((1 + η) * q)
      ≤
    (2 * ν * (2 * q - 1) / ((1 + η) * q - 1)) ^ q *
      ∫ x in (0 : ℝ)..1, (u x) ^ (γ * q)
```

Internally isolate interval_weighted_kato_neumann_identity, namely (WIBP).

## L3. The threshold-producing elliptic weight identity

```javascript
theorem interval_mOne_elliptic_weight_identity
    {p η μ ν γ : ℝ} {u v : ℝ → ℝ}
    (hp : 1 < p) (hη : 0 ≤ η)
    /* regularity, positivity/nonnegativity, Neumann, resolver ODE */ :
    η * ∫ x in (0 : ℝ)..1,
          (u x) ^ p * (deriv v x) ^ 2 / (1 + v x) ^ (η + 1)
      =
    p * ∫ x in (0 : ℝ)..1,
          (u x) ^ (p - 1) * deriv u x * deriv v x / (1 + v x) ^ η
      + μ * ∫ x in (0 : ℝ)..1,
          (u x) ^ p * v x / (1 + v x) ^ η
      - ν * ∫ x in (0 : ℝ)..1,
          (u x) ^ (p + γ) / (1 + v x) ^ η
```

Instantiate with η := 2 * p.β - 1.

## L4. Critical seed differential inequality

```javascript
theorem interval_mOne_critical_seed_diffIneq
    {pExp : ℝ}
    (hβ : 1 ≤ params.β) (hχ : 0 < params.χ₀)
    (hp : 1 < pExp)
    (hpcrit : pExp * params.χ₀ < 2 * params.β - 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∃ eps > 0, ∃ A ≥ 0, ∀ t, 0 < t → t < T →
      (1 / pExp) * deriv
          (fun τ => intervalDomain.integral
            (fun x => (u τ x) ^ pExp)) t
        ≤ -eps * intervalDomainLpWeightedGradientDissipation pExp u t
          + A * intervalDomain.integral (fun x => (u t x) ^ pExp)
          - params.b * intervalDomain.integral
              (fun x => (u t x) ^ (pExp + params.α))
```

Reuse:

- intervalDomain_lp_timeLeibniz for d/dt\int u^p;

- intervalDomain_spatial_integrationByParts_identity for both the parabolic and elliptic tests;

- the general energy-balance scaffolding in IntervalDomainEnergyStep.

## L5. All-p cross-diffusion estimate with \rho=\gamma

```javascript
theorem interval_mOne_crossDiffusion_rho_gamma
    (hβ : 1 ≤ params.β)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    CrossDiffusionBootstrapEstimate intervalDomain params T params.γ u v
```

The proof is (10)–(12), calling L2 with

```javascript
q := (pExp + params.γ) / params.γ
η := 2 * params.β - 1
```

and no seed upper-bound hypothesis.

## L6. The finite critical seed

```javascript
theorem interval_mOne_critical_Lp_seed
    {p0 T : ℝ}
    (hT : 0 < T)
    (hp0low : max 1 (params.γ / 2) < p0)
    (hp0high : p0 * params.χ₀ < 2 * params.β - 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hmass : ∃ M, ∀ t, 0 < t → t < T →
      intervalDomain.integral (u t) ≤ M) :
    LpPowerBoundedBefore intervalDomain p0 T u
```

Then package the critical bootstrap as

```javascript
⟨params.γ, params.hγ,
  interval_mOne_crossDiffusion_rho_gamma hβ hsol,
  p0, hp0low, interval_mOne_critical_Lp_seed ...⟩
```

and feed it to Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy and the existing IntervalDomainTheorem12 assembly.

# 6. Hardest formalization leaf

The single hardest leaf is the real-power weighted Neumann integration-by-parts engine:

```javascript
x ↦ (1 + v x)^(1 - (1 + η) * q) *
      |v' x|^(2*q - 2) * v' x
```

with its endpoint trace zero and exact derivative. It should be isolated once, rather than reproved inside the estimate. The threshold-specific identity L3 is algebraically easier, but it is the load-bearing place where the factor 2\beta-1 is generated.

# Final dependency DAG

```plain text
Neumann resolver Lq contraction (L1)
        + weighted Kato/IBP identity
        └── signal-weighted gradient estimate (L2)

Lp time-Leibniz + parabolic Neumann IBP
        + elliptic u^p(1+v)^-(2β-1) identity (L3)
        └── critical seed differential inequality (L4)
                + interval GNS + finite-horizon mass bound
                └── LpPowerBoundedBefore p0 (L6)

L2 with η=2β-1, q=(p+γ)/γ
        └── CrossDiffusionBootstrapEstimate with ρ=γ (L5)

L5 + L6 + max{1,γ/2}<p0
        └── Corollary 2.1
        └── IntervalDomainTheorem12 critical hcriticalBootstrap
```

The decisive correction is therefore: build both weighted identities. Proposition 2.2 supplies the \rho=\gamma all-p bootstrap, while the separate elliptic test with weight (1+v)^{-(2\beta-1)} supplies the seed threshold.