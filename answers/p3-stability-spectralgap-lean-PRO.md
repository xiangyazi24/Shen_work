# Paper 3 Theorem 2.2: spectral-gap brick for Lean

## Executive verdict

There are two related, but distinct, spectral-gap statements.

1. **Parabolic-elliptic / slaved chemical reduction.**  If the chemical variable is eliminated by

       -d2 v_xx + mu v = nu u^gamma,

   then the perturbation of u has a scalar mode eigenvalue

       sigma_k = -(d1*lambda_k + alpha*a)
                 + chi*nu*gamma*(u*)^gamma * lambda_k/(mu + d2*lambda_k).

   This is the formula in the question.

2. **Parabolic-parabolic chemical.**  If the system is genuinely

       v_t = d2 v_xx + nu u^gamma - mu v,

   then the linearized k-th mode is a 2 by 2 matrix.  The same scalar expression is not itself an eigenvalue.  Instead, it is the Schur/slow-manifold expression whose zero corresponds to the determinant threshold.  The stability threshold is the same determinant condition, but the actual semigroup spectral-gap proof needs a matrix-eigenvalue lemma.

For the first Lean brick, the cleanest self-contained theorem is the **safe scalar gap**:

    lambda/(mu+d2*lambda) <= 1/d2

implies

    sigma_k <= -eta_safe

whenever

    eta_safe = alpha*a - chi*nu*gamma*(u*)^gamma/d2 > 0.

Equivalently,

    chi < alpha*a*d2 / (nu*gamma*(u*)^gamma).

This is a correct and very Lean-friendly sufficient condition.  It is **not** the sharp paper critical sensitivity in general.  The sharp threshold is the infimum over nonzero modes:

    chi* = inf_{k >= 1}
      ((d1*lambda_k + alpha*a)*(mu+d2*lambda_k))
        /(nu*gamma*(u*)^gamma*lambda_k).

The safe threshold

    alpha*a*d2/(nu*gamma*(u*)^gamma)

is a lower bound for the sharp threshold, obtained by throwing away the stabilizing `d1*lambda_k` and bounding `lambda/(mu+d2*lambda)` by `1/d2`.

So: formalize the safe gap first if you want a quick first brick.  Formalize the sharp gap later by finite-tail plus finite-min arguments.

## 1. Linearization

Let

    u = u* + p,
    v = v* + q,

where

    u* = (a/b)^(1/alpha),
    v* = (nu/mu)*(u*)^gamma.

The logistic derivative is

    d/du [u(a-bu^alpha)] at u=u*
      = a - b*(1+alpha)*(u*)^alpha
      = -alpha*a,

because `b*(u*)^alpha = a`.

Since `v*` is constant, `v*_x = 0`.  Therefore

    -chi*d_x(u v_x)

linearizes as

    -chi*d_x(u* q_x) = -chi*u* q_xx.

For the parabolic-parabolic chemical equation,

    q_t = d2 q_xx + nu*gamma*(u*)^(gamma-1)*p - mu*q.

On the Neumann cosine mode with eigenvalue

    lambda_k = (k*pi/L)^2,

we get

    p_k' = -(d1*lambda_k + alpha*a)*p_k + chi*u*lambda_k*q_k,
    q_k' =  nu*gamma*(u*)^(gamma-1)*p_k - (d2*lambda_k + mu)*q_k.

Thus the 2 by 2 matrix is

    A_k = [ -(d1*lambda_k + alpha*a)       chi*u*lambda_k              ]
          [  nu*gamma*(u*)^(gamma-1)      -(d2*lambda_k + mu)          ].

The trace is strictly negative:

    tr A_k = -((d1+d2)*lambda_k + alpha*a + mu).

The determinant is

    det A_k
      = (d1*lambda_k + alpha*a)*(d2*lambda_k + mu)
        - chi*nu*gamma*(u*)^gamma*lambda_k.

So the parabolic-parabolic linear mode is stable iff this determinant is positive.  The threshold is exactly

    chi_k = ((d1*lambda_k + alpha*a)*(d2*lambda_k + mu))
              /(nu*gamma*(u*)^gamma*lambda_k)

for k >= 1.

For the parabolic-elliptic or slaved chemical reduction,

    (mu+d2*lambda_k)*q_k = nu*gamma*(u*)^(gamma-1)*p_k,

hence

    q_k = nu*gamma*(u*)^(gamma-1)/(mu+d2*lambda_k) * p_k.

Substituting into the p equation gives the scalar eigenvalue

    sigma_k = -(d1*lambda_k + alpha*a)
              + chi*nu*gamma*(u*)^gamma*lambda_k/(mu+d2*lambda_k).

For k = 0, the chemotaxis term vanishes and

    sigma_0 = -alpha*a.

## 2. Sharp threshold versus safe threshold

For the scalar parabolic-elliptic eigenvalue, define the exact nonzero-mode threshold

    chi_k = ((d1*lambda_k + alpha*a)*(mu+d2*lambda_k))
              /(nu*gamma*(u*)^gamma*lambda_k),       k >= 1.

Then

    sigma_k < 0  iff  chi < chi_k.

The sharp critical sensitivity is

    chiStar = inf_{k >= 1} chi_k.

This is the faithful paper-style threshold.

The simple bound suggested in the question is:

    lambda/(mu+d2*lambda) <= 1/d2.

Therefore, if

    S = nu*gamma*(u*)^gamma,

then

    sigma_k
      = -(d1*lambda_k + alpha*a) + chi*S*lambda_k/(mu+d2*lambda_k)
      <= -(d1*lambda_k + alpha*a) + chi*S/d2
      = -d1*lambda_k - (alpha*a - chi*S/d2).

So, if

    etaSafe = alpha*a - chi*S/d2 > 0,

then

    sigma_k <= -etaSafe

for every k, assuming chi >= 0.  If chi is allowed to be negative, use

    eta = min(alpha*a, etaSafe)

to include the k=0 mode safely.

The safe condition is

    chi < alpha*a*d2/S

that is,

    chi < alpha*a*d2/(nu*gamma*(u*)^gamma).

This is a **sufficient** stability condition.  It is generally not the exact `chiStar`, because the exact threshold includes the stabilizing factor `d1*lambda_k`.

Indeed,

    chi_k
      = ((d1*lambda_k + alpha*a)*(mu+d2*lambda_k))/(S*lambda_k)
      >= alpha*a*d2/S.

Thus

    chiSafe <= chiStar.

## 3. Uniform gap under the sharp threshold

If you want the full theorem under

    chi < chiStar,

then the proof is slightly longer but still elementary.

Define the positive decay rate

    a_k = -sigma_k
        = d1*lambda_k + alpha*a - chi*S*lambda_k/(mu+d2*lambda_k).

Under `chi < chiStar`, all nonzero `a_k` are positive.  To prove a uniform positive lower bound:

1. Use the tail estimate

       a_k >= d1*lambda_k + alpha*a - chi*S/d2.

   This tends to infinity as `lambda_k -> infinity`.  Therefore choose K so that for all k >= K,

       a_k >= 1

   or any convenient positive tail bound.

2. On the finite set `1 <= k < K`, each `a_k > 0`.  Take the finite minimum.

3. Include the zero mode with value `alpha*a`.

Then

    eta = min(alpha*a, 1, finite_min_{1 <= k < K} a_k) > 0

satisfies

    sigma_k <= -eta

for all k.

This is the sharp route.  It requires more finite-set bookkeeping and a lemma that the Neumann eigenvalues tend to infinity.  For the first Lean brick, the safe threshold is much simpler.

## 4. Lean definitions for the safe scalar brick

Use ASCII names in Lean even if paper notation uses Greek.

```lean
noncomputable def lambdaInterval (L : R) (k : Nat) : R :=
  ((k : R) * Real.pi / L)^2

noncomputable def sigmaScalar
    (d1 d2 mu chi nu gamma uStar alpha a lambda : R) : R :=
  -(d1 * lambda + alpha * a)
    + chi * nu * gamma * (uStar ^ gamma) * lambda / (mu + d2 * lambda)

noncomputable def chiSafe
    (d2 nu gamma uStar alpha a : R) : R :=
  alpha * a * d2 / (nu * gamma * (uStar ^ gamma))

noncomputable def etaSafe
    (d2 chi nu gamma uStar alpha a : R) : R :=
  alpha * a - chi * nu * gamma * (uStar ^ gamma) / d2
```

If real powers require explicit `Real.rpow`, replace `uStar ^ gamma` by `uStar ^ gamma` as used elsewhere in the repo, or by the precise local notation for `Real.rpow`.

## 5. Key scalar fraction lemma

The core bound is:

```lean
theorem lambda_div_mu_add_d2lambda_le_inv_d2
    {mu d2 lambda : R}
    (hmu : 0 < mu) (hd2 : 0 < d2) (hlam : 0 <= lambda) :
    lambda / (mu + d2 * lambda) <= 1 / d2 := by
  have hden : 0 < mu + d2 * lambda := by
    nlinarith [hmu, hd2, hlam]
  rw [div_le_div_iff₀ hden hd2]
  nlinarith [hmu, hd2, hlam]
```

Depending on imports, the theorem name is usually:

    div_le_div_iff₀

If it does not resolve, use the equivalent manual route:

```lean
have hden : 0 < mu + d2 * lambda := by nlinarith [hmu, hd2, hlam]
have hmul : lambda * d2 <= mu + d2 * lambda := by nlinarith [hmu]
have := (div_le_iff₀ hden).2 ?_
```

but `div_le_div_iff₀` is the cleanest.

## 6. Safe uniform sigma gap lemma

A good first Lean theorem is:

```lean
theorem sigmaScalar_le_neg_etaSafe
    {d1 d2 mu chi nu gamma uStar alpha a lambda : R}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hmu : 0 < mu)
    (hchi_nonneg : 0 <= chi)
    (hnu : 0 < nu) (hgamma : 0 < gamma)
    (huStar : 0 < uStar)
    (halpha : 0 < alpha) (ha : 0 < a)
    (hlam : 0 <= lambda) :
    sigmaScalar d1 d2 mu chi nu gamma uStar alpha a lambda
      <= - etaSafe d2 chi nu gamma uStar alpha a := by
  let S : R := nu * gamma * (uStar ^ gamma)
  have hS_nonneg : 0 <= S := by
    dsimp [S]
    positivity
  have hfrac : lambda / (mu + d2 * lambda) <= 1 / d2 :=
    lambda_div_mu_add_d2lambda_le_inv_d2 hmu hd2 hlam
  have hchem :
      chi * S * (lambda / (mu + d2 * lambda)) <= chi * S * (1 / d2) := by
    exact mul_le_mul_of_nonneg_left hfrac (mul_nonneg hchi_nonneg hS_nonneg)
  unfold sigmaScalar etaSafe
  dsimp [S] at hchem
  -- The remaining goal is linear arithmetic plus d1*lambda >= 0.
  have hd1lam : 0 <= d1 * lambda := mul_nonneg hd1.le hlam
  nlinarith [hchem, hd1lam]
```

The exact algebra may require normalizing multiplication associativity with `ring_nf` or `ring_nf at hchem`.  If `nlinarith` struggles with divisions, first rewrite

    chi*S*(1/d2) = chi*S/d2

by `ring` or `field_simp [ne_of_gt hd2]`.

## 7. Positivity of etaSafe from chi < chiSafe

```lean
theorem etaSafe_pos_of_chi_lt_chiSafe
    {d2 chi nu gamma uStar alpha a : R}
    (hd2 : 0 < d2)
    (hnu : 0 < nu) (hgamma : 0 < gamma)
    (huStar : 0 < uStar)
    (halpha : 0 < alpha) (ha : 0 < a)
    (hchi : chi < chiSafe d2 nu gamma uStar alpha a) :
    0 < etaSafe d2 chi nu gamma uStar alpha a := by
  let S : R := nu * gamma * (uStar ^ gamma)
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  unfold chiSafe etaSafe at hchi ⊢
  dsimp [S] at hchi
  -- hchi : chi < alpha*a*d2 / S
  have hmul : chi * S < alpha * a * d2 := by
    exact (lt_div_iff₀ hS_pos).mp hchi
  have hdiv : chi * S / d2 < alpha * a := by
    exact (div_lt_iff₀ hd2).2 (by
      nlinarith [hmul])
  nlinarith [hdiv]
```

Again, depending on how powers are represented, `positivity` may or may not solve `0 < uStar ^ gamma`.  If not, use the explicit lemma:

```lean
have huPow : 0 < uStar ^ gamma := Real.rpow_pos_of_pos huStar gamma
```

and build `hS_pos` manually.

## 8. Full safe gap theorem over all modes

For `[0,L]`, assume `0 < L`.  Then

```lean
theorem sigmaScalar_mode_le_neg_etaSafe
    {L d1 d2 mu chi nu gamma uStar alpha a : R}
    (hL : 0 < L)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hmu : 0 < mu)
    (hchi_nonneg : 0 <= chi)
    (hnu : 0 < nu) (hgamma : 0 < gamma)
    (huStar : 0 < uStar)
    (halpha : 0 < alpha) (ha : 0 < a)
    (hchi : chi < chiSafe d2 nu gamma uStar alpha a) :
    exists eta : R, 0 < eta and
      forall k : Nat,
        sigmaScalar d1 d2 mu chi nu gamma uStar alpha a
          (lambdaInterval L k) <= -eta := by
  refine ⟨etaSafe d2 chi nu gamma uStar alpha a, ?_, ?_⟩
  · exact etaSafe_pos_of_chi_lt_chiSafe hd2 hnu hgamma huStar halpha ha hchi
  · intro k
    have hlam : 0 <= lambdaInterval L k := by
      unfold lambdaInterval
      positivity
    exact sigmaScalar_le_neg_etaSafe
      hd1 hd2 hmu hchi_nonneg hnu hgamma huStar halpha ha hlam
```

This is the simplest first brick.

If you want to avoid assuming `0 <= chi`, use

    eta = min (alpha*a) (etaSafe ...)

and prove both terms are positive.  But for chemotaxis sensitivity in Theorem 2.2, `chi >= 0` is normally the intended regime, so the simpler version is fine.

## 9. Sharp-threshold Lean shape for later

Define:

```lean
noncomputable def sigmaCriticalChiScalar
    (d1 d2 mu nu gamma uStar alpha a lambda : R) : R :=
  ((d1 * lambda + alpha * a) * (mu + d2 * lambda)) /
    (nu * gamma * (uStar ^ gamma) * lambda)

noncomputable def scalarCriticalSet
    (L d1 d2 mu nu gamma uStar alpha a : R) : Set R :=
  {c | exists k : Nat, k ≠ 0 and
    c = sigmaCriticalChiScalar d1 d2 mu nu gamma uStar alpha a
          (lambdaInterval L k)}

noncomputable def chiStarScalar
    (L d1 d2 mu nu gamma uStar alpha a : R) : R :=
  sInf (scalarCriticalSet L d1 d2 mu nu gamma uStar alpha a)
```

Then prove:

```lean
theorem safeThreshold_le_chiStarScalar :
  chiSafe d2 nu gamma uStar alpha a <=
    chiStarScalar L d1 d2 mu nu gamma uStar alpha a
```

by showing `chiSafe <= chi_k` for each nonzero k:

```lean
chiSafe = alpha*a*d2/S
       <= ((d1*lambda + alpha*a)*(mu+d2*lambda))/(S*lambda)
```

using `lambda > 0`, `d1*lambda >= 0`, and `mu > 0`.

For the full sharp gap under `chi < chiStarScalar`, do not try to get an explicit eta from sInf immediately.  Use:

1. `chi < chiStarScalar` implies `chi < chi_k` for all k, after proving the sInf is a lower bound of the threshold set.
2. Tail lower bound:

       a_k >= d1*lambda_k + alpha*a - chi*S/d2.

3. Since `lambda_k -> infinity`, choose K with tail bound `>= 1`.
4. Take a finite minimum over `Finset.range K` excluding k=0, plus the zero mode.

This is more bookkeeping but gives the exact paper condition.

## 10. Final recommendation

First formalize the safe brick:

    chi < alpha*a*d2/(nu*gamma*(u*)^gamma)
    -> exists eta > 0, forall k, sigma_k <= -eta.

It needs only:

    lambda >= 0,
    lambda/(mu+d2*lambda) <= 1/d2,
    elementary real arithmetic.

Then later formalize the sharp `chiStar` theorem.  Do not call the safe threshold the paper critical sensitivity.  It is a sufficient subcritical condition and a very good first Lean milestone.
