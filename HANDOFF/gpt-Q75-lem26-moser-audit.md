ANSWER Q75 f3f7b5a4

# Paper 2 Lemma 2.6: audit of the seven Moser hypotheses

## Executive classification

For a positive classical solution of

on a fixed interval 0<t<T, the seven hypotheses fall into three groups.

The repository state supports this classification. IntervalDomainTierChain.lean exposes all seven assumptions explicitly. IntervalDomainEnergyStep.lean says that differentiation under the integral, interval integration by parts, and passage from the pointwise PDE to an integral identity remain analytic frontiers. The existing CODEX_SPEC_relativeMassGradient.md records that the mass-gradient interpolation is already proved from the interval Agmon inequality, while the chain-rule comparison and lower-order mass term are separate obligations.

There is also an important audit point:

The current abstract hdiss conclusion

0le frac1pfrac d{dt}int u^p+Bint u^p

does not follow merely from the usual upper energy inequality. It is an additional lower differential bound, and in general it can fail when \int u^p decays rapidly. Unless a separate argument proves it for the concrete solution, hdiss should not be described as a routine “drop” from the preceding upper inequality.

The conventional Moser route needs only the upper inequality

followed by interpolation and Young absorption. It normally does not require the extra sign assertion 0\le p^{-1}Y_p'+B_pY_p.

---

# 1. The routine hypotheses

## 1.1 hu_nonneg

For nonnegative initial data, the scalar parabolic maximum principle preserves u\ge0. In the present formal interface the solution is stronger: IsPaper2ClassicalSolution contains

Hence the required statement

is immediate by le_of_lt.

Mathematically, if one were deriving positivity rather than assuming it in the solution structure, test the equation by the negative part u_-:=\max\{-u,0\}. The reaction term vanishes at u=0, the flux has homogeneous Neumann boundary data, and the standard negative-part estimate gives

Since u_-(0)=0, Gronwall yields u_-=0.

## 1.2 hpow_int

Fix t\in(0,T). Classical regularity gives continuity of x\mapsto u(t,x) on compact [0,1], hence

For every finite exponent q>1,

and therefore

Thus hpow_int is a compactness/continuity consequence; it contains no Moser estimate.

## 1.3 hcGrad

Once one defines, for example,

positivity is immediate:

The added $+1$' is harmless and removes edge-case bookkeeping. If the bootstrap data already provide $U_T<\infty$, hcGrad` is purely algebraic.

---

# 2. Exact chain-rule comparison for hgrad

Let p>0, u>0, and put

Then pointwise on (0,1),

so

Consequently,

If

for all 0<t<T, then

Thus one may take

Two cautions matter for the Lean statement.

1. Formula (2.1) uses positivity when p/2-1<0. The current solution interface gives strict positivity, so this is legitimate at every point of the closed interval.

1. When \rho>0, hgrad is not just a chain rule. It also uses a uniform upper bound U_T. Classical regularity gives a bound on each compact strip [\tau,T']\times[0,1], but a bound uniform down to t=0 requires the initial trace/bounded-data theory or an explicit bootstrap hypothesis.

If the intended argument has no prior L^\infty control, then this particular hgrad formulation is circular for an L^\infty Moser proof. A noncircular formulation should instead use u^{(p+\rho)/2}:

and align the dissipative exponent accordingly.

---

# 3. Exact one-dimensional mass-gradient interpolation (hMG)

This is the standard one-dimensional Gagliardo--Nirenberg step. Let q>1, u\ge0, and set

Then

On [0,1], the one-dimensional GN inequality gives a constant C_{GN}(q) such that

where the interpolation exponent is determined by

Hence

Squaring (3.2), enlarging the constant, and using (3.1),

Since

Young's inequality with conjugate exponents

gives, for every \eta>0,

with

Taking

we obtain

This is the clean mass-gradient form needed by Moser iteration.

Using the chain rule,

so an equivalent weighted-gradient statement is

where

The constant C_q depends on q and on the fixed interval but not on t or u. For the unit interval there is no extra domain-volume factor.

### Lean-facing specialization

In the current hypothesis take

The only exponent side condition is

This should follow from the bootstrap assumptions $p\ge p_0$' and p_0>1' (or the stronger repository condition). The theorem already mentioned in the project, intervalDomain_classicalSolutionPositiveInterpolation, is intended to package exactly (3.5).

---

# 4. Logistic mass estimate (hmass)

Let

Integrate the PDE over [0,1]. The Neumann boundary conditions give

and

because v_x=0 at both endpoints. Therefore

Assume \theta>1. Since |[0,1]|=1, Jensen gives

Hence

Define

Whenever M>K_*, the right-hand side of (4.3) is negative. Scalar comparison therefore yields

For the usual logistic parameters a,b>0 this is simply

Now fix the Moser exponent p and interpolation constant C_\eta\ge0. Then

Thus hmass is discharged by

If the formal statement permits arbitrary real Ceta, use the safe nonnegative choice

and separately note that the inequality is trivial when C_\eta<0 because M^{p+\rho}\ge0.

### Borderline \theta=1

Then (4.1) gives

Thus

A global uniform mass bound follows only if b\ge a. On a fixed interval 0<t<T, one still has

which is enough for a finite-time hmass hypothesis. Therefore any theorem claiming a time-uniform logistic mass bound for all \theta\ge1 must separate the case \theta=1.

---

# 5. Why hdiss is the real frontier

Multiplying the PDE by u^{p-1} and integrating gives formally

The diffusion term is exactly

For the cross term, Young gives, for any \varepsilon>0,

Taking, for example, \varepsilon=1/2 leaves half of the diffusion:

What remains is to control

by the available elliptic estimate for v, the bootstrap exponent, GN interpolation, and the damping term. This is model-specific and is where the hypotheses on m,\theta, sensitivity, and the elliptic equation enter. None of this follows from classical regularity alone.

A rigorous Lean derivation of (5.1) also needs exactly the three analytic bridges already identified in IntervalDomainEnergyStep.lean:

1. differentiation under the spatial integral and the time chain rule;

1. integration by parts on [0,1] with the Neumann endpoint terms removed;

1. moving the pointwise PDE, stated on the open interior, into an almost-everywhere/integral equality.

Therefore hdiss is the dominant proof obligation.

## Audit of the current hdiss shape

The hypothesis in IntervalDomainTierChain.lean says that from an upper inequality of the form

one may conclude

There is no algebraic implication from the first display to (5.5). For example, a rapidly decreasing positive function Y_p can have Y_p'+pB Y_p<0. Thus one of the following should be done:

- prove (5.5) independently from the concrete PDE;

- weaken/reformulate the Moser closure so it uses only the upper energy inequality;

- or replace hdiss by the genuinely available fact that the gradient and logistic dissipation integrals are nonnegative.

The third option is closest to the usual paper proof.

---

# 6. Recommended Lean closure order

1. Close hu_nonneg immediately from IsPaper2ClassicalSolution.u_pos'.

1. Close hpow_int from spatial continuity on compact [0,1] and bounded-measurable integrability.

1. Use the existing interval Agmon theorem for hMG, with the exponent proof $p+\rho>1$.

1. Prove the exact rpow chain rule and then (2.3). Before doing so, decide whether the available bootstrap really supplies a noncircular uniform U_T.

1. Prove the mass identity (4.1) using the Neumann flux cancellation, Jensen (4.2), and scalar comparison; instantiate hmass with (4.6).

1. Audit/remove the extra lower-sign hdiss requirement. Then formalize the genuine weighted energy identity and chemotaxis absorption.

## Bottom line

The seven assumptions should not be treated as seven equally difficult frontiers.

- Automatic/routine: hu_nonneg, hpow_int, hcGrad.

- Standard interval analysis/algebra: hMG, hgrad.

- Short but genuinely PDE-dependent: hmass.

- The actual Lemma 2.6 frontier: hdiss, especially the chemotaxis term and the current nonstandard lower-sign formulation.