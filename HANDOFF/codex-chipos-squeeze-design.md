# A Two-Sided Buffered Squeeze on the Left Half-Line for χ > 0: Feasible Regime, Exact Budgets, and Lean Design

## Executive conclusion

The brief asks for a two-sided floor/ceiling rectangle contraction guaranteed by
`χ < chiStar`. This is false for this mechanism. The natural coupled rectangle has
the following linear eigenvalue in the width direction at `(M, ell) = (1,1)`:

```text
2 * χ * γ - α.
```

Consequently, local contraction requires at least `2 * χ * γ < α`. A concrete
counterexample is

```text
m = α = γ = 1,   χ = 3/4.
```

The repository definition gives
`chiStar = min 1 ((2m+2γ)/(m^2+m+2γ)) = 1`
(`ShenWork/Defs.lean:241-243`), so `χ < chiStar` holds, whereas the width
eigenvalue is `2χγ-α = 1/2 > 0`: the rectangle expands near equilibrium. The
missing implication `χ < chiStar -> 2χγ < α` must not be treated as a pending
arithmetic lemma in Lean; the numerical example above disproves it.

There are two feasible levels of result:

1. Under an additional hypothesis
   `hsqueeze : 2 * p.χ * p.γ < p.α`, the local two-sided buffered squeeze below
   can be implemented.
2. Under the hypotheses of paper Proposition 1.2,
   `p.χ < 1/2` and `p.m + p.γ - 1 <= p.α`, the paper's global rectangle ODE
   also supplies the burn-in from an arbitrary positive floor and finite ceiling
   into the local neighborhood. The current positive branch of Theorem 1.2 has
   only `χ < chiStar` and `α = m+γ-1`
   (`ShenWork/Paper1/Statements.lean:17126-17128`), which is insufficient for
   this route.

Thus, the design below is formalizable under `χ < 1/2`, or under
`2χγ < α` when an independent local-entry result is already available. It cannot
close the full χ-positive Theorem 1.2 under its current assumptions. Retaining the
full `χ < chiStar` range requires a non-rectangle mechanism that uses spatial
correlation or diffusion, rather than only half-line infima, suprema, and interval
bounds for the resolver.

## 1. What source paper §5 actually does

I read the repository copy of `paper1.pdf` directly. It has 50 pages. Since
`pdftotext` is unavailable in this environment, I used the installed `pypdf` to
extract and check the text of the same local PDF. The relevant facts are as
follows.

- `paper1.pdf` p.7, Proposition 1.2(2), explicitly assumes
  `0 < χ < 1/2` and `α >= m+γ-1` for positive-sensitivity stability. The Lean
  statement records the same assumptions faithfully at
  `ShenWork/Paper1/Statements.lean:16593-16605`.
- `paper1.pdf` pp.21--22, §3.2, uses the rectangle idea and compares the
  solution with the coupled ODE

  ```text
  M'   = χ M^m (M^γ-ell^γ) + M(1-M^α),
  ell' = χ ell^m (ell^γ-M^γ) + ell(1-ell^α),
  ```

  then invokes [18, Lemmas 3.1--3.2] to show that both endpoints converge to
  1; see paper equations (3.17)--(3.18).
- `paper1.pdf` p.8, Theorem 1.2, instead assumes only
  `0 <= χ < chiStar` and `α=m+γ-1` in the positive branch. The Lean statement
  likewise uses `StableWaveParameterRegime`
  (`Statements.lean:17126-17128`) in `Theorem_1_2`
  (`Statements.lean:17502-17520`).
- `paper1.pdf` pp.46--47, §5 Step 4, first obtains (5.38) from Morrey's
  inequality and the right-tail estimate, then uses a lower barrier to obtain a
  persistent positive left floor in (5.39)--(5.40). If uniform convergence fails,
  it takes a translated limit along `t_n -> infinity`, `x_n -> -infinity`, obtains
  a uniformly positive entire solution, and in the last sentence directly invokes
  Proposition 1.2 to assert that this limit is identically 1.

Therefore §5 does not provide a χ-positive buffered squeeze. It relies on
Proposition 1.2, whose positive branch covers only `χ < 1/2`. When the parameter
interval `1/2 <= χ < chiStar` is nonempty, this invocation does not match the
theorem assumptions. The repository also identifies the positive branch of
Proposition 1.2 as the remaining open content and explicitly retains `<1/2`
(`ShenWork/Paper1/Proposition12Assembly.lean:20-37`). Moreover, paper Remark
1.3(2), pp.10--11, warns that the left tail may oscillate for stronger positive
sensitivity. This is further reason not to silently assume pointwise rectangle
contraction under `χ < chiStar`.

## 2. Why `chiStar` cannot imply the requested contraction

Ignoring the buffer tail, the exact rectangle vector field is

```text
Fplus(M,ell)  = χ M^m   (M^γ-ell^γ) + M(1-M^α),
Fminus(ell,M) = χ ell^m (ell^γ-M^γ) + ell(1-ell^α).
```

At `(1,1)`, its Jacobian in coordinates `(M,ell)` is

```text
[ χγ-α   -χγ   ]
[ -χγ    χγ-α  ].
```

The common-shift direction `(1,1)` has eigenvalue `-α`; the width direction
`(1,-1)` has eigenvalue `2χγ-α`. This is not a loss caused by a coarse tail
estimate. It is the first-order linearization of the interval rectangle itself.
Equivalently, after dividing the equilibrium equations by their positive
endpoints, the local cross-gain is

```text
rho0 = χγ / (α-χγ),
rho0 < 1  <->  2χγ < α.
```

Under the critical equality `α=m+γ-1` and `m>=1`, one has `α>=γ`; hence
`χ<1/2` implies `2χγ<γ<=α`. In contrast, `χ<chiStar` does not imply this
inequality, as the example `(1,1,1,3/4)` shows.

The origin of `<1/2` is also visible in the paper's global rectangle ODE. For
`M>=1>=ell>0`,

```text
d/dt log(M/ell)
 = χ (M^(m-1)+ell^(m-1)) (M^γ-ell^γ) - (M^α-ell^α).
```

Set `beta=m+γ-1`. Termwise,

```text
M^(m-1)(M^γ-ell^γ) <= M^beta-ell^beta,
ell^(m-1)(M^γ-ell^γ) <= M^beta-ell^beta.
```

If `α>=beta`, then `M^α-ell^α >= M^beta-ell^beta`, and therefore

```text
d/dt log(M/ell)
 <= (2χ-1) (M^beta-ell^beta) < 0
```

when the endpoints differ. This supplies global burn-in under `<1/2`; it also
cannot be deduced from general `χ<chiStar`.

## 3. Exact kernel split

Let the co-moving/restarted solution be `q(t,x)`, and let
`V(t,x)=frozenElliptic p (q t) x`. Fix a half-line boundary `x0` and buffer width
`R>=0`, set `z0=x0+R`, and define

```text
tau = exp(-R)/2.
```

Suppose that, at the current stage, the solution satisfies on the left half-line
plus buffer

```text
ell <= q(t,y) <= M       for y <= z0,
0   <= q(t,y) <= G       for all y,
0 < ell <= 1 <= M <= G.
```

For `x<=x0`, the normalized kernel mass on `Ici z0` is at most `tau`. Splitting
the integral gives the exact interval bound

```text
(1-tau) ell^γ
  <= V(t,x)
  <= (1-tau) M^γ + tau G^γ.
```

The lower bound is already implemented in a slightly weaker but equivalent
sufficient form by `frozenElliptic_lower_of_left_halfLine_floor`
(`ShenWork/Paper1/WholeLineWeightedRegularityHalfLineResolverLowerNatural.lean:23-30`),
with the kernel-mass calculation at `:43-59`. An upper mirror must be added. Its
proof should reuse the same integral split rather than re-expand all of the `Psi`
analysis.

The two adverse resolver gaps are therefore

```text
V-q^γ <= (M^γ-ell^γ) + tau (G^γ-M^γ),       -- lower contact
q^γ-V <= (M^γ-ell^γ) + tau ell^γ.           -- upper contact
```

The first line uses `q>=ell`; the second uses `q<=M`. The PDE in
nondivergence form is

```text
q_t = q_xx + c q_x
      - χ m q^(m-1) q_x V_x
      + χ q^m(q^γ-V) + q(1-q^α),
```

whose exact repository expansion is at
`ShenWork/Paper1/WholeLineWeightedRegularityChiNegLeftEquilibriumNatural.lean:31-41`.
At an approximate spatial contact, the `q_x` term vanishes; the existing maximum
machinery absorbs its epsilon fencing. Thus, with the current-stage endpoints
fixed, the two defects can be taken as

```text
Hminus(ell,M,G,R)
  = χ M^m ((M^γ-ell^γ) + tau (G^γ-M^γ)),

Hplus(ell,M,R)
  = χ M^m ((M^γ-ell^γ) + tau ell^γ).
```

`Hminus` is the loss for the lower floor, and `Hplus` is the loss for the upper
ceiling. The complete contact inequalities are

```text
-- lower contact q=b, ell <= b <= M
χ b^m(b^γ-V)
  >= -χ M^m ((M^γ-ell^γ)+tau(G^γ-M^γ))
   = -Hminus,

-- upper contact q=a, ell <= a <= M
χ a^m(a^γ-V)
  <= χ M^m ((M^γ-ell^γ)+tau ell^γ)
   = Hplus.
```

## 4. Exact defect budgets for one floor/ceiling barrier step

Starting from the current endpoints `C=ell < 1 < M=D`, choose tighter raw
targets

```text
C < Lhat < 1 < Ahat < D.
```

### Lower barrier

Reuse the existing target-capped floor

```text
bminus(t) = Lhat - (Lhat-C) exp(-lambdaMinus*t).
```

A sufficient budget, already matching an existing Lean template, is

```text
Hminus < C (1-Lhat^α),
lambdaMinus
  = (C(1-Lhat^α)-Hminus)/(Lhat-C+1).
```

The pointwise chain, using `C<=bminus<=Lhat`, is

```text
bminus' + Hminus
 = lambdaMinus (Lhat-bminus) + Hminus
 <= lambdaMinus (Lhat-C) + Hminus
 <= C(1-Lhat^α)
 <= bminus(1-bminus^α).
```

This is precisely the scalar part of `chiNegKPPFloorRate` and its defect lemma:
`ShenWork/Paper1/WholeLineWeightedRegularityChiNegKPPFloorNatural.lean:21-55`
and `:59-101`. The barrier's derivative, range, and convergence lemmas are already
at `WholeLineWeightedRegularityChiZeroKPPFloorNatural.lean:19-67`.

### Upper barrier

Add the exact dual target-capped ceiling

```text
bplus(t) = Ahat + (D-Ahat) exp(-lambdaPlus*t).
```

Its budget is

```text
Hplus < Ahat(Ahat^α-1),
lambdaPlus
  = (Ahat(Ahat^α-1)-Hplus)/(D-Ahat+1).
```

For `Ahat<=bplus<=D`, the pointwise chain is

```text
bplus' = -lambdaPlus(bplus-Ahat),

-bplus'
 <= lambdaPlus(D-Ahat)
 <= Ahat(Ahat^α-1)-Hplus
 <= bplus(bplus^α-1)-Hplus,
```

or equivalently

```text
bplus' >= bplus(1-bplus^α)+Hplus.
```

Thus it is the supersolution required at an upper contact. This is not obtained
by changing one sign in the χ-negative theorem: the lower comparison needs the
new upper-resolver bound, whereas the upper comparison uses the existing
lower-resolver bound.

Compact convergence supplies both buffer boundary orderings. If
`|q-U|<delta` on `[x0,x0+R]`, the choice of `x0` from `U(-infinity)=1` also gives
`|U-1|<delta`, and `2delta < min(1-Lhat,Ahat-1)`, then throughout the future
buffer

```text
Lhat <= q(t,x) <= Ahat.
```

These are exactly the lateral conditions `bminus<=q<=bplus`. The existing
compact-closeness theorem is at
`ShenWork/Paper1/WholeLineWeightedRegularityCoMovingCompactNatural.lean:24-34`;
the χ-positive weighted input is at
`WholeLineWeightedRegularityWeightedConvergenceChiPosNatural.lean:21-36`; and
the spatial modulus is at `Theorem12Step4EnergyProducer.lean:311-320`.

## 5. A local quantitative iteration suitable for induction on `Nat`

To avoid manipulating `sInf` and `sSup` directly in Lean, first prove a package
of local constants. Assume `hsqueeze : 2*χ*γ < α`. Using the derivative of rpow
at 1, choose

```text
0 < r < 1,
0 < a,
0 < qhat < q < 1,
0 < g
```

such that, for `0<e<=r`,

```text
(1-r) * (1-(1-e)^α) >= a*e,
(1+e) * ((1+e)^α-1) >= a*e,
(1+e)^γ-(1-e)^γ <= g*e,
χ*(1+r)^m*g < a*qhat.
```

As `r -> 0` (and uniformly for `0 < e <= r`), the best constants in the first
three estimates approach `α, α, 2γ`. Hence the last inequality can be arranged
exactly when `2χγ<α`. These four properties should be packaged in a
`ChiPosLocalSqueezeConstants` structure. After proving existence once, all later
comparisons should consume its fields without expanding the difference quotients.

After obtaining the global range bound from Task 2, enlarge it to `G>=1+r`. Define

```text
Tail(R) = χ*(1+r)^m*(exp(-R)/2)*max (G^γ) 1,
h(R)    = Tail(R)/a.
```

Let the current symmetric envelope be

```text
ell_n = 1-E_n,   M_n = 1+E_n,   0<E_n<=r.
```

The exact defects from §3 admit the following common bounds, chosen only to
simplify the `Nat` recurrence:

```text
Hminus_n <= χ*(1+r)^m*g*E_n + Tail(R),
Hplus_n  <= χ*(1+r)^m*g*E_n + Tail(R).
```

Define the raw target error and published next error by

```text
Ehat_n   = qhat*E_n + 2*h(R),
E_(n+1) = q*E_n    + 3*h(R).
```

Execute a stage only while `E_(n+1)<E_n`. Since
`Ehat_n<E_(n+1)`, the barriers first converge toward the stronger raw targets
`1±Ehat_n`; after finite time they yield the closed interval actually used for
induction, `[1-E_(n+1),1+E_(n+1)]`. This slack is necessary: an exponential
barrier approaches its target but does not equal it at finite time.

The core budget chain is completely explicit:

```text
Hminus_n, Hplus_n
 <= χ*(1+r)^m*g*E_n + Tail(R)
 <  a*qhat*E_n       + 2*Tail(R)
 =  a*Ehat_n.
```

The local constants then give

```text
Hminus_n
 < (1-E_n) * (1-(1-Ehat_n)^α),

Hplus_n
 < (1+Ehat_n) * ((1+Ehat_n)^α-1),
```

which are exactly the two defect budgets in §4.

The affine `Nat` recurrence has the direct closed-form bound

```text
E_n <= q^n*E_0 + 3*h(R)/(1-q).
```

Given a final `epsilon>0`, first choose `R` so that

```text
3*h(R)/(1-q) < min(epsilon/4, r/4),
```

then choose `N` so that `q^N E_0 < epsilon/4`. Stop at the first
`E_n<=epsilon/2`. Before that point,
`E_n>epsilon/2>3h/(1-q)`, hence `E_(n+1)<E_n`; all target range conditions hold
at every executed stage. The result is `|q-1|<=E_N<epsilon/2` on the required
left half-line, leaving room to obtain the final strict inequality.

The Lean-inductable statement should not contain a changing tower of nested
`Eventually` propositions. Use a state such as

```lean
structure BufferedSqueezeState
    (q : ℝ → ℝ → ℝ) (x0 R G E T : ℝ) : Prop where
  E_pos   : 0 < E
  E_le_r  : E ≤ constants.r
  global  : ∀ t, T ≤ t → ∀ x, q t x ∈ Set.Icc 0 G
  left    : ∀ t, T ≤ t → ∀ x, x ≤ x0 →
              q t x ∈ Set.Icc (1-E) (1+E)
  buffer  : ∀ t, T ≤ t → ∀ x, x ∈ Set.Icc x0 (x0+R) →
              q t x ∈ Set.Icc (1-Ehat) (1+Ehat)
```

In the actual structure, `buffer` should preferably be a parameter of the step
theorem because `Ehat` changes at every step. The core theorem should have the
following shape:

```lean
theorem BufferedSqueezeState.step
    (hstate : BufferedSqueezeState q x0 R G E T)
    (hbudget : ...)
    (hbufferRaw : ∀ t ≥ T, ∀ x ∈ Icc x0 (x0+R),
       q t x ∈ Icc (1-Ehat) (1+Ehat))
    (hnext : Enext = qconst*E + 3*hR)
    (himprove : Enext < E) :
    ∃ Tnext ≥ T, BufferedSqueezeState q x0 R G Enext Tnext
```

Then use `Fin N` or `Nat.rec` to produce `T_n`. Only monotonicity in time is
needed; no closed form for `T_n` is required. Compact buffer closeness holds for
all sufficiently late times, so one common `Tbuffer` can be selected before the
induction. Every `T_n>=Tbuffer` then reuses it without invoking the weighted
convergence theorem at each stage.

## 6. Local entry and the seed: two dependencies that cannot be omitted

The `Nat` step above begins from `0<E0<=r`. A complete proof still needs two
independent entry results.

1. **A positive left-floor seed.** The χ-negative proof obtains `d>0` from a
   persistent plateau; the call occurs at
   `WholeLineWeightedRegularityChiNegLeftEquilibriumNatural.lean:174-182`.
   Its sign-dependent chain cannot be reused unconditionally for χ-positive
   sensitivity. The Task 1 audit determines which barrier must be rebuilt. The
   paper's entry mechanism is exactly (5.38)--(5.40). Without `ell0>0`, no
   rectangle ODE can start.
2. **Global-to-local burn-in.** The hypothesis `hsqueeze : 2χγ<α` gives only
   local contraction; it does not automatically send an arbitrary interval
   `[ell0,G]` into `[1-r,1+r]`. Under the paper assumptions `χ<1/2` and
   `α>=m+γ-1`, the log-ratio rectangle ODE from §2 can be formalized, with a
   sufficiently large `R` providing a small tail perturbation, to obtain local
   entry. If only `2χγ<α` is assumed, a separate local-entry theorem is required;
   it must not be hidden inside the step lemma.

For the current project, the safest milestone order is to complete the positive
seed, global rectangle burn-in, and local buffered `Nat` squeeze first under
`<1/2`, yielding a theorem with honest parameters. Recovering the whole
`χ<chiStar` range should then be a separate non-rectangle PDE project.

## 7. Reusable infrastructure and required new lemmas

The following infrastructure carries over directly:

- global χ-positive ceiling, restart, and limsup:
  `WholeLineCauchyChiPosLongTimeBound.lean:25-27`, `:59-77`, `:811-818`,
  `:851-884`;
- stable regime to ceiling regime:
  `WholeLineCauchyGlobalBounds.lean:31-47`; an extractor for `χ<1` already exists
  at `Statements.lean:17315-17320`;
- lower-resolver kernel split:
  `WholeLineWeightedRegularityHalfLineResolverLowerNatural.lean:23-94`;
- scalar floor, rate, defect, and exponential-tail smallness:
  `WholeLineWeightedRegularityChiNegKPPFloorNatural.lean:21-125`;
- generic approximate maximum closure on a left half-line:
  `WholeLineWeightedRegularityHalfLineMaximumNatural.lean:350-377`, with proof
  at `:378-437`;
- finite-slab plumbing from the χ-negative buffered theorem as a template:
  `WholeLineWeightedRegularityChiNegBufferedHalfLineComparisonNatural.lean:27-66`,
  resolver/tail contact calculations at `:292-325`, and the KPP wrapper at
  `:478-551`;
- χ-positive weighted convergence, eventual spatial modulus, and compact buffer
  closeness:
  `WholeLineWeightedRegularityWeightedConvergenceChiPosNatural.lean:21-36`,
  `Theorem12Step4EnergyProducer.lean:311-320`, and
  `WholeLineWeightedRegularityCoMovingCompactNatural.lean:24-34`;
- the final theorem's target definition and wave-tail bridge:
  `WholeLineCauchyLeftTailBridge.lean:18-27` and `:23-67`.

Add the following lemmas, in dependency order:

1. `frozenElliptic_upper_of_left_halfLine_ceiling`, proving
   `V <= (1-tau)M^γ+tau G^γ`, followed by a combined pinching corollary.
2. `chiPosTargetCeiling` and its zero, range, derivative, convergence, and
   restart lemmas, followed by
   `chiPosTargetCeiling_deriv_ge_reaction_add_defect`.
3. Two sign-correct generic comparisons:
   `leftHalfLine_ge_of_buffered_positive_resolver_reaction_subsolution` and
   `leftHalfLine_le_of_buffered_positive_resolver_reaction_supersolution`.
   They share the existing `leftHalfLineSlabSup_le_of_scalar_pde`, but use
   different resolver estimates at contact.
4. Two wrappers taking the current `ell,M,G,R` and raw target and returning the
   floor or ceiling barrier. Their theorem hypotheses should use the strict
   `Hminus/Hplus` budgets above directly.
5. `ChiPosLocalSqueezeConstants.exists_of_two_mul_chi_mul_gamma_lt_alpha`.
6. `BufferedSqueezeState.step`, the affine recurrence lemma, and finite `Nat`
   iteration.
7. A positive seed and global-to-local entry under `<1/2`; only then assemble
   `UniformCoMovingLeftEquilibriumConvergence`.

## 8. Recommended assumptions for the main theorem

The final theorem must not be stated only as

```lean
(hregime : StableWaveParameterRegime p) (hchi_pos : 0 < p.χ) -> ...
```

and then claimed to follow from this design. Choose one of the following honest
forms:

- a partial result with the additional hypothesis
  `hhalf : p.χ < 1/2`, matching paper Proposition 1.2 and the global burn-in;
- a local result with `hsqueeze : 2*p.χ*p.γ < p.α` and an explicit local-entry
  hypothesis; or
- leave the existing full `χ<chiStar` theorem open and develop a mechanism that
  uses diffusion and nonlocal spatial structure.

The existing `StableWaveParameterRegime.positive_branch_of_chi_nonneg` extracts
only `χ<chiStar` and the critical equality
(`Statements.lean:17149-17154`); it cannot extract either additional condition
above. This is a substantive parameter blocker, not a missing `linarith` call.
