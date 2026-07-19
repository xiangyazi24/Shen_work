ANSWER Q103 1f7b0d5d

## Executive conclusion

The paper’s critical-case boundedness proof is not a constant-ceiling argument and not an Alikakos/Moser iteration over a sequence of exponents. It is a three-stage bootstrap using one carefully chosen exponent (p>max{1,m,gamma}):

1. a uniformly translated, exponentially cutoff-weighted local (L^p) estimate for (u);

1. a uniform (L^infty) estimate for (v_x);

1. a whole-line heat-semigroup (L^{p/m}to L^infty) estimate for (w=upsi).

The two ratios

[

frac{2m-1}{m-1},qquad frac{m+gamma-1}{gamma-1}

]

do not come from two different Young absorptions. They are the two possible left-endpoint values of the same high-power absorption condition

[

frac{chi(p-1)}{p+m-1}<1,

]

once the proof also requires (p>m) for Step 3 and (p>gamma) for Step 2. If (mgegamma), the limiting admissible exponent is (pdownarrow m), giving ((2m-1)/(m-1)); if (gammage m), it is (pdownarrowgamma), giving ((m+gamma-1)/(gamma-1)).

A scalar pointwise comparison closes the critical case only for (0<chi<1). For (chige1), the worst-case scalar ODE is non-dissipative (and for (chi>1) actually blows up), so no comparison argument based only on the slab maximum principle, (vge0), and (|v|infty,|v_x|inftyle|u|_infty^gamma) can recover the paper’s larger threshold. Therefore:

- cheap first extension: generalize the existing MChi/ODE lane from χ < chiStar to all χ < 1;

- full Proposition 1.1(2): formalize the paper’s weighted uniformly-local single-(p) bootstrap for the remaining window (1lechi<chi_{mathrm{paper}}).

The paper source is Shen, arXiv:2605.04401v1, §3.1, pp. 14–20.

---

## (a) Exact paper argument in the critical case

### 1. The norm is uniformly local, not global (L^p(mathbb R))

Before §3.1, the paper explicitly observes that bounded uniformly continuous functions need not lie in global (L^p(mathbb R)). It chooses a smooth positive weight (psi) such that, for a small parameter (kappa_1>0),

[

0<psi(x)le e^{-kappa_2|x|},qquad

tag{2.9}

]

See paper p. 13, equation (2.9) and Lemma 2.5.

For every center (x_0inmathbb R), define

[

F_{p,x_0}(t):=int_{mathbb R}u(t,x)^ppsi(x-x_0),dx.

]

The exact output of Step 1 is

[

sup_{0le t<T_{max}(u_0), x_0inmathbb R}

int_{mathbb R}u(t,x)^ppsi(x-x_0),dx<infty.

tag{3.9}

]

Thus the paper’s operative norm is

[

|u(t)|{L^p{psi,mathrm{uloc}}}

:=sup_{x_0inmathbb R}

left(int_{mathbb R}|u(t,x)|^ppsi(x-x_0),dxright)^{1/p}.

]

It calls this boundedness in (L^p_{mathrm{loc}}), but the estimate proved is stronger and uniform in translations. A naive (int_{mathbb R}u^p) never appears.

### 2. Weighted (L^p) energy identity

Suppressing the translate (x_0), multiply the parabolic equation by (u^{p-1}psi). The paper obtains on pp. 16–17

[

begin{aligned}

frac1pfrac d{dt}int u^ppsi

={}&-(p-1)int u^{p-2}|u_x|^2psi

&+chi(p-1)int u^{p+m-2}u_xv_xpsi

&+int u^ppsi-int u^{p+alpha}psi.

end{aligned}

]

Using

[

(u^{p+m-1})_x=(p+m-1)u^{p+m-2}u_x,

qquad v_{xx}=v-u^gamma,

]

the two chemotaxis terms become

[

begin{aligned}

&chi(p-1)int u^{p+m-2}u_xv_xpsi

={}&frac{chi m}{p+m-1}int u^{p+m-1}v_xpsi_x

&+frac{chi(p-1)}{p+m-1}

le{}&frac{chi mkappa_1}{p+m-1}

end{aligned}

]

This is the load-bearing integration-by-parts identity. The negative (v)-term is simply discarded because (vge0).

The cutoff derivative term is estimated by

[

left|int u^{p-1}u_xpsi_xright|

le frac{kappa_1}{2}int u^{p-2}|u_x|^2psi

]

after taking (kappa_1le1). This gives the paper’s display (3.5).

Typesetting/OCR warning for Lean: the parsed PDF prints (u^{p-1}|u_x|^2) in the small positive gradient term in (3.5)/(3.6). The preceding exact identity and the valid Cauchy–Young pairing force (u^{p-2}|u_x|^2). Formalize the latter; otherwise it cannot be absorbed into the leading diffusion term.

### 3. Young absorption and weighted resolver estimate

Because (alpha+1>m), use conjugate exponents

[

r=frac{p+alpha}{p+m-1},qquad

r'=frac{p+alpha}{alpha+1-m}

]

to obtain, with a harmless rescaling of Young’s inequality,

[

int u^{p+m-1}|v_x|psi

le frac14int u^{p+alpha}psi

]

The paper writes (C_Y=1); Lean should use whatever explicit positive constant follows from the chosen Young lemma.

Paper Lemma 2.5 gives, for

[

q=frac{p+alpha}{alpha+1-m}>1,

]

[

int |v_x|^qpsi

le C_p^*int u^{gamma q}psi.

]

Substitution yields equation (3.6):

[

begin{aligned}

frac1pF'le{}&-left(p-1-frac{kappa_1}{2}right)

&+frac{chi mkappa_1}{4(p+m-1)}int u^{p+alpha}psi\

&+frac{C_p^*chi mkappa_1}{p+m-1}

&+frac{chi(p-1)}{p+m-1}

tag{3.6}

end{aligned}

]

### 4. Critical case and the unique high-power coefficient

Now assume

[

alpha=m+gamma-1.

]

Then both exponents in the bad terms collapse exactly to the damping exponent:

[

frac{gamma(p+alpha)}{alpha+1-m}=p+alpha,

qquad

p+m+gamma-1=p+alpha.

]

Hence the coefficient of

[

G_{p,x_0}(t):=int u^{p+alpha}psi(x-x_0)

]

is

[

-1+frac{chi(p-1)}{p+m-1}

]

The paper first chooses (p) so that

[

max{1,m,gamma}<p<m+gamma,

qquad

chi<frac{p+m-1}{p-1},

tag{A}

]

and then chooses (kappa_1) sufficiently small. Put

[

delta_p:=1-frac{chi(p-1)}{p+m-1}>0.

]

It is enough to impose

[

kappa_1<2(p-1),

qquad

frac{chi mkappa_1}{p+m-1}left(frac14+C_p^*right)

lefrac{delta_p}{2}.

]

Then one may take (lambda=delta_p/2>0), obtaining the key display (3.8), paper p. 18:

[

frac1pF_{p,x_0}'(t)

le left(1+frac{kappa_1}{2}right)F_{p,x_0}(t)

tag{3.8}

]

This is the entire critical-case absorption.

### 5. Where the two ratio conditions come from

Define

[

f(s):=frac{s+m-1}{s-1}=1+frac{m}{s-1},qquad s>1.

]

This is strictly decreasing. Condition (A) asks for a (p) just above

[

s_0:=max{m,gamma}.

]

Therefore such a (p) exists exactly when (chi<f(s_0)):

- if (mgegamma), (s_0=m), so

f(s_0)=frac{2m-1}{m-1};]

- if (gammage m), (s_0=gamma), so

f(s_0)=frac{m+gamma-1}{gamma-1}.]

Equivalently,

[

chi<minleft{

frac{2m-1}{m-1},

frac{m+gamma-1}{gamma-1}

right}.

]

The analytic meaning of the two lower bounds on (p) is:

- (p>gamma): Step 2 needs (p/gamma>1) to turn the local (L^p) bound on (u) into an (L^infty) bound on (v_x);

- (p>m): Step 3 needs (p/m>1) so the singularity

Thus each ratio is the endpoint forced by a different later bootstrap requirement, but both enter the same coefficient inequality (chi(p-1)<p+m-1).

For Lean, the faithful denominator-free threshold is

```javascript
χ * (m - 1) < 2 * m - 1 ∧
χ * (γ - 1) < m + γ - 1
```

so that (m=1) or (gamma=1) correctly removes, rather than destroys, the corresponding constraint. The repo already proves the equivalence in

paper1PositiveCriticalThreshold_iff_exists_admissible_exponent at commit 4947ee5.

### 6. The omitted scalar coercivity from (3.8) to (3.9)

The paper says (3.8) implies boundedness; the exact chain to formalize is short. Let

[

S_psi:=int_{mathbb R}psi(x),dxin(0,infty).

]

Weighted Hölder gives

[

F

=int (u^{p+alpha}psi)^{p/(p+alpha)}

le G^{p/(p+alpha)}S_psi^{alpha/(p+alpha)},

]

hence

[

Gge S_psi^{-alpha/p}F^{1+alpha/p}.

tag{B}

]

Writing (A=1+kappa_1/2), (3.8) becomes

[

F'le pAF-plambda S_psi^{-alpha/p}F^{1+alpha/p}.

]

Therefore

[

F_{p,x_0}(t)

le

maxleft{

F_{p,x_0}(0),

S_psileft(frac{A}{lambda}right)^{p/alpha}

right}.

]

Since (u_0in C^b_{mathrm{unif}}),

[

F_{p,x_0}(0)le|u_0|infty^pSpsi

]

uniformly in (x_0), yielding (3.9).

This is a logistic-type scalar ODE for the weighted local moment, not an (L^pto L^{2p}tocdots) Moser iteration.

### 7. Step 2: (v_x) bounded

The paper sets

[

p'=p/gamma>1

]

and invokes Gilbarg–Trudinger, Theorem 9.11, to infer from (3.9)

[

sup_{0le t<T_{max}}|v_x(t)|_infty<infty.

tag{3.10}

]

On the whole line, the explicit resolver is cheaper for Lean:

[

v_x(t,x)

=-frac12int_{-infty}^x e^{-(x-y)}u(t,y)^gamma,dy

+frac12int_x^infty e^{-(y-x)}u(t,y)^gamma,dy.

]

Partition (mathbb R) into unit intervals relative to (x). From (3.9) and positivity of (psi) on a compact neighborhood of zero, obtain a uniform bound on

[

int_Iu^p

]

for every unit interval (I). Hölder with (p/gamma>1) gives a uniform bound on (int_Iu^gamma); summing the exponentially decaying kernel over the intervals gives

[

|v_x(t)|_infty

le C_{psi,p,gamma}

left(sup_{x_0}F_{p,x_0}(t)right)^{gamma/p}.

]

This avoids formalizing local elliptic (W^{2,q}) theory.

### 8. Step 3: heat-semigroup bootstrap to (L^infty)

For a fixed translate of (psi), set (w=upsi). The paper computes

[

w_t=w_{xx}-partial_x(2upsi_x+chi u^mv_xpsi)

]

Using (e^{(Delta-I)t}), equation (3.11) is

[

begin{aligned}

w(t)={}&e^{(Delta-I)t}w(0)\

&-int_0^t e^{(Delta-I)(t-s)}

&+int_0^t e^{(Delta-I)(t-s)}

tag{3.11}

end{aligned}

]

The three terms are (I_1,I_2,I_3).

- By contraction, (|I_1|inftyle|w(0)|infty), equation (3.12).

- Since (1+alpha>m) and (|v_x|_infty) is bounded,

- Let (p''=p/m>1). Lemma 2.1, equation (2.3), yields

For the source norm, use (0<psile1), (mp''=p), and (3.9):

[

int u^{mp''}psi^{p''}leint u^ppsi,

]

and

[

int u^{p''}psi^{p''}

leint(1+u^p)psi.

]

Consequently

[

u(t,x)psi(x-x_0)le C

]

uniformly in (t<T_{max}), (x), and (x_0). Choosing (x_0=x) gives

[

u(t,x)le C/psi(0),

]

so the blow-up alternative forces (T_{max}=infty) and proves (1.10).

Second typesetting warning: the parsed coefficient in the second line of (3.14) contains 2χκ₁ for the term (2upsi_x). Directly from (3.11), that coefficient should be (2kappa_1); the chemotaxis factor (chi) belongs only to (u^mv_xpsi). Lean should derive the norm estimate from the source expression rather than copy that coefficient.

---

## (b) Exact whole-line inequality chain to formalize

### Functional and data package

Use an explicit weight, preferably

[

psi_kappa(x)=exp(-kappasqrt{1+x^2}),

]

or any existing smooth weight with:

```javascript
0 < ψ x
ψ x ≤ 1
Integrable ψ
|deriv ψ x| ≤ κ₁ * ψ x
|deriv (deriv ψ) x| ≤ κ₁ * ψ x
0 < ψ 0
```

Define

```javascript
def wholeLineLocalLpMoment
    (P : ℝ) (ψ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (t x₀ : ℝ) : ℝ :=
  ∫ x, (u t x) ^ P * ψ (x - x₀)
```

and the paper’s uniformly local envelope as the proposition

```javascript
∀ t ∈ Set.Ico 0 Tmax, ∀ x₀,
  wholeLineLocalLpMoment P ψ u t x₀ ≤ K
```

rather than taking a literal sSup until needed.

### Critical energy chain

Choose (P) from the already-proved exponent theorem:

```javascript
max 1 (max m γ) < P
P < m + γ
χ * (P - 1) < P + m - 1
```

Set

[

Q=frac{P+alpha}{alpha+1-m},qquad

F=int u^Ppsi_{x_0},qquad

G=int u^{P+alpha}psi_{x_0}.

]

The Lean chain should be exactly:

```plain text
weighted PDE identity
→ chemotaxis integration by parts using vₓₓ = v - u^γ
→ discard -χ(P-1)/(P+m-1) ∫u^(P+m-1)vψ
→ absorb cutoff derivative into diffusion
→ Young on ∫u^(P+m-1)|vₓ|ψ
→ weighted resolver-gradient estimate at exponent Q
→ critical rewrites γQ = P+α and P+m+γ-1 = P+α
→ negative high-power coefficient after choosing κ₁
→ F' ≤ P A F - P λ G
→ weighted Hölder G ≥ Sψ^(-α/P)F^(1+α/P)
→ uniform ODE barrier for F
→ uniformity in x₀ by translation invariance.
```

For the weighted resolver estimate, the whole-line kernel gives a shorter proof than the paper’s semigroup argument. Since (|psi'|lekappa_1psi) and (psi>0), prove the moderation inequality

[

psi(x)le e^{kappa_1|x-y|}psi(y).

]

For the kernel (k(z)=tfrac12e^{-|z|}), Jensen and Fubini then give, for (Q>1) and (kappa_1<1),

[

begin{aligned}

int |v_x(x)|^Qpsi(x),dx

&leintint k(x-y)u(y)^{gamma Q}psi(x),dy,dx\

&leleft(int k(z)e^{kappa_1|z|},dzright)

&=frac1{1-kappa_1}int u^{gamma Q}psi.

end{aligned}

]

This provides an explicit replacement for Lemma 2.5 with

[

C_P^*=frac1{1-kappa_1}.

]

Because this constant itself depends on (kappa_1), choose first a coarse range, e.g. (0<kappa_1le1/2), so (C_P^*le2), and then impose the coefficient smallness condition. That avoids circular parameter selection.

### Continuation must not be circular

The estimates are to be proved on every finite interval

[

[0,T],qquad T<T_{max}(u_0),

]

with constants independent of (T). Do not start from the existing globally glued positive-critical solution if its construction already assumes WholeLineCauchyCeilingRegime; that would exclude the target window and make the argument circular.

The clean architecture is:

```plain text
maximal local classical solution
→ uniform local-Lp estimate on every T<Tmax
→ uniform vₓ bound on every T<Tmax
→ uniform u∞ bound on every T<Tmax
→ finite-time blow-up alternative contradiction
→ Tmax = ∞.
```

If the repo represents local solutions by restartable fixed-length segments rather than an explicit maximal solution, prove the same estimates on each partial concatenation with constants depending only on the initial norm and parameters; the uniform (L^infty) output supplies a uniform next-step existence time, and induction gives infinitely many segments.

---

## (c) Pointwise/comparison route and its exact limit

Expand the chemotaxis divergence:

[

u_t=u_{xx}-chi m u^{m-1}u_xv_x

]

Since (vge0),

[

-chi u^m(v-u^gamma)lechi u^{m+gamma}.

]

At a spatial approximate maximum, the drift vanishes in the penalized limit and (u_{xx}le0). Thus the worst scalar upper field is

[

y'=ybigl(1-y^alpha+chi y^{m+gamma-1}bigr).

tag{C}

]

This is exactly the ODE introduced by the paper after it has proved boundedness, at pp. 19–20, to obtain the sharper limsup (3.15)/(1.11).

In the critical case (alpha=m+gamma-1), (C) becomes

[

y'=ybigl(1+(chi-1)y^alphabigr).

tag{D}

]

For (y_0>0), put (z=y^{-alpha}). Then

[

z'=-alpha z-alpha(chi-1).

]

Hence:

(0<chi<1)

[

z(t)=(1-chi)+(z_0-(1-chi))e^{-alpha t},

]

so (y) is globally bounded and

[

limsup_{ttoinfty}y(t)

le(1-chi)^{-1/alpha}=M_chi.

]

This scalar comparison is sufficient for global boundedness on the entire subunit window (0<chi<1), not merely (chi<chi_*). The repo’s present restriction to chiStar is therefore an interface/construction-regime restriction, not a limitation of the maximum-principle mathematics.

(chi=1)

[

y'=y,qquad y(t)=y_0e^t,

]

so there is no finite absorbing bound.

(chi>1)

[

z(t)=-(chi-1)+(z_0+chi-1)e^{-alpha t}.

]

It reaches zero at

[

t_*=frac1alpha

logfrac{z_0+chi-1}{chi-1},

]

and the scalar comparison solution blows up there.

This does not prove that the PDE blows up; it proves that the worst-case scalar upper inequality is too crude to bound it.

### Why a two-parameter scalar supersolution does not recover the paper threshold

Tracking only

[

U(t)=|u(t)|_infty,qquad

V(t)=|v(t)|_infty,qquad

G(t)=|v_x(t)|_infty

]

gives

[

V(t),G(t)le U(t)^gamma,

]

which substitutes back into exactly (C). The elliptic variable has no independent time ODE. To improve (C), one would need a lower bound for (v) at a point where (u) is near its maximum, or quantitative spatial thickness of a high-(u) region. Such information is precisely an anti-concentration/local-regularity estimate—the role played by the weighted local (L^p) argument. The ratios in Proposition 1.1 cannot emerge from a finite-dimensional ODE based only on supremum bounds.

Therefore there is no plausible pointwise route covering (1lechi<chi_{mathrm{paper}}) without importing information equivalent to the local-(L^p) bootstrap.

---

## (d) Lean recommendation and named lemma chain

### Lane 1: cheap extension to all critical (0<chi<1)

This should be done first because almost all ingredients already exist in

WholeLineCauchyChiPosLongTimeBound.lean and

WholeLineCauchyChiPosRangeBound.lean.

Current relevant chain:

```plain text
wholeLineCauchyChiPosCeiling
wholeLineCauchyChiPosCeiling_hasDerivAt
chiPosCeiling_supersolution
wholeLineCauchyGlobal_le_chiPosCeiling_of_chi_pos
wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
wholeLineCauchyGlobal_le_max_of_chi_pos
```

The obstruction is the extra hypothesis

```javascript
hregime : WholeLineCauchyCeilingRegime p
```

whose current critical constructor carries χ < chiStar. Replace or generalize the construction-facing regime by a mathematically exact one:

```javascript
def WholeLineCauchyConstructionCeilingRegime (p : CMParams) : Prop :=
  p.χ ≤ 0 ∨
  (0 ≤ p.χ ∧
    (p.m + p.γ - 1 < p.α ∨
      (p.χ < 1 ∧ p.α = p.m + p.γ - 1)))
```

Then clone/generalize the static clamp and segment invariance proofs. Suggested capstone:

```javascript
theorem Proposition_1_1_positive_critical_subunit_branch
    (p : CMParams)
    (hχ : 0 < p.χ) (hχ1 : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u (MChi p)
```

This closes any nonempty interval chiStar ≤ χ < 1 cheaply.

### Lane 2: the genuine residual (1lechi<chi_{mathrm{paper}})

For the full paper theorem, the weighted single-(p) route is mandatory. Recommended modules and theorem names:

Parameter selection

```plain text
paper1PositiveCriticalThreshold_iff_exists_admissible_exponent  -- already landed
prop11Critical_admissibleExponent
prop11Critical_highPowerMargin_pos
```

Weight and weighted calculus

```plain text
wholeLineLocalLpWeight
wholeLineLocalLpWeight_integrable
wholeLineLocalLpWeight_deriv_le
wholeLineLocalLpWeight_secondDeriv_le
wholeLineLocalLpWeight_moderate
wholeLineWeightedIBP_first
wholeLineWeightedIBP_second
wholeLineLocalLpMoment_hasDerivAt
```

Resolver

```plain text
frozenElliptic_deriv_kernel
frozenElliptic_deriv_weightedLp_le
frozenElliptic_deriv_sup_le_of_uniformLocalLp
```

Use the explicit kernel/Jensen proof rather than formalizing Gilbarg–Trudinger Theorem 9.11.

Step 1 energy

```plain text
wholeLineLocalLp_chemotaxis_ibp
wholeLineLocalLp_cutoffTerm_le
wholeLineLocalLp_flux_young
wholeLineLocalLp_criticalCoefficient_neg
wholeLineLocalLp_deriv_le_critical
wholeLineLocalLp_highMoment_coercive
wholeLineLocalLp_uniform_bound_critical
wholeLineLocalLp_uniform_translates
```

Step 2

```plain text
wholeLineResolverGradient_sup_of_uniformLocalLp
```

Step 3

```plain text
wholeLineWeightedSolution_pde
wholeLineWeightedSolution_duhamel
wholeLineWeightedSolution_I1_le
wholeLineWeightedSolution_I3_le
wholeLineWeightedSolution_I2_le
wholeLineWeightedSolution_sup_le
wholeLineSolution_sup_le_of_all_translates
```

The existing whole-line semigroup estimate corresponding to paper Lemma 2.1(2.3) should feed I2_le.

Continuation and headline

```plain text
wholeLineMaximalCauchy_uniformBound_of_positiveCriticalThreshold
wholeLineMaximalCauchy_global_of_uniformBound
Proposition_1_1_positive_critical_branch_full
```

The final theorem should use the faithful division-free threshold, not the old ratio expression with Lean division by zero.

### Relative cost

- Extending the ODE/ceiling lane from chiStar to χ<1: small-to-medium, mostly regime refactoring and rewiring.

- Full weighted local-(L^p) lane: medium-to-large, but no infinite Moser ladder. The deepest pieces are weighted whole-line integration by parts and the uniform-in-translate Duhamel estimate. The explicit resolver kernel substantially reduces the cost.

A reasonable implementation order is:

```plain text
1. Generalize critical Cauchy ceiling to χ<1.
2. Land the explicit moderate weight and weighted-kernel resolver lemma.
3. Land the exact Step-1 identity and coefficient absorption.
4. Close the scalar moment ODE and translation-uniform estimate (3.9).
5. Prove the explicit-kernel vₓ bound (3.10).
6. Reuse the whole-line heat-gradient semigroup for (3.11)–(3.14).
7. Connect to the maximal-time blow-up alternative.
8. Assemble the full faithful Proposition 1.1(2).
```

---

## Current repository audit

At the audited repository state:

- Proposition_1_1_positive_critical_branch closes the faithful partial window (0<chi<chi_*), and the same commit proves the residual window is nonempty using (m=1,gamma=2,alpha=2,chi=3/2).

- paper1PositiveCriticalThreshold_iff_exists_admissible_exponent already formalizes the exact exponent-selection equivalence used above.

- The most recent observed repository commit is f94d03ebd90eeff857859c8bfa50d630aa647967; it generalizes the rectangle squeeze and does not remove this Proposition 1.1 residual.

## Bottom line

For the example (m=1,gamma=2,alpha=2), the paper threshold is (chi<2):

- (0<chi<1): the scalar/maximum-principle ODE is bounded and should be closed by generalizing the existing MChi regime;

- (1lechi<2): the scalar upper ODE is useless, and the paper’s uniformly translated weighted (L^p) argument is the genuine mechanism.

So the rigorous recommendation is not (a) versus (c) as a single choice. Use (c) for the subunit part because it is cheap, then use (a) for the unavoidable superunit residual. Only the combination reaches the full paper statement.