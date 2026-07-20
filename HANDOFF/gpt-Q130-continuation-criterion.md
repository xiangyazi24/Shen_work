ANSWER Q130 e2ebdc18

## Verdict

1. Yes: Shen’s positive-sensitivity proof has the standard order

1. The precise continuation criterion is

1. A truncation-and-limit proof does not truly eliminate an a-priori continuation bound if the target is a classical BUC solution. It moves the same burden into uniform-in-truncation estimates and a compactness/identification argument, which is substantially harder to formalize.

1. The literal assertion “no constant supersolution exists” needs qualification. A constant pair ((bar u,bar v)=(M,M^gamma)) is a formal stationary supersolution pair for (Mge1), because its chemotactic flux vanishes. What fails for (alpha=m+gamma-1) and (chige1) is the universal scalar ceiling comparison against the actual resolver of the solution. Its worst-case scalar reaction is

---

## (a) Exactly where Shen obtains global existence

### The local theory is installed before Proposition 1.1

Before proving Proposition 1.1, Shen states that, by the arguments of Salako–Shen, Theorem 1.1, every nonnegative

[

u_0in C^b_{mathrm{unif}}(mathbb R)=BUC(mathbb R)

]

has a unique nonnegative maximal classical solution on a time interval

[

[0,T_{max}),qquad T_{max}in(0,infty],

]

and that

[

T_{max}<infty

implies

limsup_{tuparrow T_{max}}|u(t)|_infty=infty.

tag{BUC blow-up alternative}

]

See Shen, arXiv:2605.04401, p. 6 immediately before Proposition 1.1. Shen says “by the arguments of [39, Theorem 1.1]” rather than claiming that [39] literally contains the general powers (m,gamma,alpha). This distinction is correct: Salako–Shen treats the basic logistic parabolic–elliptic system, while its BUC fixed-point argument extends to the present locally Lipschitz powers.

### The positive-χ proof is conditional on (t<T_{max}) until Step 3

Let (P>max{1,m,gamma}) be the exponent chosen in §3.1.

Step 1. Shen tests against a translated cutoff/weight and proves a translation-uniform local-power estimate of the form

[

sup_{0<t<T_{max}}sup_{x_0inmathbb R}

int_{mathbb R}u(t,x)^Ppsi(x-x_0),dx<infty.

tag{3.9-type estimate}

]

No global existence has yet been obtained. Every estimate is on the already-existing maximal interval.

Step 2. The weighted local (L^P) control is inserted into the elliptic equation

[

(1-partial_{xx})v=u^gamma

]

to obtain

[

sup_{0<t<T_{max}}|v_x(t)|_infty<infty.

tag{3.10}

]

Again, this is still an estimate on ((0,T_{max})).

Step 3. Shen uses the heat-semigroup/Duhamel representation, the bound on (v_x), and (P/m>1) to lift the localized (L^P) information to a translation-uniform weighted (L^infty) estimate. Since the translated weight is uniformly positive near its center, this yields

[

sup_{0<t<T_{max}}|u(t)|_infty<infty.

tag{*}

]

The proof then says that this implies (T_{max}=infty) and the asserted eventual boundedness. The implication is exactly the contrapositive of the BUC blow-up alternative.

Thus the logical chain is

```plain text
local maximal solution and blow-up alternative
  -> Step 1: translation-uniform weighted local L^P bound on (0,Tmax)
  -> Step 2: uniform ||v_x||∞ bound on (0,Tmax)
  -> Step 3: uniform ||u||∞ bound on (0,Tmax)
  -> finite Tmax contradicts the blow-up alternative
  -> Tmax = infinity.
```

The later scalar comparison producing the explicit asymptotic ceiling

[

limsup_{ttoinfty}|u(t)|_infty

le (1-chi)^{-1/alpha}

]

when (alpha=m+gamma-1) and (chi<1) occurs after global existence has already been established. It is not the continuation step for the full parameter range of Proposition 1.1(2).

---

## (b) The precise BUC continuation criterion and why only ‖u‖∞ appears

### Recommended theorem statement

For the formalization, the clean theorem is:

```javascript
MaximalBUCSolution u0 u Tmax :=
  0 < Tmax
  ∧ u is the unique nonnegative mild/classical solution on [0,Tmax)
  ∧ (Tmax < ∞ -> limsup (t↑Tmax) ||u t||∞ = ∞)
```

In mathematical notation:

For each (u_0in BUC(mathbb R)), (u_0ge0), there is a unique maximal nonnegative solution

[

uin C([0,T_{max});BUC(mathbb R))

cap C^{1,2}((0,T_{max})timesmathbb R),

]

with (v(t)=(1-partial_{xx})^{-1}(u(t)^gamma)). If (T_{max}<infty), then

[

limsup_{tuparrow T_{max}}|u(t)|_{BUC}=infty.

]

The primary citation is:

- R. B. Salako and W. Shen, “Global existence and asymptotic behavior of classical solutions to a parabolic–elliptic chemotaxis system with logistic source on (mathbb R^N)”, J. Differential Equations 262 (2017), 5635–5690, Theorem 1.1; local construction in §3, especially the heat-semigroup estimate and the maximal-extension claims.

- The proof of that theorem has a published corrigendum, J. Differential Equations 376 (2023), 773–775, correcting small gaps in estimates (3.18)–(3.19). Cite the theorem together with the corrigendum.

For abstract background, Henry’s chapter “Existence, uniqueness and continuous dependence,” pp. 47–81, in Geometric Theory of Semilinear Parabolic Equations, LNM 840 (1981), is appropriate. Amann’s “Quasilinear parabolic problems via maximal regularity”, Adv. Differential Equations 10 (2005), 1081–1110, is a broader maximal-solution/global-existence reference. Neither is as close to the concrete BUC chemotaxis formulation as Salako–Shen.

### Resolvent estimates

On the line,

[

v=R(u^gamma),qquad R=(1-partial_{xx})^{-1},

]

has the explicit kernel

[

(Rf)(x)=frac12int_{mathbb R}e^{-|x-y|}f(y),dy.

]

Both the kernel and the absolute value of its first derivative have (L^1)-norm one. Hence

[

|Rf|inftyle|f|infty,

qquad

|partial_xRf|inftyle|f|infty.

tag{1}

]

Consequently, a bound (‖u(t)‖_inftyle M) automatically gives

[

|v(t)|infty+|v_x(t)|inftyle 2M^gamma.

]

No independent (v)-blow-up alternative is needed.

### Mild equation and local Lipschitz constants

Writing (S(t)=e^{tpartial_{xx}}), the mild equation is

[

begin{aligned}

u(t)=S(t)u_0

&-chiint_0^tpartial_xS(t-s)

&+int_0^tS(t-s)left[u(s)-u(s)^{alpha+1}right]ds.

end{aligned}

tag{2}

]

On a nonnegative sup-norm ball (0le u,wle R), the power map satisfies

[

|u^q-w^q|_infty

le qR^{q-1}|u-w|_infty

qquad(qge1).

tag{3}

]

Set

[

Q(u)=u^mpartial_xR(u^gamma),

qquad F(u)=u-u^{alpha+1}.

]

Using (1) and (3),

[

begin{aligned}

|Q(u)-Q(w)|_infty

&le

|u^m-w^m|infty|partial_xR(u^gamma)|infty\

&quad+‖w^m|_infty

|partial_xR(u^gamma-w^gamma)|_infty\

&le (m+gamma)R^{m+gamma-1}|u-w|_infty,

end{aligned}

tag{4}

]

and

[

|F(u)-F(w)|_infty

leleft(1+(alpha+1)R^alpharight)|u-w|_infty.

tag{5}

]

The one-dimensional heat kernel gives

[

|partial_xS(t)f|_infty

lefrac{1}{sqrt{pi t}}|f|_infty.

tag{6}

]

Therefore the contraction constant on a time interval of length (tau) can be taken as

[

frac{2chi}{sqrtpi}(m+gamma)R^{m+gamma-1}sqrttau

+τleft(1+(alpha+1)R^alpharight).

tag{7}

]

Choosing (tau>0) so that (7) is (<1), together with the analogous self-map estimate, gives a local existence time depending only on the radius (R) and the equation parameters.

### Restart proof of the blow-up alternative

Assume (T_{max}<infty) but

[

M:=sup_{0<t<T_{max}}|u(t)|_infty<infty.

]

Choose a fixed local ball radius, for example (R=2M+1). The preceding contraction argument supplies a restart length (tau(R)>0), independent of the restart time. Pick

[

t_0in(T_{max}-tau(R)/2,T_{max}).

]

Apply the local theorem with initial datum (u(t_0)). Uniqueness identifies the restarted solution with the old one on their overlap, while the restarted solution exists until (t_0+tau(R)>T_{max}). This contradicts maximality. Hence finite (T_{max}) forces unbounded sup norm.

This restart argument is the continuation criterion in its most Lean-friendly form. It avoids importing a large abstract maximal-regularity theorem: prove the local fixed point once with a time depending only on a norm radius, prove restart and uniqueness, then derive the blow-up alternative by contradiction.

---

## (c) Can one avoid an a-priori sup bound?

### 1. Globally truncated nonlinearities

Choose a smooth cutoff (η_R) and replace the powers and flux by globally Lipschitz maps, for example

[

Q_R(u)=η_R(|u|_infty)u^mpartial_xR(u^gamma),

qquad

F_R(u)=η_R(|u|_infty)(u-u^{alpha+1}).

]

The truncated mild problem is globally solvable because its nonlinearity is globally Lipschitz in the chosen phase space.

But to recover the original equation one must show, for every finite (T), that the truncated solutions satisfy an (R)-independent estimate strong enough that the cutoff is inactive on ([0,T]), or at least strong enough to extract and identify a limit. For a classical BUC limit this requires:

- uniform local-in-time bounds for (u_R), normally including (L^infty) after smoothing;

- uniform space/time Hölder or fractional-domain estimates;

- convergence of (u_R^mpartial_xR(u_R^gamma));

- control of the nonlocal kernel tails when passing from local convergence to (R(u_R^gamma));

- preservation of positivity and the initial trace;

- uniqueness, to remove subsequences and patch time intervals.

Thus truncation does not eliminate the analytic continuation estimate; it relocates it into the uniform-in-(R) compactness step. Without such bounds one may obtain a weak/generalized solution, but not automatically the unique classical BUC solution of Proposition 1.1.

Formalization verdict: substantially harder than the continuation route.

### 2. Construction separately on every finite horizon

One may avoid mentioning (T_{max}) if, for every (T>0), a fixed-point or Schauder map has an invariant set whose bounds are independent of the construction itself. One then constructs a solution on ([0,T]) and patches the family by uniqueness.

This works well when a scalar invariant ceiling is available. For example, in the supercritical case

[

alpha>m+gamma-1,

]

the damping (u^{alpha+1}) eventually dominates the worst chemotactic growth (chi u^{m+gamma}), so a sufficiently large scalar ceiling can be chosen. It also works in the critical subrange (chi<1).

It does not cover Shen’s full critical threshold, which can allow (chige1). There the elementary global invariant box fails for the scalar reason in part (d).

### 3. Monotone/comparison construction

The resolvent itself is order preserving:

[

fle gimplies Rfle Rg.

]

The full map

[

umapsto-partial_xleft(u^mpartial_xR(u^gamma)right)

]

is not order preserving. Its derivative and divergence structure prevent a cooperative scalar comparison principle between two arbitrary solutions. Therefore monotone iteration does not give an obvious global solution for the stated parameter range.

### Recommended Lean route

For a classical BUC theorem, the lowest-risk architecture is:

```plain text
BUC heat semigroup and resolvent bounds
  -> local mild fixed point on a sup-norm ball
  -> uniqueness and restart
  -> maximal solution + sup-norm blow-up alternative
  -> Shen's weighted local-Lp / resolver-gradient / semigroup estimate
  -> boundedness on [0,Tmax)
  -> Tmax = infinity.
```

The continuation theorem is small and reusable. The difficult mathematics remains exactly where Shen places it: the a-priori bootstrap.

---

## (d) Critical exponent and failure of the usual scalar ceiling for χ ≥ 1

Expand the chemotaxis divergence using

[

v_{xx}=v-u^gamma:

]

[

-chi(u^mv_x)_x

=-chi m u^{m-1}u_xv_x+χu^m(u^gamma-v).

tag{8}

]

Since (vge0),

[

chi u^m(u^gamma-v)lechi u^{m+gamma}.

]

At an upper-contact/maximum-principle argument, the drift-gradient term in (8) vanishes because (u_x=0), and diffusion has the favorable sign. The resulting scalar upper equation is

[

U'=Uleft(1-U^alpha+χU^{m+gamma-1}right).

tag{9}

]

A positive constant ceiling (Uequiv M) for this scalar worst-case comparison requires

[

1-M^alpha+χM^{m+gamma-1}le0.

tag{10}

]

Let

[

beta=m+gamma-1.

]

- If (alpha>beta), then the left side of (10) tends to (-infty) as (Mtoinfty); a large ceiling exists.

- If (alpha=beta), (10) becomes

A time-dependent scalar envelope is not a substitute for boundedness: when (chi=1), the worst-case equation contains (U'=U), giving exponential growth; when (chi>1), it contains the superlinear positive term ((chi-1)U^{alpha+1}), whose equality ODE blows up in finite time.

### Important qualification

The spatially constant pair

[

bar u=M,qquad bar v=M^gamma

]

has zero chemotactic flux and satisfies

[

0ge M(1-M^alpha)

]

for (Mge1). Thus it is a formal constant supersolution pair. The obstacle is that the chemotaxis system is not cooperative, so one cannot compare an arbitrary solution with this pair merely from (u_0le M). At a first contact with the actual solution, its actual resolver (v) can be much smaller than (M^gamma), leaving the adverse term

[

chi M^m(M^gamma-v)>0.

]

So the rigorous statement is:

For (alpha=m+gamma-1) and (chige1), there is no bounded constant supersolution for the decoupled scalar maximum-principle envelope based only on (vge0). This does not mean that no formal constant pair supersolution exists.

The paper’s critical threshold can genuinely include (chige1). For example,

[

m=gamma=2,qquad alpha=3

]

gives

[

minleft{frac{2m-1}{m-1},

frac{m+gamma-1}{gamma-1}right}=3,

]

so (1lechi<3) is allowed. Shen’s weighted-local-(L^P) bootstrap is therefore doing real work beyond the elementary ceiling argument.

---

## Lean-facing decomposition

The continuation layer can be kept independent of the difficult weighted estimates:

```javascript
structure BUCLocalWellposednessData where
  local_exists_on_ball :
    ∀ R > 0, ∃ τ > 0, ∀ u₀,
      0 ≤ u₀ -> ||u₀||∞ ≤ R ->
      ∃! u, MildSolutionOn τ u₀ u

  restart : ...
  uniqueness_on_overlap : ...
```

Then prove:

```javascript
theorem finite_maximal_time_implies_supNorm_blowup
    (S : MaximalBUCSolution u₀) :
    S.Tmax < ∞ ->
      Filter.limsup (fun t => ||S.u t||∞) (nhdsWithin S.Tmax (Iio S.Tmax)) = ∞
```

or, more conveniently for downstream use:

```javascript
theorem global_of_supNorm_bounded_before_maximalTime
    (S : MaximalBUCSolution u₀)
    (hM : ∃ M, ∀ t, 0 < t -> t < S.Tmax -> ||S.u t||∞ ≤ M) :
    S.Tmax = ∞
```

The second formulation avoids formalizing extended-real limsup before it is needed. It is exactly the implication consumed by Shen’s Step 3.

## References

- W. Shen, arXiv:2605.04401, Proposition 1.1 and §3.1, especially Steps 1–3.

- R. B. Salako and W. Shen, JDE 262 (2017), 5635–5690, Theorem 1.1 and §3.

- R. B. Salako and W. Shen, Corrigendum, JDE 376 (2023), 773–775.

- D. Henry, Geometric Theory of Semilinear Parabolic Equations, LNM 840, Springer, 1981, existence/uniqueness chapter, pp. 47–81.

- H. Amann, “Quasilinear parabolic problems via maximal regularity”, Adv. Differential Equations 10 (2005), 1081–1110.