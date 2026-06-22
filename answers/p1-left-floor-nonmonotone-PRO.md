# Q226: non-monotone left floor for the Paper 1 traveling wave

## Executive verdict

The strong maximum principle gives only

```text
U >= 0, U not identically 0  ==>  U(x) > 0 for every fixed x.
```

It does **not** by itself give

```text
exists delta > 0, exists A, forall x <= A, delta <= U(x).
```

A Harnack/compactness contradiction of the form `U(x_n) -> 0`, `x_n -> -infty`, only gives a translated limit which is the zero stationary solution.  Since zero is itself an admissible nonnegative limit of the equation, this is not a contradiction unless one adds a mechanism excluding zero left-clusters.

There is, however, a short non-monotone route to the left floor which is often enough and is much weaker than proving the full left limit `U(x) -> U_-`:

```text
small-density coercivity of the stationary equation
+ c > 0 one-sided drift
+ bounded U'
+ pointwise positivity at one anchor point
--------------------------------------------------
StrictlyPositiveAtLeft U.
```

For a chemotaxis flux of the form `partial_x(S(U) V')`, this route works whenever, at small density, the equation can be written as

```text
U'' + B(x) U' + Q(x) U = 0
```

with

```text
B(x) >= b0 > 0,
Q(x) >= q0 > 0
```

on the set where `0 < U <= eta`.  For the common power flux `S(U)=U^m`, this is automatic for both attractive and repulsive signs if `m > 1` and the true linear growth at zero is positive.  For the nondegenerate flux `m=1`, it requires a genuine smallness/sign condition.  For `m<1`, it generally fails.

If this small-density coercivity is not available, the present barrier trap does not contain enough information to force a floor.  Then the missing input is not monotonicity, but a **uniform persistence/no-zero-left-cluster theorem**, often proved as part of a full left-tail stabilization/Liouville theorem.

## 0. Notation and the one coefficient that matters

Write the stationary equation schematically as

```text
U'' + c U' - lambda U + a U - b U^(1+alpha)
  - chi * partial_x(S(U) V'[U]) = 0,                    (E)
```

where `c > 0`, `b > 0`, `alpha > 0`, and `V = V[U]` is the bounded elliptic chemical resolver.

Let

```text
rho := the coefficient of U in the equation after expanding the local linear part.
```

For the literal displayed equation above, `rho = a - lambda`.  If `lambda` is only an artificial Green-resolvent shift and the true unshifted profile equation is

```text
U'' + cU' + aU - bU^(1+alpha) - chi * partial_x(S(U)V') = 0,
```

then `rho = a`.  Every floor argument below needs

```text
rho > 0.
```

This is the statement that the zero state is linearly repelling in the left-tail ODE direction.  If `rho <= 0`, the local reaction does not force a positive floor.

Assume the Schauder construction supplies the usual global bounds

```text
0 < U(x) <= M,
|U'(x)| <= M1,
|V'(x)| <= K1,
|V''(x)| <= K2.
```

The elliptic resolver gives such `K1,K2` from `M`.  For example, if

```text
-d_V V'' + mu V = nu U^gamma
```

on the line, then the positive Green kernel gives constants of the form

```text
||V||_infty  <= (nu/mu) M^gamma,
||V'||_infty <= C1(d_V,mu,nu) M^gamma,
||V''||_infty <= C2(d_V,mu,nu) M^gamma.
```

The exact constants do not matter for the floor theorem; only finiteness does.

## 1. Why the plain Harnack/SMP contradiction does not close

Assume, toward contradiction, that

```text
x_n -> -infty,
U(x_n) -> 0.
```

Set

```text
U_n(y) := U(x_n + y),
V_n(y) := V[U](x_n + y).
```

By the global `C^2`/Green bounds and Arzela-Ascoli, a subsequence converges locally.  Since `U_n(0) -> 0` and `U_n >= 0`, a local Harnack inequality typically improves this to

```text
U_n -> 0 locally uniformly.
```

The elliptic kernel is integrable, so compact-tail splitting gives

```text
V_n -> 0,
V_n' -> 0,
V_n'' -> 0
```

locally.  The limit is therefore the stationary solution

```text
W == 0.
```

The strong maximum principle says: if a nonnegative limit is not identically zero, then it is strictly positive.  But here the limit has `W(0)=0`, hence the SMP only says `W == 0`.  That is not contradictory: zero is an equilibrium of the limiting equation.

So the Harnack route proves only:

```text
a zero left-cluster would be locally zero after translation.
```

It does not prove that zero left-clusters are impossible.

A rescaling argument also does not automatically contradict anything.  If `epsilon_n := U(x_n)` and

```text
H_n(y) := U(x_n+y) / epsilon_n,
```

then, under favorable estimates, one may extract a positive solution of the linearized equation

```text
H'' + c H' + rho H = 0,
H(0)=1.
```

For KPP wave speeds this linear equation has positive exponential solutions on the line, though they are unbounded at `-infty`.  Local convergence alone therefore still gives no contradiction.

Zero-number, sliding, and Hamiltonian/energy routes have the same problem in this nonlocal setting:

* sliding compares two translated nonlocal systems and needs a separately proved comparison principle for the coupled chemotaxis operator;
* zero-number arguments need a scalar sign-controlled difference equation, which the chemotaxis source does not provide in general;
* weighted energy identities in the moving frame require integrability that the barrier trap does not supply, and the chemotaxis divergence is not a coercive scalar gradient term in this formulation.

## 2. The short route: a no-small-left-pocket lemma

The useful observation is that one does not need the whole left limit to prove a floor.  It suffices to prove that `U` cannot enter a sufficiently small density region anywhere to the left of one point where `U` is larger than that threshold.

### 2.1 Rewriting the equation in the small-density region

For a general chemotaxis sensitivity `S`, expand the divergence term:

```text
partial_x(S(U) V') = S'(U) U' V' + S(U) V''.
```

On the set where `U > 0`, equation `(E)` becomes

```text
U'' + B(x) U' + Q(x) U = 0,                             (L)
```

where

```text
B(x) := c - chi * S'(U(x)) * V'(x),

Q(x) := rho - b * U(x)^alpha
            - chi * (S(U(x)) / U(x)) * V''(x).
```

For the power flux `S(U)=U^m`, this is

```text
B(x) = c - chi * m * U(x)^(m-1) * V'(x),

Q(x) = rho - b * U(x)^alpha
          - chi * U(x)^(m-1) * V''(x).
```

The required small-density coercivity hypothesis is:

```text
exists eta > 0, exists b0 > 0, exists q0 > 0,
forall x,
  0 < U(x) <= eta
  -> b0 <= B(x) and q0 <= Q(x).                         (SDC)
```

This is the exact local condition that replaces monotonicity.

### 2.2 The no-small-left-pocket theorem

**Theorem.**  Let `U` be positive, `C^2`, and let `|U'|` be bounded on the line.  Suppose that whenever `0 < U <= eta`, `U` satisfies `(L)` with `B >= b0 > 0` and `Q >= q0 > 0`.  Then `U` is strictly positive at left:

```text
exists delta > 0, exists A,
forall x <= A, delta <= U(x).
```

**Proof.**

Choose any anchor point `A` with `U(A) > 0`.  Such a point exists by the strong maximum principle.  Choose

```text
delta < min(eta, U(A)).
```

Assume there is some `x <= A` with `U(x) < delta`.  Consider the connected component of

```text
Omega_delta := {x <= A : U(x) < delta}
```

that contains this point.  Since `U(A) > delta`, this component has a finite right endpoint `r < A` with

```text
U(r) = delta,
U(x) < delta on the component to the left of r.
```

There are two cases.

### Case 1: finite small pocket

The component is a finite interval `(l,r)`.  Then

```text
U(l)=U(r)=delta,
0 < U < delta on (l,r).
```

By continuity, `U` attains a minimum at some `z in (l,r)`.  At this point,

```text
U'(z)=0,
U''(z) >= 0,
0 < U(z) < delta <= eta.
```

Using `(L)` and `Q(z) >= q0 > 0`,

```text
0 = U''(z) + B(z)U'(z) + Q(z)U(z)
  = U''(z) + Q(z)U(z)
  >= q0 U(z)
  > 0,
```

contradiction.

### Case 2: left-unbounded small pocket

The component is `(-infty,r)`.  Thus

```text
0 < U(x) < delta <= eta for all x < r,
U(r)=delta.
```

On `(-infty,r)`, set

```text
p(x) := exp( integral_r^x B(s) ds ).
```

Because `B >= b0 > 0`, for `x <= r`,

```text
0 < p(x) <= exp(b0*(x-r)) -> 0 as x -> -infty.
```

Since `U'` is bounded,

```text
p(x) U'(x) -> 0 as x -> -infty.
```

Multiplying `(L)` by `p` gives

```text
(p U')' = -p Q U < 0.
```

Integrating from `-infty` to `r`,

```text
p(r) U'(r) - lim_{x -> -infty} p(x)U'(x)
  = - integral_{-infty}^r p(s) Q(s) U(s) ds < 0.
```

Since `p(r)=1`, this gives

```text
U'(r) < 0.                                                (1)
```

But `U(x) < delta = U(r)` for all `x < r` near `r`, so the left derivative at `r` must satisfy

```text
U'(r) = lim_{h downarrow 0} (U(r)-U(r-h))/h >= 0,           (2)
```

contradicting `(1)`.

Therefore `Omega_delta` is empty, so

```text
forall x <= A, delta <= U(x).
```

This proves `StrictlyPositiveAtLeft U`.  No monotonicity and no full limit `U -> U_-` were used.

## 3. When the small-density coercivity holds

### 3.1 Power flux `S(U)=U^m`

Using the elliptic bounds `|V'| <= K1`, `|V''| <= K2`, the small-density coefficients satisfy, whenever `U <= eta`,

```text
B(x) >= c - |chi| * m * eta^(m-1) * K1,

Q(x) >= rho - b * eta^alpha - |chi| * eta^(m-1) * K2.
```

Hence `(SDC)` follows if `eta` is chosen so that

```text
|chi| * m * eta^(m-1) * K1 <= c/2,

b * eta^alpha + |chi| * eta^(m-1) * K2 <= rho/2.
```

This can always be done if

```text
m > 1,
rho > 0.
```

Thus, for density-degenerate chemotaxis flux `U^m V_x` with `m>1`, the left floor is only a few bricks:

```text
SMP positivity
+ elliptic C^2 bounds for V
+ small-density coercivity
+ no-small-left-pocket lemma
--------------------------------------------------
StrictlyPositiveAtLeft U.
```

This works for both attractive and repulsive chemotaxis.  The sign of `chi` is irrelevant because the chemotaxis coefficients vanish like `U^(m-1)` at low density.

### 3.2 Nondegenerate flux `m=1`

For `S(U)=U`, the coefficients are

```text
B(x) = c - chi V'(x),
Q(x) = rho - b U(x)^alpha - chi V''(x).
```

The smallness no longer improves as `U -> 0`.  A safe sign-free sufficient condition is

```text
c   > |chi| K1,
rho > |chi| K2.
```

Then choose `eta` small enough that

```text
b eta^alpha <= (rho - |chi|K2)/2.
```

With sign information one can weaken this.  For attractive chemotaxis `chi > 0`, the bad parts are the positive parts of `V'` and `V''`:

```text
c   > chi * sup_x V'(x),
rho > chi * sup_x V''(x).
```

For repulsive chemotaxis `chi < 0`, the bad parts are the negative parts:

```text
c   > |chi| * sup_x (-V'(x)),
rho > |chi| * sup_x (-V''(x)).
```

Without monotonicity, however, the trap alone does not give a useful sign for `V'` or `V''`; one normally falls back on the absolute bounds.  Therefore the attractive/repulsive sign by itself is not enough.  What matters is whether the sign-bad parts of `V'` and `V''` are small enough compared with `c` and `rho`.

### 3.3 Singular or sublinear flux `m<1`

If `S(U)=U^m` with `m<1`, then

```text
S(U)/U = U^(m-1) -> +infty
```

as `U -> 0`.  The chemotaxis contribution can dominate the positive linear reaction.  The constant-threshold argument is then unavailable unless the model has some additional cancellation, sign theorem, or a different sensitivity law.

## 4. What is the better lower barrier?

The better barrier is not another copy of

```text
phi(x) = e^{-kappa x} - D e^{-kappatilde x},
```

because that function becomes negative as `x -> -infty` and cannot yield a positive floor.

The useful barrier is the **constant threshold**

```text
underline U(x) == delta.
```

But it must be used correctly.  A positive constant cannot be launched by ordinary comparison on `(-infty,A]` unless one already knows

```text
underline U <= U at -infty,
```

which is exactly the desired floor.  Thus a naive half-line comparison proof with `underline U == delta` is circular.

The non-circular use is the no-small-pocket argument above:

```text
U may not cross below the constant level delta on the left,
```

because every hypothetical sublevel component either has an interior minimum or is a left-unbounded pocket, and both contradict the linearized equation with `B>0`, `Q>0`.

For attractive and repulsive signs:

* if `S'(s) -> 0` and `S(s)/s -> 0` as `s downarrow 0`, e.g. `S(s)=s^m`, `m>1`, the constant threshold works for both signs;
* if `S(s)=s`, the constant threshold works only under the sign/smallness inequalities in Section 3.2;
* if the bad chemotaxis coefficient is not controlled, there is no positive lower barrier supplied by the current trap.

So the correct answer to the barrier question is:

```text
Use the constant threshold delta, not as a boundary comparison subsolution,
but as a forbidden small-density level under the no-small-left-pocket lemma.
```

## 5. If small-density coercivity is absent

If `(SDC)` cannot be verified, the barrier trap

```text
0 < U <= upper,
U >= phi,
phi -> -infty at -infty
```

does not imply a left floor.  In that case the missing theorem is not an elementary maximum principle; it is a persistence/stabilization theorem.

The key logical equivalence is:

```text
StrictlyPositiveAtLeft U

iff

there is no sequence x_n -> -infty with U(x_n) -> 0.
```

Indeed, if the floor fails, then for every `n` there is `x_n <= -n` with `U(x_n) < 1/n`; conversely, such a sequence violates every proposed floor.

Thus any proof of the floor must exclude zero left-clusters.  A positive-stationary Liouville theorem alone usually says

```text
if W is bounded, entire, stationary, and uniformly positive,
then W == U_-.
```

That theorem does **not** exclude a translated limit `W == 0`.  Therefore, for the floor, the needed non-monotone input is one of the following stronger statements:

```text
NoZeroLeftCluster U:
  for every x_n -> -infty,
  no locally convergent translate U(x_n + .) has limit 0;
```

or a full left-tail theorem:

```text
LeftTailStabilization:
  bounded positive stationary profile with the right tail condition
  satisfies U(x) -> U_- as x -> -infty.
```

The full left-tail theorem immediately gives the floor by taking `delta = U_-/2` far enough left.  But if the only Liouville theorem available assumes a positive floor, using it to prove the floor would be circular.

## 6. Clean non-monotone Liouville/stabilization chain

If the project chooses the full stabilization route, the clean formal chain is this.

### 6.1 Compactness of left translates

For every sequence `s_n -> +infty`, define

```text
U_n(y) := U(y - s_n).
```

The global trap, elliptic bounds, and stationary equation give local `C^2` compactness.  Hence a subsequence converges locally to some `W`.

### 6.2 Closedness of the nonlocal equation

The whole-line elliptic resolver is translation equivariant:

```text
V[U(. - s)](y) = V[U](y - s).
```

It is also continuous under bounded locally uniform convergence: if `U_n -> W` locally uniformly and `0 <= U_n <= M`, then compact-tail splitting for the Green kernel gives

```text
V[U_n]  -> V[W],
V'[U_n] -> V'[W],
V''[U_n] -> V''[W]
```

locally.  Therefore every left-translate limit is a nonnegative entire stationary solution.

### 6.3 Strong maximum principle dichotomy

For every such limit `W`,

```text
W >= 0,
StationaryProfile W.
```

The strong maximum principle gives the dichotomy

```text
W == 0  or  W(x) > 0 for every x.
```

This is where the floor problem lives: one must rule out the `W == 0` alternative.

### 6.4 No-zero-left-cluster / persistence

This is the missing non-monotone theorem:

```text
NoZeroLeftCluster U:
  no left-translate cluster limit of U is identically zero.
```

It can be proved by the small-density coercivity theorem above.  Alternatively, it can be imported from a parabolic uniform persistence or spreading theorem in the moving frame.

### 6.5 Positive stationary Liouville

Once `W` is known to be nonzero, the SMP gives `W > 0`.  If the project has a stationary Liouville theorem

```text
PositiveStationaryLiouville:
  every bounded positive entire stationary solution is U_-,
```

then every left-cluster limit is `U_-`.

The cleanest way to prove this Liouville theorem without monotonicity is from parabolic stabilization.  Assume a theorem of the form

```text
MovingFrameStabilization:
  every global bounded uniformly positive solution of the moving-frame
  parabolic-elliptic problem converges uniformly to U_- as t -> +infty.
```

Given a stationary `W`, define the time-independent parabolic solution

```text
u(t,x) = W(x),
z(t,x) = V[W](x).
```

The stabilization theorem yields

```text
||nu(t,.) - U_-||_infty -> 0.
```

But the left side is independent of `t`, so it is already zero.  Hence

```text
W == U_-.
```

### 6.6 Left limit and floor

If every left-translate cluster is `U_-`, then

```text
U(x) -> U_- as x -> -infty.
```

The proof is the standard sequential contradiction: if not, there are `epsilon > 0` and `x_n -> -infty` with

```text
|U(x_n) - U_-| >= epsilon.
```

Translate by `x_n`, extract a cluster `W`, and evaluate at `0`.  The cluster must be `U_-`, contradicting the inequality.

Finally, since `U_- > 0`, choose `A` such that

```text
x <= A -> |U(x)-U_-| < U_-/2.
```

Then

```text
x <= A -> U(x) >= U_-/2.
```

This gives `StrictlyPositiveAtLeft U`.

## 7. Lean-formalizable statement chain

### 7.1 The target

```lean
def StrictlyPositiveAtLeft (U : Real -> Real) : Prop :=
  exists delta A : Real,
    0 < delta /\ forall x : Real, x <= A -> delta <= U x
```

### 7.2 Sequential equivalent of the floor

This is a very useful lemma because it identifies exactly what must be ruled out.

```lean
def NoZeroSequenceAtLeft (U : Real -> Real) : Prop :=
  forall xseq : Nat -> Real,
    Tendsto xseq atTop atBot ->
      not (Tendsto (fun n => U (xseq n)) atTop (nhds 0))

theorem strictlyPositiveAtLeft_iff_noZeroSequence
    (hpos : forall x, 0 < U x) :
    StrictlyPositiveAtLeft U <-> NoZeroSequenceAtLeft U := by
  -- forward direction: a left floor prevents convergence to 0.
  -- reverse direction: if no floor, choose x_n <= -n with U x_n < 1/(n+1).
  ...
```

The proof uses no PDE.

### 7.3 Small-density coefficients

For a power flux `S(U)=U^m`:

```lean
def ChemDriftCoeff (p : Params) (U V : Real -> Real) (x : Real) : Real :=
  p.c - p.chi * p.m * (U x)^(p.m - 1) * deriv V x

def SmallDensityCoeff (p : Params) (U V : Real -> Real) (x : Real) : Real :=
  p.rho - p.b * (U x)^p.alpha
        - p.chi * (U x)^(p.m - 1) * iteratedDeriv 2 V x
```

For a general sensitivity `S`, replace these by

```lean
p.c - p.chi * deriv S (U x) * deriv V x

p.rho - p.b * (U x)^p.alpha
      - p.chi * (S (U x) / U x) * iteratedDeriv 2 V x
```

on the positive set.

### 7.4 Small-density coercivity predicate

```lean
def SmallDensityCoercive
    (p : Params) (U V : Real -> Real) : Prop :=
  exists eta b0 q0 : Real,
    0 < eta /\ 0 < b0 /\ 0 < q0 /\
    forall x : Real,
      0 < U x -> U x <= eta ->
        b0 <= ChemDriftCoeff p U V x /\
        q0 <= SmallDensityCoeff p U V x
```

### 7.5 The one-sided pocket theorem

```lean
theorem strictPosAtLeft_of_smallDensityCoercive
    (hpos : forall x, 0 < U x)
    (hC2 : ContDiff Real 2 U)
    (hderiv_bdd : Bounded (Set.range (deriv U)))
    (heq_small :
      forall x,
        U x <= eta ->
          secondDeriv U x
          + B x * deriv U x
          + Q x * U x = 0)
    (hB : forall x, U x <= eta -> b0 <= B x)
    (hQ : forall x, U x <= eta -> q0 <= Q x)
    (heta : 0 < eta)
    (hb0 : 0 < b0)
    (hq0 : 0 < q0) :
    StrictlyPositiveAtLeft U := by
  -- Choose A with U A > 0 and delta < min eta (U A).
  -- If a sublevel component {x <= A | U x < delta} exists:
  --   finite component -> interior minimum contradiction.
  --   left-unbounded component -> integrating-factor contradiction.
  ...
```

For the actual formalization, it is cleaner to split the proof into two lemmas:

```lean
theorem no_finite_small_component
    (hlr : l < r)
    (hleft : U l = delta)
    (hright : U r = delta)
    (hsmall : forall x, l < x -> x < r -> U x < delta)
    (heq : forall x, l < x -> x < r ->
      secondDeriv U x + B x * deriv U x + Q x * U x = 0)
    (hQ : forall x, l < x -> x < r -> q0 <= Q x)
    (hq0 : 0 < q0)
    (hpos : forall x, 0 < U x) : False := by
  -- Weierstrass gives an interior minimizer z.
  -- At z: U'=0, U''>=0, Q U > 0.
  ...

theorem no_left_unbounded_small_component
    (hr : forall x, x < r -> U x < delta)
    (hUr : U r = delta)
    (heq : forall x, x < r ->
      secondDeriv U x + B x * deriv U x + Q x * U x = 0)
    (hB : forall x, x < r -> b0 <= B x)
    (hQ : forall x, x < r -> q0 <= Q x)
    (hb0 : 0 < b0)
    (hq0 : 0 < q0)
    (hderiv_bdd : Bounded (Set.range (deriv U)))
    (hpos : forall x, 0 < U x) : False := by
  -- p x = exp (integral r x B)
  -- (p * U')' = -p * Q * U
  -- p U' -> 0 at -infty since B >= b0 and U' bounded
  -- integrate to get U'(r) < 0
  -- but U(x) < delta = U(r) for x<r gives U'(r) >= 0
  ...
```

### 7.6 Verifying coercivity from elliptic bounds

For `m>1`:

```lean
theorem smallDensityCoercive_of_powerFlux_superlinear
    (hm : 1 < p.m)
    (hrho : 0 < p.rho)
    (hV1 : forall x, abs (deriv V x) <= K1)
    (hV2 : forall x, abs (iteratedDeriv 2 V x) <= K2) :
    exists eta b0 q0,
      0 < eta /\ 0 < b0 /\ 0 < q0 /\
      forall x,
        0 < U x -> U x <= eta ->
          b0 <= ChemDriftCoeff p U V x /\
          q0 <= SmallDensityCoeff p U V x := by
  -- choose eta so |chi|*m*eta^(m-1)*K1 <= c/2
  -- and b*eta^alpha + |chi|*eta^(m-1)*K2 <= rho/2
  -- set b0=c/2, q0=rho/2
  ...
```

For `m=1`, state a separate theorem with the smallness assumptions

```lean
abs p.chi * K1 < p.c,
abs p.chi * K2 < p.rho.
```

### 7.7 If using the full stabilization/Liouville route

```lean
def LeftTranslateLimit
    (U W : Real -> Real) : Prop :=
  exists s : Nat -> Real, exists phi : Nat -> Nat,
    Tendsto s atTop atTop /\ StrictMono phi /\
    LocallyUniformConverges
      (fun n y => U (y - s (phi n))) W

def NoZeroLeftCluster (p : Params) (U : Real -> Real) : Prop :=
  forall W,
    LeftTranslateLimit U W ->
    StationaryProfile p W ->
      W != fun _ => 0

def PositiveStationaryLiouville (p : Params) (Ustar : Real) : Prop :=
  forall W,
    StationaryProfile p W ->
    BoundedProfile W ->
    (forall x, 0 < W x) ->
      W = fun _ => Ustar

theorem stationaryLiouville_of_parabolicStabilization
    (hstab : MovingFrameParabolicStabilization p Ustar) :
    PositiveStationaryLiouville p Ustar := by
  -- turn stationary W into u(t,x)=W(x)
  -- apply stabilization
  -- the sup-norm distance is constant in t and tends to 0
  ...

theorem tendsto_atBot_of_noZeroCluster_and_liouville
    (hcompact : LeftTranslateCompactness U)
    (hclosed : LeftTranslateClosed p U)
    (hsmp : StationarySMPDichotomy p)
    (hnozero : NoZeroLeftCluster p U)
    (hliouv : PositiveStationaryLiouville p Ustar) :
    Tendsto U atBot (nhds Ustar) := by
  -- sequential contradiction, extract a left-translate limit W
  -- hclosed: W is stationary and bounded
  -- hsmp + hnozero: W > 0 everywhere
  -- hliouv: W = Ustar
  -- evaluate at y=0 and contradict the separated sequence
  ...

theorem strictPosAtLeft_of_tendsto_atBot
    (hUstar : 0 < Ustar)
    (hlim : Tendsto U atBot (nhds Ustar)) :
    StrictlyPositiveAtLeft U := by
  -- take delta = Ustar/2
  ...
```

This chain is non-monotone and Lean-clean, but it is heavier than the small-density route because it requires proving or importing `NoZeroLeftCluster` and `PositiveStationaryLiouville`.

## 8. Bottom line for the non-monotone fixed-source profile

The shortest rigorous route is:

```text
1. Prove U > 0 pointwise by the strong maximum principle.
2. Obtain global bounds on V', V'', and U' from the elliptic resolver and the trap.
3. Verify small-density coercivity:
      U'' + B U' + Q U = 0,
      B >= b0 > 0,
      Q >= q0 > 0
   whenever 0 < U <= eta.
4. Apply the no-small-left-pocket lemma.
```

This proves `StrictlyPositiveAtLeft U` directly and does not require spatial monotonicity or the full left limit `U -> U_-`.

For `S(U)=U^m` with `m>1` and positive true linear growth `rho>0`, this is a few-brick theorem and works for both attractive and repulsive chemotaxis.  For `m=1`, it is still a few-brick theorem only under the explicit smallness/sign inequalities comparing the bad chemotaxis coefficients with `c` and `rho`.  For `m<1`, or for `m=1` without those inequalities, the current barrier trap gives no positive floor; then the floor must be supplied by a separate persistence/stabilization theorem, essentially the hard left-tail theorem.

So the answer is:

```text
No, SMP/Harnack alone does not give the floor.
Yes, there is a shorter non-monotone route if small-density coercivity holds.
The better barrier is the constant threshold delta used through a no-small-pocket argument.
If small-density coercivity fails, the missing brick is genuinely a no-zero-left-cluster / left-tail stabilization theorem, not monotonicity.
```
