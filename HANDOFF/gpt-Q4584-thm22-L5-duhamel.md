ANSWER Q4584 713f1668

# Verdict

The clean L5 theorem is a restart-time weighted Duhamel contraction for the full diagonalized linearized operator, not for the zero-mode-removed Neumann heat semigroup.

There is one important correction to the proposed mechanism:

- the singular factor ((t-s)^{-vartheta}) is integrable when (0<vartheta<1), so it does not obstruct the fixed point at time zero;

- the false (t=0) conclusion comes from asking for a strong (X^{s+vartheta}) or (C^1) estimate while assuming smallness only in a weaker initial norm such as sup norm or (X^s);

- translating the autonomous equation from (0) to (t_0) does not shrink the contraction constant.  The role of (t_0>0) is to provide parabolic regularization and, in the global-stability chain, basin entry:

If the initial perturbation is already small in the strong phase norm, the same contraction works with (t_0=0).  For weak/sup-small data, the correct conclusion is eventual and the initial smallness threshold depends on the chosen positive restart time.

Repository audit: IntervalDomainSectorial.lean already separates the proved diagonal/spectral-decay part from the missing nonlinear orbit comparison, but its current IntervalDomainSpectralSemigroupOrbitBoundRaw is expressed using the pure Neumann heat semigroup with the zero mode removed.  For the present positive equilibrium, that is the wrong final multiplier: the zero mode decays at (aalpha), and every mode uses the full rate (-sigma_k).  Reuse the generic diagonal machinery in PDE/SectorialOperator.lean, the weights in PDE/FractionalPowerSpace.lean, and the singular Bochner-integral proof pattern in Wiener/WeightedL1SelfMap.lean.

# 1. Linearized diagonal semigroup and an explicit gap

Put

[

A:=aalpha>0,

qquad

lambda_k=(kpi)^2,

qquad

kappa:=chi_0gammanu u_^gamma(1+v_)^{-beta}.

]

The mode equation is

[

widehat w_k'=sigma_kwidehat w_k+widehat{N(w)}_k,

qquad

sigma_k=-A-lambda_k+frac{kappalambda_k}{lambda_k+mu}.

]

Write the positive decay multiplier

[

d_k:=-sigma_k

]

Assume (0lekappa<(sqrtmu+sqrt A)^2).  A convenient continuous-spectrum lower bound is

[

delta_{rm lin}:=

begin{cases}

A,&kappalemu,\[2mm]

A-(sqrtkappa-sqrtmu)^2,&mu<kappa.

end{cases}

]

Then (delta_{rm lin}>0) and

[

forall kinmathbb N,qquad d_kgedelta_{rm lin},

qquad sigma_kle-delta_{rm lin}.

]

The proof is a one-variable calculation.  For

[

d(lambda)=A+lambda-frac{kappalambda}{lambda+mu},

]

if (kappalemu), then (d'(lambda)=1-kappamu/(lambda+mu)^2ge0), so the minimum is (d(0)=A).  If (kappa>mu), the continuous minimum occurs at

[

lambda_*=sqrt{kappamu}-mu

]

and equals

[

d(lambda_*)=A-(sqrtkappa-sqrtmu)^2.

]

The discrete cosine spectrum can have a larger gap; δlin is a simple uniform lower bound that avoids minimizing over natural numbers.

For smoothing, one also needs growth comparable to (1+lambda_k).  Let

[

Lambda:=max{1,2kappa},

qquad

c_*:=minleft{frac14,frac{delta_{rm lin}}{1+Lambda}right}>0.

]

Then

[

d_kge c_*(1+lambda_k)

]

for every (k).  For (lambda_kleLambda), use (d_kgedelta_{rm lin}); for (lambda_kgeLambda), use

[

d_kge A+lambda_k-kappagelambda_k/2ge(1+lambda_k)/4.

]

Define the diagonal semigroup

[

(S_L(t)c)_k=e^{-d_k t}c_k.

]

No projection away from (k=0) is used.

# 2. Exact eliminated nonlinearity

Let

[

mathcal R h:=(mu-partial_{xx,N})^{-1}(nu h),

]

so that the elliptic component associated with (u_*+w) is

[

V(w):=mathcal Rbig((u_*+w)^gammabig),

qquad

v_=fracnumu u_^gamma.

]

Set

[

Z(w):=V(w)-v_*,

qquad

Z_1(w):=mathcal Rbig(gamma u_*^{gamma-1}wbig),

qquad

Z_2(w):=Z(w)-Z_1(w),

]

and

[

q(w):=(1+V(w))^{-beta},

qquad q_:=(1+v_)^{-beta}.

]

For

[

f(u):=u(a-bu^alpha),

]

one has (f(u_)=0) and (f'(u_)=-A).  The perturbation equation is exactly

[

w_t=Lw+N(w),

]

where

[

Lw=w_{xx}-chi_0u_q_,partial_{xx}Z_1(w)-Aw

]

and

[

boxed{

N(w)=

-chi_0partial_x!left[

right]

+f(u_*+w)+Aw.}

]

This is the shortest exact definition and is the best Lean definition: linearization and remainder are separated by literal subtraction.

For estimates, expand the flux remainder as

[

begin{aligned}

&(u_+w)q(w)partial_xZ(w)-u_q_*partial_xZ_1(w)\

&quad=q_*w,partial_xZ_1(w)

end{aligned}

]

Thus

[

begin{aligned}

N_{rm chem}(w)&=-chi_0partial_xBig(

&hspace{42mm} +(u_+w)(q(w)-q_)partial_xZ(w)

Big),\

N_{rm log}(w)&=f(u_*+w)+Aw.

end{aligned}

]

Every term is quadratic or higher:

- (Z_1) is linear;

- (Z_2(w)=O(w^2)) by the second-order Taylor remainder of (rmapsto r^gamma);

- (q(w)-q_*=O(w)), since the resolver is linear after the Nemytskii source and (rmapsto(1+r)^{-beta}) is smooth on ([0,infty));

- (N_{rm log}(w)=O(w^2)).

The positive equilibrium is essential here: on a sufficiently small phase-space ball, (u_+wge u_/2), so arbitrary real powers (alpha,gamma) have uniformly bounded first and second derivatives.  There is no zero-floor singularity.

# 3. Fractional coefficient spaces and the quadratic estimate

Use the repository convention

[

|c|{X^r}^2:=sum{k=0}^infty

]

This is the weight fractionalPowerWeight 1 r k in PDE/FractionalPowerSpace.lean.  One unit of (r) represents two spatial derivatives, so one spatial derivative costs (1/2) unit.

Choose

[

r=s+vartheta,

qquad

frac12<vartheta<1,

qquad

r>frac34.

]

The last condition gives the one-dimensional embedding (X^rhookrightarrow C^1([0,1])).  The strict inequality (vartheta>1/2) leaves enough room for the outer divergence in the chemotaxis term.

For a local radius (rho>0), assume

[

C_{C^0,r}rhole u_*/2.

]

Then there is a finite constant (K_rho) such that, whenever

(|w|{X^r},|z|{X^r}lerho),

[

boxed{

|N(w)|{X^s}le Krho|w|_{X^r}^2,}

]

and

[

boxed{

|N(w)-N(z)|_{X^s}

le K_rho

]

A Lean-friendly decomposition of the constant is

[

K_rho=K_{rm log}(rho)+|chi_0|K_{rm chem}(rho),

]

with

[

K_{rm chem}:=C_{rm div}Big[

Big].

]

Here the named constants mean:

- Calg: multiplication in (X^r);

- Cdiv: (|partial_xF|{X^s}le C{rm div}|F|_{X^{s+1/2}});

- CZ1: the linear resolver estimate for (Z_1);

- CZ2: the quadratic resolver/Nemytskii remainder estimate for (Z_2);

- Cq: the local Lipschitz bound for (q(w)-q_*);

- CZ: the linear local bound for (Z(w));

- Klog: the second-order Taylor constant for (f).

The exact numerical value depends on the normalization chosen for the weighted mode norm, so the faithful theorem should expose Kρ; the fixed-point threshold below is exact once Kρ is fixed.

The proof order is:

```plain text
X^r algebra and C¹ embedding
→ real-power Taylor remainders on [u*/2, u*+Cρ]
→ elliptic resolver +1 X-order
→ flux product estimate
→ divergence loses 1/2 X-order
→ X^(r-1/2) ↪ X^s because ϑ ≥ 1/2.
```

# 4. Mode-wise smoothing from the scalar maximum estimate

For (0<omega<delta_{rm lin}), the diagonal semigroup satisfies

[

|S_L(t)c|{X^r}le e^{-delta{rm lin}t}|c|_{X^r}

]

and, for (t>0),

[

|S_L(t)c|_{X^{s+vartheta}}

le M_vartheta t^{-vartheta}e^{-omega t}|c|_{X^s},

]

where one may take

[

M_vartheta

=c_*^{-vartheta}

left(

right)^vartheta.

]

Indeed, (d_kge c_*(1+lambda_k)), hence

[

(1+lambda_k)^vartheta e^{-d_kt}

le c_*^{-vartheta}d_k^vartheta e^{-d_kt}.

]

Since (d_kgedelta_{rm lin}),

[

d_k-omegage(1-omega/delta_{rm lin})d_k,

]

and the scalar estimate

[

x^p e^{-xt}leleft(frac{p}{et}right)^p

]

finishes the mode bound.

This is the direct scalar instantiation of the generic diagonal semigroup in PDE/SectorialOperator.lean; it should not be routed through unitIntervalNeumannHeatSemigroupP0Compl.

# 5. The restart-time weighted fixed point

Fix a desired decay rate

[

0<delta'<delta_{rm lin}

]

and choose

[

omega:=frac{delta_{rm lin}+delta'}2.

]

On the restarted time variable (tau=t-t_0ge0), put

[

z(tau):=w(t_0+tau),

qquad z_0:=w(t_0).

]

The exact mode-wise Duhamel equation is

[

boxed{

z_k(tau)=e^{-d_ktau}(z_0)_k

]

Use the weighted trajectory norm

[

|z|{Y{delta'}}:=

sup_{tauge0}e^{delta'tau}|z(tau)|_{X^r}.

]

The convolution constant is

[

I_{vartheta,omega,delta'}

:=int_0^infty

]

For Lean, the following elementary upper bound avoids developing the Gamma identity:

[

I_{vartheta,omega,delta'}

le I_{rm easy}:=

frac1{1-vartheta}+frac1{omega-delta'}.

]

With the chosen (omega), this is

[

I_{rm easy}=rac1{1-vartheta}+rac2{delta_{rm lin}-delta'}.

]

Let

[

A_D:=M_vartheta K_rho I_{rm easy}.

]

On the closed trajectory ball (|z|{Y{delta'}}le Rlerho), the Duhamel map (Phi) satisfies

[

|Phi z|{Y{delta'}}

le |z_0|_{X^r}+A_DR^2

]

and

[

|Phi z-Phi y|{Y{delta'}}

le2A_DR|z-y|{Y{delta'}}.

]

In estimating the quadratic term, use

[

e^{-2delta'r}le e^{-delta'r};

]

this is why only (omega>delta'), rather than (omega>2delta'), is needed.

The exact convenient contraction conditions are

[

0<Rlerho,

qquad

4A_DRle1,

qquad

|z_0|_{X^r}le R/2.

]

Then (Phi) maps the ball into itself and has Lipschitz constant at most (1/2).  Banach's fixed-point theorem gives the unique tail solution in that ball and

[

boxed{

|u(t)-u_*|_{X^r}le R e^{-delta'(t-t_0)},

qquad tge t_0.}

]

A canonical radius and restart threshold are

[

R_*:=minleft{rho,frac1{4A_D}right},

qquad

varepsilon_{rm tail}:=R_*/2.

]

Thus the exact restart hypothesis is

[

boxed{

|u(t_0)-u_*|{X^r}levarepsilon{rm tail}.}

]

Because (r>3/4), coefficient embedding and elliptic resolver Lipschitz estimates yield

[

|u(t)-u_*|_{C^1}

le C_{rm out}R_*e^{-delta'(t-t_0)}.

]

## A completely explicit canonical rate

Take

[

delta'=delta_{rm lin}/2,

qquad

omega=3delta_{rm lin}/4.

]

Then

[

M_vartheta

=c_*^{-vartheta}left(frac{4vartheta}{e}right)^vartheta,

qquad

I_{rm easy}=frac1{1-vartheta}+frac4{delta_{rm lin}},

]

and

[

A_D=

]

Therefore

[

varepsilon_{rm tail}

=frac12minleft{rho,frac1{4A_D}right}

]

is an explicit sufficient restart threshold, with final rate (delta_{rm lin}/2).

# 6. What (t_0) must satisfy

There is no standalone numerical lower bound on (t_0) coming from the tail contraction.  The tail equation is autonomous, so its constants are identical after every time translation.

The exact requirement is the restart smallness condition

[

|u(t_0)-u_*|{X^r}levarepsilon{rm tail}.

]

To express it in terms of the original weak initial perturbation, one needs a finite-time smoothing/continuous-dependence bridge

[

|u(t_0)-u_*|_{X^r}

le B(t_0)|u_0-u_*|_{X^s}.

]

Then the exact initial neighborhood is

[

boxed{

|u_0-u_*|_{X^s}le

frac{varepsilon_{rm tail}}{B(t_0)}.}

]

If the available estimate is

[

B(t_0)le C_{rm sm}t_0^{-vartheta}

qquad(0<t_0le1),

]

it is sufficient to assume

[

boxed{

|u_0-u_*|_{X^s}le

frac{varepsilon_{rm tail}}{C_{rm sm}}t_0^vartheta.}

]

This explains the zero-time obstruction: the admissible weak-norm neighborhood collapses as (t_0downarrow0) when the conclusion is measured in the stronger norm.

For the global-stability L8 route, one instead has prior uniform convergence.  It supplies some large (t_0) for which the restart norm is below εtail; L5 then upgrades that basin entry to exponential convergence.  The logical order is

```plain text
uniform convergence / basin entry
→ choose t₀ with restart X^r-smallness
→ L5 tail Duhamel contraction
→ eventual exponential X^r and C¹ convergence.
```

For a self-contained local theorem from rough data, another valid implementation is a hybrid norm beginning at zero:

[

sup_{tge0}e^{delta't}|w(t)|_{X^s}

+sup_{t>0}t^vartheta e^{delta't}|w(t)|_{X^r}.

]

That theorem gives weak-norm decay from time zero and strong/C¹ decay on every ([t_0,infty)), but it still does not give a uniform strong estimate at (t=0).

# 7. Lean-facing statement

First add the corrected eventual output predicate; do not reuse the current ExponentialC1ConvergenceWith, whose quantifier includes (t=0).

```javascript
def EventualExponentialC1ConvergenceWith
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ)
    (uStar vStar t₀ C rate : ℝ) : Prop :=
  ∀ t, t₀ ≤ t →
    N.c1Distance (u t) (fun _ => uStar) +
        N.c1Distance (v t) (fun _ => vStar) ≤
      C * Real.exp (-rate * (t - t₀))
```

The pure fixed-point engine should be independent of chemotaxis:

```javascript
structure QuadraticTailDuhamelData
    (X₀ X₁ : Type*)
    [NormedAddCommGroup X₀] [NormedSpace ℝ X₀]
    [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    [CompleteSpace X₁] where
  S11 : ℝ → X₁ →L[ℝ] X₁
  S01 : ℝ → X₀ →L[ℝ] X₁
  nonlinear : X₁ → X₀
  δ ω rate ϑ M₀ Mϑ K ρ I : ℝ
  hϑ : 0 < ϑ ∧ ϑ < 1
  hrate : 0 < rate ∧ rate < ω
  hωδ : ω < δ
  hM₀ : 0 ≤ M₀
  hMϑ : 0 ≤ Mϑ
  hK : 0 ≤ K
  hρ : 0 < ρ
  hI : 0 ≤ I
  decay : ∀ t, 0 ≤ t → ‖S11 t‖ ≤ M₀ * Real.exp (-δ * t)
  smoothing : ∀ t, 0 < t →
    ‖S01 t‖ ≤ Mϑ * t ^ (-ϑ) * Real.exp (-ω * t)
  nonlinear_zero : nonlinear 0 = 0
  quadratic : ∀ x, ‖x‖ ≤ ρ →
    ‖nonlinear x‖ ≤ K * ‖x‖ ^ 2
  locallyLipschitz : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
    ‖nonlinear x - nonlinear y‖ ≤
      K * (‖x‖ + ‖y‖) * ‖x - y‖
  kernel_bound : ∀ T, 0 ≤ T →
    (∫ q in (0 : ℝ)..T,
      q ^ (-ϑ) * Real.exp (-(ω - rate) * q)) ≤ I
  duhamel_integrable :
    -- continuity + the singular majorant, in the style of
    -- Wiener.WA.duhamel_selfmap_bound
    ...
```

Define the tail equation and weighted bound:

```javascript
def IsTailDuhamelSolution
    (H : QuadraticTailDuhamelData X₀ X₁)
    (z₀ : X₁) (z : ℝ → X₁) : Prop :=
  ContinuousOn z (Set.Ici 0) ∧ z 0 = z₀ ∧
  ∀ t, 0 ≤ t →
    z t = H.S11 t z₀ +
      ∫ s in (0 : ℝ)..t,
        H.S01 (t - s) (H.nonlinear (z s))

def HasTailWeightedBound
    (H : QuadraticTailDuhamelData X₀ X₁)
    (R : ℝ) (z : ℝ → X₁) : Prop :=
  ∀ t, 0 ≤ t → ‖z t‖ ≤ R * Real.exp (-H.rate * t)
```

The L5 abstract core is:

```javascript
theorem existsUnique_tailDuhamel_of_quadratic
    (H : QuadraticTailDuhamelData X₀ X₁)
    {R : ℝ} (hRpos : 0 < R) (hRρ : R ≤ H.ρ)
    (hcontract : 4 * H.Mϑ * H.K * H.I * R ≤ 1)
    {z₀ : X₁} (hz₀ : H.M₀ * ‖z₀‖ ≤ R / 2) :
    ∃ z : ℝ → X₁,
      IsTailDuhamelSolution H z₀ z ∧
      HasTailWeightedBound H R z ∧
      ∀ y : ℝ → X₁,
        IsTailDuhamelSolution H z₀ y →
        HasTailWeightedBound H R y → y = z
```

Internally, realize the weighted path space by exponential conjugation as a closed ball in

```javascript
BoundedContinuousFunction ℝ≥0 X₁
```

and apply Mathlib's contraction fixed-point theorem.  The mode-space instantiation uses

```javascript
X₀ := weighted cosine ℓ² at order s
X₁ := weighted cosine ℓ² at order s + ϑ
S11 t c := fun k => Real.exp (-d k * t) * c k
S01 t c := the same multiplier, viewed X^s → X^(s+ϑ)
```

The chemotaxis wrapper should have the following shape:

```javascript
theorem interval_eliminatedChemotaxis_eventualExp_of_restart_small
    (hgap : EliminatedLinearModeGap p uStar vStar δlin)
    (hquad : EliminatedChemotaxisQuadraticRemainder
      p uStar vStar s ϑ ρ Kρ)
    (hduhamel : EliminatedModeDuhamelRealization p uStar u)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hrestart :
      modeXNorm (s + ϑ) (cosineCoeffs (u t₀ - fun _ => uStar)) ≤
        εtail) :
    EventualExponentialC1ConvergenceWith
      intervalDomain intervalDomainStabilityNorms
      u v uStar vStar t₀ (Cout * Rstar) δprime
```

For an already-constructed PDE solution, add a uniqueness/identification lemma saying that its shifted coefficient trajectory is the fixed point.  The contraction theorem alone constructs a tail mild trajectory; the identification lemma transfers the bound to the physical solution.

# 8. Repository dependency DAG

```plain text
PDE/SectorialOperator.lean
  diagonalSemigroupCoeff + coefficient ℓ² infrastructure
        │
        ├─ new: LinearizedChemotaxisDiagonalSemigroup.lean
        │    d_k, δlin, c*, decay, X^s→X^(s+ϑ) smoothing
        │
PDE/FractionalPowerSpace.lean
  fractionalPowerWeight + C⁰/C¹ trace estimates
        │
        ├─ new: IntervalEliminatedChemotaxisRemainder.lean
        │    exact N, Taylor/resolver/product/divergence estimates
        │
Wiener/WeightedL1SelfMap.lean
  model for singular Bochner Duhamel integral
        │
        └─ new: WeightedTailDuhamelContraction.lean
             weighted path Banach space + Banach fixed point
                       │
                       └─ new: Paper3/IntervalDomainEventualLocalStability.lean
                            restart realization + physical-solution identification
                            + EventualExponentialC1ConvergenceWith
```

IntervalDomainInitialContinuityRaw or a stronger finite-time smoothing theorem supplies the weak-initial-data-to-restart-smallness bridge.  For Theorems 2.3–2.5, the L8 uniform-convergence/basin-entry producer supplies it at a sufficiently large orbit time.

# Final L5 statement

For every (0<delta'<delta_{rm lin}), every (frac12<vartheta<1) with (s+vartheta>3/4), and every local quadratic radius (rho), define (M_vartheta), (I), (A_D), (R_*), and (varepsilon_{rm tail}) as above.  Then

[

|u(t_0)-u_*|{X^{s+vartheta}}levarepsilon{rm tail}

]

implies

[

|u(t)-u_*|_{X^{s+vartheta}}

le R_*e^{-delta'(t-t_0)}

quad(tge t_0),

]

and hence eventual exponential (C^1) convergence of ((u,v)).  A canonical choice is (delta'=delta_{rm lin}/2).

That is the faithful, acyclic L5 leaf.  The only genuinely PDE-specific inputs left after the modal gap are the local quadratic remainder estimate, the Duhamel realization/identification, and the finite-time or basin-entry bridge that makes the restart state small in the strong coefficient norm.