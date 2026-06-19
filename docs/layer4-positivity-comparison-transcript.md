# Layer‑4 verdict

Layer‑4 should be a **comparison/SMP layer for the clamped physical mild equation**, not a second fixed-point layer and not a naive positivity-of-Duhamel layer.

The key correction is:

\[
E(t)\ge 0,\quad R\ge0
\]

are essential, but they do **not** by themselves make the full Duhamel map order-preserving, because

\[
-\chi\int_0^t \partial_xE(t-\tau)q(\tau)\,d\tau
\]

has no sign. So the lower/upper bounds should be proved by a **weak maximum principle for the clamped mild solution**, using negative/positive-part testing or an equivalent regularized comparison argument.

The strong lower bound

\[
0<\kappa\le u(t,x)\quad\text{on }[\delta,T]\times[0,1]
\]

should then come from a **strong maximum principle for the positive-time classical clamped/original equation**, plus compactness of the slab. A Harnack inequality is not needed for the existence of some \(\kappa_{\delta,T}>0\). A fully explicit lower bound in terms of \(u_0,\delta,T\) would require a stronger evolution-kernel/Harnack-type layer; do not make that part of Layer‑4 unless Paper 3 actually needs quantitative constants.

Mathlib gives useful foundations: `BoundedContinuousFunction` has the expected continuous/evaluation/completeness infrastructure, Bochner integration has norm estimates, and `lp` has completeness/summability scaffolding. It does **not** have parabolic maximum principles, strong maximum principles, Neumann heat-kernel positivity packages, or PDE comparison theorems ready-made. citeturn112730view0turn342494view4turn342494view0turn342494view2turn342494view3

---

# 1. Correct weak comparison route

Use the clamped variable

\[
z=C_M(u):=\min(\max(u,0),M).
\]

The Layer‑2 clamped mild equation should be regarded as

\[
u(t)
=
E(t)u_0
+
\int_0^tE(t-\tau)
\bigl(a z(\tau)-b z(\tau)^{1+\alpha}\bigr)\,d\tau
-
\chi\int_0^t\partial_xE(t-\tau)
\bigl(z(\tau)^mS(v(\tau))v_x(\tau)\bigr)\,d\tau,
\]

where

\[
v(\tau)=R(z(\tau)^\gamma).
\]

This is the right clamped equation for comparison, because outside \([0,M]\) the nonlinearities become structurally harmless.

## Lower bound \(u\ge0\)

Let

\[
u_-:=\max(-u,0).
\]

On the set where \(u<0\),

\[
z=C_M(u)=0.
\]

Therefore

\[
z^mS(v)v_x=0,
\qquad
az-bz^{1+\alpha}=0.
\]

Testing the weak form against \(-u_-\), or using a smooth convex approximation of \(\frac12u_-^2\), gives

\[
\frac12\frac{d}{dt}\|u_-(t)\|_{L^2}^2
\le
-\|\partial_xu_-(t)\|_{L^2}^2
\le0.
\]

Since

\[
u_0\ge0,
\]

we have

\[
u_-(0)=0,
\]

and hence

\[
u_-(t)=0
\]

for all \(t\). Thus

\[
u(t,x)\ge0.
\]

This does **not** require the Duhamel map to preserve positivity. The derivative heat term is handled through the divergence structure and the fact that the clamped flux vanishes where \(u<0\).

## Upper bound \(u\le M\)

Let

\[
w:=(u-M)_+.
\]

On the set where \(u>M\),

\[
z=C_M(u)=M.
\]

Thus

\[
z^m=M^m,
\qquad
z^\gamma=M^\gamma,
\qquad
v=R(z^\gamma),
\qquad
0\le v\le M^\gamma.
\]

The upper-bound test gives

\[
\frac12\frac{d}{dt}\|w(t)\|_{L^2}^2
=
-\|\partial_xw(t)\|_{L^2}^2
+
\int_{\{u>M\}}
w\Bigl[
-\chi\,\partial_x\bigl(M^mS(v)v_x\bigr)
+
aM-bM^{1+\alpha}
\Bigr].
\]

So \(M\) is a valid upper barrier if the bracket is pointwise nonpositive on the contact region:

\[
\boxed{
-\chi\,\partial_x\bigl(M^mS(v)v_x\bigr)
+
aM-bM^{1+\alpha}
\le0.
}
\]

Using

\[
v_{xx}=v-M^\gamma
\]

on the region where \(z=M\), one has

\[
\partial_x\bigl(M^mS(v)v_x\bigr)
=
M^m\bigl(S'(v)v_x^2+S(v)(v-M^\gamma)\bigr).
\]

Since

\[
S(v)=(1+v)^{-\beta},
\qquad
\beta\ge0,
\]

we have

\[
S(v)\ge0,
\qquad
S'(v)\le0.
\]

Also

\[
0\le v\le M^\gamma,
\]

so

\[
v-M^\gamma\le0.
\]

Therefore

\[
\partial_x\bigl(M^mS(v)v_x\bigr)\le0.
\]

If the sign convention is

\[
\chi\le0,
\]

then

\[
-\chi\,\partial_x\bigl(M^mS(v)v_x\bigr)\le0.
\]

In that favorable sign case, it is enough to require

\[
\boxed{
aM-bM^{1+\alpha}\le0.
}
\]

Equivalently,

\[
a\le bM^\alpha.
\]

If instead the model uses \(\chi>0\), then the chemotaxis term may push upward at an upper contact. In that case the simple logistic condition is not enough. Use the scalar sufficient condition

\[
\boxed{
aM-bM^{1+\alpha}
+
\chi\,C_{\mathrm{chem}}(M)
\le0,
}
\]

where one may take

\[
C_{\mathrm{chem}}(M)
=
M^m
\left(
\|S'\|_{[0,M^\gamma]}
(C_{R,1}M^\gamma)^2
+
\|S\|_{[0,M^\gamma]}M^\gamma
\right),
\]

using

\[
\|v_x\|_\infty\le C_{R,1}M^\gamma,
\qquad
0\le v\le M^\gamma.
\]

Then

\[
\frac12\frac{d}{dt}\|w(t)\|_{L^2}^2\le0.
\]

Since

\[
u_0\le M,
\]

we get

\[
w(0)=0,
\]

hence

\[
u(t,x)\le M.
\]

So the weak comparison theorem gives

\[
0\le u(t,x)\le M.
\]

Then

\[
C_M(u)=u,
\]

and the clamped mild equation becomes the real physical mild equation.

---

# 2. Strong positivity

Assume

\[
u_0\ge0,
\qquad
u_0\not\equiv0.
\]

After weak comparison and clamp removal,

\[
0\le u\le M.
\]

The explicit Neumann heat kernel fact should be pinned:

> For every \(t>0\), the Neumann heat kernel \(G_N(t,x,y)\) on \([0,1]\) is strictly positive. Therefore, for every \(0<\eta<T\),
> \[
> c_{\eta,T}:=
> \inf_{\eta\le t\le T,\ x,y\in[0,1]}G_N(t,x,y)>0.
> \]
> Hence, for \(f\ge0\),
> \[
> E(t)f(x)
> =
> \int_0^1G_N(t,x,y)f(y)\,dy
> \ge
> c_{\eta,T}\int_0^1f(y)\,dy
> \]
> for \(\eta\le t\le T\).

This is useful and should belong to Layer‑1/4. But it does **not** by itself prove strong positivity for the full chemotaxis equation, because the derivative Duhamel term is not sign-preserving.

The faithful route is:

1. use weak comparison to get \(0\le u\le M\);
2. use the clamped/original positive-time smoothing from Layer‑3 to make \(u\) classical on \([\varepsilon,T]\);
3. rewrite the equation as a linear parabolic equation in \(u\) with bounded coefficients;
4. apply a project strong maximum principle;
5. use compactness of \([\delta,T]\times[0,1]\) to extract a positive minimum.

The linearized form is

\[
u_t
=
u_{xx}
+
B(t,x)u_x
+
C(t,x)u,
\]

where

\[
B
=
-\chi\,m\,u^{m-1}S(v)v_x,
\]

and

\[
C
=
a
-
bu^\alpha
-
\chi\,u^{m-1}
\bigl(
S'(v)v_x^2+S(v)(v-u^\gamma)
\bigr).
\]

For \(m>1\), this is bounded and continuous even at \(u=0\), because \(u^{m-1}\) remains bounded and tends to \(0\) at zero. No division by \(u\) is needed.

Then the strong maximum principle says:

If

\[
u\ge0,
\qquad
u_0\not\equiv0,
\]

and \(u\) solves the above linear parabolic equation with bounded continuous coefficients and Neumann boundary condition, then

\[
u(t,x)>0
\]

for every

\[
t>0,\qquad x\in[0,1].
\]

Boundary positivity is handled either by the Neumann boundary strong maximum principle or by even reflection across the endpoints.

Finally, since \(u\) is continuous and strictly positive on the compact slab

\[
[\delta,T]\times[0,1],
\]

there exists

\[
\kappa_{\delta,T}>0
\]

such that

\[
\boxed{
u(t,x)\ge\kappa_{\delta,T}
\quad
\text{for all }(t,x)\in[\delta,T]\times[0,1].
}
\]

So no Harnack inequality is needed for the qualitative lower bound. A Harnack/Aronson-type estimate would only be needed if the later paper floors require an explicit computable lower bound depending only on parameters and \(u_0\).

---

# 3. Non-Lipschitz real-power coefficient

The dangerous coefficient is

\[
s\mapsto s^{m-1},
\qquad
1<m<2.
\]

It is Hölder, not Lipschitz, near \(0\). Therefore, a comparison proof that differences two arbitrary solutions and tries to estimate

\[
\|u^{m-1}-\tilde u^{m-1}\|
\]

near zero is the wrong route.

Layer‑4 should avoid this in two ways.

## For weak comparison against \(0\) and \(M\)

Do **not** difference two arbitrary nonlinear solutions.

Use barrier comparison for a single solution and exploit the divergence/clamping structure:

- On \(\{u<0\}\), the clamped density is \(z=0\), so the flux vanishes.
- On \(\{u>M\}\), the clamped density is \(z=M\), and the upper-barrier residual is controlled directly.
- The map \(s\mapsto s^m\) is Lipschitz on \([0,M]\) for \(m\ge1\), even though \(s^{m-1}\) is not Lipschitz at zero.

Thus weak comparison is valid for \(1<m<2\) without needing \(s^{m-1}\) to be Lipschitz.

## For comparison/uniqueness on positive-time slabs

Once strong positivity gives

\[
u,\tilde u\ge\kappa>0
\]

on \([\delta,T]\), all real-power maps are locally smooth on

\[
[\kappa,M].
\]

Then

\[
s\mapsto s^{m-1},
\qquad
s\mapsto s^m,
\qquad
s\mapsto s^\gamma,
\qquad
s\mapsto s^{1+\alpha}
\]

are locally Lipschitz with constants depending on \(\kappa,M\). So ordinary difference estimates are legal on positive-time slabs.

The faithful rule is:

\[
\boxed{
\text{near }u=0,\text{ use structure/barriers;}
\qquad
\text{after }u\ge\kappa,\text{ use Lipschitz real-power calculus.}
}
\]

---

# 4. Numbered Layer‑4 lemma DAG

Below is the interface I would pin.

## Basic clamping and coefficient lemmas

### 1. `clipC0_range`

For \(M>0\),

\[
0\le C_M(f)(x)\le M
\]

for all \(x\).

Consumes: order/lattice facts for real-valued bounded continuous functions.  
Mathlib scaffold: bounded continuous functions have algebra/order/evaluation infrastructure; pointwise extensionality and evaluation are available. citeturn112730view0

---

### 2. `clipC0_inactive_of_range`

If

\[
0\le f(x)\le M
\]

for all \(x\), then

\[
C_M(f)=f.
\]

Consumes: Lemma 1.

---

### 3. `clamped_resolvent_bounds`

Let

\[
z=C_M(f),
\qquad
v=R(z^\gamma).
\]

Then

\[
0\le v\le M^\gamma,
\]

\[
\|v_x\|_\infty\le C_{R,1}M^\gamma,
\]

and

\[
v_{xx}=v-z^\gamma.
\]

Consumes: Layer‑1 resolvent positivity, \(R1=1\), \(R''=R-I\), derivative bound.

---

### 4. `clamped_flux_bounds`

For

\[
q_M(f):=z^mS(v)v_x,
\qquad z=C_M(f),
\]

one has

\[
\|q_M(f)\|_\infty
\le
M^m\|S\|_{[0,M^\gamma]}C_{R,1}M^\gamma.
\]

Consumes: Lemma 3.

---

### 5. `clamped_reaction_bounds`

For

\[
F_M(f):=aC_M(f)-bC_M(f)^{1+\alpha},
\]

\[
|F_M(f)(x)|
\le
|a|M+bM^{1+\alpha}.
\]

Consumes: Lemma 1.

---

## Mild-to-weak bridge

### 6. `clamped_mild_to_weak_pde`

If \(u\) is a clamped mild solution, then \(u\) satisfies the weak distributional identity

\[
u_t
=
u_{xx}
-\chi\partial_x q_M(u)
+
F_M(u)
\]

with Neumann boundary terms cancelled.

Consumes: Layer‑1 semigroup generator/Neumann facts, Layer‑2 mild predicate, Bochner integral calculus.  
Mathlib scaffold: Bochner integrals and norm estimates exist; the PDE-specific mild-to-weak bridge is project infrastructure. citeturn342494view0

---

### 7. `renormalized_negative_part_test`

For a weak solution of the clamped equation,

\[
\frac12\frac{d}{dt}\|u_-(t)\|_2^2
\le
-\|\partial_xu_-(t)\|_2^2.
\]

Consumes: Lemma 6; convex approximation of \(s\mapsto \frac12s_-^2\); the fact \(C_M(u)=0\) on \(\{u<0\}\).

Status: project PDE lemma.

---

### 8. `clamped_nonnegative`

If

\[
u_0\ge0,
\]

then every clamped mild solution satisfies

\[
u(t,x)\ge0.
\]

Consumes: Lemma 7 and Gronwall in the trivial form \(Y'\le0,\ Y(0)=0\Rightarrow Y=0\).

---

## Upper-barrier block

### 9. `upper_contact_flux_formula`

On the region where

\[
C_M(u)=M,
\]

with

\[
v=R(C_M(u)^\gamma),
\]

one has

\[
\partial_x(M^mS(v)v_x)
=
M^m\bigl(S'(v)v_x^2+S(v)(v-M^\gamma)\bigr).
\]

Consumes: Layer‑1 \(R''=R-I\), calculus for \(S\).

---

### 10. `upper_contact_flux_sign_chi_nonpos`

Assume

\[
\beta\ge0,\qquad \chi\le0.
\]

Then on the upper-contact region,

\[
-\chi\,\partial_x(M^mS(v)v_x)\le0.
\]

Consumes: Lemma 9, \(S\ge0\), \(S'\le0\), \(0\le v\le M^\gamma\).

---

### 11. `upper_contact_flux_bound_chi_pos`

For arbitrary \(\chi\), define

\[
C_{\mathrm{chem}}(M)
=
M^m
\left(
\|S'\|_{[0,M^\gamma]}
(C_{R,1}M^\gamma)^2
+
\|S\|_{[0,M^\gamma]}M^\gamma
\right).
\]

Then

\[
-\chi\,\partial_x(M^mS(v)v_x)
\le
\chi_+ C_{\mathrm{chem}}(M).
\]

Consumes: Lemmas 3 and 9.

---

### 12. `constant_upper_barrier_condition`

A number \(M>0\) is an admissible upper barrier if

\[
aM-bM^{1+\alpha}
+
\chi_+C_{\mathrm{chem}}(M)
\le0.
\]

In the favorable case \(\chi\le0\), this reduces to

\[
aM-bM^{1+\alpha}\le0.
\]

Consumes: Lemmas 10 and 11.

---

### 13. `renormalized_upper_part_test`

Let

\[
w=(u-M)_+.
\]

If \(M\) satisfies the upper-barrier condition, then

\[
\frac12\frac{d}{dt}\|w(t)\|_2^2
\le
-\|\partial_xw(t)\|_2^2.
\]

Consumes: Lemmas 6, 9–12.

Status: project PDE lemma.

---

### 14. `clamped_upper_bound`

If

\[
u_0\le M
\]

and \(M\) is an admissible upper barrier, then

\[
u(t,x)\le M
\]

for all \(t,x\).

Consumes: Lemma 13.

---

### 15. `clamp_inactive_on_local_interval`

If

\[
0\le u_0\le M
\]

and \(M\) is an admissible upper barrier, then the Layer‑2 clamped mild solution satisfies

\[
0\le u(t,x)\le M.
\]

Therefore

\[
C_M(u(t))=u(t)
\]

for all \(t\), and the clamped mild solution is a genuine physical mild solution.

Consumes: Lemmas 2, 8, 14.

This is the main Layer‑2 output consumer.

---

## Heat-kernel lower bound and mass positivity

### 16. `neumann_heat_kernel_strict_positive`

For \(t>0\),

\[
G_N(t,x,y)>0
\]

for all \(x,y\in[0,1]\).

Moreover, for \(0<\eta<T\),

\[
\inf_{\eta\le t\le T,\ x,y\in[0,1]}G_N(t,x,y)>0.
\]

Consumes: Layer‑1 explicit Gaussian/even-periodic Neumann kernel.

Status: project kernel lemma.

---

### 17. `heat_semigroup_lower_by_mass`

If \(f\ge0\), then for \(\eta\le t\le T\),

\[
E(t)f(x)
\ge
c_{\eta,T}\int_0^1f(y)\,dy.
\]

Consumes: Lemma 16.

This is useful, but not sufficient alone for the full chemotaxis equation because of the derivative Duhamel term.

---

### 18. `mass_positive_if_initial_nonzero`

If

\[
0\le u\le M,
\qquad
u_0\not\equiv0,
\]

then

\[
\int_0^1u(t,x)\,dx>0
\]

for all \(t\ge0\).

Indeed,

\[
\frac{d}{dt}\int_0^1u
=
a\int_0^1u
-
b\int_0^1u^{1+\alpha},
\]

because the Neumann diffusion and chemotaxis flux integrate to zero. Since

\[
u^{1+\alpha}\le M^\alpha u,
\]

we get

\[
\frac{d}{dt}\int_0^1u
\ge
(a-bM^\alpha)\int_0^1u.
\]

Consumes: clamp inactivity, Neumann boundary cancellation, elementary Gronwall.

---

## Strong positivity block

### 19. `nonnegative_solution_linearized_coefficients`

For a clamped-inactive solution \(0\le u\le M\), define

\[
B
=
-\chi\,m\,u^{m-1}S(v)v_x,
\]

\[
C
=
a
-
bu^\alpha
-
\chi u^{m-1}
\bigl(S'(v)v_x^2+S(v)(v-u^\gamma)\bigr).
\]

Then on every positive-time slab where \(u\) is classical,

\[
u_t=u_{xx}+Bu_x+Cu,
\]

and \(B,C\) are bounded and continuous.

Consumes: Layer‑3 positive-time classicality for the clamped/original equation, Lemma 3, \(m>1\).

---

### 20. `linear_parabolic_strong_maximum_principle_neumann`

Let \(w\ge0\) solve

\[
w_t=w_{xx}+B w_x+Cw
\]

on \((0,T]\times[0,1]\), with Neumann boundary condition, bounded continuous \(B,C\), and nonzero nonnegative initial data. Then

\[
w(t,x)>0
\]

for every

\[
t>0,\quad x\in[0,1].
\]

Boundary case handled by Neumann reflection or boundary strong maximum principle.

Status: major project PDE lemma. Not in Mathlib.

---

### 21. `strong_positive_pointwise`

If

\[
u_0\ge0,
\qquad
u_0\not\equiv0,
\]

then the physical mild solution satisfies

\[
u(t,x)>0
\]

for all

\[
t>0,\quad x\in[0,1].
\]

Consumes: Lemmas 15, 18, 19, 20.

---

### 22. `positive_slab_lower_bound`

For every

\[
0<\delta<T,
\]

there exists

\[
\kappa_{\delta,T}>0
\]

such that

\[
u(t,x)\ge\kappa_{\delta,T}
\]

for all

\[
(t,x)\in[\delta,T]\times[0,1].
\]

Consumes: Lemma 21 and compactness of the slab.

This is the keystone output consumed by Layer‑2 clamp removal refinements and Layer‑3 real-power composition.

---

## Real-power and comparison unlocks

### 23. `real_power_lipschitz_on_positive_slab`

If

\[
\kappa\le s,t\le M,
\]

then for any real exponent \(\rho\),

\[
|s^\rho-t^\rho|
\le
L_{\rho,\kappa,M}|s-t|.
\]

In particular, this applies to

\[
\rho=m-1,\quad m,\quad \gamma,\quad 1+\alpha.
\]

Consumes: elementary real calculus on compact positive intervals.

---

### 24. `nonlinear_comparison_on_positive_slab`

On a slab where

\[
\kappa\le u,\tilde u\le M,
\]

the nonlinearities

\[
u^mS(R(u^\gamma))\partial_xR(u^\gamma),
\qquad
au-bu^{1+\alpha}
\]

are locally Lipschitz in the norms required by the comparison/uniqueness argument.

Consumes: Lemma 23, Layer‑1 resolvent bounds, Layer‑3 \(A^r\) algebra/composition.

---

### 25. `Ar_real_power_composition_unlocked`

On \([\delta,T]\), since

\[
\kappa_{\delta,T}\le u\le M,
\]

the maps

\[
u\mapsto u^m,\qquad
u\mapsto u^\gamma,\qquad
u\mapsto u^{1+\alpha},\qquad
v\mapsto S(v)
\]

are smooth compositions in \(A^r\).

Consumes: Lemma 22 and the Layer‑3 \(A^r\) smooth-composition theorem.

This is the Layer‑3 feedback output.

---

# 5. Mathlib gaps

## Supported scaffolding

Mathlib supports the general functional-analytic scaffolding:

- bounded continuous functions have continuity/evaluation/completeness infrastructure; citeturn112730view0turn342494view4
- Bochner integration includes the basic norm estimate for integrals; citeturn342494view0
- `lp` provides the summability/completeness infrastructure for the \(A^r\) engine, but not the weighted convolution algebra itself. citeturn342494view2turn342494view3

## Missing project lemmas

These must be built or pinned as project theorems.

1. **Mild-to-weak PDE bridge for the clamped equation.**  
   Mathlib has Bochner integrals, but not the PDE theorem converting this Duhamel formula into the weak Neumann PDE.

2. **Renormalized negative/positive-part testing.**  
   The Kato-style estimates for \(u_-\) and \((u-M)_+\) are not in Mathlib as parabolic PDE comparison theorems.

3. **Upper-contact chemotaxis residual calculation.**  
   The identity
   \[
   \partial_x(M^mS(v)v_x)
   =
   M^m(S'(v)v_x^2+S(v)(v-M^\gamma))
   \]
   and its sign/bound are project-specific.

4. **Neumann heat kernel strict positivity.**  
   Layer‑1 has the explicit kernel, but strict positivity and compact positive lower bounds must be formalized.

5. **Strong maximum principle with Neumann boundary.**  
   This is the biggest Layer‑4 gap. Mathlib does not provide a ready parabolic strong maximum principle.

6. **Boundary handling for SMP.**  
   Either formalize a Neumann boundary SMP directly or use even reflection to reduce to an interior periodic/local statement.

7. **Mass identity.**  
   The cancellation of diffusion and chemotaxis flux under Neumann boundary conditions is project-specific.

8. **Positive-slab extraction.**  
   The compactness step is ordinary topology, but the input \(u(t,x)>0\) from SMP is project PDE infrastructure.

9. **Nonlinear comparison on positive slabs.**  
   Once \(\kappa>0\) is known, this is mostly calculus plus Layer‑3 algebra, but the assembled PDE comparison theorem is project-specific.

---

# 6. Convergence check

Layer‑4 closes from Layers 1–3 only if Layer‑3 includes a **clamped positive-time regularity theorem** that does **not** depend on the strict lower bound.

There is a potential circularity:

\[
\text{Layer‑3 real-power composition}
\Longleftarrow
u\ge\kappa>0,
\]

but

\[
u\ge\kappa>0
\]

is supposed to come from Layer‑4, and Layer‑4’s strong maximum principle wants positive-time classicality.

The way to break the circle is:

1. Layer‑2 constructs the **clamped** mild solution in \(C^0\).
2. Layer‑3 proves positive-time regularity for the **clamped equation**, using bounded/clamped nonlinearities, not real-power smoothness on a positive range.
3. Layer‑4 applies weak comparison to show
   \[
   0\le u\le M.
   \]
4. Therefore the clamp is inactive.
5. Layer‑4 applies the strong maximum principle to get
   \[
   u\ge\kappa_{\delta,T}>0.
   \]
6. Layer‑3’s full real-power \(A^r\) composition/bootstrap is then unlocked on \([\delta,T]\).

So the dependency is:

\[
\boxed{
\text{clamped mild existence}
\to
\text{clamped regularity}
\to
\text{weak comparison}
\to
\text{clamp inactive}
\to
\text{strong positivity}
\to
\text{real-power }A^r\text{ bootstrap}.
}
\]

The only undesigned dependency that must be added is the **project strong maximum principle / weak comparison package**. A Harnack inequality is not necessary unless later floors require explicit quantitative lower bounds independent of the already-constructed solution.