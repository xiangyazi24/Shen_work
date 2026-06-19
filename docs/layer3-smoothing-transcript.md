# Layer‑3 verdict

The **abstract \(A^r\) bootstrap closes beautifully once you already have a positive-time \(A^\sigma\) seed**, with any

\[
0<\sigma<1.
\]

But it does **not** follow from a bare \(C^0\) mild solution by simply applying the \(A^r\to A^{r+m}\) heat estimates. The transport term has one spatial derivative:

\[
\int_0^t \partial_xE(t-\tau)\,Q(u(\tau))\,d\tau,
\]

and from a merely \(C^0\) source this is too singular to land directly in \(A^0=\ell^1\). So Layer‑3 needs a first “seed regularity” lemma, either:

\[
C^0\text{ mild}
\Longrightarrow
u\in C([\delta,T];A^\sigma),\qquad 0<\sigma<1,
\]

proved by a **time-weighted \(A^\sigma\) restart/fixed-point argument**, or by a separate physical Hölder/Schauder seed. After that, the Fourier–Wiener \(A^r\) machinery handles the rest.

Mathlib gives good underlying infrastructure for \(\ell^p\), summability, completeness, strong measurability, and Bochner integral estimates, but it does **not** appear to provide a ready-made weighted \(\ell^1\) convolution Banach algebra. The documented `lp` file gives \(\ell^p\)-style spaces, completeness for \(p\ge1\), summability/norm tools, and pointwise normed ring/algebra instances for \(p=\infty\), not the weighted \(\ell^1\) convolution algebra needed here. citeturn827968view0 Bochner integral estimates and strong measurability are available as general primitives, including norm-of-integral bounds and closure of strong measurability under algebraic operations. citeturn785980view0 citeturn366577view0

---

# 1. Semigroup smoothing estimates in \(A^r\)

Let

\[
A^r
=
\left\{
a=(a_k)_{k\in\mathbb Z}:
\|a\|_{A^r}:=
\sum_{k\in\mathbb Z}(1+|k|)^r|a_k|<\infty
\right\}.
\]

For Neumann cosine modes, work through the even \(2\)-periodic Fourier model on \(\mathbb Z\), then restrict to even real coefficients. This avoids repeated cosine-product constants.

The spectral heat semigroup is

\[
(E(t)a)_k=e^{-\pi^2k^2t}a_k.
\]

For \(m\ge0\),

\[
\boxed{
\|E(t)a\|_{A^{r+m}}
\le
C_m t^{-m/2}\|a\|_{A^r},
\qquad t>0.
}
\]

The proof is the scalar multiplier estimate

\[
(1+|k|)^m e^{-\pi^2k^2t}
\le
C_m t^{-m/2}.
\]

For spatial derivatives,

\[
\partial_x^jE(t)
\]

has multiplier \((\pi ik)^j e^{-\pi^2k^2t}\), so

\[
\boxed{
\|\partial_x^jE(t)a\|_{A^{r+m}}
\le
C_{j,m}t^{-(j+m)/2}\|a\|_{A^r}.
}
\]

The scalar time-integral is:

\[
\int_0^t(t-\tau)^{-a}\,d\tau
=
\frac{t^{1-a}}{1-a},
\qquad a<1.
\]

Thus:

\[
\int_0^t(t-\tau)^{-m/2}\,d\tau<\infty
\quad\Longleftrightarrow\quad
m<2.
\]

So a non-derivative Duhamel term

\[
\int_0^tE(t-\tau)F(\tau)\,d\tau
\]

gains any \(m<2\) derivatives from \(F\in C_tA^r\):

\[
\boxed{
\left\|
\int_0^tE(t-\tau)F(\tau)\,d\tau
\right\|_{A^{r+m}}
\le
C_m\frac{t^{1-m/2}}{1-m/2}
\|F\|_{C_tA^r},
\qquad m<2.
}
\]

For the transport term,

\[
\int_0^t\partial_xE(t-\tau)Q(\tau)\,d\tau,
\]

the kernel exponent is \((1+m)/2\). Hence

\[
\int_0^t(t-\tau)^{-(1+m)/2}\,d\tau<\infty
\quad\Longleftrightarrow\quad
m<1.
\]

So the differentiated Duhamel term gains only \(m<1\) derivatives:

\[
\boxed{
\left\|
\int_0^t\partial_xE(t-\tau)Q(\tau)\,d\tau
\right\|_{A^{r+m}}
\le
C_{1,m}
\frac{t^{(1-m)/2}}{(1-m)/2}
\|Q\|_{C_tA^r},
\qquad m<1.
}
\]

This is the key Layer‑3 constraint:

\[
\boxed{
\text{reaction Duhamel gains }<2,\qquad
\text{transport Duhamel gains }<1.
}
\]

Therefore the bootstrap step is

\[
A^r\Longrightarrow A^{r+\theta}
\quad\text{for any }0<\theta<1.
\]

Do **not** try to use \(\partial_{xx}E\) directly on the Duhamel term at this stage: the kernel exponent would be \((2+m)/2\ge1\), non-integrable for \(m\ge0\).

---

# 2. Nonlinearity estimates in \(A^r\)

Write the nonlinearities abstractly as

\[
F(u)=a u-bu^p,
\]

\[
v=R(u^\gamma),
\]

\[
Q(u)=u^m S(v)v_x,
\]

and the mild equation as

\[
u(t)=E(t)u_0
+
\int_0^tE(t-\tau)F(u(\tau))\,d\tau
-
\chi
\int_0^t\partial_xE(t-\tau)Q(u(\tau))\,d\tau.
\]

Here \(p\) can be \(1+\alpha\), and \(m,\gamma\) are the real exponents from the model.

## Product estimate

For \(r\ge0\),

\[
\boxed{
\|fg\|_{A^r}
\le
C_r\|f\|_{A^r}\|g\|_{A^r}.
}
\]

In the \(\mathbb Z\)-Fourier model this is the weighted convolution estimate:

\[
\widehat{fg}_k
=
\sum_{\ell\in\mathbb Z}\hat f_\ell\hat g_{k-\ell},
\]

with

\[
(1+|k|)^r
\le
(1+|\ell|)^r(1+|k-\ell|)^r.
\]

Then

\[
\begin{aligned}
\|fg\|_{A^r}
&\le
\sum_k\sum_\ell
(1+|\ell|)^r|\hat f_\ell|
(1+|k-\ell|)^r|\hat g_{k-\ell}|  \\
&=
\|f\|_{A^r}\|g\|_{A^r}.
\end{aligned}
\]

For the cosine model, either absorb a harmless structural constant or route through the even Fourier extension and then restrict back.

This estimate is **not a ready Mathlib theorem** in the form needed. Build it from summability, `tsum` manipulation, nonnegative series estimates, and the \(p=1\) `lp` infrastructure. Mathlib’s docs expose the relevant \(\ell^p\) and summability primitives, but the convolution algebra itself is project infrastructure. citeturn827968view0

## Resolvent estimates

The spectral resolvent multiplier is

\[
(Ra)_k=\frac{1}{1+\pi^2k^2}a_k.
\]

Hence

\[
\boxed{
\|Ra\|_{A^{r+2}}\le C_r\|a\|_{A^r}.
}
\]

Also

\[
\boxed{
\|\partial_xRa\|_{A^{r+1}}\le C_r\|a\|_{A^r},
}
\]

and

\[
\boxed{
\|\partial_{xx}Ra\|_{A^r}\le C_r\|a\|_{A^r}.
}
\]

The identity

\[
R''=R-I
\]

is also useful physically and spectrally.

## Real-power and composition estimates

For integer powers, use the Banach algebra repeatedly:

\[
\|u^n\|_{A^r}\le C_{r,n}\|u\|_{A^r}^n.
\]

For real powers, the clean interface is:

> If \(u\in A^r\), \(r\ge0\), and
> \[
> 0<\kappa\le u(x)\le M,
> \]
> then for every smooth \(\Phi\) on an interval containing \([\kappa,M]\),
> \[
> \Phi(u)\in A^r,
> \]
> with a local bound
> \[
> \|\Phi(u)\|_{A^r}
> \le
> C(r,\Phi,\kappa,M,\|u\|_{A^r}).
> \]
> Moreover, on bounded \(A^r\)-sets inside the same positive range,
> \[
> \|\Phi(u)-\Phi(w)\|_{A^r}
> \le
> C\|u-w\|_{A^r}.
> \]

This handles

\[
u^m,\qquad u^\gamma,\qquad S(R(u^\gamma)).
\]

But this composition theorem is a **major missing project lemma**. Mathlib has general smooth calculus, continuous maps, and algebraic measurability tools, but not a Fourier–Wiener composition theorem for \(A^r\). For real non-integer powers, the positivity lower bound is not cosmetic; without it, \(x\mapsto x^m\) may fail to be smooth at \(0\).

Thus Layer‑3 should expose two versions:

1. **integer-exponent version**, using only algebra products;
2. **real-exponent version**, assuming a positive slab:
   \[
   \exists\kappa>0,\quad
   \kappa\le u(t,x)
   \quad\text{on }[\delta,T]\times[0,1].
   \]

## Flux estimate

Assume

\[
u\in A^r,\qquad \kappa\le u\le M.
\]

Then

\[
u^\gamma\in A^r,
\]

\[
v=R(u^\gamma)\in A^{r+2},
\]

\[
v_x\in A^{r+1}\subset A^r,
\]

\[
S(v)\in A^r,
\]

and

\[
u^m\in A^r.
\]

Therefore

\[
\boxed{
Q(u)=u^mS(v)v_x\in A^r.
}
\]

The local bound is

\[
\boxed{
\|Q(u)\|_{A^r}
\le
C(r,\kappa,M,\|u\|_{A^r}).
}
\]

On bounded positive \(A^r\)-sets,

\[
\boxed{
\|Q(u)-Q(w)\|_{A^r}
\le
C\|u-w\|_{A^r}.
}
\]

For time regularity one degree lower, use:

If

\[
u\in A^{r+1},
\]

then

\[
Q(u)\in A^{r+1},
\]

so

\[
\partial_xQ(u)\in A^r.
\]

---

# 3. Bootstrap mechanism

The clean bootstrap is delayed in time.

Fix

\[
0<t_0<t_1<T.
\]

Assume on \([t_0,T]\):

\[
u\in C([t_0,T];A^r),
\]

and, for real powers,

\[
0<\kappa\le u(t,x)\le M.
\]

Then on \([t_1,T]\), rewrite the mild equation from time \(t_0\):

\[
u(t)=E(t-t_0)u(t_0)
+
\int_{t_0}^tE(t-\tau)F(u(\tau))\,d\tau
-
\chi
\int_{t_0}^t\partial_xE(t-\tau)Q(u(\tau))\,d\tau.
\]

The initial term

\[
E(t-t_0)u(t_0)
\]

is in \(A^{r+M_0}\) for every \(M_0\), uniformly on \(t\in[t_1,T]\), because \(t-t_0\ge t_1-t_0>0\).

The reaction term gains any \(<2\) derivatives.

The transport term gains any \(<1\) derivative.

Thus, for any

\[
0<\theta<1,
\]

\[
\boxed{
u\in C([t_1,T];A^{r+\theta}).
}
\]

This is the one-step bootstrap.

Iterating with a decreasing sequence of delays,

\[
\delta/2<\delta_1<\delta_2<\cdots<\delta,
\]

gives

\[
u\in C([\delta,T];A^R)
\]

for every finite \(R\).

For Lean, I would pin the generic one-step lemma with arbitrary \(0<\theta<1\), but downstream proofs can instantiate

\[
\theta=\frac12
\]

to avoid repeated real-inequality noise.

---

# 4. The seed problem

This is the main adversarial point.

From a pure \(C^0\) source \(q\), the estimate

\[
\|\partial_xE(s)q\|_{A^0}
\]

behaves like

\[
s^{-1}
\|q\|_{C^0}
\]

if proved through coefficient bounds, which is not time-integrable near \(s=0\). More explicitly, \(C^0\) only gives bounded Fourier coefficients, and

\[
\sum_k |k|e^{-\pi^2k^2s}
\sim s^{-1}.
\]

So the implication

\[
C^0\text{ mild}
\Longrightarrow
A^0\text{ for }t>0
\]

is **not a direct consequence** of the Layer‑1 \(A^r\to A^{r+m}\) smoothing estimates.

The least-disruptive fix is to add a Layer‑3 seed lemma:

> **Time-weighted \(A^\sigma\) seed.**  
> Let \(0<\sigma<1\). If \(u\) is the Layer‑2 \(C^0\) mild solution on \([0,T]\), then for every \(\delta>0\),
> \[
> u\in C([\delta,T];A^\sigma).
> \]

Proof idea:

Restart at \(t_0\), with datum \(u(t_0)\in C^0\). Use a fixed point on the time-weighted space

\[
\mathcal X_{\sigma,\beta,T}
=
\left\{
w\in C([0,T];C^0):
\sup_{0<s\le T}s^\beta\|w(s)\|_{A^\sigma}<\infty
\right\},
\]

with

\[
\beta=\frac{\sigma+1}{2}<1.
\]

The heat term satisfies

\[
\|E(s)f\|_{A^\sigma}
\le
C_\sigma s^{-(\sigma+1)/2}\|f\|_{C^0}.
\]

The reaction term uses

\[
\int_0^t s^{-\beta}\,ds<\infty
\quad\text{because }\beta<1.
\]

The transport term uses

\[
\int_0^t(t-\tau)^{-1/2}\tau^{-\beta}\,d\tau
=
t^{1/2-\beta}B(1/2,1-\beta),
\]

which is finite precisely because

\[
\beta<1.
\]

Multiplying by \(t^\beta\), the transport contribution is \(O(t^{1/2})\), small on short intervals. This gives a contraction in the weighted \(A^\sigma\) norm, while Layer‑2 uniqueness identifies the weighted solution with the already-constructed \(C^0\) mild solution.

This seed lemma is not Mathlib infrastructure; it is project PDE infrastructure built from the Layer‑1 heat estimates, Layer‑2 uniqueness, the Banach fixed-point theorem, scalar beta-integral estimates, and Bochner integral estimates. The interval-integral library has the general interval integral apparatus, but the specific singular-kernel formulas should be pinned as project lemmas. citeturn785980view3

---

# 5. Time regularity and classicality

Once the spatial bootstrap gives

\[
u\in C([\delta,T];A^{r+2}),
\]

and the nonlinearity estimates give

\[
F(u)\in C([\delta,T];A^r),
\]

\[
Q(u)\in C([\delta,T];A^{r+1}),
\]

then

\[
\partial_xQ(u)\in C([\delta,T];A^r),
\]

and

\[
\partial_{xx}u\in C([\delta,T];A^r).
\]

Define the full source

\[
\mathcal N(u)
=
F(u)-\chi\partial_xQ(u).
\]

Then

\[
\mathcal N(u)\in C([\delta,T];A^r).
\]

The PDE identity becomes

\[
\boxed{
\partial_tu
=
\partial_{xx}u+\mathcal N(u)
\quad\text{in }A^r.
}
\]

Thus

\[
\boxed{
u\in C^1([\delta,T];A^r)
}
\]

whenever

\[
u\in C([\delta,T];A^{r+2}).
\]

This is the parabolic trade:

\[
2\text{ spatial }A\text{-derivatives}
\quad\Longrightarrow\quad
1\text{ time derivative}.
\]

Iterating gives mixed regularity:

\[
u\in C^j([\delta,T];A^r)
\]

provided one has enough spatial regularity, schematically

\[
u\in C([\delta,T];A^{r+2j}).
\]

For physical classicality, use the Fourier embedding:

\[
A^s\hookrightarrow C^k([0,1])
\qquad\text{if }s\ge k,
\]

with

\[
\|\partial_x^k f\|_\infty
\le
C_k\|f\|_{A^k}.
\]

Since the bootstrap gives \(A^s\) for all \(s\) at positive time,

\[
u\in C^\infty_x
\]

for every \(t>0\), and the equation gives the corresponding time regularity.

For Layer‑7 compactness/equicontinuity, the useful corollary is:

If on \([\delta,T]\)

\[
\sup_t\|u(t)\|_{A^{r+2}}\le M,
\]

and the nonlinear bounds give

\[
\sup_t\|\mathcal N(u(t))\|_{A^r}\le M_N,
\]

then

\[
\|\partial_tu(t)\|_{A^r}
\le
C M+M_N.
\]

Hence

\[
\boxed{
\|u(t)-u(s)\|_{A^r}
\le
C|t-s|
}
\]

on positive-time slabs.

---

# 6. Numbered Layer‑3 lemma DAG

Below is the interface I would pin.

## Semigroup and scalar kernel block

### 1. `weight_submultiplicative`

For \(r\ge0\),

\[
(1+|k+\ell|)^r
\le
(1+|k|)^r(1+|\ell|)^r.
\]

Consumes: elementary real inequalities.  
Mathlib scaffold: ordered algebra, real powers, integer absolute value.

---

### 2. `heat_multiplier_gain`

For \(m\ge0\), \(t>0\),

\[
\sup_{k\in\mathbb Z}
(1+|k|)^m e^{-\pi^2k^2t}
\le
C_m t^{-m/2}.
\]

Consumes: scalar calculus.  
Mathlib scaffold: real exponential, finite/sup estimates over \(\mathbb Z\), comparison with continuous maximum.

---

### 3. `heat_smoothing_A`

For \(r,m\ge0\), \(t>0\),

\[
\|E(t)a\|_{A^{r+m}}
\le
C_m t^{-m/2}\|a\|_{A^r}.
\]

Consumes: Lemma 2.  
Mathlib scaffold: `lp`/summability/tsum norm estimates.

---

### 4. `heat_derivative_smoothing_A`

For \(j\in\mathbb N\), \(m\ge0\), \(t>0\),

\[
\|\partial_x^jE(t)a\|_{A^{r+m}}
\le
C_{j,m}t^{-(j+m)/2}\|a\|_{A^r}.
\]

Consumes: Lemma 2 with extra \(|k|^j\).  
Mathlib scaffold: multiplier bounds and `tsum`.

---

### 5. `kernel_power_interval_integral`

For \(0\le a<1\),

\[
\int_0^t(t-\tau)^{-a}\,d\tau
=
\frac{t^{1-a}}{1-a}.
\]

Consumes: scalar interval integration.  
Mathlib scaffold: interval integral, change of variables, real power integrability. Interval integral infrastructure exists, but this exact singular-kernel lemma should be project-pinned. citeturn785980view3

---

### 6. `beta_kernel_interval_integral`

For \(a<1\), \(b<1\), \(t>0\),

\[
\int_0^t(t-\tau)^{-a}\tau^{-b}\,d\tau
=
t^{1-a-b}B(1-a,1-b),
\]

or at least the bound

\[
\int_0^t(t-\tau)^{-a}\tau^{-b}\,d\tau
\le
C_{a,b}t^{1-a-b}.
\]

Consumes: scalar beta-integral estimate.  
Mathlib scaffold: interval integral plus domination; exact beta identity optional.

---

### 7. `duhamel_heat_gain_A`

If

\[
F\in C([0,T];A^r)
\]

and \(0\le m<2\), then

\[
t\mapsto
\int_0^tE(t-\tau)F(\tau)\,d\tau
\]

belongs to \(C([0,T];A^{r+m})\), and

\[
\left\|
\int_0^tE(t-\tau)F(\tau)\,d\tau
\right\|_{A^{r+m}}
\le
C t^{1-m/2}\|F\|_{C_tA^r}.
\]

Consumes: Lemmas 3 and 5.  
Mathlib scaffold: strong measurability from continuity, Bochner integral norm estimate. citeturn366577view0 citeturn785980view0

---

### 8. `duhamel_transport_gain_A`

If

\[
Q\in C([0,T];A^r)
\]

and \(0\le m<1\), then

\[
t\mapsto
\int_0^t\partial_xE(t-\tau)Q(\tau)\,d\tau
\]

belongs to \(C([0,T];A^{r+m})\), and

\[
\left\|
\int_0^t\partial_xE(t-\tau)Q(\tau)\,d\tau
\right\|_{A^{r+m}}
\le
C t^{(1-m)/2}\|Q\|_{C_tA^r}.
\]

Consumes: Lemmas 4 and 5.  
Mathlib scaffold: same Bochner infrastructure.

---

## \(A^r\) algebra and Fourier operators

### 9. `A_convolution_well_defined`

If \(a,b\in A^r\), then the convolution

\[
(a*b)_k=\sum_{\ell}a_\ell b_{k-\ell}
\]

is absolutely summable modewise.

Consumes: Lemma 1.  
Mathlib scaffold: summable products, `tsum` domination, nonnegative series.

---

### 10. `A_banach_algebra_product`

For \(r\ge0\),

\[
\|ab\|_{A^r}\le C_r\|a\|_{A^r}\|b\|_{A^r}.
\]

Consumes: Lemmas 1 and 9.  
Mathlib scaffold: `lp` \(p=1\), `Summable`, `tsum`, Fubini/Tonelli for nonnegative series.  
Status: **missing, must build**.

---

### 11. `A_product_lipschitz_on_ball`

For \(\|f\|_{A^r},\|g\|_{A^r},\|\tilde f\|_{A^r},\|\tilde g\|_{A^r}\le M\),

\[
\|fg-\tilde f\tilde g\|_{A^r}
\le
C_{r,M}
\left(
\|f-\tilde f\|_{A^r}
+
\|g-\tilde g\|_{A^r}
\right).
\]

Consumes: Lemma 10.  
Mathlib scaffold: normed ring estimates after project algebra is built.

---

### 12. `derivative_multiplier_A`

For \(j\in\mathbb N\),

\[
\|\partial_x^j f\|_{A^r}
\le
C_{j,r}\|f\|_{A^{r+j}}.
\]

Consumes: coefficient multiplier estimate.  
Mathlib scaffold: `tsum` comparison.

---

### 13. `laplacian_generator_A`

\[
\|\partial_{xx} f\|_{A^r}
\le
C_r\|f\|_{A^{r+2}}.
\]

Consumes: Lemma 12 with \(j=2\).  
Mathlib scaffold: multiplier estimate.

---

### 14. `resolvent_gain_A`

\[
\|Rf\|_{A^{r+2}}\le C_r\|f\|_{A^r}.
\]

Also:

\[
\|\partial_xRf\|_{A^{r+1}}\le C_r\|f\|_{A^r},
\]

\[
\|\partial_{xx}Rf\|_{A^r}\le C_r\|f\|_{A^r}.
\]

Consumes: spectral multiplier \((1+\pi^2k^2)^{-1}\).  
Mathlib scaffold: scalar inequalities plus `tsum`.

---

### 15. `A_to_Ck_embedding`

If \(s\ge k\), then

\[
A^s\hookrightarrow C^k([0,1]),
\]

with

\[
\|\partial_x^k f\|_\infty
\le
C_k\|f\|_{A^s}.
\]

Consumes: absolute convergence of differentiated Fourier series.  
Mathlib scaffold: summable uniform convergence / Weierstrass M-test, continuous functions.

---

## Composition and nonlinearities

### 16. `integer_power_A`

For \(n\in\mathbb N\),

\[
\|u^n\|_{A^r}
\le
C_{r,n}\|u\|_{A^r}^n.
\]

Consumes: Lemma 10.  
Mathlib scaffold: repeated multiplication in a normed algebra, after project algebra exists.

---

### 17. `smooth_composition_A_positive_range`

If

\[
u\in A^r,\qquad
\kappa\le u(x)\le M,
\]

and \(\Phi\) is smooth on an interval containing \([\kappa,M]\), then

\[
\Phi(u)\in A^r,
\]

with local bounds and local Lipschitz estimates.

Consumes: Lemma 10 plus a project Fourier–Wiener composition theorem.  
Status: **major missing project theorem**.  
Use for \(u^m\), \(u^\gamma\), and \(S(v)\).

---

### 18. `reaction_bound_A`

For

\[
F(u)=au-bu^p,
\]

on a positive \(A^r\)-bounded slab,

\[
\|F(u)\|_{A^r}
\le
C,
\]

and

\[
\|F(u)-F(w)\|_{A^r}
\le
C\|u-w\|_{A^r}.
\]

Consumes: Lemmas 10, 16 or 17.

---

### 19. `flux_bound_A`

For

\[
Q(u)=u^mS(R(u^\gamma))\partial_xR(u^\gamma),
\]

on a positive \(A^r\)-bounded slab,

\[
\|Q(u)\|_{A^r}
\le
C,
\]

and

\[
\|Q(u)-Q(w)\|_{A^r}
\le
C\|u-w\|_{A^r}.
\]

Consumes: Lemmas 10, 11, 14, 17.

---

### 20. `flux_bound_A_plus_one`

If

\[
u\in A^{r+1}
\]

on a positive slab, then

\[
Q(u)\in A^{r+1},
\]

and

\[
\|\partial_xQ(u)\|_{A^r}
\le
C.
\]

Consumes: Lemmas 12, 14, 17, 19.

---

## Seed and bootstrap

### 21. `C0_to_time_weighted_A_sigma_seed`

For \(0<\sigma<1\), if \(u\) is the Layer‑2 \(C^0\) mild solution, then for every \(0<\delta<T\),

\[
u\in C([\delta,T];A^\sigma).
\]

Consumes: Layer‑1 \(C^0\to A^\sigma\) heat estimate, Lemmas 6, 7, 8, Layer‑2 uniqueness.  
Status: **not in Mathlib; project PDE lemma**.

---

### 22. `A_bootstrap_one_step`

Let \(0<t_0<t_1<T\). Suppose

\[
u\in C([t_0,T];A^r),
\]

and, for real powers,

\[
\kappa\le u(t,x)\le M.
\]

Then for every \(0<\theta<1\),

\[
u\in C([t_1,T];A^{r+\theta}).
\]

Consumes: Lemmas 7, 8, 18, 19.

---

### 23. `A_bootstrap_all_orders_positive_time`

If \(u\) satisfies the seed lemma and the positive-slab hypotheses, then for every \(\delta>0\) and every \(R\ge0\),

\[
u\in C([\delta,T];A^R).
\]

Consumes: Lemmas 21 and 22, finite iteration.

---

## Classicality and time regularity

### 24. `mild_solution_differentiable_in_time_A`

If

\[
u\in C([\delta,T];A^{r+2}),
\]

\[
F(u)\in C([\delta,T];A^r),
\]

\[
Q(u)\in C([\delta,T];A^{r+1}),
\]

then

\[
u\in C^1([\delta,T];A^r),
\]

and

\[
\partial_tu
=
\partial_{xx}u+F(u)-\chi\partial_xQ(u).
\]

Consumes: Lemmas 12, 13, 20, semigroup generator identity, Bochner fundamental theorem.  
Mathlib scaffold: Bochner integral and calculus primitives; exact semigroup-generator theorem is project-specific.

---

### 25. `positive_time_classical_solution`

For every \(\delta>0\),

\[
u\in C^1_tC^k_x([\delta,T]\times[0,1])
\]

for all finite \(k\), and the PDE holds pointwise with Neumann boundary conditions.

Consumes: Lemmas 15, 23, 24, Layer‑1 Neumann spectral facts.

---

### 26. `time_equicontinuity_A_for_compactness`

If on \([\delta,T]\)

\[
\sup_t\|u(t)\|_{A^{r+2}}\le M,
\]

then

\[
\|u(t)-u(s)\|_{A^r}
\le
C|t-s|.
\]

Consumes: Lemma 24.  
Used by: Layer‑7 time-translate compactness.

This is slightly beyond the requested 15–25 count; if you want exactly 25, merge Lemmas 24 and 26, but I would keep the equicontinuity corollary separately because Layer‑7 will consume it directly.

---

# 7. Mathlib gaps: missing vs derivable

## Already supported by Mathlib primitives

These are not PDE-ready, but the underlying infrastructure exists.

1. **\(\ell^p\)-style sequence spaces, summability, completeness.**  
   Mathlib documents `lp` as a subtype of functions satisfying a finite \(p\)-norm condition, with completeness for \(p\ge1\), plus useful norm and summability tools. citeturn827968view0

2. **Strong measurability from continuity and closure under operations.**  
   Useful for \(t\mapsto F(u(t))\), \(t\mapsto Q(u(t))\), and Banach-valued Duhamel integrands. citeturn366577view0

3. **Bochner integral norm estimates.**  
   The norm estimate
   \[
   \left\|\int f\right\|\le\int\|f\|
   \]
   is part of the documented Bochner integral API. citeturn785980view0

4. **Interval integrals and change-of-variable scaffolding.**  
   Enough to build the scalar singular-kernel estimates, though the exact heat-kernel power integrals should be pinned in the project. citeturn785980view3

## Derivable but must be built in this repo

These are straightforward but not one-line Mathlib applications.

1. Weighted \(A^r\) definition over \(\mathbb Z\).
2. \(A^r\) norm equivalence with weighted \(\ell^1\).
3. Heat multiplier smoothing.
4. Derivative multiplier smoothing.
5. Resolvent multiplier smoothing.
6. \(A^r\to C^k\) Fourier embedding.
7. Duhamel smoothing estimates with weakly singular kernels.
8. Time-continuity of the Duhamel maps.
9. Semigroup generator identity in \(A^r\).
10. Physical/spectral compatibility for the mild equation.

## Genuinely missing project infrastructure

These are the big ones.

### Gap A: weighted \(\ell^1\) convolution Banach algebra

Mathlib does not appear to have the exact theorem:

\[
\ell^1((1+|k|)^r)\ast\ell^1((1+|k|)^r)
\subset
\ell^1((1+|k|)^r).
\]

Build it.

Closest scaffold:

\[
\text{lp} + \text{Summable} + \text{tsum} + \text{nonnegative Tonelli-style rearrangements}.
\]

This is essential.

### Gap B: Fourier–Wiener smooth composition

Needed for real powers and \(S(v)\):

\[
u\in A^r,\quad \kappa\le u\le M
\quad\Longrightarrow\quad
\Phi(u)\in A^r.
\]

This is not a generic Mathlib composition theorem. It is a serious project lemma.

If you want to reduce scope, first prove:

1. integer powers by algebra;
2. reciprocal on positive range;
3. rational powers if needed by analytic construction;
4. then smooth composition later.

But for arbitrary real \(m,\gamma\), you need this.

### Gap C: positive lower bound on positive-time slabs

For non-integer real powers, nonnegativity is not enough for \(C^\infty\) composition. You need either:

\[
u(t,x)\ge\kappa_{\delta,T}>0
\quad\text{on }[\delta,T]\times[0,1],
\]

or you must restrict to exponent regimes where \(x\mapsto x^m\) is smooth at \(0\), such as integer powers.

Layer‑2 positivity gives \(u\ge0\). It does **not** automatically give the strict lower bound needed for smooth real-power composition. A strong-positivity or Harnack-style lemma is an additional PDE dependency.

### Gap D: \(C^0\to A^\sigma\) seed

The seed

\[
C^0\text{ mild}\Longrightarrow A^\sigma\text{ for }t>0
\]

is not automatic from the \(A^r\)-semigroup estimates. It needs the time-weighted \(A^\sigma\) fixed-point/restart lemma described above.

---

# 8. Convergence check

Layer‑3 does **not** close from only:

\[
\text{Layer‑1 }A^r\text{ smoothing}
+
\text{Layer‑2 bare }C^0\text{ mild existence output}.
\]

It needs three extra interfaces pinned inside Layer‑3 or as prerequisites:

1. **Seed regularity**
   \[
   C^0\text{ mild}
   \Longrightarrow
   C([\delta,T];A^\sigma),
   \qquad 0<\sigma<1.
   \]
   Best proved by a time-weighted \(A^\sigma\) restart/fixed-point argument.

2. **Composition in \(A^r\)**
   for real powers and \(S(v)\), ideally on positive ranges:
   \[
   \kappa\le u\le M.
   \]

3. **Strict positive lower bound**, unless all problematic powers are integer/smooth at zero.

Once those are available, the rest of Layer‑3 is self-contained:

\[
A^\sigma
\overset{+\,\theta<1}{\Longrightarrow}
A^{\sigma+\theta}
\overset{+\,\theta<1}{\Longrightarrow}
A^{\sigma+2\theta}
\Longrightarrow
\cdots
\Longrightarrow
A^R
\quad\forall R<\infty.
\]

Then

\[
A^{r+2}
+
\text{nonlinearity in }A^r
\Longrightarrow
\partial_tu\in A^r,
\]

and

\[
A^R\ \forall R
\Longrightarrow
C^\infty_x
\]

for every positive time.

So the final Layer‑3 interface should be:

\[
\boxed{
\text{time-weighted seed}
+
\text{\(A^r\) algebra}
+
\text{\(A^r\) composition}
+
\text{Duhamel gain }(<1\text{ because of transport})
\Longrightarrow
\text{positive-time }A^\infty\text{ smoothing}.
}
\]

The dangerous false shortcut is:

\[
C^0
\overset{E}{\Longrightarrow}
A^0
\]

inside the transport Duhamel term. That shortcut fails because the differentiated heat kernel loses one derivative and the resulting coefficient bound is not summable at the endpoint.