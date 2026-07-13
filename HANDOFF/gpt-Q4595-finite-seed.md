ANSWER Q4595 49169192

# Critical \(m=1\) finite seed on the unit interval

## Executive conclusion

The finite seed is true, but the requested derivation mixes up the two different steps in Chen–Ruau–Shen, Part I, §4.3.

* **Seed step:** for \(1<p<(2\beta-1)/\chi _0\), one must use the elliptic equation once with the special weight exponent \(2\beta-1\). This absorbs the chemotactic term directly into a strict fraction of the diffusion and leaves only a multiple of \(\int u^p\). This is the mechanism behind equations (4.7)–(4.10) in the paper.
* **Bootstrap step:** after the seed has already been obtained, one uses \(q=(p+\gamma)/\gamma\) and the signal-weighted estimate to get
  
  \[
  \text{chemotaxis}\le \varepsilon G_p+C_{\varepsilon,p}\int u^{p+\gamma}.
  \]
  
  This is equation (4.13), used to feed Corollary 2.1. It is **not** the finite-seed closure.

The proposed assertion

\[
\int_0^1u^{p+\gamma}
 \le \frac{c_0}{2}G_p+C(\|u\|_{L^1})
 \qquad\text{merely from }p>\gamma/2
\tag{false in general}
\]

is false for unrestricted \(\gamma>0\). With the \(L^1\) mass as low anchor, the exact one-dimensional Gagliardo–Nirenberg exponent is absorbable precisely when \(\gamma<2\), independently of \(p\). The condition \(p>\gamma/2\) occurs only if the low anchor is the current \(L^p\) energy \(Y_p=\int u^p\), and then the remainder is a superlinear power of \(Y_p\), not a mass-only constant.

Below is the exact corrected proof. Since the question assumes \(b>0\), the remaining logistic term gives the requested scalar absorbing ODE with completely explicit constants. The same seed can also be closed for \(b=0\), as in the paper, by the mass/Ehrling lemma.

---

## 0. Choice of the seed exponent

On \(N=1\), set

\[
\chi_\beta:=\frac{2(2\beta-1)}{\max\{2,\gamma\}}.
\]

If

\[
0<\chi_0<\chi_\beta,
\]

then

\[
\frac{2\beta-1}{\chi_0}
  >\frac{\max\{2,\gamma\}}2
  =\max\left\{1,\frac\gamma2\right\}.
\]

Hence the interval

\[
\left(\max\left\{1,\frac\gamma2\right\},
      \frac{2\beta-1}{\chi_0}\right)
\]

is nonempty. A Lean-friendly explicit choice is

\[
p_0:=\frac12\left(
       \max\left\{1,\frac\gamma2\right\}
       +\frac{2\beta-1}{\chi_0}\right).
\]

The lower inequality \(p_0>\max\{1,\gamma/2\}\) is needed by the **later bootstrap** with \(ho=\gamma\), \(N=1\). The finite-seed energy argument below itself only needs

\[
1<p_0<\frac{2\beta-1}{\chi_0}.
\]

---

## 1. Exact \(u^p\) energy inequality and the \(2\beta-1\) absorption

Fix temporarily

\[
1<p<\frac{2\beta-1}{\chi_0}.
\]

Write

\[
\begin{aligned}
Y(t)&:=\int_0^1u(t,x)^p\,dx,\\
H(t)&:=\int_0^1u^{p-2}|u_x|^2\,dx,\\
G_p(t)&:=\int_0^1\left|\partial_xu^{p/2}\right|^2dx
       =\frac{p^2}{4}H(t),\\
Z(t)&:=\int_0^1u^{p+\alpha}\,dx,\\
I_s(t)&:=\int_0^1
  \frac{u^{p-1}u_xv_x}{(1+v)^s}\,dx,\\
J_s(t)&:=\int_0^1
  \frac{u^p|v_x|^2}{(1+v)^s}\,dx.
\end{aligned}
\]

All quantities are evaluated at the same time \(t\). Positivity of \(u\), nonnegativity of \(v\), classical regularity, and the Neumann conditions justify the following integrations by parts.

### 1.1 Testing the parabolic equation by \(u^{p-1}\)

Multiplication by \(u^{p-1}\), integration over \([0,1]\), and the Neumann boundary conditions give the exact identity

\[
\boxed{
\frac1pY'(t)+(p-1)H(t)+bZ(t)
 =(p-1)\chi_0 I_\beta(t)+aY(t).
}
\tag{1.1}
\]

Equivalently, in terms of the requested \(G_p\),

\[
\boxed{
Y'(t)+\frac{4(p-1)}pG_p(t)+pbZ(t)
 =p(p-1)\chi_0 I_\beta(t)+paY(t).
}
\tag{1.2}
\]

The first Young estimate is

\[
(p-1)\chi_0I_\beta
 \le \frac{p-1}{2}H
   +\underbrace{\frac{(p-1)\chi_0^2}{2}}_{=:B_c}
     J_{2\beta}.
\tag{1.3}
\]

The entire issue is to control the \(B_cJ_{2\beta}\) term without spending all of the remaining diffusion.

### 1.2 The weighted elliptic identity

Let \(\delta>0\). Multiply

\[
0=v_{xx}-\mu v+\nu u^\gamma
\]

by \(u^p(1+v)^{-\delta}\) and integrate. Since \(v_x=0\) at both endpoints,

\[
\boxed{
\delta J_{\delta+1}
 =pI_\delta
  +\mu\int_0^1\frac{u^pv}{(1+v)^\delta}\,dx
  -\nu\int_0^1\frac{u^{p+\gamma}}{(1+v)^\delta}\,dx.
}
\tag{1.4}
\]

Now choose

\[
\delta=2\beta-1.
\]

This is the first exact appearance of \(2\beta-1\): the positive elliptic gradient term has denominator exponent \(\delta+1\), and matching the \(J_{2\beta}\) produced by (1.3) forces

\[
\delta+1=2\beta
\quad\Longleftrightarrow\quad
\delta=2\beta-1.
\]

Because \(\beta\ge1\), we have \(\delta\ge1\) and

\[
0\le\frac{v}{(1+v)^\delta}\le1.
\]

Discarding the favorable last term in (1.4) and multiplying by \((p-1)\chi_0/p\) gives

\[
\frac{(p-1)\chi_0(2\beta-1)}pJ_{2\beta}
 \le (p-1)\chi_0I_{2\beta-1}
    +\frac{(p-1)\chi_0\mu}{p}Y.
\tag{1.5}
\]

A second Young estimate gives

\[
(p-1)\chi_0I_{2\beta-1}
 \le \frac{p-1}{2}H+B_cJ_{4\beta-2}.
\tag{1.6}
\]

Since \(v\ge0\) and \(\beta\ge1\),

\[
4\beta-2\ge2\beta,
\qquad
J_{4\beta-2}\le J_{2\beta}.
\]

Therefore

\[
\boxed{
D_cJ_{2\beta}
 \le \frac{p-1}{2}H
   +\frac{(p-1)\chi_0\mu}{p}Y,
}
\tag{1.7}
\]

where

\[
D_c
 :=\frac{(p-1)\chi_0(2\beta-1)}p-B_c
 =(p-1)\chi_0
   \left(\frac{2\beta-1}{p}-\frac{\chi_0}{2}\right).
\]

### 1.3 Why \(p\chi_0<2\beta-1\) is the exact strict-absorption condition

To use (1.7) in (1.3), define

\[
\lambda_p:=\frac{B_c}{D_c}
 =\frac{p\chi_0}{2(2\beta-1)-p\chi_0}.
\tag{1.8}
\]

Merely having \(D_c>0\) would require only

\[
p\chi_0<2(2\beta-1).
\]

That is not enough. The first Young inequality has already spent one half of the diffusion. To control \(B_cJ_{2\beta}\) and still leave a **strictly positive** part of the other half, one needs

\[
B_c<D_c.
\]

The coefficient algebra is exact:

\[
\begin{aligned}
B_c<D_c
&\Longleftrightarrow
 \frac{(p-1)\chi_0^2}{2}
 <\frac{(p-1)\chi_0(2\beta-1)}p
   -\frac{(p-1)\chi_0^2}{2}\\
&\Longleftrightarrow
 \chi_0<\frac{2\beta-1}{p}\\
&\Longleftrightarrow
 p<\frac{2\beta-1}{\chi_0}.
\end{aligned}
\tag{1.9}
\]

Equivalently,

\[
0<\lambda_p<1.
\]

Multiplying (1.7) by \(\lambda_p=B_c/D_c\) and substituting into (1.3) yields

\[
\boxed{
(p-1)\chi_0I_\beta
 \le \frac{p-1}{2}(1+\lambda_p)H
   +\lambda_p\frac{(p-1)\chi_0\mu}{p}Y.
}
\tag{1.10}
\]

Inserting (1.10) into (1.1) gives

\[
\frac1pY'
 +\frac{p-1}{2}(1-\lambda_p)H
 +bZ
 \le
 \left(a+\lambda_p\frac{(p-1)\chi_0\mu}{p}\right)Y.
\tag{1.11}
\]

Since \(H=4G_p/p^2\), after multiplying by \(p\),

\[
\boxed{
Y'+c_0G_p+pbZ\le A_pY,
}
\tag{1.12}
\]

with the completely explicit constants

\[
\boxed{
\begin{aligned}
\lambda_p
  &:=\frac{p\chi_0}{2(2\beta-1)-p\chi_0},\\[1mm]
c_0
  &:=\frac{2(p-1)}p(1-\lambda_p)
   =\frac{4(p-1)((2\beta-1)-p\chi_0)}
          {p(2(2\beta-1)-p\chi_0)}>0,\\[1mm]
A_p
  &:=pa+\lambda_p(p-1)\chi_0\mu.
\end{aligned}
}
\tag{1.13}
\]

This is the desired finite-seed differential inequality. No \(u^{p+\gamma}\) term remains.

### 1.4 The second appearance of \(2\beta-1\): the later \(q\)-estimate

For the later bootstrap, Young with conjugate exponents \((p+\gamma)/p\) and

\[
q:=\frac{p+\gamma}{\gamma}
\]

produces a signal term with denominator \((1+v)^{2\beta q}\). The signal estimate has denominator

\[
(1+v)^{(1+\delta)q}.
\]

Matching these exponents again requires

\[
(1+\delta)q=2\beta q
\quad\Longleftrightarrow\quad
\delta=2\beta-1.
\]

Thus the same weight appears in both steps, but its roles are different:

1. in the finite seed, the **coefficient comparison** \(B_c<D_c\) creates the threshold \(p\chi_0<2\beta-1\);
2. in the bootstrap, \(\delta=2\beta-1\) only matches denominator powers and yields a bound by \(C\int u^{p+\gamma}\).

The latter estimate contains no mechanism that would by itself produce the critical interval \(p<(2\beta-1)/\chi_0\).

---

## 2. Audit of the proposed Gagliardo–Nirenberg closure

The requested mass-only estimate for \(\int u^{p+\gamma}\) is not valid in the stated generality. Here are the exact exponents.

Set

\[
f:=u^{p/2},
\qquad
r:=\frac{2(p+\gamma)}p,
\qquad
\int u^{p+\gamma}=\|f\|_{L^r}^r,
\qquad
G_p=\|f_x\|_2^2.
\]

### 2.1 Using the \(L^1\) mass as the low anchor

The mass identity is

\[
\|f\|_{L^{2/p}}^{2/p}=\int_0^1u=M.
\]

The one-dimensional GN relation

\[
\frac1r
 =\theta\left(\frac12-1\right)
  +\frac{1-\theta}{2/p}
\]

gives

\[
\boxed{
\theta
 =\frac{p(p+\gamma-1)}{(p+\gamma)(p+1)}.
}
\tag{2.1}
\]

Raising the GN estimate to the \(r\)-th power gives

\[
\boxed{
\int_0^1u^{p+\gamma}
 \le C
 G_p^{\frac{p+\gamma-1}{p+1}}
 M^{\frac{2p+\gamma}{p+1}}
 +CM^{p+\gamma}.
}
\tag{2.2}
\]

Indeed,

\[
\frac{\theta r}{2}=\frac{p+\gamma-1}{p+1}.
\]

The gradient power is strictly below \(1\) precisely when

\[
\frac{p+\gamma-1}{p+1}<1
\quad\Longleftrightarrow\quad
\gamma<2.
\tag{2.3}
\]

Therefore, only for \(0<\gamma<2\) can Young's inequality turn (2.2) into

\[
\boxed{
\int_0^1u^{p+\gamma}
 \le \varepsilon G_p
  +C_{\varepsilon,p,\gamma}
   \left(
    M^{\frac{2p+\gamma}{2-\gamma}}+M^{p+\gamma}
   \right).
}
\tag{2.4}
\]

For \(\gamma=2\), the leading term in (2.2) is \(CM^2G_p\), so absorption requires a small-mass condition. For \(\gamma>2\), the power of \(G_p\) is greater than \(1\), and no estimate of the form \(\varepsilon G_p+C(M)\) is possible.

### 2.2 Scaling obstruction

Choose a nonnegative \(\phi\in C_c^\infty((-1,1))\) with \(\int\phi=1\), fix \(x_0\in(0,1)\), and set for small \(\delta>0\)

\[
u_\delta(x):=M\delta^{-1}
 \phi\left(\frac{x-x_0}{\delta}\right).
\]

Then \(\int u_\delta=M\), while

\[
\int u_\delta^{p+\gamma}
 \asymp M^{p+\gamma}\delta^{1-p-\gamma},
\qquad
G_p(u_\delta)
 \asymp M^p\delta^{-p-1}.
\]

Hence

\[
\frac{\int u_\delta^{p+\gamma}}{G_p(u_\delta)}
 \asymp M^\gamma\delta^{2-\gamma}.
\]

For \(\gamma>2\), this ratio tends to infinity. For \(\gamma=2\), it stays proportional to \(M^2\), so an arbitrarily prescribed coefficient such as \(c_0/2\) cannot be obtained without a smallness assumption. This rules out the requested mass-only inequality under the theorem's unrestricted \(\gamma>0\).

### 2.3 Where \(p>\gamma/2\) actually enters

If instead the low anchor is \(\|f\|_2^2=Y\), then

\[
\frac1r
 =\theta\left(\frac12-1\right)
  +\frac{1-\theta}{2}
\]

gives

\[
\theta=\frac{\gamma}{2(p+\gamma)},
\qquad
\theta r=\frac\gamma p.
\]

Thus \(p>\gamma/2\) is exactly the condition \(\theta r<2\) needed to absorb the derivative factor. The resulting estimate is

\[
\boxed{
\int u^{p+\gamma}
 \le C G_p^{\gamma/(2p)}Y^{1+\gamma/(2p)}
   +CY^{1+\gamma/p}
}
\tag{2.5}
\]

and hence, when \(p>\gamma/2\),

\[
\boxed{
\int u^{p+\gamma}
 \le \varepsilon G_p
  +C_\varepsilon
    Y^{\frac{2p+\gamma}{2p-\gamma}}
  +CY^{1+\gamma/p}.
}
\tag{2.6}
\]

This is not a mass-only remainder. With arbitrary \(\alpha>0\), the logistic term does not necessarily dominate either power in (2.6). For example, domination of the first remainder would require

\[
\alpha\ge\frac{2p\gamma}{2p-\gamma},
\]

which is not a hypothesis of the critical branch.

Therefore \(p>\gamma/2\) is **not** the missing finite-seed GN condition. In the paper it is the input threshold \(p_0>\rho N/2\) for the subsequent bootstrap, with \(\rho=\gamma\) and \(N=1\).

### 2.4 Correct mass-based replacement when \(b\) is allowed to vanish

The paper's seed works even for \(b=0\). After (1.11), use the one-dimensional Ehrling/mass estimate: for every \(\eta>0\),

\[
\boxed{
Y\le \eta G_p+C_{\eta,p}M^p.
}
\tag{2.7}
\]

Choose \(\eta=c_0/(A_p+1)\). From \(Y'+c_0G_p\le A_pY\), one gets

\[
Y'+Y\le C_pM^p.
\tag{2.8}
\]

Thus a uniform or absorbing \(L^1\) mass bound immediately gives a uniform or absorbing \(L^p\) seed. This is the paper-faithful closure. The estimate involving \(u^{p+\gamma}\) is not used here.

---

## 3. Logistic absorbing ODE and explicit constants

Under the question's assumptions \(b>0\) and \(|[0,1]|=1\), Jensen's inequality gives

\[
Z(t)=\int_0^1u^{p+\alpha}
 =\int_0^1(u^p)^{1+\alpha/p}
 \ge \left(\int_0^1u^p\right)^{1+\alpha/p}
 =Y(t)^{1+\alpha/p}.
\tag{3.1}
\]

Drop the nonnegative term \(c_0G_p\) from (1.12). Then

\[
\boxed{
Y'(t)\le A_pY(t)-B_pY(t)^{1+\alpha/p},
}
\tag{3.2}
\]

where

\[
\boxed{
A_p:=pa+\lambda_p(p-1)\chi_0\mu,
\qquad
B_p:=pb.
}
\tag{3.3}
\]

These constants are independent of the time horizon and of the solution.

Let

\[
K_p:=\left(\frac{A_p}{B_p}\right)^{p/\alpha}.
\]

The scalar vector field \(A_py-B_py^{1+\alpha/p}\) is nonpositive for \(y\ge K_p\). Standard scalar comparison therefore yields

\[
Y(t)\le\max\{Y(s),K_p\}
\qquad (t\ge s),
\tag{3.4}
\]

and, on a global trajectory,

\[
\boxed{
\limsup_{t\to\infty}\int_0^1u(t,x)^p\,dx
 \le
 \left(
  \frac{pa+\lambda_p(p-1)\chi_0\mu}{pb}
 \right)^{p/\alpha}.
}
\tag{3.5}
\]

Equivalently,

\[
\boxed{
\limsup_{t\to\infty}\|u(t)\|_{L^p}
 \le
 \left(
  \frac{pa+\lambda_p(p-1)\chi_0\mu}{pb}
 \right)^{1/\alpha}.
}
\tag{3.6}
\]

Taking \(p=p_0\) gives the required finite seed. In particular, for every horizon \(T<T_{\max}\),

\[
\sup_{0\le t\le T}Y(t)
 \le\max\{Y(0),K_{p_0}\},
\]

with a right-hand side independent of \(T\). The given \(L^1\) absorbing bound is redundant for this \(b>0\) closure, although it is exactly what closes the stronger \(b\ge0\) paper route through (2.7)–(2.8).

---

## 4. Final finite-seed theorem

A clean corrected statement is:

> **Finite critical seed on \([0,1]\).**  Assume \(\beta\ge1\), \(a,b,\alpha,\gamma,\mu,\nu>0\), and
> 
> \[
> 0<\chi_0<\frac{2(2\beta-1)}{\max\{2,\gamma\}}.
> \]
> 
> Let \((u,v)\) be a positive classical Neumann solution of the parabolic–elliptic system. Choose
> 
> \[
> \max\{1,\gamma/2\}<p_0<(2\beta-1)/\chi_0.
> \]
> 
> Define
> 
> \[
> \lambda_0:=
> \frac{p_0\chi_0}{2(2\beta-1)-p_0\chi_0}.
> \]
> 
> Then \(0<\lambda_0<1\), and
> 
> \[
> \frac{d}{dt}\int u^{p_0}
> +\frac{2(p_0-1)}{p_0}(1-\lambda_0)
>   \int\left|\partial_xu^{p_0/2}\right|^2
> +p_0b\int u^{p_0+\alpha}
> \le
> \bigl(p_0a+\lambda_0(p_0-1)\chi_0\mu\bigr)
> \int u^{p_0}.
> \]
> 
> Consequently
> 
> \[
> \limsup_{t\to\infty}\int u^{p_0}
> \le
> \left(
>  \frac{p_0a+\lambda_0(p_0-1)\chi_0\mu}{p_0b}
> \right)^{p_0/\alpha}.
> \]

This is the finite seed needed before invoking the \(\rho=\gamma\) bootstrap estimate.

---

## 5. Lean 4 formalization plan: five dependency-ordered lemmas

Use `Real.rpow` for all real powers. The following interfaces are deliberately separated into scalar algebra, fixed-time elliptic analysis, the parabolic energy identity, and scalar ODE closure.

### Lemma 1 — existence of the critical seed exponent

```lean
/-- In dimension one, chi₀ < chiBeta opens the seed interval. -/
theorem exists_criticalSeedExponent
    {β γ χ₀ : ℝ}
    (hβ : 1 ≤ β) (hγ : 0 < γ) (hχ : 0 < χ₀)
    (hcrit : χ₀ < 2 * (2 * β - 1) / max 2 γ) :
    ∃ p₀ : ℝ,
      max 1 (γ / 2) < p₀ ∧
      p₀ < (2 * β - 1) / χ₀ := by
  -- midpoint choice; field_simp/linarith after positivity of denominators
  ...
```

This is pure ordered-field algebra.

### Lemma 2 — weighted elliptic \(J_{2\beta}\) control **(single hardest)**

At a fixed time, package the slice regularity, positivity, elliptic equation, endpoint Neumann data, and integrability. The target is

```lean
/-- Elliptic test by u^p / (1+v)^(2β-1). -/
theorem criticalWeightedEllipticControl
    (H : CriticalWeightedEllipticSliceData p β χ₀ μ ν u v) :
    let Hgrad := ∫ x, Real.rpow (u x) (p - 2) * (deriv u x)^2
                    ∂ intervalMeasure 1
    let Y := ∫ x, Real.rpow (u x) p ∂ intervalMeasure 1
    let J := ∫ x,
      Real.rpow (u x) p * (deriv v x)^2 /
        Real.rpow (1 + v x) (2 * β)
      ∂ intervalMeasure 1
    ((p - 1) * χ₀ * ((2 * β - 1) / p - χ₀ / 2)) * J
      ≤ (p - 1) / 2 * Hgrad
        + (p - 1) * χ₀ * μ / p * Y := by
  ...
```

The proof performs the weighted elliptic integration by parts, discards the nonpositive \(-\nu\int u^{p+\gamma}(1+v)^{-(2\beta-1)}\) term, applies Young to \(I_{2\beta-1}\), and proves the denominator monotonicity

```lean
Real.rpow (1 + v x) (-(4 * β - 2))
  ≤ Real.rpow (1 + v x) (-(2 * β))
```

from \(1\le1+v(x)\) and \(\beta\ge1\).

This is the hardest lemma because it combines real-rpow differentiation, interval integration by parts, endpoint cancellation, and weighted-integral monotonicity. It is the genuine analytic crux. Do not replace it by the \(q=(p+\gamma)/\gamma\) signal estimate.

### Lemma 3 — strict chemotactic absorption coefficient

```lean
def criticalSeedLambda (p β χ₀ : ℝ) : ℝ :=
  p * χ₀ / (2 * (2 * β - 1) - p * χ₀)

theorem criticalSeedLambda_mem_Ioo
    {p β χ₀ : ℝ}
    (hp : 1 < p) (hβ : 1 ≤ β) (hχ : 0 < χ₀)
    (hsub : p * χ₀ < 2 * β - 1) :
    criticalSeedLambda p β χ₀ ∈ Set.Ioo (0 : ℝ) 1 := by
  ...

/-- Combine the two Young inequalities with the elliptic control. -/
theorem criticalChemotaxisAbsorption
    (H : CriticalWeightedEllipticSliceData p β χ₀ μ ν u v)
    (hsub : p * χ₀ < 2 * β - 1) :
    (p - 1) * χ₀ * Iβ p β u v
      ≤ (p - 1) / 2 *
          (1 + criticalSeedLambda p β χ₀) * Hgrad p u
        + criticalSeedLambda p β χ₀ *
          ((p - 1) * χ₀ * μ / p) * Y p u := by
  ...
```

Once Lemma 2 exists, this is mostly `field_simp`, positivity, and `linarith`/`nlinarith`.

### Lemma 4 — critical \(L^p\) energy differential inequality

```lean
/-- PDE test by u^(p-1), followed by critical chemotactic absorption. -/
theorem criticalLpEnergy_diffIneq
    (S : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp : 1 < p)
    (hβ : 1 ≤ params.β)
    (hχ : 0 < params.χ₀)
    (hsub : p * params.χ₀ < 2 * params.β - 1) :
    ∀ t, 0 < t → t < T →
      HasDerivAt (fun s => Y p u s) (Ydot p u t) t ∧
      Ydot p u t
        + criticalSeedC0 p params.β params.χ₀ * G p u t
        + p * params.b * Z p params.α u t
      ≤ criticalSeedA p params * Y p u t := by
  ...
```

with

```lean
def criticalSeedC0 (p β χ₀ : ℝ) : ℝ :=
  2 * (p - 1) / p * (1 - criticalSeedLambda p β χ₀)

def criticalSeedA (p : ℝ) (params : CM2Params) : ℝ :=
  p * params.a
    + criticalSeedLambda p params.β params.χ₀
        * (p - 1) * params.χ₀ * params.μ
```

The existing time-Leibniz and Neumann diffusion-IBP infrastructure should be reused here.

### Lemma 5 — scalar logistic closure and final seed

```lean
/-- On a probability interval, the higher logistic moment dominates Y^(1+α/p). -/
theorem interval_logisticMoment_ge
    (hu : ∀ x, 0 ≤ u x) (hp : 0 < p) (hα : 0 < α) :
    Real.rpow (∫ x, Real.rpow (u x) p ∂ intervalMeasure 1)
        (1 + α / p)
      ≤ ∫ x, Real.rpow (u x) (p + α) ∂ intervalMeasure 1 := by
  ...

/-- Generic scalar absorbing logistic differential inequality. -/
theorem limsup_le_of_logistic_diffIneq
    {Y : ℝ → ℝ} {A B r : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hr : 0 < r)
    (hY : ∀ t, 0 ≤ Y t)
    (hDI : ∀ t, HasDerivAt Y (deriv Y t) t ∧
      deriv Y t ≤ A * Y t - B * Real.rpow (Y t) (1 + r)) :
    Filter.limsup Y Filter.atTop ≤ Real.rpow (A / B) (1 / r) := by
  ...
```

The final theorem instantiates

```lean
A := criticalSeedA p₀ params
B := p₀ * params.b
r := params.α / p₀
```

and obtains the seed bound.

---

## 6. Implementation warning for Codex

Do **not** create or attempt to prove a lemma of the form

```lean
p > γ / 2 →
∫ u^(p+γ) ≤ ε * Gp u + C (∫ u)
```

under unrestricted \(\gamma>0\). It is false, and the spike scaling above supplies a direct counterexample.

The correct attack order is:

```text
critical exponent interval
  → weighted elliptic identity with δ = 2β−1          [hardest]
  → coefficient ratio λp < 1
  → tested u^p energy inequality with c0 > 0
  → logistic scalar ODE (b > 0),
       or Ehrling + L¹ mass (paper's stronger b ≥ 0 route)
  → finite L^{p0} seed
  → only then use q=(p+γ)/γ and Corollary 2.1 bootstrap.
```

That separation matches the actual proof architecture and avoids building a false GN bridge.