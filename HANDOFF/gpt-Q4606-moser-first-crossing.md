ANSWER Q4606 d0ebf916

# Corrected finite-\(L^p\) Moser first crossing for Paper 2, Theorem 1.2

## Executive verdict

The finite-exponent bootstrap is valid for every \(\gamma>0\). It does **not** require \(\gamma<2\). The exact mechanism is the one in Chen–Ruau–Shen, Part I, Lemma 2.6:

1. start from one bounded exponent \(s=p_0>\max\{1,\gamma/2\}\);
2. using that \(L^s\) bound as the low Gagliardo–Nirenberg anchor, prove boundedness at every target exponent
   \[
   s<p<2s;
   \]
3. choose, for example, the new anchor \(s_1=\tfrac32s\), and repeat;
4. after finitely many repetitions, reach any prescribed finite \(P\).

The exact one-dimensional GN exponent is
\[
\eta=\frac{p+\gamma-s}{p+s}.
\]
It is absorbable into \(G_p=\|\partial_xu^{p/2}\|_2^2\) precisely when
\[
\eta<1\quad\Longleftrightarrow\quad s>\frac\gamma2.
\]
The condition \(p<2s\) is a different requirement: it ensures that the low anchor exponent used in the ordinary Banach-space GN inequality is at least one.

There are two paper-fidelity corrections to the proposed formulation.

* The paper's ladder is a **window ladder** \(s<p<2s\), not an unrestricted additive step \(p\mapsto p+\gamma\) from the original seed. An additive step is justified only after the current anchor satisfies \(p>\gamma\), because \(p+\gamma<2p\) is then true.
* The critical branch of Theorem 1.2 permits \(b=0\). Therefore the paper cannot rely on the logistic damping \(-b\int u^{p+\alpha}\) to propagate finite exponents. The faithful proof drops that term, adds a linear \(+Y_p\) damping term, and obtains a linear absorbing inequality
  \[
  Y_p'+pY_p\le pD_p.
  \]
  A logistic superlinear ODE is available as an optional stronger route when \(b>0\), but it is not the theorem's general argument.

Finally, only one high **finite** exponent is needed. In one space dimension, Proposition 2.5 is fed by any
\[
P>\max\{1,\gamma\}.
\]
There is no need to prove a Moser \(p\to\infty\) endpoint, no need for \(\sup_p C_p^{1/p}<\infty\), and no need for a quantitative root tower.

---

# 1. Exact one-dimensional anchored Gagliardo–Nirenberg step

Fix an exponent \(s>\gamma/2\) for which
\[
\sup_{0<t<T}\int_0^1u(t,x)^s\,dx\le M_s,
\]
and fix a target exponent
\[
s<p<2s.
\]
Set
\[
f=u^{p/2},\qquad
R=\frac{2(p+\gamma)}p,\qquad
Q=\frac{2s}{p}.
\]
Then
\[
\int_0^1u^{p+\gamma}=\|f\|_{L^R}^R,
\qquad
\|f\|_{L^Q}^Q=\int_0^1u^s.
\]
Because \(s<p<2s\),
\[
1<Q<2<R.
\]
The restriction \(p<2s\) is exactly what gives \(Q>1\), so that the standard one-dimensional GN theorem can be used with an honest \(L^Q\) norm.

The one-dimensional GN inequality is
\[
\|f\|_{L^R}
\le C_{GN}\|f_x\|_{L^2}^{a}\|f\|_{L^Q}^{1-a}
   +C_{GN}\|f\|_{L^Q},
\tag{GN}
\]
where \(a\) is determined by
\[
\frac1R=-\frac a2+\frac{1-a}{Q}.
\]
Substituting \(R=2(p+\gamma)/p\) and \(Q=2s/p\) gives the exact exponent
\[
\boxed{
 a=\frac{p(p+\gamma-s)}{(p+\gamma)(p+s)}.
}
\]
Since \(p>s\) and \(\gamma>0\), one has \(0<a<1\).

Raise (GN) to the power \(R\). Writing
\[
G_p:=\|f_x\|_2^2=\int_0^1\left|\partial_xu^{p/2}\right|^2,
\qquad
M:=\max\{1,M_s\},
\]
one obtains, after the elementary two-term power estimate,
\[
\int_0^1u^{p+\gamma}
\le C_{p,s,\gamma}\,
     G_p^{\eta}M^{\kappa}
   +C_{p,s,\gamma}M^{\nu},
\tag{1.1}
\]
with the exact exponents
\[
\boxed{
\eta=\frac{aR}{2}=\frac{p+\gamma-s}{p+s},
}
\]
\[
\boxed{
\kappa=\frac{(1-a)R}{Q}=\frac{2p+\gamma}{p+s},
\qquad
\nu=\frac RQ=\frac{p+\gamma}{s}.
}
\]

The crucial absorption condition is
\[
\eta<1
\iff p+\gamma-s<p+s
\iff \gamma<2s
\iff s>\frac\gamma2.
\tag{1.2}
\]
Thus the finite seed assumption is exactly the condition that makes the gradient power strictly sublinear.

Young's inequality applied to the first term in (1.1) gives, for every \(\varepsilon>0\),
\[
C_{p,s,\gamma}G_p^\eta M^\kappa
\le \varepsilon G_p
 +C'_{p,s,\gamma}\,
   \varepsilon^{-\eta/(1-\eta)}M^{\kappa/(1-\eta)}.
\]
Here
\[
\boxed{
\frac{\eta}{1-\eta}
 =\frac{p+\gamma-s}{2s-\gamma},
\qquad
\frac{\kappa}{1-\eta}
 =\frac{2p+\gamma}{2s-\gamma}.
}
\]
Since \(M\ge1\) and
\[
\frac{p+\gamma}{s}
\le \frac{2p+\gamma}{2s-\gamma},
\]
the lower-order term in (1.1) is absorbed into the same power of \(M\). Therefore the exact usable interpolation statement is
\[
\boxed{
\int_0^1u^{p+\gamma}
\le \varepsilon G_p
 +C_{\varepsilon,p,s,\gamma}
  M^{\frac{2p+\gamma}{2s-\gamma}},
}
\tag{1.3}
\]
where one may take
\[
C_{\varepsilon,p,s,\gamma}
\le C'_{p,s,\gamma}
 \left(1+
 \varepsilon^{-\frac{p+\gamma-s}{2s-\gamma}}
 \right).
\]

## Why no assumption \(\gamma<2\) is needed

If one insists on using the mass bound, i.e. the fixed anchor \(s=1\), then (1.2) becomes \(\gamma<2\). That is the source of the misleading restriction.

The finite-seed argument does not use \(s=1\). It uses the already-proved \(L^{p_0}\) bound with
\[
p_0>\gamma/2.
\]
Every later anchor is larger than \(p_0\), so the same absorption condition remains true. Hence the finite-\(p\) iteration works for arbitrary \(\gamma>0\).

The constants may deteriorate as the target exponent grows. That is harmless because only finitely many steps are taken for a prescribed finite \(P\).

---

# 2. The paper-faithful energy inequality and first crossing

Let
\[
Y_p(t):=\int_0^1u(t,x)^p\,dx,
\qquad
Z_p(t):=\int_0^1u(t,x)^{p+\gamma}\,dx.
\]
Testing the parabolic equation with \(u^{p-1}\), using Neumann boundary conditions, gives
\[
\frac1pY_p'
 +\frac{4(p-1)}{p^2}G_p
 =\text{chemotaxis}
 +aY_p-b\int_0^1u^{p+\alpha}.
\]
By the given signal-weighted estimate, choose the Young parameter so that half of the diffusion remains. In the notation of the paper this yields
\[
\frac1pY_p'
 +A_pG_p
\le C_pZ_p+aY_p-b\int_0^1u^{p+\alpha},
\tag{2.1}
\]
where one may take
\[
A_p=\frac{2(p-1)}{p^2}>0
\]
and \(C_p\ge0\) is the chemotaxis constant at exponent \(p\).

For the theorem's full parameter range, discard the logistic term. Add \(Y_p\) to both sides and use, on the unit interval,
\[
u^p\le1+u^{p+\gamma}.
\]
Then
\[
\boxed{
\frac1pY_p'+A_pG_p+Y_p
\le K_pZ_p+L_p,
}
\tag{2.2}
\]
with the explicit choices
\[
\boxed{
K_p=C_p+a+1,
\qquad
L_p=a+1.
}
\]
If the chemotaxis estimate was written with coefficient \((p-1)C_{1/2,p}\), then correspondingly
\[
K_p=(p-1)C_{1/2,p}+a+1.
\]
This is the \(N=1\), \(\rho=\gamma\) instance of the energy hypothesis used in Lemma 2.6.

Now suppose \(Y_s(t)\le M_s\) for the anchor \(s\), and let \(s<p<2s\). Apply (1.3) with
\[
\varepsilon_p=\frac{A_p}{2K_p}
\]
when \(K_p>0\). If \(K_p=0\), no interpolation is needed. For \(K_p>0\),
\[
K_pZ_p\le\frac{A_p}{2}G_p+D_{p,s},
\]
where
\[
\boxed{
D_{p,s}
:=K_pC_{\varepsilon_p,p,s,\gamma}
   \bigl(\max\{1,M_s\}\bigr)^{\frac{2p+\gamma}{2s-\gamma}}
   +L_p.
}
\tag{2.3}
\]
Substitution into (2.2) gives
\[
\boxed{
\frac1pY_p'+\frac{A_p}{2}G_p+Y_p\le D_{p,s}.
}
\tag{2.4}
\]
Dropping the nonnegative gradient term,
\[
Y_p'+pY_p\le pD_{p,s}.
\tag{2.5}
\]
Thus
\[
Y_p(t)
\le e^{-pt}Y_p(0)+D_{p,s}(1-e^{-pt})
\le \max\{Y_p(0),D_{p,s}\}.
\tag{2.6}
\]
For continuous initial data on \([0,1]\), \(Y_p(0)<\infty\). In the current Lean architecture this is exactly why `IntegratedMoserFirstCrossingRegularity` contains an `initialPowerBound` field at every exponent.

## Integrated first-crossing form

The proof can avoid solving the ODE explicitly. Integrating (2.5) on \([t_1,t_2]\) gives
\[
Y_p(t_2)-Y_p(t_1)
 +p\int_{t_1}^{t_2}Y_p(s)\,ds
\le pD_{p,s}(t_2-t_1).
\tag{2.7}
\]
Let
\[
R_{p,s}:=\max\{Y_p(0),D_{p,s}\}.
\]
If continuity allowed a first crossing above \(R_{p,s}\), let \(t_*\) be the last time before the excursion at which \(Y_p=R_{p,s}\). On the subsequent interval, \(Y_p\ge R_{p,s}\ge D_{p,s}\). Then (2.7) implies
\[
Y_p(t)-R_{p,s}
\le p\int_{t_*}^{t}(D_{p,s}-Y_p(\tau))\,d\tau\le0,
\]
contradicting the excursion. Therefore
\[
\sup_{0<t<T}Y_p(t)\le R_{p,s}.
\]
This is the corrected first-crossing conclusion.

## The literal first step

Take
\[
p_1=\frac32p_0.
\]
Then
\[
Q=\frac{2p_0}{p_1}=\frac43>1,
\]
and
\[
\eta_1
=\frac{p_1+\gamma-p_0}{p_1+p_0}
=\frac{p_0+2\gamma}{5p_0}<1
\]
exactly because \(p_0>\gamma/2\).

The Young estimate becomes
\[
Z_{p_1}
\le \varepsilon G_{p_1}
 +C_{\varepsilon,p_0,\gamma}
   \bigl(\max\{1,M_{p_0}\}\bigr)^{
     \frac{3p_0+\gamma}{2p_0-\gamma}}.
\]
Consequently
\[
\boxed{
\sup_{0<t<T}\int_0^1u^{p_1}
\le
\max\left\{
  \int_0^1u_0^{p_1},
  D_{p_1,p_0}
\right\}.
}
\tag{2.8}
\]
This is the genuine first crossing from the finite seed.

---

# 3. Optional logistic ODE when \(b>0\)

If \(b>0\), one may retain the logistic term in (2.1). After the GN absorption,
\[
Y_p'
\le apY_p-bp\int_0^1u^{p+\alpha}+pC_{p,s}.
\]
Because the interval has measure one,
\[
\int_0^1u^{p+\alpha}\ge Y_p^{1+\alpha/p}.
\]
Hence
\[
Y_p'\le apY_p-bpY_p^{1+\alpha/p}+pC_{p,s}.
\tag{3.1}
\]
This contains an additive constant. On the high region \(Y_p\ge1\), it implies
\[
Y_p'\le A_{p,s}Y_p-B_pY_p^{1+\alpha/p},
\]
with
\[
\boxed{
A_{p,s}=p(a+C_{p,s}),
\qquad
B_p=bp.
}
\]
Thus a first-crossing barrier is
\[
R^{\rm log}_{p,s}
=\max\left\{
 1,\,Y_p(0),\,
 \left(\frac{A_{p,s}}{B_p}\right)^{p/\alpha}
\right\}.
\]
At a crossing above this value the right side is nonpositive, so \(Y_p\) cannot increase through the barrier.

This explains the requested ODE form, but it is an optional strengthening. It cannot be the main Paper 2 Theorem 1.2 argument, because that theorem includes \(b=0\). The linear damping route (2.2)–(2.7) is the paper-faithful one.

---

# 4. Finite ladder and termination at any prescribed \(P\)

Define the paper's convenient anchor sequence
\[
s_k=\left(\frac32\right)^kp_0.
\]
The first-crossing window theorem says:

> If \(L^{s_k}\) is uniformly bounded, then every exponent
> \[
> s_k<p<2s_k
> \]
> is uniformly bounded.

In particular, \(s_{k+1}=\tfrac32s_k\) lies in that interval, so the induction continues.

More strongly, after stage \(k\), all exponents below \(2s_k\) and above \(1\) are controlled: exponents above the current anchor are obtained by the window step, and lower exponents follow by downward \(L^q\)-to-\(L^p\) monotonicity on the unit-measure interval.

Given any finite \(P>1\), choose \(k\) so that
\[
P<2\left(\frac32\right)^kp_0.
\tag{4.1}
\]
Such a finite \(k\) exists because \((3/2)^k\to\infty\). Then either

* \(P\le s_k\), in which case the \(L^{s_k}\) bound implies the \(L^P\) bound; or
* \(s_k<P<2s_k\), in which case one final window step gives the \(L^P\) bound.

Therefore
\[
\boxed{
\forall P>1,\qquad
\sup_{0<t<T}\int_0^1u(t,x)^P\,dx<\infty.
}
\tag{4.2}
\]
For Theorem 1.2 one need not retain the universal quantifier. Choose one concrete finite exponent
\[
P>\max\{1,\gamma\}.
\]
Then (4.2) gives `LpPowerBoundedBefore` at that \(P\), and Proposition 2.5 supplies the \(L^\infty\) bound.

## Why this is strictly easier than Moser-to-\(L^\infty\)

For a prescribed finite \(P\):

* only finitely many GN applications are made;
* every constant may depend on \(P\), on the number of steps, and on all preceding bounds;
* no uniform estimate of \(C_p^{1/p}\) is needed;
* no infinite product of iteration constants is needed;
* no `MoserQuantitativeEndpoint`, root tower, or \(p\to\infty\) limiting argument is needed.

This is exactly the right cut for the critical branch: finite \(P\) first, Proposition 2.5 second.

---

# 5. Important correction to the current additive Lean predicate

The current repository definition in

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

is

```lean
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u
```

As stated from the original seed, this is stronger than the paper's GN step. To obtain \(L^{p+\rho}\) from an \(L^p\) anchor by testing the energy at exponent \(p+\rho\), the target must satisfy
\[
p+\rho<2p,
\]
i.e.
\[
p>\rho.
\]
But the seed assumption only gives \(p_0>\rho/2\), and allows \(p_0\le\rho\).

The paper-faithful analytic predicate should therefore be the window form:

```lean
def IntegratedMoserFirstCrossingWindowStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ s, p0 ≤ s →
    LpPowerBoundedBefore D s T u →
      ∀ p, s < p → p < 2 * s →
        LpPowerBoundedBefore D p T u
```

There are two migration options.

### Preferred: use the paper's geometric window ladder

Build all finite exponents directly from `IntegratedMoserFirstCrossingWindowStep` and \(s_{k+1}=3s_k/2\).

### Minimal migration preserving the additive downstream chain

First choose
\[
p_{\rm start}\in(\max\{p_0,\rho\},2p_0).
\]
This interval is nonempty because \(p_0>\rho/2\). The window step gives an \(L^{p_{\rm start}}\) bound. Since \(p_{\rm start}>\rho\), every later additive jump satisfies
\[
p+\rho<2p.
\]
Thus the existing additive predicate can validly be instantiated with base exponent \(p_{\rm start}\), rather than with the original \(p_0\).

---

# 6. Lean-4-formalizable dependency plan

Below is a dependency-ordered six-lemma plan. The statements deliberately separate scalar exponent algebra, the concrete interval GN theorem, the first-crossing scalar closure, and the finite ladder.

## Lemma 1 — exact exponent algebra

```lean
theorem oneDim_anchoredMoser_exponents
    {s p rho : ℝ}
    (hrho : 0 < rho)
    (hs_rho : rho / 2 < s)
    (hsp : s < p)
    (hp2s : p < 2 * s) :
    let Q := 2 * s / p
    let R := 2 * (p + rho) / p
    let a := p * (p + rho - s) / ((p + rho) * (p + s))
    let eta := (p + rho - s) / (p + s)
    1 < Q ∧ Q < 2 ∧ 2 < R ∧
      0 < a ∧ a < 1 ∧
      eta = a * R / 2 ∧ eta < 1 ∧
      1 - eta = (2 * s - rho) / (p + s)
```

This is elementary ordered-field algebra and should be discharged by `field_simp`, `positivity`, and `nlinarith` after proving all denominators positive.

## Lemma 2 — anchored interval GN/Young estimate

```lean
theorem interval_higherPower_le_eps_gradient_of_Ls_bound
    {u : intervalDomain.Point → ℝ}
    {s p rho M eps : ℝ}
    (hrho : 0 < rho)
    (hs_rho : rho / 2 < s)
    (hsp : s < p)
    (hp2s : p < 2 * s)
    (hM : 1 ≤ M)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hLs : intervalDomain.integral (fun x => u x ^ s) ≤ M)
    (hregular : /* chain rule + H¹ data for u^(p/2) */)
    (heps : 0 < eps) :
    intervalDomain.integral (fun x => u x ^ (p + rho)) ≤
      eps * intervalDomain.integral (fun x =>
        intervalDomain.gradNorm (fun y => u y ^ (p / 2)) x ^ 2) +
      C p s rho eps * M ^ ((2 * p + rho) / (2 * s - rho))
```

**Hardest lemma.** This is the analytic crux. It needs the concrete one-dimensional GN inequality with low exponent \(Q=2s/p\), the real-power chain rule for \(u^{p/2}\), interval integrability, and the exact Young-exponent bookkeeping. The repository's old arbitrary-power interpolation is correctly marked false for constants; this anchored version is the satisfiable replacement because its constant depends on the known \(L^s\) bound.

## Lemma 3 — scalar integrated first crossing

```lean
theorem bounded_of_integrated_linear_damping
    {Y : ℝ → ℝ} {T p D Y0 : ℝ}
    (hp : 0 < p)
    (hD : 0 ≤ D)
    (hcont : ContinuousOn Y (Set.Icc 0 T))
    (hY0 : Y 0 ≤ Y0)
    (hwindow :
      ∀ t1 ∈ Set.Icc 0 T, ∀ t2 ∈ Set.Icc t1 T,
        Y t2 - Y t1 + p * ∫ t in t1..t2, Y t
          ≤ p * D * (t2 - t1)) :
    ∀ t ∈ Set.Icc 0 T, Y t ≤ max Y0 D
```

This is the reusable first-crossing theorem. It can be proved by the repository's existing last-exit/threshold machinery or by an integrating-factor Grönwall lemma.

## Lemma 4 — one paper window step

```lean
theorem integratedMoser_windowStep_of_energy_and_anchoredGN
    {u : ℝ → intervalDomain.Point → ℝ}
    {T rho p0 s p : ℝ}
    (hrho : 0 < rho)
    (hp0 : max 1 (rho / 2) < p0)
    (hp0s : p0 ≤ s)
    (hsp : s < p)
    (hp2s : p < 2 * s)
    (hseed_s : LpPowerBoundedBefore intervalDomain s T u)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hGN : /* Lemma 2 for every positive-time slice */) :
    LpPowerBoundedBefore intervalDomain p T u
```

Internally:

1. extract a uniform anchor constant \(M_s\);
2. use Lemma 2 at each time;
3. choose \(\varepsilon=A_p/(2K_p)\);
4. integrate the energy inequality on closed windows;
5. invoke Lemma 3.

## Lemma 5 — geometric finite ladder

```lean
theorem all_finite_Lp_of_windowStep_and_seed
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hrho : 0 < rho)
    (hp0 : max 1 (rho / 2) < p0)
    (hseed : LpPowerBoundedBefore D p0 T u)
    (hwindow : IntegratedMoserFirstCrossingWindowStep D u T rho p0)
    (hmono :
      ∀ {p q}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u →
        LpPowerBoundedBefore D p T u) :
    ∀ P, 1 < P → LpPowerBoundedBefore D P T u
```

Use \(s_k=(3/2)^kp_0\), induction, and an Archimedean lemma producing \(k\) with \(P<2s_k\).

## Lemma 6 — critical-branch high finite exponent

```lean
theorem criticalBranch_has_Prop25_exponent
    {u : ℝ → intervalDomain.Point → ℝ}
    {T gamma p0 : ℝ}
    (hfinite : ∀ P, 1 < P →
      LpPowerBoundedBefore intervalDomain P T u) :
    ∃ P, max 1 gamma < P ∧
      LpPowerBoundedBefore intervalDomain P T u := by
  refine ⟨max 1 gamma + 1, ?_, ?_⟩
  · linarith
  · exact hfinite _ (by linarith [le_max_left (1 : ℝ) gamma])
```

This is the terminal handoff to Proposition 2.5. It intentionally stops at one finite \(P\).

---

# Bottom line

The corrected critical-branch chain is

```text
χ₀ < chiBeta
  → finite seed p₀ with p₀ > max{1, γ/2}
  → anchored GN window step: L^s → L^p for s < p < 2s
  → geometric finite ladder sₖ = (3/2)^k p₀
  → one finite P > max{1, γ}
  → Proposition 2.5
  → L∞ boundedness.
```

The load-bearing exponent is
\[
\eta=\frac{p+\gamma-s}{p+s}<1
\iff s>\frac\gamma2.
\]
There is no \(\gamma<2\) restriction once the low anchor is the finite seed rather than the mass. The finite ladder is strictly easier than a Moser \(p\to\infty\) endpoint, and the existing additive Lean predicate should either be replaced by the paper-faithful window predicate or started only after a first window crossing to an anchor larger than \(\gamma\).
