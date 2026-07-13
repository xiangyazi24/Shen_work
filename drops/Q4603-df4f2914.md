ANSWER Q4603 df4f2914

# Verdict

Yes: the restarted mild route gives the desired uniform \(L^\infty\) bound from one uniform finite \(L^P\) bound, with the sharp combined threshold

\[
P>\max\{1,\gamma\}.
\]

For the current \(m=1\) interval equation, the endpoint estimate needs **no** pointwise-in-time Moser-gradient bound and **no** condition \(2\gamma<\alpha\). The latter condition appears only in the currently committed Agmon endpoint in `PDE/IntervalDomain1DLinfRoute.lean`; it is not intrinsic to the restarted semigroup endpoint.

There are two important implementation corrections.

1. The chemotaxis term must be handled by the B-form operator
   
   \[
   B_N(\tau)Q(x):=-\int_0^1 \partial_yK_N(\tau,x,y)Q(y)\,dy,
   \]
   
   not by differentiating a merely \(L^P\) flux. If \(Q(0)=Q(1)=0\), then \(B_N(\tau)Q=S_N(\tau)\partial_xQ\).
2. One must **not** try to bound
   
   \[
   \|u(a-bu^\alpha)\|_{L^P}
   \]
   
   from \(\|u\|_{L^P}\): the sink part would require \(L^{P(1+\alpha)}\). Instead split the mild reaction leg and use positivity preservation:
   
   \[
   aS_N(\tau)u-bS_N(\tau)u^{1+\alpha}
   \le aS_N(\tau)u.
   \]

This is the clean endpoint mechanism.

Repository audit, `chatgpt-scratch`:

- `IntervalConjugateDuhamelMap.lean` already has the correct full-kernel B-operator and sign:
  ```lean
  def intervalConjugateKernelOperator (t : ℝ) (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
    -∫ y, deriv (fun y' => intervalNeumannFullKernel t x y') y * Q y
      ∂ intervalMeasure 1

  def intervalConjugateDuhamelMap ... :=
    intervalFullSemigroupOperator t ...
      + (-p.χ₀) * ∫ s in 0..t,
          intervalConjugateKernelOperator (t-s) (chemFluxLifted p (u s)) ...
      + ∫ s in 0..t, intervalFullSemigroupOperator (t-s) (logisticLifted p (u s)) ...
  ```
- `IntervalFullKernelSupBound.lean` proves the genuine full-Neumann \(L^\infty\to L^\infty\) contraction.
- `IntervalHeatGradient.lean` and `IntervalConjugateDuhamelMap.lean` prove the full-kernel \(L^\infty\to L^\infty\), \(	au^{-1/2}\) gradient/B bounds.
- `HeatKernelLpEstimates.lean` has finite-\(L^P\) estimates for the **zeroth-reflection helper** `intervalSemigroupOperator`; those are useful templates but are not yet the genuine full Neumann propagator needed here.
- `IntervalDomain1DLinfRoute.lean` currently reaches `Proposition_2_5` only through the stronger `IntervalDomainPointwiseMoserGradientBoundBefore` frontier and assumes \(2\gamma<\alpha\). The route below replaces that endpoint.

# 1. Full Neumann \(L^P\to L^\infty\) estimates

Let \(K_N(\tau,x,y)\) be the full periodized Neumann kernel on \([0,1]\), and put

\[
r=P'=\frac{P}{P-1},\qquad
\zeta_P=\frac1{2P},\qquad
\eta_P=\frac12+\frac1{2P}=\frac{P+1}{2P}.
\]

For every \(P>1\), there are constants \(C_{S,P},C_{B,P}>0\), depending only on \(P\) and the interval, such that for every \(\tau>0\),

\[
\boxed{
\|S_N(\tau)f\|_\infty
\le C_{S,P}\bigl(1+\tau^{-\zeta_P}\bigr)\|f\|_{L^P}.}
\tag{H}
\]

and

\[
\boxed{
\|B_N(\tau)g\|_\infty
\le C_{B,P}\bigl(1+\tau^{-\eta_P}\bigr)\|g\|_{L^P}.}
\tag{B}
\]

On \(0<\tau\le1\), absorb the `1` into the singular term:

\[
\|S_N(\tau)f\|_\infty
\le A_P\tau^{-1/(2P)}\|f\|_P,
\qquad
\|B_N(\tau)g\|_\infty
\le D_P\tau^{-1/2-1/(2P)}\|g\|_P.
\tag{1.1}
\]

## 1.1 Kernel proof of (H)

Use

\[
K_N\ge0,\qquad \int_0^1K_N(\tau,x,y)\,dy=1,
\]

and the standard short-time pointwise bound

\[
\sup_{x,y}K_N(\tau,x,y)\le C_K\tau^{-1/2}
\qquad(0<\tau\le1).
\]

Then

\[
\begin{aligned}
\|K_N(\tau,x,\cdot)\|_{L^r}^r
&\le \|K_N(\tau,x,\cdot)\|_\infty^{r-1}
     \|K_N(\tau,x,\cdot)\|_1,\\
\|K_N(\tau,x,\cdot)\|_{L^r}
&\le C_K^{1/P}\tau^{-1/(2P)}.
\end{aligned}
\]

Hölder in \(y\) gives (H).

## 1.2 Kernel proof of (B)

The repository already has the load-bearing \(L^1\) derivative-kernel estimate, in second-variable form,

\[
\sup_x\int_0^1|\partial_yK_N(\tau,x,y)|\,dy
\le C_1\tau^{-1/2}.
\tag{1.2}
\]

Add the short-time pointwise derivative estimate

\[
\sup_{x,y}|\partial_yK_N(\tau,x,y)|\le C_\infty\tau^{-1},
\qquad 0<\tau\le1.
\tag{1.3}
\]

For \(h(y)=\partial_yK_N(\tau,x,y)\), elementary \(L^1\)-\(L^\infty\) interpolation gives

\[
\|h\|_{L^r}
\le \|h\|_1^{1/r}\|h\|_\infty^{1-1/r}.
\]

Since \(1/r=1-1/P\), the time power is

\[
\frac12\left(1-\frac1P\right)+\frac1P
=\frac12+\frac1{2P}.
\]

Thus

\[
\sup_x\|\partial_yK_N(\tau,x,\cdot)\|_{L^r}
\le D_P\tau^{-1/2-1/(2P)},
\]

and Hölder gives (B).

The singularity is time-integrable precisely when

\[
\eta_P<1
\iff \frac12+\frac1{2P}<1
\iff P>1.
\tag{1.4}
\]

This is the exact semigroup threshold.

# 2. Uniform \(L^P\) bound for the chemotaxis flux

Set

\[
Q(t,x)=u(t,x)(1+v(t,x))^{-\beta}v_x(t,x).
\]

Let

\[
q=\frac P\gamma.
\]

The condition \(P>\gamma\) gives \(q>1\). For each time slice, the Neumann elliptic equation is

\[
-v_{xx}+\mu v=\nu u^\gamma.
\]

The one-dimensional Neumann resolvent satisfies

\[
\|v\|_{W^{2,q}(0,1)}
\le C_E(\mu,q)\nu\|u^\gamma\|_{L^q}.
\]

Since \(q>1\), \(W^{2,q}(0,1)\hookrightarrow W^{1,\infty}(0,1)\), hence

\[
\|v_x\|_\infty
\le C_E(\mu,q)\nu\|u^\gamma\|_q.
\tag{2.1}
\]

For \(u\ge0\),

\[
\|u^\gamma\|_q=\|u\|_P^\gamma.
\]

If

\[
\sup_{t>0}\|u(t)\|_P\le K_P,
\]

then

\[
\sup_{t>0}\|v_x(t)\|_\infty
\le C_E(\mu,P/\gamma)\nu K_P^\gamma.
\tag{2.2}
\]

Because \(v\ge0\) and \(\beta\ge0\),

\[
0<(1+v)^{-\beta}\le1.
\]

Therefore

\[
\boxed{
\|Q(t)\|_P
\le C_E(\mu,P/\gamma)\nu K_P^{\gamma+1}
=:K_Q.}
\tag{2.3}
\]

This endpoint leg does **not** require the signal-weighted estimate from Q4589. That weighted estimate is indispensable upstream for constructing the critical finite-\(L^{p_0}\) seed and the all-\(p\) cross-diffusion bootstrap. Once a sufficiently high \(L^P\) bound is already available, the ordinary resolver gain \(L^{P/\gamma}\to W^{1,\infty}\) is the shorter endpoint route.

A Lean-friendly alternative to abstract elliptic regularity is the Green-kernel estimate

\[
|v_x(x)|
\le \nu\|\partial_xG_\mu(x,\cdot)\|_{L^{q'}}\|u^\gamma\|_q,
\]

with

\[
C_E(\mu,q)=\sup_{x\in[0,1]}
\|\partial_xG_\mu(x,\cdot)\|_{L^{q'}}<\infty.
\]

That formulation aligns directly with the repository's spectral/Green resolver machinery.

# 3. Exact restarted mild formula

For \(0<t_0<t<T\), the classical solution should satisfy

\[
\begin{aligned}
u(t)
={}&S_N(t-t_0)u(t_0)
-\chi_0\int_{t_0}^t B_N(t-s)Q(s)\,ds\\
&+a\int_{t_0}^t S_N(t-s)u(s)\,ds
-b\int_{t_0}^t S_N(t-s)u(s)^{1+\alpha}\,ds.
\end{aligned}
\tag{3.1}
\]

The B-form is legitimate because \(v_x=0\) at \(0,1\), hence \(Q(s,0)=Q(s,1)=0\), and

\[
S_N(\tau)\partial_xQ=B_N(\tau)Q.
\]

The current repository has the time-zero fixed-point predicate `IntervalConjugateMildSolution`, but the endpoint needs the generic theorem that **every** interval classical solution satisfies (3.1) after an arbitrary positive restart. This is a separate shared infrastructure lemma, obtained either by:

- variation of constants for the classical PDE; or
- the time-zero mild identity plus semigroup composition and splitting the Duhamel integral at \(t_0\).

Since \(S_N\) is positivity preserving, \(b\ge0\), and \(u\ge0\),

\[
-bS_N(t-s)u(s)^{1+\alpha}\le0.
\]

Taking a pointwise upper bound in (3.1) yields

\[
\begin{aligned}
0\le u(t,x)
\le{}& |S_N(t-t_0)u(t_0)(x)|\\
&+|\chi_0|\int_{t_0}^t
 |B_N(t-s)Q(s)(x)|\,ds\\
&+a\int_{t_0}^t
 |S_N(t-s)u(s)(x)|\,ds.
\end{aligned}
\tag{3.2}
\]

This is why no \(L^{P(1+\alpha)}\) input is needed.

# 4. One-unit restart and the uniform bound

For \(t\ge1\), choose \(t_0=t-1\). Apply (1.1), (2.3), and set \(\theta=t-s\). The homogeneous term has a full unit of smoothing:

\[
\|S_N(1)u(t-1)\|_\infty\le A_PK_P.
\]

The chemotaxis leg is bounded by

\[
|\chi_0|D_PK_Q
\int_0^1\theta^{-\eta_P}\,d\theta.
\]

Because \(P>1\),

\[
\int_0^1\theta^{-\eta_P}\,d\theta
=\frac1{1-\eta_P}
=\frac{2P}{P-1}.
\tag{4.1}
\]

The positive growth leg is bounded by

\[
aA_PK_P\int_0^1\theta^{-\zeta_P}\,d\theta,
\]

and

\[
\int_0^1\theta^{-\zeta_P}\,d\theta
=\frac1{1-\zeta_P}
=\frac{2P}{2P-1}.
\tag{4.2}
\]

Consequently, for every \(t\ge1\),

\[
\boxed{
\begin{aligned}
\|u(t)\|_\infty\le M_\infty:={}&A_PK_P\\
&+|\chi_0|D_PC_E(\mu,P/\gamma)\nu
 K_P^{\gamma+1}\frac{2P}{P-1}\\
&+aA_PK_P\frac{2P}{2P-1}.
\end{aligned}}
\tag{4.3}
\]

Thus the exact combined threshold is

\[
\boxed{P>1\quad\text{and}\quad P>\gamma,
\quad\text{i.e.}\quad P>\max\{1,\gamma\}.}
\]

No \(\alpha\)-condition enters (4.3).

## 4.1 Patching the initial interval for `IsPaper2BoundedBefore`

For the eventual `IsPaper2Bounded` conclusion, (4.3) is already enough. `Proposition_2_5`, however, returns `IsPaper2BoundedBefore`, which quantifies over every \(0<t<T\).

Use `InitialTrace` with, say, \(\varepsilon=1\), plus bounded admissible initial data, to choose \(t_* >0\) and \(M_*>0\) such that

\[
\|u(t)\|_\infty\le M_*
\qquad(0<t\le t_*).
\]

Then:

- for \(t_*<t\le t_*+1\), restart at \(t_*\); use the \(L^\infty\) contraction for the homogeneous term and the same two integrable Duhamel kernels;
- for \(t>t_*+1\), restart at \(t-1\) and use (4.3).

One bound valid on the whole positive horizon is

\[
M=\max\left\{
M_*+|\chi_0|D_PK_Q\frac{2P}{P-1}
+aA_PK_P\frac{2P}{2P-1},
\ M_\infty
\right\}.
\tag{4.4}
\]

In the repository, `LpPowerBoundedBefore` stores a bound on the \(P\)-th power integral, not directly the norm. If

\[
\int_0^1u(t)^P\le C_P,
\]

set

\[
K_P=(\max\{0,C_P\})^{1/P}.
\]

Positivity of \(u\) then gives the required uniform \(L^P\)-norm bound.

# 5. Lean targets, dependency order

A clean file is

```lean
ShenWork/Paper2/IntervalDomainRestartedLpLinf.lean
```

with the following seven targets.

## L1. Genuine full-kernel heat \(L^P\to L^\infty\)

```lean
def IntervalFullHeatLpLinfEstimate (P : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧
    ∀ ⦃τ : ℝ⦄, 0 < τ → τ ≤ 1 →
    ∀ ⦃f : ℝ → ℝ⦄,
      MeasureTheory.MemLp f (ENNReal.ofReal P)
        (ShenWork.IntervalDomain.intervalMeasure 1) →
      ∀ x : ℝ,
        |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            τ f x| ≤
          A * τ ^ (-(1 / (2 * P)) : ℝ) *
            MeasureTheory.lpNorm f (ENNReal.ofReal P)
              (ShenWork.IntervalDomain.intervalMeasure 1)
```

```lean
theorem intervalFullHeat_Lp_Linfty
    {P : ℝ} (hP : 1 < P) :
    IntervalFullHeatLpLinfEstimate P
```

Internally prove the full-kernel \(L^{P'}\) norm bound from nonnegativity, mass \(1\), and the pointwise Gaussian bound. Do not substitute the zeroth-reflection helper theorem.

## L2. Genuine B-kernel \(L^P\to L^\infty\)

```lean
def IntervalConjugateLpLinfEstimate (P : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧
    ∀ ⦃τ : ℝ⦄, 0 < τ → τ ≤ 1 →
    ∀ ⦃Q : ℝ → ℝ⦄,
      MeasureTheory.MemLp Q (ENNReal.ofReal P)
        (ShenWork.IntervalDomain.intervalMeasure 1) →
      ∀ x : ℝ,
        |ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
            τ Q x| ≤
          D * τ ^ (-(1 / 2 + 1 / (2 * P)) : ℝ) *
            MeasureTheory.lpNorm Q (ENNReal.ofReal P)
              (ShenWork.IntervalDomain.intervalMeasure 1)
```

```lean
theorem intervalConjugateKernel_Lp_Linfty
    {P : ℝ} (hP : 1 < P) :
    IntervalConjugateLpLinfEstimate P
```

The new analytic core is the \(L^{P'}\) estimate for `deriv ... intervalNeumannFullKernel ...` obtained by interpolating:

```lean
-- already present, second-variable L¹ tiling bound
∫ y in 0..1, |∂ᵧ K_N τ x y| ≤ C₁ * τ^(-1/2)

-- new short-time pointwise bound
|∂ᵧ K_N τ x y| ≤ C∞ * τ^(-1)
```

## L3. Resolver \(L^{P/\gamma}\to W^{1,\infty}\)

```lean
theorem intervalNeumannResolver_grad_Linfty_of_Lp
    {p : CM2Params} {P K : ℝ}
    (hγP : p.γ < P) (hK : 0 ≤ K) :
    ∃ C_E : ℝ, 0 ≤ C_E ∧
      ∀ {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        0 < t → t < T →
        MeasureTheory.lpNorm (intervalDomainLift (u t))
            (ENNReal.ofReal P) (intervalMeasure 1) ≤ K →
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |deriv (intervalDomainLift (v t)) x| ≤
            C_E * p.ν * K ^ p.γ
```

The constant is uniform in \(u,v,t,T\) and depends only on \(p.\mu\) and \(P/p.\gamma\).

## L4. Flux \(L^P\) bound

Use the existing interval flux from the classical-solution energy files.

```lean
theorem intervalFlux_lpNorm_le_of_solution_Lp
    {p : CM2Params} {P K : ℝ}
    (hP : max 1 p.γ < P) (hK : 0 ≤ K) :
    ∃ C_Q : ℝ, 0 ≤ C_Q ∧
      ∀ {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        0 < t → t < T →
        MeasureTheory.lpNorm (intervalDomainLift (u t))
            (ENNReal.ofReal P) (intervalMeasure 1) ≤ K →
        MeasureTheory.lpNorm
            (ShenWork.Paper2.intervalFlux p (u t) (v t))
            (ENNReal.ofReal P) (intervalMeasure 1) ≤
          C_Q * K ^ (p.γ + 1)
```

The proof is exactly

```text
(1+v)^(-β) ≤ 1
+ resolver gradient L∞ bound
+ ‖u vₓ‖P ≤ ‖u‖P ‖vₓ‖∞.
```

## L5. Generic classical restarted B-form mild identity

```lean
def IntervalClassicalRestartedBFormMild (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    ∀ {t₀ t : ℝ}, 0 < t₀ → t₀ < t → t < T →
    ∀ x : intervalDomain.Point,
      u t x =
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          (t - t₀) (intervalDomainLift (u t₀)) x.1
        + (-p.χ₀) *
            (∫ s in t₀..t,
              ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
                (t - s)
                (ShenWork.Paper2.intervalFlux p (u s) (v s)) x.1)
        + ∫ s in t₀..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (t - s)
              (intervalDomainLift
                (fun y => u s y * (p.a - p.b * (u s y) ^ p.α))) x.1
```

```lean
theorem intervalClassicalSolution_restarted_bform_mild
    (p : CM2Params) :
    IntervalClassicalRestartedBFormMild p
```

This is the main shared restart law. It should reuse full-kernel semigroup composition, the Duhamel interval split, `flux_endpoint_zero`, and the classical PDE.

## L6. Quantitative one-window smoothing

```lean
theorem interval_restarted_mild_Lp_Linfty_bound
    {p : CM2Params} {P K M₀ : ℝ}
    (hP : max 1 p.γ < P)
    (hK : 0 ≤ K) (hM₀ : 0 ≤ M₀)
    (hheat : IntervalFullHeatLpLinfEstimate P)
    (hB : IntervalConjugateLpLinfEstimate P)
    (hrestart : IntervalClassicalRestartedBFormMild p)
    {T t₀ t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht₀ : 0 < t₀) (ht : t₀ < t) (htT : t < T)
    (hwindow : t - t₀ ≤ 1)
    (huLp : ∀ s, t₀ ≤ s → s ≤ t →
      MeasureTheory.lpNorm (intervalDomainLift (u s))
        (ENNReal.ofReal P) (intervalMeasure 1) ≤ K)
    (hu₀inf : ∀ x, |u t₀ x| ≤ M₀) :
    ∃ M, 0 ≤ M ∧ ∀ x, u t x ≤ M
```

The resulting \(M\) is bounded by

\[
M_0+|\chi_0|D_PC_E\nu K^{\gamma+1}\frac{2P}{P-1}
+aA_PK\frac{2P}{2P-1}.
\]

Also provide the one-unit version in which the homogeneous term uses \(A_PK\) rather than \(M_0\).

## L7. Final `Proposition_2_5` producer

For the equation in this question, expose the \(m=1\) specialization honestly:

```lean
theorem intervalDomain_Proposition_2_5_of_restarted_mild_Lp_smoothing
    (p : CM2Params)
    (hm : p.m = 1)
    (hheat : ∀ P, 1 < P → IntervalFullHeatLpLinfEstimate P)
    (hB : ∀ P, 1 < P → IntervalConjugateLpLinfEstimate P)
    (hrestart : IntervalClassicalRestartedBFormMild p) :
    Proposition_2_5 intervalDomain p
```

Proof outline after unfolding `Proposition_2_5`:

```lean
intro u₀ hu₀ T hT u v hsol htrace P hP hLp

-- On N=1 and m=1, the Proposition_2_5 threshold gives max 1 γ < P.
have hPcrit : max 1 p.γ < P := by
  simpa [hm] using hP

-- Convert the carried power-integral bound to a uniform Lp norm K_P.
obtain ⟨C_P, hC_P⟩ := hLp
let K_P := (max 0 C_P) ^ (1 / P)

-- InitialTrace + admissible bounded datum gives a bounded positive-time seed slice.
obtain ⟨t₀, ht₀, M₀, hM₀, hsmall_time, hslice₀⟩ :=
  interval_initialTrace_short_sup_bound hu₀ htrace hT

-- [t₀,t₀+1]: restart at t₀, homogeneous L∞ contraction.
-- [t₀+1,T): restart at t-1, homogeneous Lp→L∞ smoothing.
-- Combine with hsmall_time.
refine ⟨max Msmall Mlate, ?_⟩
intro t ht0 htT
by_cases ht : t ≤ t₀
· exact ...
by_cases hunit : t ≤ t₀ + 1
· exact ...
· exact ...
```

This producer is structurally independent of `IntervalDomainPointwiseMoserGradientBoundBefore`.

# 6. Hardest leaves and Paper 3 reuse

## Hardest analytic leaf

The hardest new analytic theorem is L2: the **genuine full-kernel second-variable derivative \(L^{P'}\) bound**. The mathematics is only \(L^1\)-\(L^\infty\) interpolation, but Lean must coordinate:

- the periodized full-kernel derivative;
- `lpNorm`/`MemLp` real-exponent bookkeeping;
- the existing \(L^1\) tiling theorem;
- a uniform short-time pointwise \(O(\tau^{-1})\) derivative bound;
- Hölder for the B-operator.

Do not accidentally prove this only for `normalizedZerothReflectionKernel`.

## Hardest wiring leaf

L5 is the other keystone: a generic arbitrary-restart B-form identity for an `IsPaper2ClassicalSolution`. The local Picard fixed-point identity already has the right B-form, but `Proposition_2_5` is stated for an arbitrary classical solution supplied to it, so the restart theorem must be exported at that level.

## Shared with Paper 3

The following infrastructure is common to this endpoint and the Paper 3 full-mode orbit estimate:

1. genuine full-Neumann \(L^P\to L^\infty\) smoothing;
2. genuine B-kernel \(L^P\to L^\infty\) smoothing;
3. semigroup composition and arbitrary-time Duhamel restart;
4. fixed-window singular-convolution estimates;
5. resolver-to-flux mapping bounds;
6. the same split into homogeneous, divergence, and value-source legs.

Paper 3 adds an exponential spectral factor and a locally quadratic/Lipschitz nonlinear remainder, but its weighted orbit estimate is the same restarted Volterra calculation. Building L1, L2, and L5 once is therefore the correct cross-paper infrastructure investment.

# Bottom line

The desired theorem is mathematically clean:

\[
\sup_{t\ge1}\|u(t)\|_\infty
\le C\left(K_P+K_P^{\gamma+1}\right),
\qquad P>\max\{1,\gamma\},
\]

with the explicit bound (4.3). It bypasses the pointwise-gradient Agmon gap, bypasses the current \(2\gamma<\alpha\) restriction, and uses exactly the same full-kernel restart machinery needed later by Paper 3.