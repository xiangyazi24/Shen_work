ANSWER Q83 8c92ab40

# Executive verdict

The full nonlocal PDE is temporally linearly stable at (u,v)=(1,1) throughout the entire range claimed in Theorem 1.2. The exact Fourier dispersion relation is

```plain text
λ(k) = −α − k² + χγ k²/(1+k²).
```

The formula proposed in the question,

```plain text
−k² − χ(γ/(1+k²) − 1) − α,
```

is correct only when γ=1; in general its positive identity contribution must also carry the factor γ.

Writing s=k² and q=χγ, the exact spectral bound is

```plain text
sup_k λ(k) = −α                              if q ≤ 1,
             (sqrt(q)−1)² − α               if q > 1.
```

The first linear instability occurs at

```plain text
χ_lin = (1 + sqrt(α))² / γ,
k_c²  = sqrt(α).
```

In the critical regime α=m+γ−1 with m,γ≥1, one has α≥γ, and therefore

```plain text
χ_lin = (1+sqrt(α))²/γ > α/γ ≥ 1.
```

Since the paper’s χ*≤1, no temporal/Turing eigenvalue crosses zero anywhere in 0<χ<χ*. In particular, for the standard case m=α=γ=1,

```plain text
λ(k)=−1−k²+χ k²/(1+k²),
χ_lin=4,
```

not 1/2 and not 1.

This settles the strategic fork as follows:

- The interval χ∈[α/(2γ),χ*) is not ruled out by linear instability.

- There is no small-amplitude periodic or stationary branch bifurcating from (1,1) in that interval.

- The factor-two rectangle threshold is a limitation of the sup/inf comparison mechanism, not the true linear threshold.

- Nevertheless, linear stability alone proves only local nonlinear exponential stability. It does not prove global uniform stabilization for every bounded datum with inf u₀>0.

- I found no published counterexample for the exact whole-line model in the interval between the rectangle threshold and χ*. The mathematically honest status is therefore: the paper’s proof has a genuine gap there, but the theorem is not disproved; global stabilization in that range appears open and plausible.

# 1. Exact linearization of the nonlocal PDE

The system is

```plain text
u_t = u_xx − χ (u^m v_x)_x + u(1−u^α),
0   = v_xx − v + u^γ.
```

Set

```plain text
u = 1 + εw,
v = 1 + εz.
```

## Elliptic component

At order ε,

```plain text
z_xx − z + γw = 0,
```

so, with

```plain text
R := (1−∂xx)^−1,
```

we have

```plain text
z = γRw.
```

For a Fourier mode w=e^{ikx},

```plain text
z = γ/(1+k²) · w.
```

## Chemotaxis component

Because the equilibrium signal is constant, v_x=0 at zeroth order. Thus

```plain text
u^m v_x
 = (1+mεw+O(ε²))(εz_x+O(ε²))
 = εz_x+O(ε²).
```

Consequently,

```plain text
−χ(u^m v_x)_x = −χεz_xx + O(ε²).
```

The exponent m does not appear in the linearized flux. It enters only through nonlinear terms and, in the critical regime, through α=m+γ−1.

## Logistic component

Since

```plain text
(1+εw)^α = 1 + αεw + O(ε²),
```

we get

```plain text
u(1−u^α) = −αεw + O(ε²).
```

## Linearized operator

The perturbation equation is therefore

```plain text
w_t = w_xx − χz_xx − αw
    = w_xx − χγ ∂xx Rw − αw.
```

Using

```plain text
−∂xx R = I−R,
```

one may write

```plain text
L = ∂xx + χγ(I−R) − αI.
```

On e^{ikx} this gives

```plain text
λ(k)
 = −k² + χγ k²/(1+k²) − α
 = −α − k² + χγ(1−1/(1+k²)).
```

In a frame moving at speed c, the extra transport term contributes only ick (up to the sign convention). Hence it does not change Re λ(k).

# 2. Exact maximization and instability threshold

Put

```plain text
s = k² ≥ 0,
q = χγ.
```

Then

```plain text
λ(s) = −α − s + q s/(1+s),
λ'(s)= −1 + q/(1+s)².
```

## Case q≤1

Here λ'(s)≤0, so the maximum occurs at s=0:

```plain text
sup λ = λ(0)=−α.
```

## Case q>1

The unique interior maximizer is

```plain text
s_* = sqrt(q)−1.
```

Substitution gives

```plain text
sup λ = (sqrt(q)−1)² − α.
```

Therefore the crossing condition is

```plain text
(sqrt(χγ)−1)² = α,
```

or

```plain text
χ = χ_lin := (1+sqrt(α))²/γ.
```

At the crossing,

```plain text
k_c² = sqrt(α),
k_c  = α^(1/4).
```

The exact linear decay margin is

```plain text
δ_lin(χ) = α                                      if χγ≤1,
             α − (sqrt(χγ)−1)²                   if χγ>1,
```

and sup Re λ = −δ_lin(χ).

Under α=m+γ−1,

```plain text
α≥γ,
χ_lin=(1+sqrt(α))²/γ>1.
```

Thus every χ<χ*≤1 has a strict spectral gap.

# 3. Functional-space meaning of the spectral calculation

The cleanest exact statement is on L²(R), where L is a real self-adjoint Fourier multiplier and its spectrum is the range closure of λ(k).

The paper’s Cauchy phase space is bounded uniformly continuous functions, not raw L∞. This distinction matters:

- The heat semigroup is strongly continuous on BUC(R)=C^b_unif(R).

- It is not strongly continuous on all of raw L∞(R).

- On BUC, L is a sectorial Laplacian plus the bounded translation-invariant operator χγ(I−R)−αI.

- Standard analytic-semigroup spectral theory therefore turns the negative spectral bound into local exponential stability in BUC or in sufficiently regular Sobolev/Hölder spaces.

Near u=1, all real powers are smooth and the nonlinear remainder is quadratic. Schematically,

```plain text
w_t = Lw + N(w),
‖N(w)‖ ≤ C‖w‖²
```

in an appropriate positive neighborhood of 1. Hence one should be able to prove:

For every χ<χ_lin, sufficiently small BUC perturbations of 1 converge exponentially to 1.

This includes all χ<χ*. It is a valid non-rectangle result, but it is only a local basin theorem.

# 4. What this says about periodic or oscillatory counterexamples

## No local Turing branch below χ_lin

On a periodic interval or a Neumann interval, replace k² by a Laplacian eigenvalue s_n>0. A stationary mode loses invertibility when

```plain text
0 = −α − s_n + χγ s_n/(1+s_n),
```

that is,

```plain text
χ_n = ((α+s_n)(1+s_n))/(γs_n)
    = (1+α+s_n+α/s_n)/γ.
```

Minimizing continuously over s>0 gives s=sqrt(α) and the same threshold

```plain text
min_s χ(s) = (1+sqrt(α))²/γ = χ_lin.
```

Therefore no small-amplitude nonconstant steady state bifurcates from (1,1) for χ<χ_lin; in particular none does so in (1/2,1) in the standard case. Because the parabolic-elliptic linearized eigenvalues are real, there is also no Hopf bifurcation from (1,1) in that range.

Classical bounded-domain bifurcation papers on Keller–Segel systems with logistic growth find patterned branches when the chemotaxis parameter crosses precisely such mode-dependent Turing values. They support, rather than contradict, the above calculation.

A counterexample below χ_lin would therefore have to be one of the following:

- a disconnected, finite-amplitude or subcritical steady-state branch;

- a genuinely nonlinear time-dependent entire solution;

- a whole-line structure not arising as a perturbation of 1.

I found no published construction of such an object for this exact system with χ<1.

## Oscillatory traveling-wave tails are a different spectrum

Remark 1.3(2) concerns spatial behavior of a traveling profile, not temporal stability of the homogeneous Cauchy problem.

For a traveling wave ξ=x−ct, linearize

```plain text
U=1+p,
V=1+q.
```

The profile equations become

```plain text
p'' + cp' − χq'' − αp = 0,
q'' − q + γp = 0.
```

With (p,q)=e^{rξ}(P,Q), the spatial characteristic equation is

```plain text
(r²+cr−α)(r²−1) + χγr² = 0.
```

This quartic can have complex spatial roots, producing damped oscillation of a wave tail, even while every temporal Fourier mode has Re λ(k)<0. Thus:

An oscillatory left tail of a traveling wave does not imply temporal instability of (1,1) and does not supply a counterexample to whole-line stabilization of uniformly positive Cauchy data.

It may obstruct a monotonicity argument or a particular half-line comparison, but it is logically distinct from the temporal dispersion relation.

# 5. Why the rectangle threshold is smaller

For upper and lower ODE barriers (M(t),ℓ(t)), the width variable samples the worst possible mismatch between the global upper and lower signal bounds. Linearizing that two-number system at (1,1) gives width eigenvalue

```plain text
2χγ − α.
```

Hence it contracts exactly under

```plain text
2χγ < α.
```

The full PDE does not realize both worst-case nonlocal errors independently on every Fourier mode. The resolvent attenuates a mode by 1/(1+k²), and the destabilizing contribution is only

```plain text
χγ k²/(1+k²).
```

The rectangle method discards this frequency structure and pays a factor of two. It is therefore sufficient but far from spectrally sharp.

For m=1, criticality gives α=γ, so the rectangle condition is χ<1/2, while the true linear threshold is

```plain text
χ_lin=(1+sqrt(γ))²/γ>1.
```

For γ=1, this is the dramatic gap 1/2 versus 4.

# 6. Audit of the paper’s Theorem 1.2

The paper states positive-sensitivity wave stability for χ<χ*, where

```plain text
χ* = min(1,(2m+2γ)/(m²+m+2γ)).
```

Its left-tail step invokes Proposition 1.2(2), whose written positive-sensitivity hypothesis is χ<1/2. The underlying rectangle computation can be sharpened to 2χγ<α, so that mechanism repairs the proof only through

```plain text
χ < α/(2γ).
```

Therefore, whenever

```plain text
α/(2γ) < χ*,
```

the interval

```plain text
[α/(2γ),χ*)
```

is not covered by the cited argument.

The dispersion calculation shows that this is not evidence that the theorem is false: the equilibrium remains strictly linearly stable throughout that interval. The correct paper-audit conclusion is:

Theorem 1.2 has a proof gap in the stronger-positive-sensitivity range. Linear analysis supports the statement but does not fill the global nonlinear left-tail step.

For m=1, χ*=1 and α=γ, so the uncovered interval is exactly [1/2,1).

# 7. Candidate (a): what the spectral mechanism can actually prove

The spectral/semigroup approach should prove a clean theorem:

```plain text
small ‖u₀−1‖_BUC
      ⇒ ‖u(t,·)−1‖_BUC ≤ C e^(−δt) ‖u₀−1‖_BUC
```

for every χ<χ_lin, hence for every χ<χ*.

This is valuable for two reasons:

1. It certifies that the theorem’s disputed interval has the correct local dynamics.

1. It reduces the global problem to an eventual-entry problem: show that every uniformly positive bounded orbit eventually enters a sufficiently small neighborhood of 1.

But the latter is exactly what the rectangle proof supplied only below α/(2γ). Weighted traveling-wave convergence gives little control at the far-left end because the weight decays there, so one cannot simply bootstrap local stability without an independent left-tail trapping or Liouville argument.

# 8. Candidate (b): a promising nonlocal entropy, and its obstruction

There is a natural entropy that preserves the exact nonlocal structure rather than replacing it by upper/lower rectangles.

Choose H by

```plain text
H''(u)=γ u^(γ−m−1),
H'(1)=0.
```

Equivalently,

```plain text
H'(u)= γ/(γ−m) (u^(γ−m)−1)    if γ≠m,
H'(u)= γ log u                  if γ=m.
```

On a periodic domain, a Neumann domain, or for sufficiently decaying perturbations on R, multiplication by H'(u) gives

```plain text
d/dt ∫H(u)
 = −γ∫u^(γ−m−1)|u_x|²
   + χ∫(u^γ)_x v_x
   + ∫H'(u)u(1−u^α).
```

Using u^γ=v−v_xx,

```plain text
∫(u^γ)_x v_x = ∫(|v_x|²+|v_xx|²).
```

Thus

```plain text
dE/dt
 = −γ∫u^(γ−m−1)|u_x|²
   + χ∫(|v_x|²+|v_xx|²)
   − ∫H'(u)u(u^α−1).
```

The last integrand is nonnegative after the minus sign because H'(u) and u^α−1 have the same sign.

At quadratic order around u=1, this identity is exactly

```plain text
E' = γ ∫ λ(k)|ŵ(k)|² dk.
```

So this entropy sees the true dispersion relation and does not intrinsically impose the rectangle threshold 2χγ<α. This is the strongest candidate for a new proof.

However, two substantial gaps remain.

## Global scalar coercivity degenerates near zero

The resolvent term satisfies schematically

```plain text
∫(|v_x|²+|v_xx|²)
 = ⟨u^γ−1,(I−R)(u^γ−1)⟩
 ≤ ‖u^γ−1‖²_2.
```

To absorb it purely by reaction, one would need a uniform lower bound for

```plain text
H'(u)u(u^α−1) / (u^γ−1)².
```

Its limit at u=1 is α/γ, which recovers the favorable local margin. But it can degenerate as u↓0. In the standard case m=γ=α=1, the ratio is

```plain text
u log(u)/(u−1) → 0    as u↓0.
```

Thus a global entropy proof needs an eventual uniform positive floor, or a more subtle combined diffusion-reaction inequality. The assumption inf u₀>0 is helpful, but one must prove a quantitatively useful persistent floor and then show that the resulting coercivity dominates the chosen χ.

## Whole-line entropy may be infinite

For arbitrary BUC data, even u−1 need not be integrable or square-integrable on R. A global integral entropy may therefore be infinite. One likely needs one of:

- a uniformly-local entropy with sliding cutoffs;

- a relative entropy per unit length;

- an omega-limit/Liouville argument applied after space-time translation;

- a frequency-localized estimate on bounded windows.

The uniformly-local L^p methods used by Henderson and Rezek for strong-chemotaxis traveling waves show that such whole-line technology is realistic, but their result is not a global equilibrium-stability theorem.

So candidate (b) is plausible and structurally well matched, but it is not currently a one-line transfer from the bounded-domain Paper 3 Lyapunov functional.

# 9. Candidate (c): counterexample status

The exact linear computation rules out the most natural counterexample mechanism in the disputed range:

- no linear instability;

- no local stationary/Turing bifurcation;

- no Hopf bifurcation from (1,1).

The bounded-domain pattern literature constructs nonconstant branches only after explicit Turing thresholds and then studies large-chemotaxis spikes. For the standard normalized model, the continuous-mode threshold is χ=4; finite domains generally move the first admissible threshold upward unless an eigenvalue happens to be near the optimal wave number.

The strong-chemotaxis traveling-wave literature establishes waves without smallness assumptions and reports numerical changes in wave shape/stability, but it does not give a uniformly positive periodic steady state or Cauchy orbit contradicting convergence to 1 for χ∈(1/2,1).

After targeted searching, I found no known counterexample for the exact model in the interval [α/(2γ),χ*). This is not a proof of nonexistence; a finite-amplitude subcritical branch remains logically possible. But the evidence currently points to “missing global argument,” not “known false theorem.”

# 10. Best strategic route for the paper and for Lean

The most credible non-rectangle program is a three-stage argument.

## Stage 1: formalize local exponential stability

Prove the operator identity and exact spectral gap:

```plain text
L = ∂xx + χγ(I−(1−∂xx)^−1) − αI,

s(L)= −α                                           if χγ≤1,
      = (sqrt(χγ)−1)²−α                            if χγ>1.
```

Then prove local nonlinear stability in BUC using the existing whole-line semigroup infrastructure. This part should be technically feasible and gives an unconditional theorem throughout χ<χ*.

## Stage 2: compactness plus uniform persistence

For bounded uniformly positive initial data, establish:

- a time-uniform positive floor after some transient;

- positive-time spatial regularity and equicontinuity;

- precompactness of arbitrary space-time translates.

The repository already contains much of the smoothing/compactness infrastructure required for such a route.

## Stage 3: nonlinear Liouville theorem

Prove that every bounded entire solution satisfying

```plain text
0<δ≤u(t,x)≤M<∞
```

in the relevant χ<χ* regime is identically 1. A uniformly-local version of the entropy above is the most promising tool because its quadratic form is exactly the stable Fourier multiplier.

Once the Liouville theorem is known, a contradiction/omega-limit argument gives global uniform stabilization: if convergence failed, translate a bad sequence (t_n,x_n) and extract a nonconstant bounded entire limit, contradicting Liouville rigidity.

This route also fits the traveling-wave left-tail problem: it can be run on translated far-left windows and does not require monotonicity of the wave tail.

# 11. Lean-facing recommendation

Do not replace the missing global left-tail theorem by the dispersion relation alone. The safe formalization split is:

1. HomogeneousLinearization.lean

1. HomogeneousDispersion.lean

1. HomogeneousLocalStability.lean

1. Keep the global theorem as an explicit frontier:

```javascript
UniformlyPositive u₀ →
UniformConvergesToConstant (wholeLineCauchyGlobalU p u₀) 1
```

for α/(2γ)≤χ<χ*.

1. Pursue a separate uniformly-local entropy/Liouville producer. Only after that bridge is proved should it be wired into Theorem 1.2’s left-tail step.

# Final answer to the strategic question

Is stabilization in [α/(2γ),χ*) actually true?

The exact temporal spectrum strongly supports “yes,” and proves local exponential stability there. It rules out a Turing or small-periodic counterexample. But it does not by itself establish global stabilization from every uniformly positive datum.

Can a non-rectangle mechanism prove it?

Likely yes in principle. The best candidate is a uniformly-local nonlocal entropy combined with persistence, compactness, and a Liouville theorem. The entropy with H''(u)=γu^(γ−m−1) reproduces the exact dispersion relation at quadratic order and avoids the factor-two rectangle loss.

Is there a known counterexample below χ*≤1?

I found none for this exact system. Known patterned steady states bifurcate at the much larger mode threshold χ_n=((α+s_n)(1+s_n))/(γs_n), whose continuous minimum is χ_lin>1. Strong-chemotaxis oscillatory traveling-wave tails are spatial-spectrum phenomena, not counterexamples to temporal stabilization.

Paper verdict: Theorem 1.2 is not validated by its cited left-tail argument in the gap range, but the linear calculation does not falsify it. The correct classification is open nonlinear proof gap, with favorable spectral evidence.

# Sources

- W. Shen, “Existence, uniqueness, stability, and monotonicity of traveling waves for repulsion/attraction chemotaxis models with logistic type source,” arXiv:2605.04401. Relevant items: Proposition 1.2(2), Theorem 1.2, Remark 1.3(2), and the Section 5 left-tail argument.

- R. B. Salako and W. Shen, “Parabolic-elliptic chemotaxis model with space-time dependent logistic sources on R^N. II. Existence, uniqueness, and stability of strictly positive entire solutions,” arXiv:1801.05310. In the homogeneous standard model, the established global stability threshold remains of factor-two type.

- M. A. J. Chaplain and J. I. Tello, “On the stability of homogeneous steady states of a chemotaxis system with logistic growth term,” Applied Mathematics Letters 57 (2016), 1–6. Gives a classical sufficient condition 2χ|h'|<μ, again reflecting upper/lower comparison rather than the exact Fourier threshold.

- Q. Wang, J. Yan, and C. Gai, “Qualitative analysis of stationary Keller–Segel chemotaxis models with logistic growth,” arXiv:1312.0258. Derives explicit mode-dependent Turing/bifurcation values and patterned branches after loss of linear stability.

- C. Henderson and M. Rezek, “Traveling waves for the Keller–Segel–FKPP equation with strong chemotaxis,” JDE 379 (2024), 497–523; arXiv:2304.10024. Uses tailored uniformly-local L^p energy estimates for strong chemotaxis; useful methodological evidence but not a global homogeneous-stabilization theorem.