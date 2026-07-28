# Correcting the shifting-habitat integrodifference model

## 1. Source and status

This audit concerns `CMBE_2026.pdf`, “Spatial Dynamics of an
Integro-Difference Lotka–Volterra Model in a Shifting Habitat,” by Xiang Huang
and Liang Kong.

The proposal says that Theorems 2.1–2.3 are results “we propose to establish.”
They should therefore be treated as proof targets, not as established results.
The source PDF has SHA-256

```text
5b9c9053541a5e8f7c7524e871444d571669208e038e14d0eccf2406e08044d3
```

## 2. The smallest useful model correction

The printed focal-species response is

\[
F(\rho,\alpha;u,v)
  = \frac{(1+\rho)u}{1+\rho(u+\alpha v)}.
\]

When \(\rho<0\), its denominator need not remain positive on the positive
cone, and its derivative with respect to \(v\) has the wrong sign for
competition. Merely imposing \(u+\alpha v\le 1\) repairs positivity but does
not repair this reversal of competitive order.

The recommended correction is

\[
\widehat F(\rho,\alpha;u,v)
  = \frac{(1+\rho)u}
         {1+[\rho]_+(u+\alpha v)},\qquad
[\rho]_+ := \max\{\rho,0\}.
\]

This changes only the unfavorable part of the habitat:

- if \(\rho\ge0\), then \(\widehat F=F\), so the proposed favorable dynamics
  and equilibrium are unchanged;
- if \(-1<\rho\le0\), then \(\widehat F=(1+\rho)u\), which is nonnegative
  subcritical growth;
- density dependence never changes sign.

The more general modelling principle is to separate signed low-density growth
from nonnegative density dependence:

\[
F_i(s;u,v)
  = \frac{R_i(s)u}{1+b_i(s)(u+\alpha_i v)},
  \qquad R_i(s)>0,\quad b_i(s)\ge0.
\]

The positive-part model is the minimal special case
\(R_i=1+\rho_i\), \(b_i=[\rho_i]_+\).

## 3. Assumptions for a corrected theorem package

Use one environmental function \(\rho_i\) for each species; the proposal is
the special case \(\rho_1=\rho_2\). Assume:

1. \(\rho_i\) is continuous and nondecreasing, with
   \(-1<\rho_i^-<0<\rho_i^+\), where
   \(\rho_i^\pm=\rho_i(\pm\infty)\).
2. \(k_i\) is a continuous, strictly positive probability density. Its moment
   generating function is finite on an open interval containing the positive
   weights used below.
3. The initial data are continuous, compactly supported, take values in
   \([0,1]^2\), and every species claimed to persist is initially nonzero.
4. The corrected response \(\widehat F\) is used in both equations.
5. For conclusions identifying an exact nonlinear spreading speed, impose the
   standard irreducibility and linear-determinacy hypotheses at the relevant
   zero or semi-trivial equilibrium.

Let

\[
M_i(\mu)=\int_{\mathbb R} k_i(z)e^{\mu z}\,dz,\qquad
R_i=1+\rho_i^+,
\]

and define the empty-habitat speeds

\[
c_i^*=\inf_{\mu>0}\frac{\log(R_iM_i(\mu))}{\mu}.
\]

For weak competition, the growth multiplier of a rare species against the
other species at density one is

\[
\widetilde R_1=\frac{R_1}{1+\rho_1^+\alpha_1},
\qquad
\widetilde R_2=\frac{R_2}{1+\rho_2^+\alpha_2}.
\]

Thus the conservative coexistence-front speeds are

\[
\widetilde c_i^*
  =\inf_{\mu>0}
     \frac{\log(\widetilde R_iM_i(\mu))}{\mu},
\qquad
c_{\rm coex}=\min\{\widetilde c_1^*,\widetilde c_2^*\}.
\]

These reduced speeds, rather than merely
\(\min\{c_1^*,c_2^*\}\), are the natural sufficient threshold for a
two-species coexistence corridor.

## 4. Corrected theorem statements

The following are the mathematically defensible targets. The local algebra,
exponential propagation, scalar domination, moving-frame geometry,
unit-square state-space invariance, competitive comparison, and zero-species
invariance are already formalized. The full nonlinear long-time conclusions
still require the persistence arguments listed in Section 6.

### Corrected Theorem 2.1: fast-habitat extinction

Assume the hypotheses in Section 3. If

\[
c>\max\{c_1^*,c_2^*\},
\]

then

\[
\lim_{n\to\infty}
  \sup_{x\in\mathbb R}\max\{u_n(x),v_n(x)\}=0.
\]

The restriction of the initial data to the invariant unit square replaces the
proposal's insufficient “nonnegative and bounded” assumption.

### Corrected Theorem 2.2: intermediate-speed exclusion

Assume \(c_1^*<c<c_2^*\), and assume \(v_0\not\equiv0\). Then

\[
\lim_{n\to\infty}\sup_{x\in\mathbb R}u_n(x)=0.
\]

For every

\[
0<\varepsilon<\frac{c_2^*-c}{2},
\]

the surviving species converges to its favorable single-species equilibrium
in the one-sided corridor

\[
E_n^\varepsilon
  =\{x:(c+\varepsilon)n\le x\le(c_2^*-\varepsilon)n\}:
\]

\[
\lim_{n\to\infty}
  \sup_{x\in E_n^\varepsilon}|v_n(x)-1|=0.
\]

A precise spreading statement should additionally include

\[
\lim_{n\to\infty}
  \sup_{x\ge(c_2^*+\varepsilon)n}v_n(x)=0
\]

and extinction behind every line slower than the habitat. If the ordering of
the two speeds is reversed, interchange the species.

The symmetric region \(|x-cn|\le\eta n\) must not be used: its left edge moves
at speed \(c-\eta<c\) and therefore samples the unfavorable far-left
environment.

### Corrected Theorem 2.3: weak-competition coexistence

Assume \(0<\alpha_1,\alpha_2<1\), both initial components are nonzero, the
linear-determinacy hypotheses hold, and

\[
0<c<c_{\rm coex}.
\]

Define

\[
u^*=\frac{1-\alpha_1}{1-\alpha_1\alpha_2},
\qquad
v^*=\frac{1-\alpha_2}{1-\alpha_1\alpha_2}.
\]

For every

\[
0<\varepsilon<\frac{c_{\rm coex}-c}{2},
\]

one should prove

\[
\lim_{n\to\infty}
  \sup_{(c+\varepsilon)n\le x\le(c_{\rm coex}-\varepsilon)n}
  \max\{|u_n(x)-u^*|,\ |v_n(x)-v^*|\}=0.
\]

The fixed-observer version is:

\[
c<c'<c_{\rm coex},\quad R>0
\quad\Longrightarrow\quad
\lim_{n\to\infty}\sup_{|x-c'n|\le R}
  \max\{|u_n(x)-u^*|,\ |v_n(x)-v^*|\}=0.
\]

The lower bound \(c<c'\) is essential. For \(c'<c\), the moving coordinate
\((c'-c)n\) tends to \(-\infty\), so the observer samples the unfavorable
environment and cannot generally converge to the positive far-right
equilibrium.

## 5. What is already proved in Lean

All files below compile without `sorry` and without project-specific axioms.
Their axiom audits report only Lean/Mathlib foundations such as propositional
extensionality, quotient soundness, and classical choice.

| File | Verified content |
|---|---|
| `ShenWork/Liang/ModelAudit.lean` | Positivity on the admissible simplex for the printed map; exact coexistence equilibrium; fixed-point identities; moving-frame limits |
| `ShenWork/Liang/CorrectedModel.lean` | Global positivity of the corrected map; invariant unit bound; monotonicity in the focal species; antitonicity in the competitor; favorable equilibrium preservation; weak- and strong-competition invasion-multiplier inequalities |
| `ShenWork/Analysis/DispersalKernel.lean` | Convolution change of variables; exponential-tail eigenfunction; exact discrete exponential orbit; speed-dependent moving-frame decay |
| `ShenWork/Liang/LinearDeterminacy.lean` | Critical-speed specialization and an exact bridge to ShenWork's existing `kernelConvVal` convention |
| `ShenWork/Liang/IDEComparison.lean` | Continuity-based integrability of the corrected update; probability-kernel lifting of the unit-interval bound; corrected nonlinear step dominated by the far-right linear step; order preservation; exponential-barrier induction; moving-frame extinction of sublinear orbits |
| `ShenWork/Liang/StateSpace.lean` | Bounded-continuous two-species state; direct construction with ShenWork `greenConvBCF`; a proved self-map of unit-square states; competitive product-order preservation; recursive orbit; proof that an initially absent species remains absent |
| `ShenWork/Liang/MovingCorridor.lean` | Nonemptiness of the corrected one-sided corridor; every point sequence in it samples the favorable far-right environment |

In particular, the formalization has moved beyond finding counterexamples:
the recommended response has the complete local order structure needed by a
comparison proof, and the upper-spreading exponential argument is already
machine checked.

## 6. Remaining proof architecture

The global theorems should be completed in this order:

1. Establish strong positivity and quantitative positivity propagation for
   the now-bundled discrete state update. The competitive product-order
   theorem is complete.
2. Prove the scalar moving-habitat theorem for the corrected Beverton–Holt
   equation: extinction above \(c_i^*\), persistence below \(c_i^*\), and
   interior convergence in \((c,c_i^*)\).
3. Deduce Corrected Theorem 2.1 by componentwise scalar domination.
4. For Corrected Theorem 2.2, first extinguish the slower component, then
   sandwich the surviving component between scalar equations with a vanishing
   competition perturbation.
5. For Corrected Theorem 2.3, construct compact moving subsolutions using the
   reduced multipliers \(\widetilde R_i\), obtain a positive floor in the
   coexistence corridor, and iterate upper/lower homogeneous competition maps
   to squeeze the solution to \((u^*,v^*)\).

This is a discrete-time analogue of the corridor strategy in the continuous
nonlocal competition literature, not a direct reuse of a continuous-time PDE
theorem.

## 7. Exact connection to ShenWork

The overlap is real but low-level:

- both developments use the convention
  \((K*f)(x)=\int K(x-y)f(y)\,dy\);
- both need translation of that integral to
  \(\int K(z)f(x-z)\,dz\);
- both use exponential modes/barriers and comparison arguments;
- both study waves or moving frames.

The existing ShenWork `kernelConvVal` acts on bounded continuous functions.
The new `StateSpace.lean` directly uses ShenWork's `greenConvBCF` to construct
each next-generation profile and proves that it remains a bounded continuous
unit-square state. The IDE speed calculation also uses the globally unbounded
test function \(e^{-\mu x}\), so a raw-integral generalization was necessary.
The Lean bridge theorem proves that the raw and bounded-continuous operators
agree exactly on their common domain.

The large ShenWork chemotaxis PDE compactness and implicit-Euler theorems do
not directly prove the IDE long-time dynamics: continuous versus discrete
time and scalar versus competitive order are substantive differences.

The accompanying `CORRECTED_THEOREMS.pdf` is deliberately written as a
standalone mathematical note: its main body contains only proved statements
and clearly labelled conjectures, with no formalization or build terminology.
Its appendix gives the model-level, theorem-level, strong-competition, PINN,
and editorial defects in the original proposal, together with a repair for
each category.

## 8. Further generalizations

The corrected framework naturally extends to:

- species-dependent environments \(\rho_i\) and carrying capacities;
- general nonnegative density-dependence coefficients \(b_i(s)\);
- asymmetric kernels and direction-dependent speeds;
- higher-dimensional directional moments
  \(M_i(\mu,e)=\int k_i(z)e^{\mu e\cdot z}\,dz\);
- more than two competitors, with a coexistence matrix replacing
  \(1-\alpha_1\alpha_2\);
- nonconstant habitat displacement \(C_n\), provided its asymptotic speed and
  moving-coordinate margins are controlled.

## 9. Claims that should not yet appear as theorems

- “Under strong competition, the faster species excludes the other” needs
  explicit invasion eigenvalue and initial-data hypotheses. Strong
  competition can produce bistability, so speed ordering alone is
  insufficient.
- “PINN loss tending to zero implies convergence to the analytic wave and
  consistent speed recovery” needs compactness, stability, identifiability,
  and approximation hypotheses. It is a computational proposal, not a
  consequence of the current model assumptions.

## 10. Primary references used for the correction

- M. A. Lewis, N. G. Marculis, and Z. Shen,
  [“Integrodifference equations in the presence of climate change:
  persistence criterion, travelling waves and inside dynamics”](https://www.math.ualberta.ca/~mlewis/Publications%202018/Lewis_Marculis_Shen.pdf).
- C. Wu, Y. Wang, and X. Zou,
  [“Spatial-temporal dynamics of a Lotka–Volterra competition model with
  nonlocal dispersal under shifting environment”](https://www.uwo.ca/apmaths/faculty/zou/repr/jde19-2.pdf).
- L. Kong, N. Rawal, and W. Shen,
  [“Spreading Speeds and Linear Determinacy for Two Species Competition
  Systems with Nonlocal Dispersal in Periodic Habitats”](https://arxiv.org/abs/1410.0317).
