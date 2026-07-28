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
\(\min\{c_1^*,c_2^*\}\), are the candidate threshold in the desired sharp
two-species coexistence theorem.

The proved certificate theorems below deliberately use different, stronger
spatial hypotheses: Theorem 2.2 uses compact support and a kernel
minorization, while Theorem 2.3 additionally uses exact favorable tails.

## 4. Corrected statements and current formal status

The variational formulas in Section 3 describe the desired sharp theorem
package. The current Lean development proves Corrected Theorem 2.1 and
quantitative certificate versions of Corrected Theorems 2.2 and 2.3. It would
be inaccurate to describe the latter two as general sharp-speed theorems.

### Corrected Theorem 2.1: proved fast-habitat extinction

`correctedIDEOrbit_fastHabitat_extinction` is the proved two-species theorem.
For species \(i\), Lean defines

\[
c_{i,\mathrm{adm}}
  =\operatorname{extinctionCriticalSpeed}(k_i,1+\rho_i^+)
\]

as the infimum over `ExtinctionWeight`: a positive exponential weight for
which the weighted kernel is integrable and the complete linear multiplier is
positive. The theorem assumes that this admissible set is nonempty,
that each environment is nondecreasing with the stated negative left and
positive right limits, and that each initial component in the invariant unit
square vanishes to the right of a finite bound. If

\[
c>\max\{c_{1,\mathrm{adm}},c_{2,\mathrm{adm}}\},
\]

then the bounded-continuous sup norms of both components tend to zero. This is
a complete uniform-extinction result under its stated assumptions, with no
`sorry` and no project-specific axiom.

The admissible-domain qualification matters. The formal theorem does not
identify `extinctionCriticalSpeed` with an infimum over exponential weights
for which the moment or logarithm may be undefined.

### Corrected Theorem 2.2: proved certified-front version

`correctedIntermediateSpeedExclusion_of_minorization` proves the nonlinear
fast-component relaxation from uniform extinction of the slow component.
The assembly theorem
`correctedIntermediateSpeedExclusion_of_bcf_extinction_and_minorization`
takes instead the bounded-continuous norm limit
\(\|\mathrm{slow}_n\|_\infty\to0\), exactly the output shape of the
component extinction theorem, and discharges the pointwise extinction bridge
internally. For the fast component it assumes the corrected IDE recurrence,
a continuous compactly supported probability kernel, a nonnegative kernel
minorization on a finite displacement window, a compact positive seed, a
favorable-tail lower bound, and explicit fixed-floor reproduction and
corridor geometry inequalities. It concludes

\[
\mathrm{UniformlyExtinct}(\mathrm{slow})
\quad\text{and}\quad
\sup_{x\in E_n}
  |\mathrm{fast}_n(x)-1|\longrightarrow0,
\]

where

\[
E_n=[(c+\varepsilon_{\rm target})n,\,
     (\mathrm{front}-\varepsilon_{\rm target})n].
\]

The theorem also proves internally that the seed expansion stays in the
certified favorable tail. The bridge
`uniformlyExtinct_of_bcf_norm_tendsto_zero` is the exact step used by the
assembly theorem.

The formal obstruction
`minorization_reproduction_forces_growth_margin` also shows that the
one-step reproduction certificate necessarily satisfies

\[
1\leq \rho_0
  \bigl(1-2\,\mathrm{seed}
          -2\alpha\,\delta_{\mathrm{seed}}\bigr).
\]

In particular, it forces \(\rho_0>1\). Thus the certificate is a genuinely
strong sufficient hypothesis, not a consequence of merely having a positive
favorable growth rate.

This result is not the sharp statement
\(c_1^*<c<c_2^*\). In particular:

- the slow component's extinction is supplied separately rather than derived
  from the displayed speed ordering;
- `front` is a speed certified by the seed/minorization inequalities and is
  not identified with \(c_2^*\);
- no general leading-edge extinction theorem at speeds above \(c_2^*\) is
  asserted.

The one-sided corridor is essential. A symmetric region around \(cn\) has a
left edge moving slower than the habitat and therefore enters the
unfavorable far-left environment.

### Corrected Theorem 2.3: proved finite-range theorem with certified floors

For \(0<\alpha_1,\alpha_2<1\), define

\[
u^*=\frac{1-\alpha_1}{1-\alpha_1\alpha_2},
\qquad
v^*=\frac{1-\alpha_2}{1-\alpha_1\alpha_2}.
\]

The main proved spatial theorem is
`certified_weak_competition_spatial_coexistence`. It assumes:

- continuous compactly supported probability kernels with a common support
  radius;
- an `ExactFavorableTail` for each environment, so the environment is exactly
  equal to its favorable value beyond a stated threshold;
- a corrected two-species orbit in the invariant unit square;
- weak competition \(0<\alpha_i<1\);
- eventual positive floors for both species on a wider favorable corridor;
- margins satisfying
  \(0<\varepsilon_{\rm wide}<\varepsilon_{\rm target}\) and
  \(c+2\varepsilon_{\rm target}\le\mathrm{front}\).

Finite kernel range and exact favorable tails turn those floors into the
fixed-depth seeded-envelope comparison. The theorem then proves uniform
convergence of both components to \((u^*,v^*)\) on

\[
[(c+\varepsilon_{\rm target})n,\,
  (\mathrm{front}-\varepsilon_{\rm target})n].
\]

`constant_speed_observer_tendsto_of_uniform_corridor` then gives convergence
along every constant-speed observer that remains in this corridor.

The further theorem
`certified_weak_competition_spatial_coexistence_of_minorization` replaces the
two eventual-floor assumptions by one `CorridorFloorCertificate` per species.
Each certificate contains a kernel minorization window, compact positive seed,
one-step reproduction inequality, and explicit geometry keeping its expanding
interval inside the exact favorable tail. This is an additional numerical
sufficient condition, not an automatic consequence of
\(0<\alpha_i<1\). The theorem
`corridorFloorCertificate_forces_growth_restriction` proves the exact
necessary inequality

\[
1\leq \rho_i^+
  \bigl(1-2\,\mathrm{floor}_i-2\alpha_i\bigr).
\]

Consequently, this one-step certificate forces
\(\alpha_i<1/2\) and \(\rho_i^+>1\); it is impossible when
\(\alpha_i\geq1/2\). This obstruction concerns the particular certificate,
not the positive-floor coexistence theorem itself.

Neither theorem is a general sharp-threshold theorem. Although
`WeakCompetitionCoexistence.lean` defines the admissible reduced speed
`coexistenceCriticalSpeed`, its theorem
`corrected_weak_competition_uniform_corridor_convergence` still assumes the
global fixed-depth seeded-envelope comparison. The main spatial theorem
discharges that comparison under its finite-range, exact-tail, and
eventual-floor hypotheses; the minorization corollary produces those floors
when its two numerical certificate assumptions are supplied. Their `front`
is not identified with \(c_{\rm coex}\). The implication from
\(c<c_{\rm coex}\) and merely nonzero initial data to the required eventual
floors, or to the stronger numerical certificates, remains unproved.

## 5. What is already proved in Lean

All files below compile without `sorry` and without project-specific axioms.
Their axiom audits report only Lean/Mathlib foundations such as propositional
extensionality, quotient soundness, and classical choice. The dependency
column lists direct project imports and omits Mathlib imports.

| File | Direct project dependencies | Verified content |
|---|---|---|
| `ShenWork/Liang/ModelAudit.lean` | — | Positivity on the admissible simplex for the printed map; exact coexistence equilibrium; fixed-point identities; moving-frame limits |
| `ShenWork/Liang/CorrectedModel.lean` | `ModelAudit` | Global positivity and unit bound of the corrected map; focal monotonicity; competitor antitonicity; favorable equilibrium preservation; invasion-multiplier inequalities |
| `ShenWork/Analysis/DispersalKernel.lean` | — | Convolution change of variables; exponential-tail eigenfunction; exact discrete exponential orbit; moving-frame decay |
| `ShenWork/Liang/LinearDeterminacy.lean` | `DispersalKernel`, `ModelAudit`, existing `WaveRotheTrap` | Critical-speed specialization and an exact bridge to ShenWork's `kernelConvVal` convention |
| `ShenWork/Liang/IDEComparison.lean` | `DispersalKernel`, `CorrectedModel` | Corrected-update integrability and unit bound; linear domination; order preservation; exponential barriers; moving-frame extinction of sublinear orbits |
| `ShenWork/Liang/StateSpace.lean` | `IDEComparison`, existing `WaveRotheTrap` | Bounded-continuous unit-square state; corrected self-map and orbit; competitive product order; zero-species invariance |
| `ShenWork/Liang/MovingCorridor.lean` | `ModelAudit` | Nonemptiness and favorable-tail geometry of one-sided moving corridors |
| `ShenWork/Liang/GlobalDynamicsTools.lean` | `CorrectedModel` | Algebraic response tests and the weak-competition rectangle squeeze |
| `ShenWork/Liang/FastHabitatExtinction.lean` | `StateSpace`, `LinearDeterminacy` | Admissible extinction weights, component extinction, and the top theorem `correctedIDEOrbit_fastHabitat_extinction` |
| `ShenWork/Liang/ScalarPersistence.lean` | `IDEComparison` | Beverton–Holt convergence, positivity propagation, interval seeds, an expanding-interval positive floor, and the necessary growth margin for a one-step minorization certificate |
| `ShenWork/Liang/IntermediateSpeedExclusion.lean` | `ScalarPersistence`, `MovingCorridor`, `StateSpace` | Compact-support comparison, corridor floor and convergence, the norm-to-extinction bridge, the conditional relaxation theorem, and the assembled result `correctedIntermediateSpeedExclusion_of_bcf_extinction_and_minorization` |
| `ShenWork/Liang/SeededEnvelope.lean` | `GlobalDynamicsTools` | Valid nested seeded envelopes and `seededEnvelopeOrbit_tendsto_coexistence` |
| `ShenWork/Liang/WeakCompetitionCoexistence.lean` | `GlobalDynamicsTools`, `LinearDeterminacy`, `MovingCorridor`, `SeededEnvelope` | Admissible reduced speeds, homogeneous and seeded-envelope convergence, the conditional corridor theorem `corrected_weak_competition_uniform_corridor_convergence`, and the observer corollary |
| `ShenWork/Liang/SpatialCoexistenceCertificate.lean` | `IntermediateSpeedExclusion`, `WeakCompetitionCoexistence` | Exact finite-depth spatial comparison; `certified_weak_competition_spatial_coexistence` from eventual positive wider-corridor floors; the stronger-assumption minorization corollary; and the proof that its one-step certificate forces \(\alpha_i<1/2\) and \(\rho_i^+>1\) |

## 6. What remains for the sharp proposal-level package

1. Relate the admissible-domain speed in Corrected Theorem 2.1 to any preferred
   unrestricted notation only after stating enough moment-domain hypotheses.
   The extinction theorem itself is complete.
2. For Corrected Theorem 2.2, derive both the slow-species extinction and the
   surviving-species positive floor directly from
   \(c_1^*<c<c_2^*\) under a general linear-determinacy theorem. Then identify
   the certified `front` with the sharp \(c_2^*\) and add the leading-edge
   extinction statement. The present proof instead uses compact support and
   a finite-window minorization certificate.
3. For Corrected Theorem 2.3, derive the two eventual positive corridor floors
   from
   \(c<c_{\rm coex}\), general admissible kernels, and nontrivial initial data.
   Then identify the corridor front with the sharp reduced speed. The present
   spatial theorem assumes compact support and exact favorable tails; the
   one-step minorization corollary is only one additional sufficient route to
   the required floors.

The proved certificate arguments are discrete-time corridor arguments. They
do not follow directly from a continuous-time nonlocal PDE theorem.

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
standalone mathematical note: its main body contains proved statements,
explicitly conditional speed corollaries, and clearly identified remaining
analytic steps, with no formalization or build terminology. Its appendix
gives the model-level, theorem-level, strong-competition, PINN, and editorial
defects in the original proposal, together with a repair for each category.

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
