# PDE-Library Design Campaign — PLAN (先规划，再动手)

Goal: build, over months, a Lean 4 parabolic-PDE library that GENUINELY proves the Chen–Ruau–Shen
chemotaxis-growth system's well-posedness + long-time behavior (so every Paper 3 floor is discharged, not
labeled). Target system, on a bounded domain Ω (start: interval [0,1], Neumann):
  u_t = Δu − χ∇·(u·s(v)∇v) + a u − b u^{1+α},   0 = Δv − v + u^γ,   ∂ν u = ∂ν v = 0,   s(v)=χ₀/(1+v)^β.

## Method (Xiang's directive)
Multi-round (≥10) design dialogue WITH ChatGPT Pro to architect the framework BEFORE writing Lean. Each
round pins one architectural layer; I push back, cross-check against ACTUAL Mathlib (what exists vs what we
must build), and refine. Converge to a stable, dependency-consistent architecture + an explicit Mathlib-gap
list. Only then implement bottom-up.

## Convergence criterion
The campaign has converged when: (i) every layer's Lean INTERFACE (the key defs/theorem signatures) is
pinned; (ii) the dependency DAG between layers is acyclic and complete; (iii) the foundational Mathlib-gap
pieces (what's missing and must be built first) are enumerated with a build order; (iv) two consecutive
rounds produce no structural change (only polish). Track per-round deltas; stop when deltas → 0.

## Round structure (the architecture layers — order may adapt as rounds reveal dependencies)
- R0  Framing + state-of-Mathlib audit: what parabolic/semigroup/Sobolev/compactness machinery does Mathlib
      v4.29 actually have? (the hard constraint that shapes every choice). Decide the core formulation:
      classical (C^{2,1}) vs Sobolev/weak vs semigroup/mild — and the function-space representation in Lean.
- R1  Function spaces: how to represent the working spaces (C^{k,α} Hölder, W^{k,p} Sobolev, fractional
      X_p^σ / interpolation) given Mathlib; what to build, what to reuse.
- R2  1D Neumann elliptic layer: Green/resolvent kernel for −∂xx+1 on [0,1] Neumann; elliptic regularity +
      gradient estimates (the v-equation; Lemma 7.1).
- R3  Linear parabolic layer: the Neumann heat semigroup on the interval (spectral/Fourier construction),
      its smoothing/decay estimates — the backbone for Duhamel and for sectoriality.
- R4  Local existence + continuation: mild/Duhamel fixed point for the u-equation (with the frozen-v
      elliptic solve); positivity, continuation criterion.
- R5  Maximum principles + comparison: parabolic SMP, sub/super-solutions on the interval.
- R6  A-priori bounds / boundedness: energy + logistic damping, L^p→L^∞ (Moser/Alikakos) bootstrap;
      negative-sensitivity branch first → global existence (P3.1).
- R7  Compactness: parabolic-Hölder Arzelà-Ascoli vs Aubin–Lions; time-translate compactness (P3.2/P3.5).
- R8  Sectorial / analytic semigroups: sectoriality of the linearized Neumann operator, fractional domains,
      local exponential stability (P3.4, P3.3 nonlinear).
- R9  Lyapunov + LaSalle: dissipation → ω-limit → global convergence → C¹ exponential upgrade (P3.6).
- R10 Composition + floor map: how the layers compose to discharge each Paper 3 floor; the abstraction
      boundaries (so layers are reusable, not Shen-specific).
- R11 Mathlib-gap consolidation + build order: the full bottom-up implementation sequence + the from-scratch
      Mathlib pieces, with rough effort sizing.
- R12+ Iterate any layer that didn't converge; adversarial review of the whole DAG.

## Discipline
- ChatGPT designs; I VERIFY every claim about Mathlib against the actual library (it has no repo/Mathlib
  access — it WILL invent APIs; catch them). Architecture is faithful to the paper's proof, not a shortcut.
- Record each round's outcome here (a running design log). The artifact of this campaign is THIS document
  growing into the library's architecture spec.
- Paper 1 per-step (genuine elliptic/Rothe PDE) finishes in parallel as the warm-up; its truncated-box /
  greenConv / max-principle machinery is itself reusable scaffolding for this library.

## Design log
(rounds appended here as they complete)

### R0 — Mathlib audit (done, 2026-06-18)
Mathlib v4.29 has **NO** parabolic-PDE infrastructure: no heat/parabolic/evolution equations; no semigroups
(C0/analytic/sectorial — only algebraic subsemigroups); no Sobolev SPACES (only `SobolevInequality`, the GNS
inequality); no maximum principle; no elliptic regularity. HAS: Hölder continuity + norms
(`Topology/MetricSpace/Holder`, `HolderNorm`, `Analysis/Calculus/ContDiffHolder`); **Arzelà-Ascoli**
(`Topology/UniformSpace/Ascoli`); Fourier series; Lebesgue integration; ContDiff/calculus; Banach spaces +
bounded operators; measure theory. NO Aubin-Lions, NO Rellich.
Repo already has (Paper 3): `unitIntervalNeumannSpectrum` (eigenvalues n²π², first nonzero π²),
`unitIntervalNeumannHeatSemigroupP0Compl` (heat semigroup on zero-mean subspace, operator-norm decay e^{-π²t}).
**Architectural consequence:** build the 1D interval theory CONCRETELY via the explicit Neumann Fourier
eigenbasis (heat semigroup = Σ e^{-n²π²t}⟨·,φₙ⟩φₙ; regularity = Fourier-coefficient decay), NOT abstract
semigroup theory. This is the only route buildable on current Mathlib and is faithful for the 1D domain.

### R0 — CORE FORMULATION DECIDED (ChatGPT R0 + Mathlib-verified)
**Core = physical-space MILD (Duhamel) formulation as the base solution layer; kernel + all estimates
PROVED from the explicit Neumann Fourier basis. NOT a Gevrey/coefficient fixed point.** Two-layered:
- BASE: physical C⁰ = `BoundedContinuousFunction` on [0,T]×[0,1] (Banach ✓). Local existence = Banach fixed
  point (Mathlib `Contracting.lean` ✓) on the Duhamel map. Crux: chemotaxis transport is CLEAN in C⁰ —
  v=R(u^γ)≥0 keeps 1+v≥1 so S(v)=(1+v)^{-β} is Lipschitz, q=u·S(v)·v_x bounded+Lipschitz, and
  ‖∂xE(t)f‖∞≤C t^{-1/2} gives the √t contraction (∫₀ᵗ(t-τ)^{-1/2}dτ=2√t). Avoids real-power coefficient
  composition at the foundation.
- ENGINE/REGULARITY: A^r = ℓ¹((1+|k|)^r) Fourier-Wiener (Banach algebra under convolution; Mathlib `lp` ✓).
  Heat smoothing gains derivatives ‖E(t)f‖_{A^{r+m}}≤C t^{-m/2}‖f‖_{A^r}; COMPACTNESS via tail control
  ‖P_{>N}f‖_{A^r}≤(1+N)^{-δ}‖f‖_{A^{r+δ}} — the interval-Fourier replacement for Rellich/Aubin-Lions.
Global boundedness: NO pure sup-norm shortcut for full χ₀>0; do χ₀≤0 / small-χ₀ / exponent-dominant first,
full theorem needs energy/Moser. Mathlib primitives verified present: Contracting, BCF, Fourier
(FourierMultiplier/Gaussian/AddCircle), lp, Gronwall, PicardLindelof. To BUILD: the explicit kernel + t^{-1/2}
smoothing + resolvent + composition lemmas. Revised layer order: 1 kernel/semigroup/resolvent → 2 C⁰ mild
existence → 3 smoothing bootstrap → 4 positivity/comparison/continuation → 5 restricted boundedness →
6 full energy/Moser → 7 compactness (Fourier tails) → 8 spectral+nonlinear stability → 9 Lyapunov.

### R1 — LAYER 1 (heat semigroup + resolvent) DESIGNED (ChatGPT R1 + Mathlib-verified)
**Heat semigroup PRIMARY def: E_phys(t)f = G_t * f_{even,2per}** (whole-line Gaussian convolution of the even
2-periodic extension; G_t=(4πt)^{-1/2}e^{-z²/4t}). All load-bearing estimates from the Gaussian's L¹ norms:
‖E(t)f‖∞≤‖f‖∞; ‖∂xE(t)f‖∞≤‖G_t'‖_{L¹}‖f‖∞=(πt)^{-1/2}‖f‖∞ (the t^{-1/2} smoothing); ‖∂xxE‖∞≤t^{-1}‖f‖∞;
positivity (G_t>0); E(t)1=1; Neumann BC (even-symmetry ⟹ ∂xE odd integrand at 0,1 → 0); semigroup
(G_t*G_s=G_{t+s}). Reflected-Gaussian-sum kernel + Poisson identity = DEFERRED theorems, not the def (dodges
all the hard convergence/differentiation). SPECTRAL face E_spec(t)a_k=e^{-π²k²t}a_k for A^r (repo has it).
Bridge = mode-action coeff identity ⟨E_phys(t)f,φ_k⟩=e^{-π²k²t}⟨f,φ_k⟩ (via Gaussian FT on cos modes, NOT
full Poisson). **Resolvent PRIMARY: R_phys via explicit POSITIVE Green's fn G_R(x,y)=cosh(min(x,y))·
cosh(1−max(x,y))/sinh1** ⟹ f≥0⟹Rf≥0 free; R1=1; ‖Rf‖∞≤‖f‖∞; R''=Rf−f dodges diagonal diff ⟹ ‖R''‖∞≤2‖f‖∞;
Neumann BC from the split-derivative formula. Spectral face (1+π²k²)^{-1} for A^r. ONE new utility:
fold01:ℝ→[0,1] (even 2-periodic fold). MATHLIB VERIFIED present: Gaussian Integral+FourierTransform+
PoissonSummation, Convolution, ParametricIntegral (∂xE), Floor/fract (fold01), cosh/sinh. TO BUILD: the
Neumann assembly + estimates + fold01 + Green's-fn resolvent (Gaussian-conv-semigroup likely derivable from
the Gaussian FT). Full ~25-lemma Layer-1 interface pinned in the R1 transcript. Layer-1 = Mathlib-feasible.

### R7 — LAYER 7 (COMPACTNESS, Aubin-Lions replacement) DESIGNED (ChatGPT, independent of existence thread)
Replace Rellich/Aubin-Lions (absent in Mathlib) with weighted-ℓ¹ tail compactness on A^r.
- SPATIAL: A^{r+δ} ⊂⊂ A^r. Criterion (TOTAL-BOUNDEDNESS, not diagonal extraction): uniform tail smallness
  sup_S ‖Q_N a‖_{A^r}≤ε + finite-mode precompactness (P_N S in a finite coordinate box) ⟹ S precompact.
  Core estimate `tail_bound_high_to_low`: ‖a−P_N a‖_{A^r} ≤ (1+N)^{-δ}‖a‖_{A^{r+δ}}. NOT discrete-ℤ Ascoli
  (misses the tail). Plus `high_norm_retention_under_low_convergence` (A^r-limit keeps the A^{r+δ} bound) — key for ω-limits.
- PHYSICAL: A^r ↪ C^0 (‖F^{-1}a‖_∞ ≤ ‖a‖_{A^r}, r≥0); A^{m+δ}⊂⊂A^m↪C^m. A^r-compactness ⟹ C^0-compactness
  through the continuous Fourier reconstruction — NO separate physical Arzelà-Ascoli needed.
- TIME (the Aubin-Lions replacement): uniform A^{r+δ} bound (⟹ spatial precompact per t) + Duhamel
  EQUICONTINUITY modulus ω(h)=η_{M,δ}(h)+B0·h+2C·B1·h^{1/2} (η = semigroup-strong-continuity, low/high-mode
  split) ⟹ precompact in C([0,T];A^r) via Mathlib's Arzelà-Ascoli (the ONE place to use it).
- ω-LIMIT: translate family u(·+t_n) precompact on each window (modulus is translation-invariant) + diagonal
  across windows. Limit continuous into A^r, keeps A^{r+δ} bound pointwise.
- ADVERSARIAL GAP (must build with this layer): compactness alone does NOT make the limit solve the SAME
  equation — need CLOSEDNESS: u_n→u in C_t A^r + uniform A^{r+δ} + nonlinear LOCAL-LIPSCHITZ (from A^r Banach
  algebra + Fourier-multiplier R-bound + heat smoothing) ⟹ u is a mild solution. The Duhamel terms pass to
  the limit (∂xE integral ≤ 2C T^{1/2}‖H(u_n)−H(u)‖). This is nonlinear-continuity, NOT a new compactness theorem.
~15-lemma interface pinned. Mathlib: Arzelà-Ascoli (time layer) ✓, lp/tsum (tails) ✓; weighted-ℓ¹ criterion = ours to build.

### R3 — LAYER 3 (SMOOTHING / A^r REGULARITY BOOTSTRAP) DESIGNED (ChatGPT cron2 + verified) — full transcript docs/layer3-smoothing-transcript.md
The abstract A^r bootstrap closes cleanly ONCE you have a positive-time A^σ seed (0<σ<1); it does NOT
follow from a bare C⁰ mild solution by applying A^r→A^{r+m} heat estimates. 26-lemma DAG pinned.
- DUHAMEL GAIN (the key constraint, VERIFIED): reaction term ∫E(t−τ)F gains any m<2 derivatives
  (kernel t^{−m/2}, ∫₀ᵗ integrable iff m<2); TRANSPORT term ∫∂xE(t−τ)Q gains only m<1 (∂xE multiplier
  (πik)e^{−π²k²t} ⟹ t^{−(1+m)/2}, integrable iff m<1). So one-step bootstrap = A^r ⟹ A^{r+θ}, any 0<θ<1;
  iterate with decreasing delays ⟹ A^R for all finite R at positive time ⟹ C^∞_x. Do NOT use ∂xxE on the
  Duhamel term (exponent (2+m)/2≥1, non-integrable).
- A^r ALGEBRA: ‖fg‖_{A^r}≤C_r‖f‖‖g‖ via weight-submultiplicativity (1+|k|)^r≤(1+|ℓ|)^r(1+|k−ℓ|)^r + ℓ¹
  convolution; resolvent ‖Rf‖_{A^{r+2}}≤C‖f‖_{A^r}; A^s↪C^k (s≥k). Real powers u^m,u^γ,S(v) via smooth
  composition on a POSITIVE range κ≤u≤M.
- TIME REG: A^{r+2} + nonlinearity in A^r ⟹ ∂t u∈A^r ⟹ u∈C¹([δ,T];A^r) (parabolic trade 2 space=1 time);
  + Lipschitz-in-time ‖u(t)−u(s)‖_{A^r}≤C|t−s| on positive slabs (the equicontinuity Layer-7 consumes).
- CONVERGENCE CHECK (honest — does NOT close from Layer-1 + bare-C⁰-Layer-2): surfaces THREE NEW
  cross-layer dependencies that must be pinned:
  (Dep-1 SEED) C⁰ mild ⟹ C([δ,T];A^σ), 0<σ<1 — the C⁰→A^σ singularity ∑|k|e^{−π²k²s}~s⁻¹ is NOT
    time-integrable, so this is NOT automatic; proved by a TIME-WEIGHTED A^σ restart fixed-point on
    X_{σ,β,T}={w: sup_s s^β‖w(s)‖_{A^σ}<∞}, β=(σ+1)/2<1, identified with the Layer-2 C⁰ solution by uniqueness.
  (Dep-2 COMPOSITION) Fourier-Wiener smooth composition Φ(u)∈A^r for κ≤u≤M — a SERIOUS project lemma
    (not generic Mathlib); split integer-power (algebra) vs real-power (needs positivity).
  (Dep-3 STRICT POSITIVITY) real powers need κ≤u (strict, not just u≥0) on positive-time slabs — a
    Harnack/strong-positivity dependency on the max-principle layer (Layer-4/5), NOT given by Layer-2 u≥0.
- MATHLIB GAPS: Gap A weighted-ℓ¹ convolution Banach algebra (essential, build from lp p=1 + Summable +
  tsum + Tonelli); Gap B Fourier-Wiener smooth composition; Gap C strict positive lower bound; Gap D the
  C⁰→A^σ seed. Underlying lp/Summable/Bochner-norm/interval-integral primitives confirmed present.
NET: Layer-3 is feasible but couples to a SEED sub-layer + a strong-positivity max-principle dependency —
the layer DAG is NOT purely bottom-up linear (Layer-3 ⟂ Layer-4 positivity). Build seed + algebra + (integer-power)
composition first; real-power composition + strict-positivity gate the full nonlinear bootstrap.

### R-Layer2 — LAYER 2 (C⁰ MILD LOCAL EXISTENCE) DESIGNED (ChatGPT, Xiang-rescued paste) — full transcript docs/layer2-mild-existence-transcript.md
Layer 2 = a TRUNCATED C⁰ mild fixed-point engine on C([0,T];C⁰([0,1])); transport −χ∂xq enters as
−χ∫∂xE(t−τ)q(u) (derivative on the heat semigroup, flux only C⁰-bounded+Lipschitz). Closes LOCAL clamped
existence+uniqueness from Layer-1 + resolvent; does NOT discharge the full PDE alone. 36-lemma DAG pinned.
- FOUNDATION = CLAMP, not positivity: all real powers on clipC0 M u = min(M,max(0,u)); positivity/comparison
  is a LATER layer proving the clamp INACTIVE (recovers real powers). Mirrors the Paper-1 truncbox lesson.
- SPACES: C0=BoundedContinuousFunction I01 ℝ, Path T=BCF (IT T) C0; NEW P3Params (m α γ β χ c a b), not CMParams.
- Φ(U)(t)=E(t)u₀+∫E(t−τ)F_M+∫∂xE(t−τ)B_M; ball M=2(‖u₀‖+1); √T smallness from ∫(t−τ)^{-1/2}=2√t;
  ContractingWith (1/2) on the closed ball for explicit short T_*=min(T_map,T_ctr).
- DRIFT CAVEAT: literal +c·u_x is NOT compatible with the even-reflection Neumann kernel unless c=0; set c=0
  in the first production theorem, keep c optional with a warning (Shen's wave has c≠0 — Paper-3 bounded domain
  recommends c=0 first; c≠0↔classical advection needs a drift-Neumann/boundary lemma).
- NEW LAYER-1 DEPENDENCY (pin NOW): resolventGradC0 — ∂xR as a C0→C0 map with C⁰ operator-norm + Lipschitz.
  R1 only pinned R''=Rf−f and the resolvent; the GRADIENT C⁰ map is unpinned, and WITHOUT it the flux
  u^m·S(v)·vx is not even a closed C⁰ map → Layer-2 cannot start. Add to Layer-1 interface.
- MATHLIB GAPS: heatC0/heatGradC0 semigroup; ∫(t−τ)^{-1/2}=2√t + Bochner version; TIME-CONTINUITY of the
  weakly-singular Duhamel term (genuine gap, ParametricIntegral alone insufficient); BCF-valued Duhamel
  constructors; Duhamel splitting/concatenation; maximal-mild framework (use ℝ≥0∞ for Tmax); positivity for
  clamp removal; c≠0 Neumann compatibility. Present: ContractingWith, BCF completeness, interval-integral bounds.
- CONVERGENCE: closes local clamped existence; remaining deps to full PDE = (1) clamp removal via a
  positivity/max-principle layer, (2) global a-priori C⁰ bound (energy/Moser) to push Tmax=∞.
CROSS-LAYER NET (Layer-2 ∪ Layer-3): both surface the SAME positivity dependency (strict 0<κ≤u on slabs) and
the SAME clamp/composition pattern — positivity (a max-principle layer) is the shared keystone gating both the
clamp-removal (Layer-2 → real PDE) and the real-power bootstrap (Layer-3). Build order: heat/resolvent (incl.
resolventGrad) → C⁰ clamped mild (Layer-2) → positivity/comparison → clamp removal + A^σ seed → A^r bootstrap (Layer-3).
