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
