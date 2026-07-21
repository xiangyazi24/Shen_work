To: lkong9@uis.edu
Subject: Shen chemotaxis stability — Lean formalization status and an open threshold question

Hi Liang,

A status update on the Lean 4 formalization of Shen's 1D chemotaxis traveling-wave
stability paper (arXiv:2605.04401, Theorem 1.2), plus one genuinely open question
I'd value your take on.

Scale
- ~801,000 lines of Lean 4 across 2,119 files, roughly 5,550 theorems.
- 0 sorry, 0 axiom — every result closes on only the three standard Lean foundations
  (propext, Classical.choice, Quot.sound). Scope is the 1D system.

Headline theorems proven
- Theorem 1.2 (asymptotic stability of the traveling wave). The global Cauchy solution
  converges to the wave in the co-moving frame, in two senses simultaneously: weighted
  L² (CoMovingWeightedL2Convergence) and uniform in the moving frame
  (UniformMovingFrameConvergence: ∀ε>0 ∃T, ∀t≥T ∀x, |u(t,x) − U(x−ct)| < ε). Proved for
  χ < 0, χ = 0, and 0 < χ < 1/2 (sharp version up to chiStar), in both the "natural" and
  the paper's phase spaces. Crucially it is proved NON-VACUOUSLY: there is a concrete
  instance (χ > 0, wave speed c > 2, a genuine Schauder-constructed profile U,V) so the
  standing hypotheses are met, not merely assumed.
- Theorem 1.3 (uniqueness of the traveling wave) for positive sensitivity below the
  threshold, and on the union of the proved sensitivity ranges.
- Global existence: an explicit global Cauchy solution from the initial datum
  (IsGlobalCauchySolutionFrom), built as a glued BUC mild-solution orbit.

The far-left piece (relevant to the open question below)
- The far-left equilibrium convergence — the co-moving solution approaching u ≡ 1
  uniformly on far-left half-lines — is fully proved across all three sensitivity
  regimes; the positive-χ case reaches the sharp threshold
  chiStar = min(1, (2m+2γ)/(m²+m+2γ)).
- Architecture: a buffered half-line "KPP-rectangle successor" — a persistent lower-
  barrier plateau, then a KPP subsolution that lifts the far-left floor to 1, advanced
  rectangle by rectangle. The positive-χ case mirrors the χ ≤ 0 proof, with the
  chemotaxis defect controlled through the resolver (frozen-elliptic) term.

The open question (where the paper's threshold is not the true one)
The chemotaxis sensitivity χ is the hard parameter. The paper's sufficient threshold
is χ*; the formalization reaches chiStar. But the linear (Turing) analysis of the
far-left plateau — dispersion σ(k) = −k² + χγ·k²/(1+k²) − α — gives an instability
threshold of (1+√α)², which is 4 at m = γ = α = 1, well above chiStar (~1). So there
is a real gap between what the current rectangle/comparison machinery can prove and
where the plateau is actually (linearly) stable.

Two concrete obstructions to closing that gap, if you have thoughts:
1. The comparison currently bounds the resolver aggregation defect V − u^γ crudely (by
   the band width M^γ − x^γ), which caps the provable threshold at chiStar. A genuinely
   sharper, time-dependent estimate — ideally a c-dependent bound of the form
   |V − u| ≲ χB(B−A)/(c − χ(B−A)) on each evolving slice — would give the √(c/2)
   scaling. We have a steady-state crest version, but it assumes no overshoot (b ≤ 1),
   whereas the restarted Cauchy slices have M > 1. This really wants a parabolic
   Bernstein/gradient estimate for the time-dependent orbit, which is the crux.
2. The comparison regime is structurally built on χ < 1 (the ceiling regime and a
   target-monotonicity step both use 1 − χ > 0). Reaching past 1 (needed at m = γ = 1,
   where chiStar = 1) means reworking those too.

And a caveat worth stating plainly: (1+√α)² is the linear threshold. That it is the
exact nonlinear far-left threshold is, so far, numerical evidence rather than a theorem.

If any of this is close to your interests — especially the parabolic gradient estimate
in obstruction (1) — I'd be glad to talk it through. Happy to share the repository and
a short technical note with the precise lemma statements.

Best,
Xiang
