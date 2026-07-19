import ShenWork.PDE.P3MoserAgmonDirectRoute
import ShenWork.Paper2.IntervalDomainLem26PhaseA

/-!
# Lemma 2.6 for concrete interval-domain solutions, without `hdiss`

`Lemma_2_6` (Paper2/Statements.lean:2276) is stated abstractly, over an
arbitrary `BoundedDomainData` and an arbitrary `u` satisfying only the two
bootstrap hypotheses.  Two statement-level defects were identified while
auditing the committed route:

1. The pointwise dissipation-drop interface `MoserDissipationDropBefore`
   (consumed by `moser_step_of_energy_dissipation_relative_interpolation`) is
   over-quantified: it asks that EVERY quadruple `(A,B,K,L)` making the energy
   inequality true also forces `0 ≤ (1/p)Y_p' + B Y_p`.  Taking a spatially
   constant decaying profile with `A = B = K = L = 0` makes the antecedent
   true and the conclusion false, so no PDE can supply it.  Restricting to the
   physical constants does not repair it: extracting the pointwise gradient
   bound from the energy inequality needs a lower bound on `Y_p'`, which needs
   an upper bound on the dissipation — the estimate being derived.
2. Even with a sound dissipation interface, the abstract conclusion
   `LpPowerBoundedBefore` demands control uniform down to `t = 0` at EVERY
   exponent, while the hypotheses supply an initial `L^{p0}` bound only.  The
   honest conclusion of a Moser/Agmon bootstrap is control on every terminal
   window `[s, T)` with `s > 0`.

Both are avoided by the repository's Agmon absorption route, which is already
`hdiss`-free.  This file records that the practical content of Lemma 2.6 — the
statement the paper actually uses on solutions — is discharged unconditionally
for interval-domain classical solutions.
-/

open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

noncomputable section

namespace ShenWork.Paper2

/-- Lemma 2.6 for concrete interval-domain classical solutions: every finite
exponent is bounded on every terminal window, from the bootstrap and energy
hypotheses ALONE — no dissipation-drop frontier. -/
theorem Lemma_2_6_intervalDomain_concrete_terminal
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u
      (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0) :
    ∀ pExp > 1, LpPowerBoundedOnTerminalWindow intervalDomain pExp T u :=
  intervalDomain_abstractLpBootstrap_terminal hsol hboot henergy

/-- The abstract `LpPowerBoundedBefore` conclusion is strictly stronger than
the terminal-window one: a bound before `T` restricts to every terminal
window, but not conversely (the terminal form says nothing as `s ↓ 0`). -/
theorem lpPowerBoundedOnTerminalWindow_of_before
    {pExp T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (h : LpPowerBoundedBefore intervalDomain pExp T u) :
    LpPowerBoundedOnTerminalWindow intervalDomain pExp T u :=
  lpPowerBoundedOnTerminalWindow_of_boundedBefore h

section AxiomAudit

#print axioms Lemma_2_6_intervalDomain_concrete_terminal
#print axioms lpPowerBoundedOnTerminalWindow_of_before

end AxiomAudit

end ShenWork.Paper2
