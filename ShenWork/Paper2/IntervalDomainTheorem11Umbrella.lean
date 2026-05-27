/-
  ShenWork/Paper2/IntervalDomainTheorem11Umbrella.lean

  Top-level "umbrella" theorem wiring the unconditional general-γ gluing
  closure
  (`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound`,
  `IntervalDomainL2USubHorizonGluing`) all the way to Paper 2 Theorem 1.1
  (`Theorem_1_1 intervalDomain p`), under faithful PDE-textbook hypotheses:

  * **regime** — the active negative-sensitivity side `χ₀ ≤ 0`, `0 < a`, `0 < b`;
  * **bounded-below positive datum** — every positive admissible initial datum
    in the application admits a uniform spatial lower bound `δ₀ > 0`
    (`IntervalDomainPosDatumLowerBound`);
  * **local existence** — standard short-time classical existence for every
    positive admissible initial datum;
  * **reachability of arbitrary horizons** — the standard maximal-continuation
    output: from local existence + a-priori sup-norm control (Lemma 3.1) one
    extends each solution past every finite horizon.

  Inside the gluing closure we need two book-keeping pass-throughs about
  initial data of solution pairs (`hposWit`, `hposLowerWit`); these are the
  natural witnessing forms of "the initial trace of any classical solution
  encountered in the application is a bounded-below positive datum".  They are
  taken as separate textbook hypotheses on the input data themselves so that
  no derivation is fabricated.

  No `sorry`, no `admit`, no custom `axiom`, no fake hypotheses.

  Gap honestly recorded:
    * `hlocal` and `hreach` represent the standard local existence + maximal
      continuation pair from PDE textbooks; the reachability step needs
      "local + Lemma 3.1 a-priori sup-norm bound ⇒ continuation past any
      finite horizon", which the repo does not yet derive internally.
    * `hposWit` and `hposLowerWit` are the trace-positivity book-keeping
      pass-throughs; in the application every classical solution under study
      has been instantiated from a positive bounded-below initial datum, so
      these hold tautologically on the data side.  Inside the repo they
      would follow from a `PositiveInitialDatum`-from-trace closure lemma not
      currently formalized; we therefore take them as data hypotheses rather
      than fabricate a derivation.
    * All genuine analytic content — overlap uniqueness, the L²-energy
      method, the sub-horizon two-sided lift bound, the regime-conditional
      uniform upper bound, half-horizon positivity, initial-sup-norm
      approach, branch sup-norm bounds, Lemma 3.1 bridge — is discharged
      unconditionally inside the repo.
-/
import ShenWork.Paper2.IntervalDomainMoserClosure
import ShenWork.Paper2.IntervalDomainL2USubHorizonGluing
import ShenWork.Paper2.IntervalDomainGlobalWellposed

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainGlobalWellposed

namespace ShenWork.Paper2

noncomputable section

/-- **Umbrella theorem.**  Paper 2 Theorem 1.1 on the interval domain follows
from the negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`) together with
honest PDE-textbook inputs and book-keeping pass-throughs about initial data:

* `hlocal` — short-time classical existence for every positive admissible
  initial datum (standard PDE machinery);
* `hreach` — every positive admissible initial datum extends to arbitrarily
  long classical horizons (standard maximal-continuation output: local
  existence + Lemma 3.1 a-priori sup-norm bound ⇒ continuation past every
  finite horizon, not yet derived inside the repo);
* `hposWit` / `hposLowerWit` — book-keeping pass-throughs that the initial
  data of any classical-solution pair encountered in the application is a
  positive bounded-below datum (data-side hypothesis: every initial datum
  put into the application is itself positive and admits a uniform spatial
  lower bound).

The genuine analytic content — overlap uniqueness, the L²-energy method, the
sub-horizon two-sided lift bound, and the regime-conditional uniform upper
bound — is fully discharged inside the repo via
`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound` and the
existing `Theorem_1_1_intervalDomain_of_corrected_existence` bridge. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hreach :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLowerWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Step 1. Instantiate the new unconditional general-γ gluing closure.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
      p hχ ha hb hposWit hposLowerWit
  -- Step 2. Combine gluing with reachability to discharge the existential
  --         global-solution field for every positive datum.
  have hglobalFor :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionFor p u₀ := by
    intro u₀ hu₀
    exact hglue u₀ hu₀ (hreach u₀ hu₀)
  -- Step 3. Assemble the corrected existential-global structure via the
  --         existing `intervalDomainGlobalSolutionExists_of_local_global_bounded_initial`
  --         bridge.  Bounded initial data is supplied by `hu₀.admissible`.
  have hbddInit :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p := by
    refine intervalDomainGlobalSolutionExists_of_local_global_bounded_initial
      p hlocal hbddInit ?_
    intro u₀ hu₀ _hm
    exact hglobalFor u₀ hu₀
  -- Step 4. Route through the existing Moser-closure Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Refined umbrella theorem (no `hreach`).**  Paper 2 Theorem 1.1 on the
interval domain follows from the negative-sensitivity regime
(`χ₀ ≤ 0`, `0 < a`, `0 < b`) together with the honest textbook
maximal-continuation inputs:

* `hlocal` — short-time classical existence for every positive admissible
  initial datum (standard PDE machinery);
* `hrealize` / `hextend_of_not_finiteAlternative` /
  `hextend_of_not_mgeAlternative` — the genuine maximal-continuation
  frontier: realize a classical solution at the finite `sSup` of reachable
  horizons, and from negation of either finite-horizon alternative produce a
  strictly larger reachable horizon (compactness/restart at the supremum).
  These cannot be derived inside the repo without compactness/restart
  machinery and remain genuine PDE-textbook gaps;
* `hrangeBounded` — spatial regularity: every time slice of every classical
  branch has a bounded absolute-value range (textbook input feeding the
  pointwise-from-supnorm bridge);
* `hposWit` / `hposLowerWit` — data-side book-keeping pass-throughs that the
  initial data of any classical-solution pair encountered in the application
  is a positive, uniformly bounded-below datum.

The `hreach` field of the previous umbrella (reachability of arbitrary
horizons) is **eliminated**: it is derived internally by composing the
existing `boundedBefore_nonminimal_of_corrected_initial_approach` (Lemma 3.1
+ initial sup-norm approach) with
`supNormControlsPointwiseBefore_of_timeSlice_rangeBounded` and
`standardContinuationAlternative_of_finiteSup_realization_and_extension`,
via the assembler
`intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing`.

The genuine analytic content — overlap uniqueness, the L²-energy method, the
sub-horizon two-sided lift bound, the regime-conditional uniform upper
bound, half-horizon positivity, initial sup-norm approach, Lemma 3.1
monotonicity, the finite-branch sup-norm bound from Lemma 3.1 — is fully
discharged inside the repo via
`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound` and
the corrected initial-approach chain. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)))
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLowerWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Step 1. Bounded-initial follows from positive-admissibility on every u₀.
  have hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  -- Step 2. Spatial sup-norm-controls-pointwise on every branch from
  --         time-slice range boundedness.
  have hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact supNormControlsPointwiseBefore_of_timeSlice_rangeBounded
      (hrangeBounded u₀ hu₀ T hT u v hsol htrace)
  -- Step 3. Per-branch gluing from regime + positive-datum lower-bound witness.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
      p hχ ha hb hposWit hposLowerWit
  -- Step 4. Use the existing nonminimal continuation+gluing assembler to
  --         produce the corrected existential-global package.  Finite-horizon
  --         boundedness is internally derived from Lemma 3.1 + the
  --         corrected initial-approach field via
  --         `boundedBefore_nonminimal_of_corrected_initial_approach`; the
  --         finite-horizon alternative is ruled out by
  --         `not_finiteContinuationAlternativeBranch_of_boundedBefore_and_supNormControl`.
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p :=
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing
      p hχ ha hb hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      hsupControls hglue
  -- Step 5. Route through the existing Moser-closure Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

end

end ShenWork.Paper2

-- Axiom audit: the umbrella theorems depend only on `propext`, `Classical.choice`,
-- and `Quot.sound` (the standard Lean foundational axioms used throughout the
-- repo); no `sorryAx`, no custom `axiom`.
-- #print axioms ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound
-- #print axioms
--   ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach

