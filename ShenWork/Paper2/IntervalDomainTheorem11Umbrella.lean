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
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne

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

/-- **Tightened umbrella theorem (no `hreach`, no `hrangeBounded`).**  Same as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach` except
that the `hrangeBounded` time-slice range-boundedness hypothesis is dropped:
it is discharged internally by `classicalSolution_u_range_bddAbove`, which
extracts conjunct (7) (closed-domain `C²` regularity of the lift on `Icc 0 1`)
of the classical-solution regularity bundle and converts continuity on the
compact `[0,1]` into boundedness of `|u t ·|` on the subtype range.

The remaining textbook-input hypotheses (`hlocal`, `hrealize`,
`hextend_of_not_finiteAlternative`, `hextend_of_not_mgeAlternative`,
`hposWit`, `hposLowerWit`) are identical to the `_no_hreach` variant. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded
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
  -- Internally discharge `hrangeBounded` from conjunct (7) of the classical
  -- regularity bundle on every interior time `t ∈ (0,T)`.
  have hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
    intro _u₀ _hu₀ T _hT u v hsol _htrace t ht_pos ht_T
    exact classicalSolution_u_range_bddAbove hsol ⟨ht_pos, ht_T⟩
  -- Route through the existing `_no_hreach` umbrella with the derived
  -- `hrangeBounded` field.
  exact Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach
    p hχ ha hb hlocal hrealize hextend_of_not_finiteAlternative
    hextend_of_not_mgeAlternative hrangeBounded hposWit hposLowerWit

/-- **Bundled continuation data for the Paper 2 interval-domain umbrella.**

Packages the four textbook PDE continuation hypotheses (`local`, `realize`,
`extend_finite`, `extend_mge`) together with the two book-keeping
pass-throughs (`posWit`, `posLowerWit`) consumed by
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`
into a single record, for cleaner downstream composition.  The field shapes
mirror the umbrella signature verbatim. -/
structure IntervalDomainPaper2ContinuationData (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extend_finite :
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
            p u₀)
  extend_mge :
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
            p u₀)
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀
  posLowerWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainPosDatumLowerBound u₀

/-- **Bundled-input wrapper for the Paper 2 interval-domain umbrella.**

Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`,
but consuming the six textbook/pass-through hypotheses as a single
`IntervalDomainPaper2ContinuationData` record for cleaner composition. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_continuationData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hData : IntervalDomainPaper2ContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded
    p hχ ha hb hData.localExistence hData.realize hData.extend_finite
    hData.extend_mge hData.posWit hData.posLowerWit

/-! ## Refined umbrella: `extend_finite` eliminated

The next umbrella variant drops the `hextend_of_not_finiteAlternative` textbook
PDE-input field of the maximal-continuation interface entirely.  Its content
is internally redundant in the `1 ≤ p.m` regime (the only regime that drives
the global-existence path inside the corrected existential package), because:

* `MGeOneFiniteHorizonAlternative` is the unboundedness disjunct of
  `FiniteHorizonAlternative`, so `¬ Finite → ¬ MGeOne` (logical implication).
* In the negative-sensitivity regime `χ₀ ≤ 0, 0 < a, 0 < b`, the Lemma 3.1
  monotonicity + the initial sup-norm approach (proved unconditionally inside
  the repo by `initialSupNormApproach_intervalDomain` from bounded initial data)
  give an `IsPaper2BoundedBefore` sup-norm bound on the open `(0, T*)`.  The
  closed-domain spatial `C²` regularity (conjunct (7) of the classical
  regularity bundle, unconditionally available via
  `classicalSolution_u_range_bddAbove`) converts that sup-norm bound into a
  pointwise upper bound on `u t x` for `0 < t < T*` and every `x : Point`,
  which rules out `MGeOneFiniteHorizonAlternative T* u` directly via
  `not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore`.

So the maximal-continuation contradiction at the realized supremum `T*` only
ever needs `hextend_of_not_mgeAlternative`.  The full chain is bundled in
`reachableArbitrarilyLong_of_realize_extend_mge_in_negative_regime` and
`intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing_no_extend_finite`.

The remaining textbook PDE inputs (`hlocal`, `hrealize`,
`hextend_of_not_mgeAlternative`) are the three genuinely-analytic frontiers of
the standard maximal continuation theorem on the interval domain:

* `hlocal` — short-time classical existence (standard Picard);
* `hrealize` — realization of a classical solution at the finite supremum
  `sSup` of reachable horizons (compactness + Ascoli–Arzelà passage to limit);
* `hextend_of_not_mgeAlternative` — restart past `T*` from non-blow-up via
  local existence applied to the limit datum, together with overlap
  uniqueness/gluing to concatenate. -/

/-- **Tightened umbrella (no `hreach`, no `hrangeBounded`, no
`hextend_of_not_finiteAlternative`).**  Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`,
but the `hextend_of_not_finiteAlternative` textbook PDE-input is **eliminated**:
it is internally redundant in the `1 ≤ p.m` regime (see the rationale above
this declaration), being subsumed by Lemma 3.1 + initial-approach + conjunct
(7) of regularity, all unconditional inside the repo.

The remaining textbook PDE-input hypotheses are `hlocal`, `hrealize`,
`hextend_of_not_mgeAlternative` — exactly the three genuine analytic frontiers
of the standard maximal continuation theorem:
short-time existence, realization at `sSup`, and restart-past-`sSup`
in the non-blow-up regime. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite
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
  -- Bounded-initial from positive-admissibility.
  have hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  -- Per-branch gluing from regime + positive-datum lower-bound witness.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
      p hχ ha hb hposWit hposLowerWit
  -- Direct existential-global package via the new no-extend_finite assembler.
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p :=
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing_no_extend_finite
      p hχ ha hb hlocal hboundedInitial hrealize
      hextend_of_not_mgeAlternative hglue
  -- Route through the existing corrected-existence Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Bundled continuation data, `extend_finite` eliminated.**  Packages the
**three** genuine textbook PDE continuation hypotheses (`localExistence`,
`realize`, `extend_mge`) together with the two book-keeping pass-throughs
(`posWit`, `posLowerWit`) consumed by
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite`
into a single record.  Strictly fewer fields than
`IntervalDomainPaper2ContinuationData` (5 vs 6): `extend_finite` is dropped. -/
structure IntervalDomainPaper2ContinuationData_no_extend_finite
    (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extend_mge :
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
            p u₀)
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀
  posLowerWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainPosDatumLowerBound u₀

/-- **Bundled-input wrapper (no `extend_finite`).**  Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite`,
but consuming the **five** textbook/pass-through hypotheses as a single
`IntervalDomainPaper2ContinuationData_no_extend_finite` record.  One textbook
PDE input fewer than `Theorem_1_1_intervalDomain_via_regime_and_continuationData`. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_continuationData_no_extend_finite
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hData : IntervalDomainPaper2ContinuationData_no_extend_finite p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite
    p hχ ha hb hData.localExistence hData.realize hData.extend_mge
    hData.posWit hData.posLowerWit

/-- Forgetful map: every old continuation-data bundle (6 fields) gives rise to
the new leaner bundle (5 fields) by simply dropping `extend_finite`.  This
witnesses that the new umbrella consumes a strict subset of the old textbook
PDE-input surface. -/
def IntervalDomainPaper2ContinuationData.toNoExtendFinite
    {p : CM2Params} (h : IntervalDomainPaper2ContinuationData p) :
    IntervalDomainPaper2ContinuationData_no_extend_finite p :=
  { localExistence := h.localExistence
    realize := h.realize
    extend_mge := h.extend_mge
    posWit := h.posWit
    posLowerWit := h.posLowerWit }

/-! ## Paper 2-aligned umbrella (γ ≥ 1)

Paper 2 (Chen-Ruau-Shen) only addresses the case `γ ≥ 1` (confirmed with
author Liang on 2026-05-27).  In this regime the local Lipschitz constant
of the source `x ↦ x^γ` on `[0, M]` is the well-defined `L_γ = γ·M^{γ-1}`,
**without** any positive lower bound `δ > 0`, so the gluing closure
`GlobalSolutionGluingFromReachability_of_regime_gammaGeOne` consumes only
the **per-pair `PositiveInitialDatum`** book-keeping pass-through and
drops the `IntervalDomainPosDatumLowerBound` pass-through entirely.

The variant below mirrors
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`
field-by-field except:

* it carries an extra `1 ≤ p.γ` hypothesis (Paper 2's actual regime);
* it routes through the γ≥1 gluing closure instead of the general-γ one;
* it has **no** `hposLowerWit` field. -/

/-- **Paper 2-aligned umbrella theorem (γ≥1).**  In the negative-sensitivity
regime `χ₀ ≤ 0, 0 < a, 0 < b` together with `1 ≤ p.γ` — i.e. exactly the
case addressed by Paper 2 (Chen-Ruau-Shen, confirmed with author Liang
2026-05-27) — Paper 2 Theorem 1.1 on the interval domain follows from
the textbook PDE continuation inputs (`hlocal`, `hrealize`,
`hextend_of_not_finiteAlternative`, `hextend_of_not_mgeAlternative`) and
the **single** book-keeping pass-through `hposWit` (per-pair positive
initial datum of any classical-solution pair).  **No
`IntervalDomainPosDatumLowerBound` is required**: the γ≥1 gluing chain
discharges its δ-free analogue uniformly via `L_γ = γ·M^{γ-1}`.

The spatial range-boundedness (`hrangeBounded`) is internally discharged
from conjunct (7) of the classical-solution regularity bundle, exactly
as in `Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
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
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Step 1. Bounded-initial from positive-admissibility.
  have hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  -- Step 2. Internal `hrangeBounded` from conjunct (7) of the classical
  --         regularity bundle.
  have hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
    intro _u₀ _hu₀ T _hT u v hsol _htrace t ht_pos ht_T
    exact classicalSolution_u_range_bddAbove hsol ⟨ht_pos, ht_T⟩
  -- Step 3. Sup-norm-controls-pointwise per branch.
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
  -- Step 4. **Paper 2's actual gluing chain**: γ≥1 closure, NO `posLowerWit`.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regime_gammaGeOne
      p hχ ha hb hγ_ge_one hposWit
  -- Step 5. Existential-global package via the nonminimal continuation+gluing assembler.
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p :=
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing
      p hχ ha hb hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      hsupControls hglue
  -- Step 6. Route through the existing Moser-closure Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Paper 2-aligned bundled continuation data (γ ≥ 1).**

Packages the four textbook PDE continuation hypotheses (`localExistence`,
`realize`, `extend_finite`, `extend_mge`) together with the **single**
book-keeping pass-through `posWit` consumed by
`Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData`.

This is the Paper 2 (Chen-Ruau-Shen)-aligned analogue of
`IntervalDomainPaper2ContinuationData`: the `posLowerWit` field is dropped
because Paper 2 only addresses the γ ≥ 1 regime (confirmed with author
Liang 2026-05-27), and the γ≥1 gluing closure does not need any positive
lower bound. -/
structure IntervalDomainPaper2ContinuationDataGammaGeOne (p : CM2Params) :
    Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extend_finite :
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
            p u₀)
  extend_mge :
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
            p u₀)
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- **Paper 2-aligned bundled-input wrapper (γ ≥ 1).**

Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData`,
but consuming the five textbook/pass-through hypotheses as a single
`IntervalDomainPaper2ContinuationDataGammaGeOne` record. -/
theorem Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2ContinuationDataGammaGeOne p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData
    p hχ ha hb hγ_ge_one hData.localExistence hData.realize
    hData.extend_finite hData.extend_mge hData.posWit

end

end ShenWork.Paper2

-- Axiom audit: the umbrella theorems depend only on `propext`, `Classical.choice`,
-- and `Quot.sound` (the standard Lean foundational axioms used throughout the
-- repo); no `sorryAx`, no custom `axiom`.
-- #print axioms ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound
-- #print axioms
--   ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach
-- #print axioms
--   ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded

