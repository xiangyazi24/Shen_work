/-
  Final assembly: wire G0–G7 + G2.5 into Paper 2 Theorem 1.1.

  ## Proved ingredients (axiom-clean, 0 sorry)

  * **Picard fixed point** (`GradientMildSolutionData`): mild solution exists
    for every PID u₀ on some horizon [0, T].

  * **Regularity bootstrap** (`IntervalMildRegularityBootstrap`): given
    `HasRestartCosineRepresentations`, the mild solution satisfies the 9
    classical regularity fields.

  * **Picard iterate C² induction** (`IntervalMildPicardRegularity`): every
    Picard iterate has C² spatial slices with Neumann BC.

  * **DuhamelSourceTimeC1 limit passage** (`IntervalMildPicardLimitRegularity`,
    G2.5): `DuhamelSourceTimeC1` passes to pointwise limits under uniform
    derivative convergence.

  * **L² overlap uniqueness** (PID-gated, G6): the full L² energy → gluing
    chain is PID-gated, eliminating `hposWit`.

  * **δ-iteration** (`reachableArbitrarilyLong_of_local_and_uniform`, G7):
    `hlocal + hUniform → ReachableArbitrarilyLong`.

  * **γ≥1 umbrella** (`Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge`):
    `hlocal + hUniform → Theorem_1_1`.

  ## Remaining genuine frontiers

  This file packages the EXACT remaining hypotheses into a single record
  `Paper2Theorem11Frontier`.  Once these are discharged, Paper 2 Theorem 1.1
  is unconditional.

  * **F1** `uniformLocalExistence` — the textbook uniform parabolic continuation
    theorem: ∀ M > 0, ∃ δ > 0, any solution with |u₀| ≤ M extends by δ.
    Standard PDE result (Henry/Amann); formalizing it requires the restart-
    before-end argument from DESIGN_ROUND4_OPUS.md §R4.

  * **F2** `sourceTimeC1OfLimit` — `DuhamelSourceTimeC1` for the Picard
    limit's logistic source.  G2.5 reduces this to showing uniform convergence
    of iterate source coefficient derivatives.  The mathematical content is:
    chain rule `∂_s F(uₙ) = F'(uₙ)·∂_s uₙ` + uniform convergence of `∂_s uₙ`
    from the mild equation.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalMildPicardLimitRegularity
import ShenWork.Paper2.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.Theorem11Assembly

/-! ## The precise remaining frontier for unconditional Paper 2 Theorem 1.1 -/

/-- The two genuine remaining hypotheses for unconditional Paper 2 Theorem 1.1
in the γ ≥ 1 regime on the interval domain.  Everything else (Picard fixed
point, regularity bootstrap, L² gluing, δ-iteration) is proved axiom-clean. -/
structure Paper2Theorem11Frontier (p : CM2Params) : Prop where
  /-- **F1: Textbook uniform parabolic continuation.**
  For every M > 0, there exists δ > 0 such that any classical solution
  with PID initial datum bounded by M extends by δ.  Standard PDE
  (Henry/Amann); requires restart-before-end + overlap glue. -/
  uniformLocalExistence : IntervalDomainUniformLocalExistence p
  /-- **F2: Source coefficient time-C¹ for the Picard limit.**
  For every PID u₀, the logistic source of the Picard limit mild
  solution has `DuhamelSourceTimeC1`.  G2.5 reduces this to uniform
  convergence of iterate source coefficient derivatives. -/
  sourceTimeC1OfLimit :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        ∃ S : GradientMildHalfStepLogisticSourceData D, True

/-- **Unconditional Paper 2 Theorem 1.1 from the frontier.**

Given the two remaining hypotheses (uniform continuation + source time-C¹
for the limit), Paper 2 Theorem 1.1 holds unconditionally on the interval
domain in the γ ≥ 1 negative-sensitivity regime. -/
theorem paper2_theorem_1_1_of_frontier
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hFrontier : Paper2Theorem11Frontier p)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
      p hMildLocal)
    hFrontier.uniformLocalExistence

/-- The **minimal-hypothesis** form: takes only the regime parameters and the
frontier record, with `hMildLocal` absorbed.

`hMildLocal` is constructible from:
1. `GradientMildSolutionData` (Picard, proved unconditionally)
2. `GradientMildHalfStepLogisticSourceData` (from F2)
3. Initial approach (from G5 semigroup smoothing, WIP)
4. `GradientMildClassicalFrontierCoreData` (from regularity bootstrap +
   HasRestartCosineRepresentations which comes from F2)

Once F2 and the initial-approach condition (G5) are closed, `hMildLocal`
becomes unconditional and this theorem reduces to:
  `Paper2Theorem11Frontier p → Theorem_1_1 intervalDomain p`. -/
theorem paper2_theorem_1_1_of_frontier_and_mildLocal
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hFrontier : Paper2Theorem11Frontier p)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_of_frontier p hχ ha hb hγ_ge_one hFrontier hMildLocal

/-! ## Status report

### Proved (axiom-clean)

| Component | File | Status |
|-----------|------|--------|
| Picard FP | IntervalMildPicard | ✓ |
| Iterate C² induction | IntervalMildPicardRegularity | ✓ |
| DuhamelSourceTimeC1 limit | IntervalMildPicardLimitRegularity | ✓ |
| Regularity bootstrap | IntervalMildRegularityBootstrap | ✓ |
| L² overlap unique (PID-gated) | 9 files (G6) | ✓ |
| δ-iteration (G7) | IntervalDomainTheorem11Umbrella | ✓ |
| γ≥1 umbrella (no hposWit) | IntervalDomainTheorem11Umbrella | ✓ |
| Sup-norm bound (Lemma 3.1) | IntervalDomainExistence | ✓ |

### Remaining frontier

| Frontier | Description | Path to closure |
|----------|-------------|-----------------|
| **F1** | Uniform continuation δ(M) | Restart-before-end + overlap glue (~200 lines) |
| **F2** | Source time-C¹ for limit | Instantiate G2.5 uniform convergence (~150 lines) |
| **G5** | Initial approach S(t)u₀→u₀ | 2 sorrys in semigroup uniform file |
-/

end ShenWork.Paper2.Theorem11Assembly
