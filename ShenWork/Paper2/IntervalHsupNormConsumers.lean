/-
  HsupNorm refactor — CONSUMER CATALOGUE.

  Companion to `IntervalHsupNormProof.lean` / `IntervalHsupNormHeat.lean`.
  Those files establish that the sup-norm conjuncts of
  `intervalDomainClassicalRegularity` are over-strong:

    * conjunct (1) `supnormLogistic` and conjunct (2) `supnormZero` are
      `∀ q : CM2Params, …`-quantified, but the body
      `IntervalDomainSupNormDerivativeNonposOn u …` does NOT depend on
      `q`.  So the ∀q makes them equivalent to the UNCONDITIONAL
      differentiable certificate — which is false (a flat datum
      `u₀≡ε < (a/b)^{1/α}` has strictly increasing sup-norm), and even the
      true above-capacity content is only *monotone*, not *differentiable*.

  This file is the refactor's working map: it lists EVERY site that
  consumes `.regularity.1` (supnormLogistic) or `.regularity.2.1`
  (supnormZero) on the interval domain, classifies each as a genuine
  downstream use vs. mere transfer-plumbing, and records what each
  actually needs.

  ## Bottom line for the refactor

  The ONLY genuine downstream consumer is `Lemma_3_1_intervalDomain`
  (Statements.lean), and it immediately collapses the differentiable
  certificate into **monotonicity** via
  `SupNormAntitoneData.supNorm_nonincreasing_of_deriv_nonpos`.  So the
  faithful carrier is the MONOTONE predicate
  `Paper2.SupNormNonincreasingOn` (no differentiability), gated by the
  GIVEN `p` (not `∀ q`).  Every other site merely transfers the conjunct
  and would transfer monotonicity equally well.

  No `sorry`/`admit`/custom `axiom` (documentation + one summary lemma).
-/
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain (intervalDomain intervalDomainSupNorm)

noncomputable section

namespace ShenWork.Paper2.HsupNormConsumers

/-! ## A. Genuine DOWNSTREAM consumer (real mathematical use)

### A1. `Lemma_3_1_intervalDomain`  (Paper2/Statements.lean ~L3627)

  Part 1 (above carrying capacity), uses `hreg.1 p hχ ha hb t₀ …`:
    extracts `IntervalDomainSupNormDerivativeNonposOn u (Ioc 0 t₀)`,
    reads off `.continuousOn / .differentiableOn / .deriv_nonpos`, and
    feeds them to
      `SupNormAntitoneData.supNorm_nonincreasing_of_deriv_nonpos`
    to conclude `‖u(t₂)‖ ≤ ‖u(t₁)‖` (MONOTONICITY) on `Ioc 0 t₀`.

  Part 2 (`a = b = 0`), uses `hreg.2.1 p hχ ha hb`: identical pattern on
    `Ioo 0 T`.

  WHAT IT ACTUALLY NEEDS:  sup-norm MONOTONICITY only — i.e.
    `SupNormNonincreasingOn intervalDomain u (Ioc 0 t₀)`  [part 1]
    `SupNormNonincreasingOn intervalDomain u (Ioo 0 T)`   [part 2],
  for the GIVEN `p`.  The differentiable certificate is a throwaway
  intermediate.  → Carry `SupNormNonincreasingOn` directly.

(The `∀ q` in the current conjuncts is spurious here: `Lemma_3_1`
instantiates `q := p`, the given parameter.  No site needs `q ≠ p`.)
-/

/-- The refactor's carrier target, made explicit: what `Lemma_3_1`'s two
branches actually consume is monotonicity of the sup-norm on the relevant
sub-interval, for the given `p`.  This is `Paper2.SupNormNonincreasingOn`,
which (unlike the differentiable certificate) is TRUE for both the
above-capacity logistic regime and the `a=b=0` heat regime. -/
def Lemma31CarrierTarget
    (u : ℝ → intervalDomain.Point → ℝ) (I : Set ℝ) : Prop :=
  SupNormNonincreasingOn intervalDomain u I

/-! ## B. TRANSFER plumbing (consume the conjunct only to re-emit it)

These sites do NOT use the sup-norm property for downstream math; they
transport it from one solution/horizon to another while rebuilding a
`intervalDomainClassicalRegularity`.  They would transport
`SupNormNonincreasingOn` with the same one-line moves.

### B1. `intervalDomainClassicalRegularity_mono`  (Existence.lean ~L2911)
  `hreg.1 p … (lt_of_lt_of_le ht₀T hTL) hsup`   — restrict horizon, cond.1
  `intervalDomainSupNormDerivativeNonposOn_mono (hreg.2.1 p …) …` — cond.2
  NEEDS: restriction of the carried property to a shorter horizon
  (`SupNormNonincreasingOn` restricts identically: a sub-interval of a
  nonincreasing set is nonincreasing).

### B2. `intervalDomainClassicalRegularity_congr_Ioo`  (Existence.lean ~L4895)
  `hreg.1 q …` + `intervalDomainSupNormDerivativeNonposOn_congr_of_eqOn`
  `hreg.2.1 q …` + same congr lemma
  NEEDS: transfer along a pointwise-equal trajectory (`u t = U t` on the
  slab).  `SupNormNonincreasingOn` transfers via `supNorm`-congruence on
  the eqOn set (`SupNormNonincreasingOn.of_forall_eq`-style).

### B3. `localExistence` glued-solution producer  (Existence.lean ~L5615–5735)
  `dpick.sol.regularity.1 q hqχ hqa hqb t₀ …`   (cond.1, glued ← dpick)
  `dpick.sol.regularity.2.1 q hqχ hqa hqb`       (cond.2, glued ← dpick)
  both followed by `…congr_of_eqOn` against `boundedReachableGlued`.
  NEEDS: transfer of the carried property from the chosen reachable
  solution `dpick.sol` to the glued solution along their slab agreement —
  again a `supNorm`-congruence move on monotonicity.

## C. NON-interval-domain hits (NOT in scope — different BoundedDomainData)

  These access a `.regularity.1` of a DIFFERENT domain whose
  `classicalRegularity` is a plain `Differentiable`/other predicate, not
  the interval sup-norm conjunct:
    * Paper2/Statements.lean L6209   (unit-point `()`-domain: `.regularity.1`
      is `Differentiable ℝ (fun t => u t ())`)
    * Paper2/UnitPointLogisticBridge.lean L197
    * Paper3/UnitPointLogisticBridge.lean L528
  Ignore for the interval refactor.

## D. PRODUCER of the (false) conjunct

  `RegularityFrontierWiring.gradientMildClassicalRegularityFrontierData_of_spectral`
  (IntervalRegularityFrontierWiring.lean) sets
    `supnormLogistic := … HsupNorm`
    `supnormZero     := fun _q _ _ _ => HsupNorm`
  from the ledger field `HsupNorm` — the over-strong differentiable
  certificate.  This is the field to REPLACE: emit two regime-gated
  `SupNormNonincreasingOn` facts (above-capacity logistic decay; a=b=0
  heat sub-Markov) for the GIVEN `p`, instead of the ∀q differentiable
  certificate.

## E. Refactor recipe (summary)

  1. In `IntervalDomain.intervalDomainClassicalRegularity`, replace
     conjuncts (1),(2) bodies `IntervalDomainSupNormDerivativeNonposOn u …`
     with `SupNormNonincreasingOn intervalDomain u …`, and drop the
     spurious `∀ q` (use the solution's own `p`, threaded through
     `IsPaper2ClassicalSolution`).
  2. Update the three transfer sites (B1–B3) to the monotone restriction/
     congruence lemmas (one-liners).
  3. Update `Lemma_3_1_intervalDomain` (A1): it now reads the carried
     monotonicity directly, dropping the
     `SupNormAntitoneData.supNorm_nonincreasing_of_deriv_nonpos` step.
  4. Replace the producer (D) with the two true regime-gated monotone
     facts; `IntervalHsupNormHeat.heat_supNorm_le_initial` is the heat
     sub-Markov input.
-/

/-- Sanity hook: the carrier target is definitionally the existing
monotone predicate, so the refactor introduces no new notion. -/
theorem carrierTarget_eq
    (u : ℝ → intervalDomain.Point → ℝ) (I : Set ℝ) :
    Lemma31CarrierTarget u I = SupNormNonincreasingOn intervalDomain u I :=
  rfl

end ShenWork.Paper2.HsupNormConsumers
