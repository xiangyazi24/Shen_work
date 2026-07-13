ANSWER Q3619 bccafe31

# Q3619: Task154 route audit after `bFormPositiveLocalFrontier_of_localHyp`

Repo point audited: `main` at `7eb94305`.

Files read:

- `ShenWork/Paper2/IntervalBFormPositiveDatumLocalExistence.lean`
- `ShenWork/Paper2/IntervalBFormPositiveDatumLocalExistenceSq.lean`
- `ShenWork/Paper2/IntervalBFormPositiveDatumLocalExistenceSqRegular.lean`
- `ShenWork/Paper2/IntervalBFormPositiveDatumLocalExistenceSqDeepest.lean`
- `ShenWork/Paper2/IntervalBFormPositiveDatumQuantWiring.lean`
- `ShenWork/Paper2/IntervalBFormPositiveDatumNegPartFrontier.lean`
- also checked the downstream Task154-style wrapper already present in `ShenWork/Paper2/IntervalDomainBoundaryChemDivLimit.lean`.

## Verdict: choose **B** as the next best Lean target

The best next non-circular Lean target is **B: define/prove a paper-positive negative-part frontier**, then wire the squared-barrier packages into that frontier using their actual datum class.

Reason: after `bFormPositiveLocalFrontier_of_localHyp`, the all-positive negative-part frontier is already produced from

```lean
PositiveDatumBFormLocalHyp p
```

via

```lean
ShenWork.Paper2.BFormPositiveDatumLocal.bFormPositiveLocalFrontier_of_localHyp
```

in `IntervalBFormPositiveDatumLocalExistence.lean`.  The new downstream headline in `IntervalDomainBoundaryChemDivLimit.lean` already exploits this to prove

```lean
ShenWork.Paper2.BFormPositiveDatumLocal
  .paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_of_localHyp
```

from `PositiveDatumBFormLocalHyp p` and `ConeQuantBridge.PicardLimitRestartFrontier p`.

That means more `hPerDatum -> hBForm` wrappers are not the main missing mathematical edge anymore.  The remaining all-positive assumption is now exactly `PositiveDatumBFormLocalHyp p`.  Constructing it for **all** `PositiveInitialDatum intervalDomain u₀` is option A, but that is a genuinely hard analytic producer: it must construct all fields of `PositiveDatumBFormLocalComponents p u₀` for arbitrary positive data, not just paper-positive data.

The squared-barrier packages are not candidates for A, because their hypotheses are paper-positive:

```lean
PositiveDatumBFormLocalHypSq p
PositiveDatumBFormLocalHypSqRegular p
PositiveDatumBFormLocalHypSqDeepest p
```

and each quantifies over

```lean
PaperPositiveInitialDatum intervalDomain u₀
```

not arbitrary

```lean
PositiveInitialDatum intervalDomain u₀
```

So the faithful next Lean move is to expose a paper-positive version of the negative-part frontier and prove that the squared-barrier packages feed it.  This is useful because it lets the `Sq`/`SqRegular` stack feed paper-positive Theorem 1.1 routes without pretending to produce the all-positive frontier.

## Comparison of options

### A. Construct base `PositiveDatumBFormLocalHyp p` for all positive data

This is the **eventual hard all-positive producer**, but not the best immediate Task154-sized target.

`PositiveDatumBFormLocalHyp p` is defined in `IntervalBFormPositiveDatumLocalExistence.lean` as:

```lean
∀ u₀ : intervalDomainPoint → ℝ,
  PositiveInitialDatum intervalDomain u₀ →
    Nonempty (PositiveDatumBFormLocalComponents p u₀)
```

The component structure requires real fields:

- `DB : ConjugateMildExistenceData p u₀`
- `Hpde : HasBFormSpectralPdeAgreement p DB.T ...`
- truncated Picard data and bridge: `DT`, `Hbridge`
- `HmildWeak : TruncatedMildToWeakAvailable p DB`
- `Henergy : NegativePartEnergyCoreData p DB`
- a heat lower barrier
- `regularity`, `hpde_v`, `neumann`

The existing squared-barrier packages do not prove this because their datum input is `PaperPositiveInitialDatum`, not arbitrary `PositiveInitialDatum`.

### B. Define/prove a paper-positive negative-part frontier

This is the recommended next Lean target.

It is datum-faithful and mostly pure wiring for `Sq` and `SqRegular`.  It does not close the all-positive route, but it prevents the common bad move of trying to use the squared-barrier paper-positive package as though it covered all positive data.

For `SqDeepest`, the paper-positive frontier is not quite pure wiring yet unless the route gets a `negativePart_zero`/`TruncatedMildToWeakAvailable` bridge; more details below.

### C. Add more wrappers replacing `hPerDatum : BFormPositiveLocalFrontier p` by `hBForm : PositiveDatumBFormLocalHyp p`

This is valid but mostly bookkeeping now.

The important downstream headline already exists in `IntervalDomainBoundaryChemDivLimit.lean`:

```lean
ShenWork.Paper2.BFormPositiveDatumLocal
  .paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_of_localHyp
```

Additional uniform/quant wrappers in `IntervalBFormPositiveDatumQuantWiring.lean` would be harmless, but they would not reduce the real remaining assumptions: `PositiveDatumBFormLocalHyp p` and `ConeQuantBridge.PicardLimitRestartFrontier p` remain.

### D. Existing theorem chain already closes a stronger route

I do not see one in the audited files.

The strongest existing all-positive chain after `7eb94305` is still the downstream local-hyp headline:

```lean
PositiveDatumBFormLocalHyp p
ConeQuantBridge.PicardLimitRestartFrontier p
------------------------------------------
Theorem_1_1 intervalDomain p
```

The squared-barrier routes close paper-positive local existence plus continuation-style headlines, but they do not produce `PositiveDatumBFormLocalHyp p`, and they do not produce `BFormPositiveLocalFrontier p` for all `PositiveInitialDatum`.

## Exact Lean target to implement next

Add a paper-positive frontier definition in:

```text
ShenWork/Paper2/IntervalBFormPositiveDatumNegPartFrontier.lean
```

near the existing all-positive frontier:

```lean
/-- Paper-positive per-datum B-form frontier.

This is the datum-faithful analogue of `BFormPositiveLocalFrontier` for packages
whose constructors require `PaperPositiveInitialDatum`. -/
def BFormPaperPositiveLocalFrontier (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormPositiveClassicalFrontier p DB)
```

Then implement this theorem in:

```text
ShenWork/Paper2/IntervalBFormPositiveDatumLocalExistenceSqRegular.lean
```

under:

```lean
namespace ShenWork.Paper2.BFormPositiveDatumLocalSq
```

Full target:

```lean
theorem bFormPaperPositiveLocalFrontier_of_sqRegular
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSqRegular p) :
    ShenWork.Paper2.BFormPositiveDatumNegPart.BFormPaperPositiveLocalFrontier p := by
  intro u₀ hu₀paper
  obtain ⟨K⟩ := hBForm u₀ hu₀paper
  exact ⟨K.DB, ⟨K.toBFormPositiveClassicalFrontier⟩⟩
```

I recommend adding the following helper immediately above it in the same namespace/file:

```lean
/-- A `SqRegular` component package builds the negative-part classical frontier
record, with the datum class kept paper-positive. -/
theorem PositiveDatumBFormLocalComponentsSqRegular.toBFormPositiveClassicalFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ShenWork.Paper2.BFormPositiveDatumNegPart.BFormPositiveClassicalFrontier
      p K.DB := by
  let R := K.route
  have hreg :
      intervalDomainClassicalRegularity K.DB.T
        (conjugatePicardLimit p u₀ K.DB.T)
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ K.DB.T)) := by
    simpa [intervalDomain] using K.regularity
  have hpdeV :
      ∀ t x, 0 < t → t < K.DB.T → x ∈ intervalDomain.inside →
        0 = intervalDomain.laplacian
              ((mildChemicalConcentration p
                (conjugatePicardLimit p u₀ K.DB.T)) t) x
            - p.μ *
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ K.DB.T)) t x
            + p.ν *
              ((conjugatePicardLimit p u₀ K.DB.T) t x) ^ p.γ :=
    bForm_mildChemical_hpde_v_of_resolver_standardFacts
      K.neumannFacts.resolver_source_decay hreg R.strictPos
  refine
    { route := R
      regularity := K.regularity
      v_nonneg := ?_
      hpde_v := hpdeV
      neumann := K.neumann }
  intro t x ht htT
  exact ShenWork.IntervalMildToClassical.mildChemical_nonneg
    (T := K.DB.T) p
    (u := conjugatePicardLimit p u₀ K.DB.T)
    (conjugateMildSolutionData_of_data K.DB).hnonneg
    (conjugateMildSolutionData_of_data K.DB).hcont
    ht (le_of_lt htT) x
```

Then the global theorem is:

```lean
/-- The `SqRegular` paper-positive B-form package produces the paper-positive
negative-part frontier. -/
theorem bFormPaperPositiveLocalFrontier_of_sqRegular
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSqRegular p) :
    ShenWork.Paper2.BFormPositiveDatumNegPart.BFormPaperPositiveLocalFrontier p := by
  intro u₀ hu₀paper
  obtain ⟨K⟩ := hBForm u₀ hu₀paper
  exact ⟨K.DB, ⟨K.toBFormPositiveClassicalFrontier⟩⟩
```

## Proof status

For the `SqRegular` target above, the proof is expected to be **pure wiring**.

It uses existing pieces already present in `IntervalBFormPositiveDatumLocalExistenceSqRegular.lean`:

- `K.route : BFormNegativePartPositivityRoute p K.DB`
- `K.regularity`
- `K.neumann`
- `bForm_mildChemical_hpde_v_of_resolver_standardFacts`
- `K.neumannFacts.resolver_source_decay`
- `R.strictPos`
- `ShenWork.IntervalMildToClassical.mildChemical_nonneg`
- `(conjugateMildSolutionData_of_data K.DB).hnonneg`
- `(conjugateMildSolutionData_of_data K.DB).hcont`

No final theorem, no quantitative factory, and no datum-class conversion is needed.

## Import notes

The frontier definition belongs in `IntervalBFormPositiveDatumNegPartFrontier.lean`; that file already imports `IntervalBFormDirectClassical` and already defines `BFormPositiveClassicalFrontier` and `BFormPositiveLocalFrontier`.

The `SqRegular` theorem can be added directly to `IntervalBFormPositiveDatumLocalExistenceSqRegular.lean`.  No new import should be needed: the file already imports the negative-part/frontier stack through its existing imports and already has the opens needed for `intervalDomainClassicalRegularity`, `conjugatePicardLimit`, `conjugateMildSolutionData_of_data`, and `mildChemicalConcentration`.

If you prefer a separate additive file, use:

```lean
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqRegular

open Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint
   intervalDomainClassicalRegularity)
open ShenWork.IntervalConjugatePicard
  (conjugateMildSolutionData_of_data conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

-- theorem goes here

end ShenWork.Paper2.BFormPositiveDatumLocalSq
```

But same-file placement is cleaner.

## What about `Sq` and `SqDeepest`?

A parallel theorem for `PositiveDatumBFormLocalHypSq p` should also be pure wiring, because `PositiveDatumBFormLocalComponentsSq` already has:

- `route`
- `regularity`
- `hpde_v`
- `neumann`
- `mildChemical_nonneg` proof pattern in `isClassicalSolution`

A parallel theorem for `PositiveDatumBFormLocalHypSqDeepest p` is **not** obviously pure wiring yet.  `PositiveDatumBFormSqDeepestHypotheses` has `Henergy` and a `TruncatedMildToWeakRegularData` package, but it does not expose the old all-test-function field

```lean
TruncatedMildToWeakAvailable p DB
```

which is what `bform_negativePart_zero_of_concrete_truncated_energyCore` consumes.  The bridge in `IntervalBFormCron2MildToWeak.lean` is:

```lean
truncatedMildToWeakAvailable_of_regularData_allTests
```

and it requires:

```lean
all_tests : ∀ φ : ℝ → ℝ, Test φ
```

So the smallest extra subpackage for `SqDeepest -> BFormPaperPositiveLocalFrontier` is one of:

1. add/produce `all_tests : ∀ φ, H.Test φ`, then use `truncatedMildToWeakAvailable_of_regularData_allTests`; or
2. better, prove a narrower negative-part-energy bridge that only needs the specific negative-part test class instead of all tests, producing the `negativePart_zero` field directly from `H.weakOn` and `H.Henergy`.

That is an interface/analytic field issue, not a final-theorem issue.

## Circular/vacuous moves to avoid

1. **Do not use `PositiveInitialDatum -> PaperPositiveInitialDatum`.**  The direction available in the squared-barrier files is `PaperPositiveInitialDatum.toPositive`; the reverse is false and was explicitly ruled out.

2. **Do not claim `PositiveDatumBFormLocalHypSq p` or `PositiveDatumBFormLocalHypSqRegular p` proves `PositiveDatumBFormLocalHyp p`.**  The datum classes differ.  The squared-barrier hypotheses quantify over `PaperPositiveInitialDatum`, while `PositiveDatumBFormLocalHyp p` quantifies over all `PositiveInitialDatum`.

3. **Do not use final `Theorem_1_1`, `FinalWiring.paper2_theorem_1_1_from_quant`, or any `hQuant` output to build a frontier.**  The frontier must be constructed from component fields, not from a theorem headline or quantitative factory.

4. **Do not treat extra `hPerDatum -> hBForm` wrappers as assumption reduction.**  They are useful for API ergonomics, but after the `IntervalDomainBoundaryChemDivLimit.lean` local-hyp headline, they do not change the real frontier.

5. **Do not use the `SqDeepest` package to build `BFormPositiveClassicalFrontier` until the `negativePart_zero` route is actually exposed.**  Its current local solution theorem uses direct classical data and strict positivity, but a `BFormPositiveClassicalFrontier` record specifically requires a `BFormNegativePartPositivityRoute`, including `negativePart_zero`.

## Bottom line

Implement **B** first:

1. define `BFormPaperPositiveLocalFrontier` next to `BFormPositiveLocalFrontier`;
2. prove `bFormPaperPositiveLocalFrontier_of_sqRegular` in `IntervalBFormPositiveDatumLocalExistenceSqRegular.lean`.

This is the next best non-circular Lean target: it is datum-faithful, pure wiring for `SqRegular`, and it prevents the squared-barrier stack from being misused as an all-positive producer.  The eventual all-positive route is still option A, but that is a real analytic construction of `PositiveDatumBFormLocalHyp p`, not a wrapper task.
