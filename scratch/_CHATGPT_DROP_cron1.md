# Q403 / cron1: Barrier B — can `ConjugatePicardInfThresholdData` be weakened to windowed bounds with no consumer fallout?

## Executive verdict

The proposed **mathematical** direction is correct:

```text
unconditional-in-s bounds  ⇒  windowed bounds on 0 < s ≤ T
```

and the available banked producer facts in `IntervalBankInfAndLogSrcWiring.lean` are exactly windowed:

```lean
iterChemFlux_windowBound      : ∀ s, 0 < s → s ≤ D.T → ∀ y, |chemFluxLifted ...| ≤ iterCQ D
iterLogistic_windowBound      : ∀ s, 0 < s → s ≤ D.T → ∀ y, |logisticLifted ...| ≤ iterCL D
iterChemFlux_integrable       : ∀ s, 0 < s → s ≤ D.T → Integrable ...
```

So weakening the `ConjugatePicardInfThresholdData` fields to windowed bounds is the right conceptual fix for Barrier B.

But the proposed “change only the structure fields and everything else compiles as-is” is **not correct**.  Lean will not automatically turn an old projection application such as

```lean
H.hQ_int n s
H.hQ_bound n s
H.hL_bound n
```

into

```lean
H.hQ_int n s hs hsT
H.hQ_bound n s hs hsT
H.hL_bound n s hs hsT
```

Consumers do not necessarily pattern-match on the structure, but they do use the **exact projection types** and exact arities.  Those call sites will break and need mechanical eta-expansion / localized-bound rewiring.

The good news: this is a **syntactic/API retype**, not an analytic obstacle.  The producer can be changed/wrapped cheaply, and the consumers can be patched mechanically.  The one slightly nontrivial spot is the logistic value-Duhamel bound, because the currently called theorem expects an unconditional `∀ s y` bound; a small windowed/cutoff variant is needed there or the proof must use an existing cutoff theorem.

---

## Current structure: the three problematic fields are unconditional

Current definition in `ShenWork/Paper2/IntervalConjugatePicardInfThreshold.lean`:

```lean
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalConjugatePicardBounds
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter conjugatePicardLimit)
open ShenWork.IntervalMildPicard
  (real_cauchySeq_of_geometric_bound)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalFullSemigroupOperator_lower_bound)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.Paper2
  (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- B-form Picard facts needed by the inf-threshold argument.  This package
contains ball-derived source bounds and geometric convergence, but no positivity
field for the map or the limit. -/
structure ConjugatePicardInfThresholdData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) where
  K : ℝ
  C₀ : ℝ
  CQ : ℝ
  CL : ℝ
  hT : 0 < T
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hCQ : 0 ≤ CQ
  hCL : 0 ≤ CL
  hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
    ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀
  hQ_int : ∀ n s,
    Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s))
      (intervalMeasure 1)
  hQ_bound : ∀ n s y,
    |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ
  hB_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
  hL_bound : ∀ n s y,
    |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
  hL_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
```

Fields already windowed:

```lean
hgeom
hB_int
hL_int
```

Fields that should be retyped:

```lean
hQ_int
hQ_bound
hL_bound
```

Recommended windowed shape, matching the landed bank producers:

```lean
hQ_int : ∀ n s, 0 < s → s ≤ T →
  Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s))
    (intervalMeasure 1)

hQ_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
  |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ

hL_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
  |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
```

This order is intentional: it matches `IntervalBankInfAndLogSrcWiring` exactly.

---

## The landed bank facts are windowed, not unconditional

`ShenWork/Paper2/IntervalBankInfAndLogSrcWiring.lean` explicitly says the fully landed facts are windowed and that the old producer demanded unconditional-in-`s` bounds that the bank cannot derive outside the active window.

Relevant definitions/theorems:

```lean
/-- **Windowed chemotaxis-flux sup bound over the iterates** (`hQ_bound` on the
window `(0, D.T]`). -/
theorem iterChemFlux_windowBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ iterCQ D

/-- **Windowed logistic sup bound over the iterates** (`hL_bound` on the
window `(0, D.T]`). -/
theorem iterLogistic_windowBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ iterCL D

/-- **`hQ_int`: per-slice spatial integrability of the chemotaxis flux over the
iterates** (windowed). -/
theorem iterChemFlux_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T →
      Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s)) (intervalMeasure 1)
```

So if the aim is to use the banked facts, the structure really should not require unconditional `∀ s` bounds.

---

## Producer: close, but not literally unchanged

Current producer in `IntervalConjugatePicardInfThresholdDischarge.lean` takes unconditional bounds and assigns them directly:

```lean
def conjugatePicardInfThresholdData_of_picard_bounds
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (CQ CL : ℝ) (hCQ : 0 ≤ CQ) (hCL : 0 ≤ CL)
    (hQ_int : ∀ n s,
      Integrable
        (ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
          (conjugatePicardIter p u₀ n s))
        (ShenWork.IntervalDomain.intervalMeasure 1))
    (hQ_bound : ∀ n s y,
      |ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
          (conjugatePicardIter p u₀ n s) y| ≤ CQ)
    ...
    (hL_bound : ∀ n s y,
      |ShenWork.IntervalGradientDuhamelMap.logisticLifted p
          (conjugatePicardIter p u₀ n s) y| ≤ CL)
    ... :
    ConjugatePicardInfThresholdData p u₀ D.T := by
  ...
  exact
    { K := D.K
      C₀ := D.C₀
      CQ := CQ
      CL := CL
      ...
      hQ_int := hQ_int
      hQ_bound := hQ_bound
      hB_int := hB_int
      hL_bound := hL_bound
      hL_int := hL_int }
```

If the structure fields become windowed but the producer still accepts unconditional inputs, the field assignments must be eta-expanded:

```lean
hQ_int := fun n s _hs _hsT => hQ_int n s
hQ_bound := fun n s _hs _hsT y => hQ_bound n s y
hL_bound := fun n s _hs _hsT y => hL_bound n s y
```

So the producer is not literally unchanged.  It is a tiny proof-term change.

If the real producer source is `IntervalBankInfAndLogSrcWiring`, it is even cleaner to change the producer signature to accept windowed inputs:

```lean
(hQ_int : ∀ n s, 0 < s → s ≤ D.T → Integrable ...)
(hQ_bound : ∀ n s, 0 < s → s ≤ D.T → ∀ y, |...| ≤ CQ)
(hL_bound : ∀ n s, 0 < s → s ≤ D.T → ∀ y, |...| ≤ CL)
```

then the record fields can be filled directly from:

```lean
fun n => iterChemFlux_integrable D n
fun n => iterChemFlux_windowBound D n
fun n => iterLogistic_windowBound D n
```

Either way, this is not an analytic problem.

---

## Consumers: they will not compile “as-is”

The representative consumer is `intervalConjugateDuhamelMap_ge_half_floor` in `IntervalConjugatePicardInfThreshold.lean`.

Current chemotaxis part:

```lean
have hB_abs : |B| ≤
    heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ := by
  simpa [B] using
    ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
      ht htT (fun s _ _ => H.hQ_int n s) H.hCQ
      (fun s _ _ => H.hQ_bound n s) x.1 (H.hB_int n t ht htT x)
```

Notice that `conjugateDuhamel_sup_bound` itself already has a **windowed API**:

```lean
theorem conjugateDuhamel_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, 0 < s → s ≤ T → Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hq_sup : ∀ s, 0 < s → s ≤ T → ∀ y, |q s y| ≤ Cq) (x : ℝ)
    ...
```

So after weakening the fields, this call should become:

```lean
ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
  ht htT
  (fun s hs hsT => H.hQ_int n s hs hsT)
  H.hCQ
  (fun s hs hsT => H.hQ_bound n s hs hsT)
  x.1
  (H.hB_int n t ht htT x)
```

Lean will not infer those proof arguments from the old

```lean
fun s _ _ => H.hQ_int n s
```

because, after the field retype, `H.hQ_int n s` is a function waiting for proofs, not an `Integrable ...` term.

Current logistic part:

```lean
have hR_abs : |R| ≤ T * H.CL := by
  simpa [R] using
    ShenWork.IntervalGradDuhamelBound.valueDuhamel_sup_bound
      ht htT H.hCL (H.hL_bound n) x.1 (H.hL_int n t ht htT x)
```

This one is more important: `valueDuhamel_sup_bound` currently expects an unconditional source bound:

```lean
theorem valueDuhamel_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r : ℝ → ℝ → ℝ}
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hr_sup : ∀ s y, |r s y| ≤ Cr) (x : ℝ)
    (hr_int : IntervalIntegrable ...)
```

So after weakening `H.hL_bound`, this call cannot be fixed by merely adding hidden proof arguments to the same theorem.  You need one of:

1. a small windowed version of `valueDuhamel_sup_bound`, analogous to `conjugateDuhamel_sup_bound`, excluding both endpoints `s = 0` and `s = t` as null sets; or
2. a cutoff-source proof, like `IntervalConjugateBallSupBound.valueDuhamel_sup_bound_of_ball`, but without requiring data not stored in `ConjugatePicardInfThresholdData`; or
3. keep a separate unconditional logistic field, which defeats the purpose if only windowed facts are available.

A useful local theorem would have the shape:

```lean
theorem valueDuhamel_sup_bound_window
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r : ℝ → ℝ → ℝ}
    {Cr : ℝ} (hCr : 0 ≤ Cr)
    (hr_sup : ∀ s, 0 < s → s ≤ T → ∀ y, |r s y| ≤ Cr) (x : ℝ)
    (hr_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (r s) x) volume 0 t) :
    |∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x| ≤ T * Cr
```

Its proof is almost the same as `valueDuhamel_sup_bound`, with both `{0}` and `{t}` removed as null sets, or via a cutoff source.

Then the consumer becomes:

```lean
ShenWork.IntervalGradDuhamelBound.valueDuhamel_sup_bound_window
  ht htT H.hCL
  (fun s hs hsT => H.hL_bound n s hs hsT)
  x.1
  (H.hL_int n t ht htT x)
```

---

## Does this “touch 12 files”?

It may still touch many files, depending on how many constructors/projections appear outside the core file.  But it is not 12 files of analytic redesign.  It is mostly mechanical API fallout:

1. Change the three structure fields.
2. Adjust `conjugatePicardInfThresholdData_of_picard_bounds` either by eta-expanding unconditional inputs or by changing its signature to windowed inputs.
3. Patch direct uses of `H.hQ_int`, `H.hQ_bound`, `H.hL_bound` to pass window hypotheses.
4. Add or use a windowed value-Duhamel bound for the logistic leg.
5. Patch record literals that assign these fields directly.

So: **the proposed weakening is the right simplification**, but **not zero-touch**.

---

## Answer to the exact question

> “If we weaken the structure fields to windowed bounds, the producer can still fill them from unconditional bounds, and consumers compile as-is. Is this correct?”

Half-correct:

```text
Correct: unconditional ⟹ windowed, so the old producer can still fill weakened fields.
Incorrect: the producer and consumers do not compile literally as-is.
```

The producer needs eta-expansion or a windowed signature.  Consumers using projections must pass the new proof arguments.  The chemotaxis consumer is easy because `conjugateDuhamel_sup_bound` already has a windowed API.  The logistic consumer needs a windowed/cutoff value-Duhamel lemma or a proof rewrite, because the currently called `valueDuhamel_sup_bound` expects an unconditional `∀ s y` bound.

> “Or do the consumers pattern-match on the EXACT field type and break?”

They mostly do not “pattern-match” in the semantic sense, but yes, they break for the same practical reason: Lean projection applications are exact.  A field retype changes the type of every `H.hQ_int`, `H.hQ_bound`, and `H.hL_bound` occurrence.  Old code such as

```lean
H.hQ_int n s
H.hQ_bound n s
H.hL_bound n
```

will no longer elaborate unless it is rewritten to feed the window hypotheses or routed through a localized bound theorem.

---

## Recommended minimal patch shape

```lean
-- In ConjugatePicardInfThresholdData:
hQ_int : ∀ n s, 0 < s → s ≤ T →
  Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s)) (intervalMeasure 1)

hQ_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
  |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ

hL_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
  |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
```

Then update the old unconditional producer with wrappers if keeping its old signature:

```lean
hQ_int := fun n s _hs _hsT => hQ_int n s
hQ_bound := fun n s _hs _hsT y => hQ_bound n s y
hL_bound := fun n s _hs _hsT y => hL_bound n s y
```

or change the producer signature to take windowed facts and assign them directly.

Finally, patch the inf-threshold proof:

```lean
-- chem leg
ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
  ht htT
  (fun s hs hsT => H.hQ_int n s hs hsT)
  H.hCQ
  (fun s hs hsT => H.hQ_bound n s hs hsT)
  x.1
  (H.hB_int n t ht htT x)

-- logistic leg: use/add a windowed value-Duhamel bound
valueDuhamel_sup_bound_window
  ht htT H.hCL
  (fun s hs hsT => H.hL_bound n s hs hsT)
  x.1
  (H.hL_int n t ht htT x)
```

That is the simple fix: weaken the ledger to the actual domain of use, but budget for mechanical projection updates and one localized logistic bound lemma.
