# Q425 / cron1: Barrier B — windowed `ConjugatePicardInfThresholdData` vs new parallel structure

## Executive verdict

Your corrected diagnosis is right:

```text
windowed ⇒ unconditional is NOT available.
unconditional ⇒ windowed is trivial but is the wrong direction.
```

The old `ConjugatePicardInfThresholdData` is over-typed.  Its current fields

```lean
hQ_int   : ∀ n s, Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s)) ...
hQ_bound : ∀ n s y, |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ
hL_bound : ∀ n s y, |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
```

ask for all real `s`, but the actual Picard ball / source-control facts are only on the fixed-point horizon window `(0,T]`.  There is no reason in the current definitions to expect the B-form Picard iterates to be uniformly bounded for `s > T`, and for `s < 0` the heat/Duhamel objects are merely total Lean definitions, not analytic semigroup-time objects with paper meaning.

So the honest theorem shape is windowed:

```lean
hQ_int   : ∀ n s, 0 < s → s ≤ T → Integrable ...
hQ_bound : ∀ n s, 0 < s → s ≤ T → ∀ y, |...| ≤ CQ
hL_bound : ∀ n s, 0 < s → s ≤ T → ∀ y, |...| ≤ CL
```

Adding a **new windowed structure** is viable, but not as a pure one-line change to `BFormBankedInputs` unless you also route the B-form downstream theorems through windowed variants.  Existing downstream theorems currently take `ConjugatePicardInfThresholdData`; if `BFormBankedInputs.Hinf` is changed to a new type, any theorem that consumes `B.Hinf` will stop elaborating unless it is duplicated/generalized.

The best low-risk patch is therefore:

```text
Add WindowedConjugatePicardInfThresholdData + producer from the banked windowed facts.
Add windowed analogues of the few positivity/PDE theorems that BFormBankedInputs needs.
Change the B-form bank/frontier path to use the windowed structure.
Leave the old over-typed structure and old theorem stack untouched for compatibility.
```

This avoids the full 12-file retype of the old API, but it does **not** avoid touching the B-form bank path and its direct consumers.

---

## Why the unconditional bound is not justified

Current iterates are defined in `IntervalConjugatePicard.lean` as total functions, but the convergence/ball package is explicitly windowed.  `ConjugatePicardInfThresholdData` itself stores `hgeom` windowed:

```lean
hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
  ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ (n + 1) t x
      - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀
```

and its Duhamel integrability fields are already windowed:

```lean
hB_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, ...
hL_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, ...
```

But the three source fields remain unconditional:

```lean
hQ_int : ∀ n s, Integrable ...
hQ_bound : ∀ n s y, |...| ≤ CQ
hL_bound : ∀ n s y, |...| ≤ CL
```

That mismatch is exactly the over-typing.

The landed bank file says this explicitly in its module comment:

```lean
IMPORTANT — neither top-level field is fully landed here; see the trailing
report.  Field 2's producer demands UNCONDITIONAL-in-`s` bounds
(`hQ_bound/hL_bound : ∀ n s y, …`) that are NOT derivable from the
window-only data `D` (no `s > T` control); field 6 needs a restart-cosine
representation + time-`C¹` coefficient data for `conjugatePicardLimit` that is
not landed anywhere in the tree.  The bricks below are exactly the windowed
half that IS axiom-clean.
```

So the repo itself already documents the conclusion: the currently landed facts are windowed, and unconditional-in-`s` is not derivable from the current data.

The relevant landed windowed facts are:

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

These are exactly the facts a windowed threshold package should carry.

---

## Why changing only the producer cannot work

The current producer has the old unconditional signature:

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
```

You cannot change this producer to accept windowed inputs and still return the old structure, because the old structure literally demands unrestricted fields.  A windowed input cannot fill:

```lean
hQ_bound : ∀ n s y, ...
```

unless you invent/prove behavior outside `(0,T]`, or define a cutoff iterate/source, which would no longer be the same `conjugatePicardIter p u₀ n s`.

So there are only three honest options:

1. **Retype the old structure** to windowed fields.  Correct but cascades.
2. **Add a new windowed structure** and route new B-form bank/frontier code through it.  Compatible with old files.
3. **Keep old structure and prove unconditional bounds**.  Not supported by current analytic data and likely false / meaningless outside the horizon.

---

## Is a parallel windowed structure viable?

Yes.  This is viable and probably the least disruptive approach if you want to avoid editing every old consumer.

Suggested new structure:

```lean
structure ConjugatePicardInfThresholdDataOn
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
  hQ_int : ∀ n s, 0 < s → s ≤ T →
    Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s))
      (intervalMeasure 1)
  hQ_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
    |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ
  hB_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
  hL_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
    |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
  hL_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
```

Suggested producer from the landed bank facts:

```lean
def conjugatePicardInfThresholdDataOn_of_picard_bounds
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (CQ CL : ℝ) (hCQ : 0 ≤ CQ) (hCL : 0 ≤ CL)
    (hQ_int : ∀ n s, 0 < s → s ≤ D.T → Integrable ...)
    (hQ_bound : ∀ n s, 0 < s → s ≤ D.T → ∀ y, |...| ≤ CQ)
    (hB_int : ∀ n t, 0 < t → t ≤ D.T → ∀ x, IntervalIntegrable ...)
    (hL_bound : ∀ n s, 0 < s → s ≤ D.T → ∀ y, |...| ≤ CL)
    (hL_int : ∀ n t, 0 < t → t ≤ D.T → ∀ x, IntervalIntegrable ...) :
    ConjugatePicardInfThresholdDataOn p u₀ D.T := ...
```

This producer can be filled directly from:

```lean
CQ := iterCQ D
CL := iterCL D
hCQ := iterCQ_nonneg D
hCL := iterCL_nonneg D
hQ_int := fun n => iterChemFlux_integrable D n
hQ_bound := fun n => iterChemFlux_windowBound D n
hB_int := iterChemFlux_duhamel_intervalIntegrable D
hL_bound := fun n => iterLogistic_windowBound D n
hL_int := iterLogistic_duhamel_intervalIntegrable D
```

This is cleaner than trying to coerce windowed facts into the old over-typed structure.

---

## But can you change only `BFormBankedInputs.Hinf` to the windowed structure?

Not by itself.

Current `BFormBankedInputs` in `IntervalBFormDirectClassical.lean` has:

```lean
structure BFormBankedInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  ...
```

and `BFormBankedInputs.hpde_u` passes `B.Hinf` to a theorem whose type expects the old structure:

```lean
ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_PID_global_restart_on
    DB B.huPaper B.Hinf B.hsmall
    ...
```

Likewise `IntervalBFormEndToEnd.lean` has a parallel `BFormBankedInputs` structure with the old `Hinf : ConjugatePicardInfThresholdData p u₀ DB.T` field.

And strict positivity uses old `Hinf` directly:

```lean
theorem bform_strictPos_closed
    ...
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hsmall : ... Hinf.CQ ... Hinf.CL ...)
    ...
```

with the immediate barrier helper:

```lean
theorem squareHeatBarrier_paperPositiveConstSeed_initial_le
    ...
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    ...
```

So if `BFormBankedInputs.Hinf` becomes `ConjugatePicardInfThresholdDataOn`, old calls like these break unless you also introduce windowed versions of the positivity/PDE theorems.

---

## Minimal viable parallel-windowed path

Do **not** try to convert the new windowed structure back to the old one.  Instead add new variants along the B-form route:

```text
ConjugatePicardInfThresholdDataOn
conjugatePicardInfThresholdDataOn_of_picard_bounds
intervalConjugateDuhamelMap_ge_half_floor_on
conjugatePicardIter_ge_half_floor_of_PID_on
conjugatePicardLimit_ge_half_floor_of_PID_on
conjugatePicardLimit_pos_of_PID_on
squareHeatBarrier_paperPositiveConstSeed_initial_le_on
bform_strictPos_closed_on
```

For the PDE route, either:

```text
intervalConjugateMildSolution_pde_u_PID_global_restart_on_on
```

or, better, inspect whether the existing `intervalConjugateMildSolution_pde_u_PID_global_restart_on` only carries `Hinf` for positivity/smallness.  If so, replace its dependency by a smaller interface:

```lean
structure ConjugateInfThresholdLike ... where
  CQ CL : ℝ
  hT : 0 < T
  hCQ : 0 ≤ CQ
  hCL : 0 ≤ CL
  hgeom : ... windowed ...
  hQ_int : ... windowed ...
  hQ_bound : ... windowed ...
  hB_int : ... windowed ...
  hL_bound : ... windowed ...
  hL_int : ... windowed ...
```

or pass only the actual derived positivity theorem:

```lean
hpos : ∀ t, 0 < t → t < T → ∀ x, 0 < conjugatePicardLimit p u₀ T t x
```

where possible.  This is often even cleaner: many downstream classical/PDE theorems do not need the original inf-threshold structure, only the positivity consequence and the constants in `hsmall`.

---

## Is this less work than the 12-file retype?

Probably yes if you keep the old API untouched and add a windowed B-form route, but it is not free.

Expected edits:

1. One new structure file or addendum in `IntervalConjugatePicardInfThreshold.lean`.
2. One new producer using `IntervalBankInfAndLogSrcWiring` facts.
3. Windowed copies/generic versions of the inf-threshold positivity chain.
4. Windowed variants of the few B-form bank consumers that currently require old `Hinf`.
5. Change `BFormBankedInputs` / `BFormDirectFrontier` for the new route only.

This avoids touching old clients that still use `ConjugatePicardInfThresholdData`, but it does mean maintaining two routes temporarily.

---

## Recommended implementation strategy

Best short-term path:

```text
A. Leave old ConjugatePicardInfThresholdData exactly as-is.
B. Add ConjugatePicardInfThresholdDataOn with windowed fields.
C. Add a bank producer from iterChemFlux_windowBound / iterLogistic_windowBound / iterChemFlux_integrable.
D. Add windowed variants of the positivity lemmas by copying the old proofs and replacing:
     H.hQ_int n s     → H.hQ_int n s hs hsT
     H.hQ_bound n s   → H.hQ_bound n s hs hsT
     H.hL_bound n s   → H.hL_bound n s hs hsT
   plus use a windowed/cutoff value-Duhamel bound for the logistic leg if needed.
E. Change only the new/direct B-form bank path to use HinfOn.
```

This is viable and avoids editing old consumers.  But if your goal is a single canonical API, the cleaner final state is still to retype `ConjugatePicardInfThresholdData` itself to windowed fields and patch the fallout once.

---

## Final answer

* The unconditional bound `∀ s` is not justified by the current Picard ball machinery and is likely false / analytically meaningless outside `(0,T]`.
* The old structure is over-typed.
* You cannot produce the old unconditional structure from windowed inputs without adding nontrivial and probably false outside-window facts.
* Adding a new windowed structure is viable.
* But changing `BFormBankedInputs.Hinf` to the new structure requires windowed variants/generic versions of the B-form consumers that currently expect `ConjugatePicardInfThresholdData`; it is not a pure one-field change.
* This parallel route is still a reasonable way to avoid the full 12-file old-API retype while preserving backward compatibility.
