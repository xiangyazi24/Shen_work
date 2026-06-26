# Q709 (cron2): logistic successor search for `IntervalConjugateBFormSourceTower.lean`

Static repo inspection only; I did not run a Lean build.

## Executive answer

For line 73, the **generic logistic successor infrastructure exists**, but I did **not** find a conjugate/B-form-specific `_succ` wrapper that directly proves

```lean
DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c DB.T
```

from the level-`n` B-form predecessor package.

So line 73 is not already solved by one landed theorem with the exact target.  It looks like a small wrapper/wiring lemma still needs to be written, using the generic successor lemma plus the B-form cosine-series representation.  The likely work is **wiring**, not new chemDiv-style analytic infrastructure, assuming the needed window facts/representation/integrability/source bridge are already available from `DB`/`Hinf`/existing bridge files.

## 1. `intervalConjugateDuhamelMap_cosineSeries`

Yes, it exists.

File:

```text
ShenWork/Paper2/IntervalConjugateCosineSeries.lean
```

Namespace:

```lean
ShenWork.IntervalConjugateCosineSeries
```

The theorem is:

```lean
theorem intervalConjugateDuhamelMap_cosineSeries
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {t x M₀ : ℝ}
    (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p u))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
```

This is exactly the B-form restart/cosine representation you want for

```lean
conjugatePicardIter p u₀ (n + 1)
```

because `conjugatePicardIter` has successor clause

```lean
| n + 1 => fun t x =>
    intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

One import note: `IntervalConjugateBFormSourceTower.lean` currently imports `IntervalBankInfAndLogSrcWiring`, but the theorem itself lives in `IntervalConjugateCosineSeries.lean`; line 73 will likely need that import, directly or indirectly.

## 2. `sourceTimeC1On_succ`

I did **not** find an exact standalone symbol named

```lean
sourceTimeC1On_succ
```

The landed theorem is named:

```lean
sourceTimeC1On_succ_of_sourceTimeC1On
```

File:

```text
ShenWork/Paper2/IntervalPicardSourceTimeC1OnRecursion.lean
```

Namespace:

```lean
ShenWork.IntervalPicardSourceTimeC1OnRecursion
```

Its target is generic in the produced profile `w`:

```lean
DuhamelSourceTimeC1On
  (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

It consumes:

```lean
src : DuhamelSourceTimeC1On a 0 W
```

plus the shifted-window map, restart representation, positivity, upper bound, G1/G2 bounds, slice continuity, and joint profile continuity.

The ordinary Picard tower already uses this theorem successfully in:

```text
ShenWork/Paper2/IntervalPicardSourceTower.lean
```

inside its successor construction `srcOn1`.  That usage is the best template for line 73: it shifts the predecessor source to `[0,W]`, builds the restart representation, proves profile joint continuity, and then calls `sourceTimeC1On_succ_of_sourceTimeC1On`.

## 3. `conjLogSourceTimeC1On_level0` and `_succ`

`conjLogSourceTimeC1On_level0` exists.

File:

```text
ShenWork/Paper2/IntervalConjugateIterSourceTower.lean
```

It defines:

```lean
abbrev ConjLogSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (c T : ℝ) :=
  DuhamelSourceTimeC1On
    (fun s k => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k)
    c T
```

and the level-0 producer:

```lean
noncomputable def conjLogSourceTimeC1On_level0 ... :
  ConjLogSourceTimeC1On p u₀ 0 c T :=
  level0Source_timeC1On ...
```

I did **not** find a `conjLogSourceTimeC1On_succ` / `_succ` version.  Searching `conjLogSourceTimeC1On` only turned up the level-0/base file plus the level-0 B-form wrapper file.

There is also a level-0 restatement in terms of `coupledLogisticSourceCoeffs`:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

```lean
noncomputable def level0_logisticSource_timeC1On ... :
  DuhamelSourceTimeC1On
    (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  conjLogSourceTimeC1On_level0 ...
```

But I did not find the analogous successor restatement.

## 4. Theorem producing `DuhamelSourceTimeC1On` for `coupledLogisticSourceCoeffs` at level `n+1` from level `n`

I did **not** find a direct theorem with this shape for conjugate/B-form iterates:

```lean
DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c T
```

from

```lean
DuhamelSourceTimeC1On
  (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) ...
```

or from the tower IH.

What does exist:

1. `intervalConjugateDuhamelMap_cosineSeries`, which can give the local restart representation of the B-form successor using `bFormSourceCoeffs p (conjugatePicardIter p u₀ n)`.

2. `sourceTimeC1On_succ_of_sourceTimeC1On`, which can turn a restart representation plus a predecessor `DuhamelSourceTimeC1On a 0 W` package into logistic-source `TimeC1On` for the successor profile.

3. Definitional bridge:

```lean
coupledLogisticSourceCoeffs p u s k
= cosineCoeffs (logisticLifted p (u s)) k
```

because `coupledLogisticSourceCoeffs` unfolds through `coupledLogisticSourceLift`, and `logisticLifted p w` is `intervalDomainLift (intervalLogisticSource p w)`.

So the missing landed theorem is probably a wrapper like:

```lean
noncomputable def conjLogSourceTimeC1On_succ_of_bFormSourceTimeC1On
    ...
    (hpred : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) ...)
    ... :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p
        (conjugatePicardIter p u₀ (n + 1))) c T := by
  -- shift hpred to [0,W]
  -- obtain restart representation from intervalConjugateDuhamelMap_cosineSeries
  -- feed representation/positivity/bounds/joint-continuity into
  --   sourceTimeC1On_succ_of_sourceTimeC1On
  -- finish by simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
  --   ShenWork.IntervalGradientDuhamelMap.logisticLifted]
```

## Verdict for line 73

Line 73 is **not** pure one-line reuse of an existing conjugate successor lemma.  But the hard logistic successor theorem already exists in generic form.  The missing piece is a conjugate/B-form wrapper that:

1. shifts the IH source package;
2. uses `intervalConjugateDuhamelMap_cosineSeries` to prove the restart representation for `conjugatePicardIter ... (n+1)`;
3. supplies the existing window facts required by `sourceTimeC1On_succ_of_sourceTimeC1On`;
4. rewrites from `cosineCoeffs (logisticLifted ...)` to `coupledLogisticSourceCoeffs`.

So: **mostly wiring, but not already packaged**.
