# Q731 (cron2): Tower base / limit / extension machinery

Static repo inspection only; I did not run a Lean build or `#print axioms`.

## Executive verdict

### Line 60 base case

`level0_bFormSource_duhamelSourceTimeC1On_auto` **exists** in:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Namespace:

```lean
ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

However, there are two important caveats.

1. The local body of `level0_bFormSource_duhamelSourceTimeC1On_auto` is wiring, but it is **not transitively sorry-free yet**.  The file explicitly says this self-contained variant “Uses sorry,” because it constructs `Level0ChemDivSourceData` internally from:

```lean
level0_chemDiv_envelope_summable
level0_chemDiv_timeDerivData
```

and the file comments say these are the two Level0 chemDiv residuals.

2. The Tower comment’s suggested call

```lean
exact level0_bFormSource_duhamelSourceTimeC1On_auto p DB hu₀pos hc hcT.le
```

is **not the current signature** of the theorem I found.  The current theorem takes the raw Level0 window hypotheses:

```lean
noncomputable def level0_bFormSource_duhamelSourceTimeC1On_auto
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  level0_bFormSource_duhamelSourceTimeC1On p hc hcT hα ha hb hu₀_cont hu₀_bound
    hpos hub hG1 hG2 hUdot
    (level0ChemDivSourceData p hc hcT.le hu₀_cont hu₀_bound hpos hub)
```

There are helper theorems immediately below it:

```lean
level0_heat_pos_of_data
level0_heat_sup_of_data
```

which extract the heat-level positivity and sup bounds from `ConjugateMildExistenceData`/`PositiveInitialDatum`, but I did **not** find a convenience wrapper with the exact `p DB hu₀pos hc hcT.le` signature in the current file.

So: line 60 is **morally pure wiring once Level0 is complete**, but the current repo still needs either:

* a wrapper matching the Tower comment, or
* an explicit call passing the raw arguments (`hα`, `ha`, `hb`, `hu₀_cont`, coefficient bound, `hpos`, `hub`, `hG1`, `hG2`, `hUdot`).

## Line 92 limit passage

`duhamelSourceTimeC1On_of_uniform_limit` **exists**.

File:

```text
ShenWork/Paper2/IntervalMildPicardLimitRegularityOn.lean
```

Namespace:

```lean
ShenWork.IntervalMildPicardLimitRegularityOn
```

The file header explicitly says:

```text
No `sorry`/`admit`/custom `axiom`.
```

The main theorem is:

```lean
def duhamelSourceTimeC1On_of_uniform_limit
    {a : ℝ → ℕ → ℝ} {aSeq : ℕ → ℝ → ℕ → ℝ}
    {lo hi : ℝ}
    (hconv : ∀ s ∈ Icc lo hi, ∀ k, Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
    {adotSeq : ℕ → ℝ → ℕ → ℝ}
    (hderiv_each : ∀ n, ∀ s ∈ Icc lo hi, ∀ k,
      HasDerivWithinAt (fun r => aSeq n r k) (adotSeq n s k) (Icc lo hi) s)
    {adot : ℝ → ℕ → ℝ}
    (hadot_unif : ∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k)
      (fun s => adot s k) atTop (Icc lo hi))
    (hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Icc lo hi))
    {envelope : ℕ → ℝ}
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |aSeq n s k| ≤ envelope k)
    {D : ℝ}
    (hderiv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |adotSeq n s k| ≤ D) :
    DuhamelSourceTimeC1On a lo hi
```

This matches the Tower line 92 comment well: it needs iterate packages on `[c,T]`, pointwise coefficient convergence, uniform derivative convergence, a common summable envelope, and a common derivative bound.

## Line 111 extension to `[0,T]`

I found `DuhamelSourceTimeC1On` restriction/shift utilities, but I did **not** find a completed theorem that extends from “for all `c > 0`, `DuhamelSourceTimeC1On a c T`” down to `DuhamelSourceTimeC1On a 0 T`.

File:

```text
ShenWork/PDE/IntervalDuhamelSourceTimeC1On.lean
```

Existing machinery:

```lean
structure DuhamelSourceTimeC1On (a : ℝ → ℕ → ℝ) (lo hi : ℝ) where
  adot : ℝ → ℕ → ℝ
  hderiv : ∀ s ∈ Set.Icc lo hi, ∀ n,
    HasDerivWithinAt (fun r => a r n) (adot s n) (Set.Icc lo hi) s
  hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Set.Icc lo hi)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s ∈ Set.Icc lo hi, ∀ n, |a s n| ≤ envelope n
  derivBound : ℝ
  hderivBound : ∀ s ∈ Set.Icc lo hi, ∀ n, |adot s n| ≤ derivBound
```

```lean
def DuhamelSourceTimeC1.toOn {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (lo hi : ℝ) (hlo : 0 ≤ lo) : DuhamelSourceTimeC1On a lo hi
```

```lean
def DuhamelSourceTimeC1On.shift_zero {a : ℝ → ℕ → ℝ} {offset W : ℝ}
    (src : DuhamelSourceTimeC1On a offset (offset + W)) :
    DuhamelSourceTimeC1On (fun s n => a (offset + s) n) 0 W
```

```lean
def DuhamelSourceTimeC1On.restrict_hi {a : ℝ → ℕ → ℝ} {lo hi hi' : ℝ}
    (src : DuhamelSourceTimeC1On a lo hi) (hhi' : hi' ≤ hi) :
    DuhamelSourceTimeC1On a lo hi'
```

Also available:

```lean
DuhamelSourceTimeC1On.const_mul
DuhamelSourceTimeC1On.add
```

I did **not** find:

```lean
DuhamelSourceTimeC1On.restrict_lo
DuhamelSourceTimeC1On.extend_lo
DuhamelSourceTimeC1On.extend_zero
DuhamelSourceTimeC1On_of_forall_pos_lo
```

or any named theorem that packages the Tower line 111 step.

So line 111 still appears to need a new endpoint-extension lemma or a direct construction at `lo = 0`.  The existing restriction machinery only goes from a larger closed window to a smaller upper endpoint (and shifts `[offset, offset+W]` to `[0,W]`); it does not lower the left endpoint from `c` to `0`.

## Bottom line

* **Line 60:** `level0_bFormSource_duhamelSourceTimeC1On_auto` exists.  Its local body is wiring, but it transitively depends on the Level0 chemDiv sorries.  Also, the exact `p DB hu₀pos hc hcT.le` wrapper suggested by the Tower comment is not the theorem signature I found.
* **Line 92:** `duhamelSourceTimeC1On_of_uniform_limit` exists and is explicitly documented as sorry-free.
* **Line 111:** restriction/shift machinery exists (`toOn`, `shift_zero`, `restrict_hi`), but I found no completed extension-to-left-endpoint / `[c,T]`-to-`[0,T]` theorem.
