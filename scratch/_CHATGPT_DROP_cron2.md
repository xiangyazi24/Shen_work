# Q1036 (cron2) — exact wiring audit for Tower's 5 sorries after Level0

Static repo inspection only; I did **not** run Lean.

I read:

- `ShenWork/Paper2/IntervalConjugateBFormSourceTower.lean`
- `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`
- `ShenWork/Paper2/IntervalPicardSourceTimeC1OnRecursion.lean`
- `ShenWork/Paper2/IntervalConjugateCosineSeries.lean`
- `ShenWork/Paper2/IntervalMildPicardLimitRegularityOn.lean`
- `ShenWork/PDE/IntervalDuhamelSourceTimeC1On.lean`
- `ShenWork/Paper2/IntervalChiNegFinalClose.lean`
- `ShenWork/Paper2/IntervalBFormSpectralHtime.lean`

## Executive verdict

Once Level0 is 0-sorry, Tower's first sorry is close, but the Tower is **not** five `exact`s away.

The committed theorem names exist for the advertised pieces, but the current Tower skeleton is missing several wiring hypotheses/packages:

1. The Level0 theorem `level0_bFormSource_duhamelSourceTimeC1On_auto` is committed, but its actual signature is **not** the short call in the Tower comment.
2. The logistic successor theorem is committed and sorry-free, but the Tower needs a conjugate restart/cosine representation package and shifted predecessor package before it can call it.
3. The chemDiv successor is the genuine remaining analytic wall; it needs a successor-level analogue of Level0 chemDiv C²/source/H²/time-derivative infrastructure.
4. The limit-passage theorem is committed and sorry-free, but the convergence/common-envelope hypotheses are not produced by the Tower skeleton.
5. The extension from all `[c,T]`, `c>0`, to `[0,T]` is **not trivial** and may be false for the current zero-at-0 `conjugatePicardLimit` unless a new endpoint-regularity/patch theorem is proved.

## Tower sorries in `IntervalConjugateBFormSourceTower.lean`

The current skeleton is:

```lean
noncomputable def conjBFormSourceTimeC1OnUpTo_all ... :
    ∀ n, ConjBFormSourceTimeC1OnUpTo p u₀ n DB.T := by
  intro n
  induction n with
  | zero =>
    intro c hc hcT
    sorry
  | succ n ih =>
    intro c hc hcT
    have _hpred := ih (c / 2) (by linarith) (by linarith)
    have _hlog : DuhamelSourceTimeC1On
        (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c DB.T := by
      sorry
    have _hchem : DuhamelSourceTimeC1On
        (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c DB.T := by
      sorry
    exact ShenWork.IntervalBFormSpectral.bFormSource_duhamelSourceTimeC1On _hlog _hchem
```

Then:

```lean
noncomputable def conjBFormSourceTimeC1On_limit ... :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) c DB.T := by
  sorry
```

and:

```lean
noncomputable def hsrcBDirect_of_data ... :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T := by
  sorry
```

## Sorry #1 — Level0 base case

### Committed theorem name

The Level0 export currently is:

```lean
ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_bFormSource_duhamelSourceTimeC1On_auto
```

File:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

There is also the lower-level constructor:

```lean
ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_bFormSource_duhamelSourceTimeC1On
```

which takes an explicit:

```lean
chemData : Level0ChemDivSourceData p u₀ c T
```

and combines it via:

```lean
ShenWork.IntervalBFormSpectral.bFormSource_duhamelSourceTimeC1On
```

from:

```text
ShenWork/Paper2/IntervalBFormSpectralHtime.lean
```

### Important signature mismatch

The Tower comment says:

```lean
exact level0_bFormSource_duhamelSourceTimeC1On_auto p DB hu₀pos hc hcT.le
```

That is **not** the actual committed signature.  The actual theorem is:

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
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T
```

So the exact line #1 cannot yet be a one-liner from `(DB, huPaper, hu₀pos, Hinf)` unless a DB-wrapper theorem is added.

### Existing helper names

These Level0 helper names are committed:

```lean
ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_heat_pos_of_data
ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_heat_sup_of_data
```

They supply `hpos` and `hub`.  But I did **not** find a committed wrapper extracting all of:

```lean
hα : 1 ≤ p.α
hu₀_cont
hu₀_bound
hG1
hG2
hUdot
```

from the Tower arguments.

Also note: `CM2Params` has `p.hα : 0 < p.α`, not `1 ≤ p.α`.  So the Tower theorem either needs an extra hypothesis `hα : 1 ≤ p.α`, or a different upstream structure must supply it.

### Exact base-case wiring after adding/exposing missing inputs

Once those inputs are available, line #1 should be:

```lean
  | zero =>
    intro c hc hcT
    exact ShenWork.Paper2.ConjugateLevel0BFormSourceOn
      .level0_bFormSource_duhamelSourceTimeC1On_auto
        (p := p) (u₀ := u₀) (T := DB.T)
        (hc := hc) (hcT := hcT)
        hα p.ha p.hb
        hu₀_cont hu₀_bound
        (ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_heat_pos_of_data
          DB hu₀pos hc hcT.le)
        (ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_heat_sup_of_data
          DB hc hcT.le)
        hG1 hG2 hUdot
```

where `hα`, `hu₀_cont`, `hu₀_bound`, `hG1`, `hG2`, `hUdot` must be supplied by a new wrapper or added to the Tower inputs.

### Status

`level0_bFormSource_duhamelSourceTimeC1On_auto` is already committed.  It is not currently sorry-free because it calls `level0ChemDivSourceData`, which calls the Level0 chemDiv infrastructure still being closed.  Once Level0 is 0-sorry, this theorem should become clean, but the Tower base still needs the argument-wrapper mismatch fixed.

## Sorry #2 — logistic successor

### Exact committed theorem names

The recursion theorem is:

```lean
ShenWork.IntervalPicardSourceTimeC1OnRecursion.sourceTimeC1On_succ_of_sourceTimeC1On
```

File:

```text
ShenWork/Paper2/IntervalPicardSourceTimeC1OnRecursion.lean
```

The theorem is committed and the file header says no `sorry`/`admit`/custom axiom.

The conjugate cosine-series representation theorem is:

```lean
ShenWork.IntervalConjugateCosineSeries.intervalConjugateDuhamelMap_cosineSeries
```

File:

```text
ShenWork/Paper2/IntervalConjugateCosineSeries.lean
```

The file header also says no `sorry`/`admit`/custom axioms.

### What they actually are

`sourceTimeC1On_succ_of_sourceTimeC1On` is not a theorem specifically about conjugate iterates.  It is a generic endpoint-inclusive successor logistic source package.  It consumes:

```lean
src : DuhamelSourceTimeC1On a 0 W
```

plus a shifted restart representation:

```lean
hrestart : ∀ s ∈ Icc lo hi, ∀ x : intervalDomainPoint,
  intervalDomainLift (w s) x.1 =
    ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1
```

and per-window data:

```lean
hbsum, hagree, hpos, hub, hG1, hG2, hC2cont, hprofile_joint
```

`intervalConjugateDuhamelMap_cosineSeries` proves the B-form conjugate Duhamel map has the cosine restart form, but it itself requires several nontrivial inputs:

```lean
hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p u)
hB_int : IntervalIntegrable ... chemFlux Duhamel leg
hlog_int : IntervalIntegrable ... logistic Duhamel leg
hsource_bridge : ∀ s ∈ Ioo 0 t, ... = unitIntervalCosineHeatValue ...
```

The source-bridge can be reduced using committed theorems in:

```text
ShenWork/Paper2/IntervalChiNegFinalClose.lean
```

especially:

```lean
ShenWork.Paper2.IntervalChiNegFinalClose.source_bridge_slice_of_sliceC1
ShenWork.Paper2.IntervalChiNegFinalClose.divMode_of_sliceC1
```

but these still require per-slice `C¹` data of the chemotaxis flux and continuity/bounds.

### Is sorry #2 just `ih + intervalConjugateDuhamelMap_cosineSeries + sourceTimeC1On_succ`?

Not directly.

The predecessor package from the Tower is:

```lean
_hpred : DuhamelSourceTimeC1On
  (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) (c/2) DB.T
```

To feed `sourceTimeC1On_succ_of_sourceTimeC1On`, one first needs to shift it to zero:

```lean
DuhamelSourceTimeC1On.shift_zero
```

from:

```text
ShenWork/PDE/IntervalDuhamelSourceTimeC1On.lean
```

A typical setup would be:

```lean
let offset : ℝ := c / 2
let W : ℝ := DB.T - c / 2
have hpred_shifted : DuhamelSourceTimeC1On
    (fun ρ k => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) (offset + ρ) k)
    0 W := by
  -- from `_hpred`, after rewriting `DB.T = offset + W`
  simpa [offset, W] using _hpred.shift_zero
```

Then set:

```lean
w := conjugatePicardIter p u₀ (n + 1)
a₀ := cosineCoeffs (intervalDomainLift u₀)
a  := fun ρ k => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) (offset + ρ) k
lo := c
hi := DB.T
```

But the Tower still needs the representation and regularity inputs for `w`.  Those are not produced by `ih` alone.  They require a conjugate analogue of the canonical `TowerLevel` carrier from `IntervalPicardSourceTower.lean`, or at least a window-local package containing:

```lean
bc, hbsum, hagree, hpos, hub, hG1, hG2, hrestart, hC2cont, hprofile_joint
```

So the exact successor logistic wiring is possible with the committed theorem, but the current Tower skeleton is missing the carrier fields needed to call it.

## Sorry #3 — chemDiv successor

This is the genuine analytic wall.

The Tower comment says:

```lean
sorry -- Needs chemDiv C² for iterate n+1 (same gap as level 0)
```

That is accurate in spirit, but the successor case is not literally closed by the Level0 theorem.  Level0 uses heat semigroup smoothing for:

```lean
u = conjugatePicardIter p u₀ 0 = S(t)u₀
```

For successor levels:

```lean
u = conjugatePicardIter p u₀ (n + 1)
```

one must get positive-time spatial and time regularity from the B-form Duhamel restart representation driven by the predecessor B-form source.

So #3 needs the **same category of chemDiv infrastructure** as Level0:

- resolver value joint regularity,
- resolver gradient joint regularity,
- positivity floor for `1 + v`,
- flux/source chain rule,
- closed-slab source representative for uniform sup/envelope,
- H²/second-derivative representative for quadratic decay,
- time-derivative coefficient package.

But it must be generalized from heat Level0 to arbitrary conjugate iterate successor windows.  The canonical logistic tower has a robust carrier design in:

```text
ShenWork/Paper2/IntervalPicardSourceTower.lean
```

with `TowerLevel`, `SourceWin`, `srcOn`, `srcBdd`, etc.  The conjugate B-form Tower currently does not carry an analogous per-level analytic package.  Therefore #3 is **not** solved by Level0 becoming 0-sorry.

Expected missing theorem shape:

```lean
conjugateIter_chemDivSourceTimeC1On_succ
  : predecessor B-form TimeC1On / restart representation / window regularity
    → DuhamelSourceTimeC1On
        (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ (n+1))) c DB.T
```

I did not find such a committed theorem.

## Sorry #4 — limit passage

### Exact committed theorem name

The theorem is:

```lean
ShenWork.IntervalMildPicardLimitRegularityOn.duhamelSourceTimeC1On_of_uniform_limit
```

File:

```text
ShenWork/Paper2/IntervalMildPicardLimitRegularityOn.lean
```

Its file header says no `sorry`/`admit`/custom axioms.

Its signature is:

```lean
def duhamelSourceTimeC1On_of_uniform_limit
    {a : ℝ → ℕ → ℝ} {aSeq : ℕ → ℝ → ℕ → ℝ}
    {lo hi : ℝ}
    (hconv : ∀ s ∈ Icc lo hi, ∀ k,
      Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
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

### Is Tower #4 just an exact call?

No.  The theorem is committed and sorry-free, but the Tower must still prove all its hypotheses for:

```lean
aSeq n := bFormSourceCoeffs p (conjugatePicardIter p u₀ n)
a      := bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)
```

The current Tower gives iterate packages, but it does not produce:

```lean
hconv
hadot_unif
hadot_cont
common envelope
common derivative bound
```

The comments point toward `conjugatePicardIter_geometric + Lipschitz of bFormSourceCoeffs`, but I did not find a committed theorem packaging these exact hypotheses for the B-form source.

Expected missing theorem shape:

```lean
conjugateBFormSource_limit_inputs
  : ... →
    -- all hypotheses of duhamelSourceTimeC1On_of_uniform_limit for bFormSourceCoeffs
```

Without that package, #4 is not just `exact duhamelSourceTimeC1On_of_uniform_limit ...`.

## Sorry #5 — extension `[c,T] → [0,T]`

This is **not** truly trivial in the current definitions.

The relevant structure is:

```lean
structure DuhamelSourceTimeC1On (a : ℝ → ℕ → ℝ) (lo hi : ℝ) where
  adot : ℝ → ℕ → ℝ
  hderiv : ∀ s ∈ Icc lo hi, ∀ n,
    HasDerivWithinAt (fun r => a r n) (adot s n) (Icc lo hi) s
  hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc lo hi)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s ∈ Icc lo hi, ∀ n, |a s n| ≤ envelope n
  derivBound : ℝ
  hderivBound : ∀ s ∈ Icc lo hi, ∀ n, |adot s n| ≤ derivBound
```

At `s = 0`, this requires a one-sided derivative within `[0,T]` and continuity of `adot` at `0`.

Knowing only that coefficients are `0` at `s=0` is not enough.  One must prove something like:

```lean
HasDerivWithinAt (fun r => a r n) (adot 0 n) (Icc 0 T) 0
ContinuousWithinAt (fun s => adot s n) (Icc 0 T) 0
```

and compatible envelope/derivative bounds at `0`.

Moreover, `conjugatePicardLimit` is defined by:

```lean
if 0 < t ∧ t ≤ T then limUnder ... else 0
```

so at `t=0` the profile is forced to `0`.  But as `t → 0+`, the positive-time limit is expected to approach the initial datum/semigroup trace, not necessarily `0`.  The B-form source coefficients at `0` may therefore be discontinuous from the right.  If so, a `DuhamelSourceTimeC1On ... 0 T` statement is not just nontrivial; it may be false without a patched source definition or stronger vanishing-at-zero theorem.

The committed utilities in:

```text
ShenWork/PDE/IntervalDuhamelSourceTimeC1On.lean
```

include:

```lean
DuhamelSourceTimeC1.toOn
DuhamelSourceTimeC1On.shift_zero
DuhamelSourceTimeC1On.restrict_hi
DuhamelSourceTimeC1On.const_mul
DuhamelSourceTimeC1On.add
```

but I did not find a theorem extending positive windows all the way to lower endpoint `0`.

So #5 should not be treated as trivial.  The safer route is one of:

1. keep the final consumer positive-window only (`∀ c>0, DuhamelSourceTimeC1On ... c T`), or
2. define/use a patched source that is actually time-C¹ at `0`, or
3. prove a genuine endpoint theorem showing the right derivative and `adot` continuity at `0` for the current source.

## Exact answer list

### 1. Base theorem name and status

Committed theorem:

```lean
ShenWork.Paper2.ConjugateLevel0BFormSourceOn.level0_bFormSource_duhamelSourceTimeC1On_auto
```

File:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Status: committed, but currently inherits Level0 chemDiv sorries; once Level0 is 0-sorry, this theorem should be clean.  However it is not directly callable with the short Tower comment signature; extra hypotheses/wrapper are needed.

### 2. Logistic successor theorem names and status

Committed theorem:

```lean
ShenWork.IntervalPicardSourceTimeC1OnRecursion.sourceTimeC1On_succ_of_sourceTimeC1On
```

File:

```text
ShenWork/Paper2/IntervalPicardSourceTimeC1OnRecursion.lean
```

Committed cosine-series representation theorem:

```lean
ShenWork.IntervalConjugateCosineSeries.intervalConjugateDuhamelMap_cosineSeries
```

File:

```text
ShenWork/Paper2/IntervalConjugateCosineSeries.lean
```

Status: both committed and their files state no `sorry`/`admit`/custom axioms.  But Tower #2 still needs shifted predecessor source packaging and conjugate successor representation/regularity facts before these theorems can be called.

### 3. ChemDiv successor infrastructure

No committed one-line theorem found.  This needs a successor-level analogue of Level0 chemDiv C²/time-C¹ infrastructure.  It is the same class of analysis as Level0 — resolver joint regularity, chemDiv flux/source regularity, closed representatives, H² envelope, time derivative — but generalized from heat Level0 to arbitrary conjugate iterates using the restart/Duhamel representation.

### 4. Limit passage theorem and status

Committed theorem:

```lean
ShenWork.IntervalMildPicardLimitRegularityOn.duhamelSourceTimeC1On_of_uniform_limit
```

File:

```text
ShenWork/Paper2/IntervalMildPicardLimitRegularityOn.lean
```

Status: committed and file header says no `sorry`/`admit`/custom axioms.  But Tower still must prove its convergence, uniform derivative convergence, common envelope, and common derivative-bound hypotheses for `bFormSourceCoeffs`.

### 5. Extension `[c,T] → [0,T]`

No committed theorem found.  It is not trivial from “coefficients are zero at `s=0`.”  The `DuhamelSourceTimeC1On` structure requires one-sided differentiability and continuity of the derivative field at `0`.  Given the current zero-outside/zero-at-0 definition of `conjugatePicardLimit`, this endpoint extension may be false unless a patched source or additional endpoint regularity theorem is introduced.

## Bottom-line wiring plan

After Level0 is 0-sorry, the Tower still needs the following new wrappers/packages:

1. `level0_bFormSource_duhamelSourceTimeC1On_of_DB` or equivalent wrapper extracting all arguments for `level0_bFormSource_duhamelSourceTimeC1On_auto`.
2. A conjugate successor representation/regularity package feeding `sourceTimeC1On_succ_of_sourceTimeC1On`.
3. A successor chemDiv source TimeC1On theorem for `conjugatePicardIter (n+1)`.
4. A B-form source limit-input package feeding `duhamelSourceTimeC1On_of_uniform_limit`.
5. A genuine endpoint-0 theorem or a revised final target avoiding `lo = 0`.

So the exact answer is: Level0 0-sorry closes only the Level0 analytic wall; it does **not** automatically close all five Tower sorries.
