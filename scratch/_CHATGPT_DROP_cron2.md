# Q800 (cron2) — Tower file wiring audit

Static repo inspection only; I did not run a Lean build.

Files inspected:

```text
ShenWork/Paper2/IntervalConjugateBFormSourceTower.lean
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
ShenWork/Paper2/IntervalPicardSourceTimeC1OnRecursion.lean
ShenWork/Paper2/IntervalConjugateCosineSeries.lean
ShenWork/Paper2/IntervalMildPicardLimitRegularityOn.lean
ShenWork/PDE/IntervalDuhamelSourceTimeC1On.lean
ShenWork/Paper2/IntervalBFormSpectralHtime.lean
```

## Tower state

`IntervalConjugateBFormSourceTower.lean` is indeed only a skeleton right now.  The five `sorry` are:

```text
line ~60  : zero base case
line ~73  : logistic successor
line ~77  : chemDiv successor
line ~92  : limit passage
line ~111 : extension from positive windows to [0,T]
```

## Line 60: zero base case / `level0_bFormSource_duhamelSourceTimeC1On_auto`

The exact signature of `level0_bFormSource_duhamelSourceTimeC1On_auto` is:

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

It is not currently callable from the Tower with only:

```lean
p DB hu₀pos hc hcT.le
```

The comment in the Tower file is stale/optimistic.  The current function requires the full heat-window data: `hα`, `ha`, `hb`, `hu₀_cont`, coefficient bound, positivity, sup bound, two spatial derivative bounds, and a heat time-derivative bound.

There are two helper theorems in the same Level0 file:

```lean
theorem level0_heat_pos_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (_D : ConjugateMildExistenceData p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {c : ℝ} (hc : 0 < c) (_hcT : c ≤ _D.T) :
    ∀ σ ∈ Icc c _D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x
```

and

```lean
theorem level0_heat_sup_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    {c : ℝ} (hc : 0 < c) (hcT : c ≤ D.T) :
    ∀ σ ∈ Icc c D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ D.M
```

But I did not find a finished wrapper that extracts **all** arguments needed by `level0_bFormSource_duhamelSourceTimeC1On_auto` from `DB`, `huPaper`, `hu₀pos`, and `Hinf`.

Practical conclusion: after Level0 is sorry-free, the base case is close, but not a one-line direct call unless you first add a convenience wrapper with the Tower’s exact inputs.  The shape should be something like:

```lean
noncomputable def level0_bFormSource_duhamelSourceTimeC1On_of_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀)
    (hu₀pos : PositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    {c : ℝ} (hc : 0 < c) (hcT : c < DB.T) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c DB.T := ...
```

That wrapper must source or assume:

```text
1 ≤ p.α
hu₀ continuity
initial coefficient bound M₀
G1/G2 bounds for S(t)u₀ on [c,T]
heat time-derivative bound Udot
```

Note: `CM2Params` has `p.ha` and `p.hb`, but only `p.hα : 0 < p.α`, not `1 ≤ p.α`.  So `hα : 1 ≤ p.α` must come from an extra hypothesis or a stronger parameter bundle.

## Line 73: logistic successor

The successor theorem exists, but it is not a two-argument one-liner.  It is:

```lean
noncomputable def sourceTimeC1On_succ_of_sourceTimeC1On
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ M G1 G2 : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (hlohi : lo ≤ hi)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi,
      Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (hrestart : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hC2cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

So the logistic successor is **mostly wiring** once these data are available, but it is not just `ih + intervalConjugateDuhamelMap_cosineSeries`.

The predecessor package from the Tower has shape:

```lean
ih (c / 2) ... :
  DuhamelSourceTimeC1On
    (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) (c / 2) DB.T
```

while the successor theorem expects:

```lean
src : DuhamelSourceTimeC1On a 0 W
```

So one wiring step is to use `DuhamelSourceTimeC1On.shift_zero` with `offset := c / 2`, `W := DB.T - c / 2`, and a shifted `a`.

Also, `intervalConjugateDuhamelMap_cosineSeries` exists, but its signature consumes a **global** `DuhamelSourceTimeC1`, not an `On` package:

```lean
theorem intervalConjugateDuhamelMap_cosineSeries
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {t x M₀ : ℝ}
    (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p u))
    (hB_int : IntervalIntegrable ...)
    (hlog_int : IntervalIntegrable ...)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t, ... ) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
```

Therefore, with only windowed `DuhamelSourceTimeC1On`, the Tower may need either:

```text
- a global clamped source witness agreeing on the read window, or
- an `On` analogue of intervalConjugateDuhamelMap_cosineSeries.
```

Conclusion for line 73: it is pure wiring only after the representation/restart facts, shifted source package, positivity/sup/G1/G2, C² slice continuity, and joint profile continuity are already packaged.  The current Tower skeleton does not yet carry all of these facts.

## Line 77: chemDiv successor

This is the same **kind** of gap as Level0, but not a direct reuse of the Level0 theorem.

Level0 builds chemDiv source data for:

```lean
coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0)
```

via the heat semigroup’s positive-time smoothing.  The successor needs:

```lean
coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))
```

So structurally it needs the same fields:

```text
summable envelope for chemDiv coefficients
HasDerivWithinAt for chemDiv coefficient time derivative
ContinuousOn of adot
uniform derivative bound
```

but for an arbitrary iterate `n+1`, using its restart/cosine representation and C²/joint regularity rather than the heat semigroup-specific Level0 route.

Conclusion: line 77 is not mere boilerplate.  It is the same analytic/regularity gap as Level0, generalized from the heat semigroup level to every conjugate iterate.  A likely useful target is a generic theorem/structure:

```lean
ConjIterChemDivSourceData p u₀ n c T
  → DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n)) c T
```

with Level0 as `n = 0` and successor using the restart representation.

## Line 92: limit passage / `duhamelSourceTimeC1On_of_uniform_limit`

The theorem exists in:

```text
ShenWork/Paper2/IntervalMildPicardLimitRegularityOn.lean
```

Exact signature:

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

For the Tower limit passage, instantiate:

```lean
aSeq n := bFormSourceCoeffs p (conjugatePicardIter p u₀ n)
a      := bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)
lo     := c
hi     := DB.T
```

It needs:

```text
1. Pointwise coefficient convergence on [c,T]
   bFormSourceCoeffs(iter n) s k → bFormSourceCoeffs(limit) s k.

2. Per-iterate derivative data
   from conjBFormSourceTimeC1OnUpTo_all p DB ... n c.

3. Uniform convergence of derivative coefficient families on [c,T]
   for every mode k.

4. ContinuousOn of the limit derivative family.

5. A common summable envelope, independent of n and s ∈ [c,T].

6. A common scalar derivative bound, independent of n, s, k.
```

The existing tower of iterate packages gives item 2 only.  Items 1, 3, 4, 5, and 6 are separate convergence/uniform-envelope facts.  The comment in the Tower file is accurate here: this is not just an application of the tower; it also needs Lipschitz/continuity of `bFormSourceCoeffs` under the iterate convergence and uniform derivative estimates.

## Line 111: extension from all positive lower endpoints to `[0,T]`

I did not find a theorem named:

```text
DuhamelSourceTimeC1On_of_forall_pos_lo
of_forall_pos_lo
forall_pos_lo
```

or an obvious equivalent.

The available `DuhamelSourceTimeC1On` structural tools are:

```lean
def DuhamelSourceTimeC1.toOn
    (src : DuhamelSourceTimeC1 a) (lo hi : ℝ) (hlo : 0 ≤ lo) :
    DuhamelSourceTimeC1On a lo hi
```

```lean
def DuhamelSourceTimeC1On.shift_zero
    (src : DuhamelSourceTimeC1On a offset (offset + W)) :
    DuhamelSourceTimeC1On (fun s n => a (offset + s) n) 0 W
```

```lean
def DuhamelSourceTimeC1On.restrict_hi
    (src : DuhamelSourceTimeC1On a lo hi) (hhi' : hi' ≤ hi) :
    DuhamelSourceTimeC1On a lo hi'
```

plus `const_mul` and `add`.

There is **no lower-endpoint extension** theorem in `IntervalDuhamelSourceTimeC1On.lean`.

Conclusion: line 111 is not currently solved by an existing lemma.  To produce:

```lean
DuhamelSourceTimeC1On
  (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
```

from packages on every `[c, DB.T]`, you need to add a new theorem, or construct the structure directly at `lo = 0`.

A new theorem would need hypotheses beyond “for every `c > 0`”, because `DuhamelSourceTimeC1On` requires data **at the endpoint `s = 0`**:

```lean
hderiv : ∀ s ∈ Icc 0 T, ∀ n,
  HasDerivWithinAt (fun r => a r n) (adot s n) (Icc 0 T) s
hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc 0 T)
henv_bound : ∀ s ∈ Icc 0 T, ∀ n, |a s n| ≤ envelope n
hderivBound : ∀ s ∈ Icc 0 T, ∀ n, |adot s n| ≤ derivBound
```

So any `of_forall_pos_lo` lemma must also supply or prove the `s = 0` derivative value, continuity into `0`, and the envelope/derivative bounds at `0`.  The Tower comment’s proposed direct construction at `s = 0` is the right route, but it is not currently packaged.

## Overall verdict

```text
line 60 zero base:
  Level0 theorem exists, but current signature is not directly callable from Tower.
  Add a DB/huPaper/hu₀pos/Hinf wrapper or pass all required heat-window bounds.

line 73 logistic successor:
  The core theorem exists (`sourceTimeC1On_succ_of_sourceTimeC1On`).
  It is mostly wiring only after shifted source, restart representation,
  positivity/sup/G1/G2, C²-continuity, and joint-continuity facts are available.
  `intervalConjugateDuhamelMap_cosineSeries` is global-source, so check whether
  a clamped/global witness or an On analogue is needed.

line 77 chemDiv successor:
  Same analytic gap as Level0, generalized to iterates.  Not pure wiring.

line 92 limit:
  `duhamelSourceTimeC1On_of_uniform_limit` exists and needs pointwise coefficient
  convergence, per-iterate derivative packages, uniform derivative convergence,
  limit derivative continuity, common summable envelope, and common derivative bound.

line 111 extension to [0,T]:
  No existing `of_forall_pos_lo` found.  Need a new endpoint-extension theorem or
  direct construction of `DuhamelSourceTimeC1On ... 0 T`, including endpoint `s=0` data.
```
