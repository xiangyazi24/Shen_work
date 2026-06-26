# Q841 (cron2) — fastest path after Level0 is sorry-free: Tower’s 5 sorries

Static repo inspection only; I did not run a local Lean build.

## Short answer

Once Level0 is clean, only **two** Tower sorries are close to pure wiring:

```text
Line 60  zero base case       mostly wiring, but needs a wrapper / extra assumptions threaded
Line 73  logistic successor   wiring if the restart representation inputs are already available
```

The other three are not pure wiring:

```text
Line 77   chemDiv successor   needs real new iterate-level chemDiv infrastructure
Line 92   limit passage       theorem exists, but the convergence/common-bound hypotheses are new infrastructure
Line 111  extension to [0,T]  definitely new endpoint-extension lemma/data
```

Fastest path:

```text
A. Fix the Tower signature/API first: thread `hα1 : 1 ≤ p.α` and enough level-0 bounds.
B. Close line 60 with a Level0 wrapper.
C. Close line 73 by adapting the existing endpoint-inclusive logistic recursion.
D. Do line 77 as the main analytic generalization: Level0 chemDiv → arbitrary iterate chemDiv.
E. Do line 92 using `duhamelSourceTimeC1On_of_uniform_limit`, after adding coefficient/adot convergence and common-bound lemmas.
F. Do line 111 last: new [c,T]→[0,T] endpoint extension lemma; not automatic from positive windows.
```

## Tower file facts

`IntervalConjugateBFormSourceTower.lean` has the five sorries exactly as listed:

```lean
| zero =>
  intro c hc hcT
  sorry
...
have _hlog : DuhamelSourceTimeC1On ... := by
  sorry
...
have _hchem : DuhamelSourceTimeC1On ... := by
  sorry
...
noncomputable def conjBFormSourceTimeC1On_limit ... := by
  sorry
...
noncomputable def hsrcBDirect_of_data ... := by
  sorry
```

The file comments already say the base should call Level0, the logistic successor should use the successor recursion, the chemDiv successor is a genuine gap, the limit should use `duhamelSourceTimeC1On_of_uniform_limit`, and the final step is an endpoint extension.

## 1. Line 60 — zero base case

Classification: **mostly pure wiring, but current API/signature is not enough for a one-line fill.**

The intended target is:

```lean
DuhamelSourceTimeC1On
  (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c DB.T
```

The candidate theorem exists:

```lean
level0_bFormSource_duhamelSourceTimeC1On_auto
```

but its actual signature requires:

```lean
hc : 0 < c
hcT : c < T
hα : 1 ≤ p.α
ha : 0 ≤ p.a
hb : 0 ≤ p.b
hu₀_cont : Continuous u₀
hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀
hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc 0 1, 0 < intervalDomainLift (...) x
hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc 0 1, intervalDomainLift (...) x ≤ M
hG1, hG2, hUdot : uniform heat derivative bounds
```

The Tower skeleton currently has only `p`, `DB`, `huPaper`, `hu₀pos`, and `Hinf` in scope.  It can get `ha` and `hb` from `p.ha` and `p.hb`, and Level0 has helpers for heat positivity/sup from data:

```lean
level0_heat_pos_of_data
level0_heat_sup_of_data
```

But the Tower signature does **not** visibly carry `hα1 : 1 ≤ p.α`; `CM2Params` only has `p.hα : 0 < p.α`.  Also, the current Level0 file does not expose a single wrapper extracting all of `hu₀_cont`, `hu₀_bound`, `hG1`, `hG2`, and `hUdot` from `DB`/`huPaper`/`Hinf`.

So line 60 is fast, but the fastest implementation is to first add a wrapper:

```lean
theorem level0_bFormSource_duhamelSourceTimeC1On_auto_of_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀)
    (hu₀pos : PositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hα1 : 1 ≤ p.α)
    {c : ℝ} (hc : 0 < c) (hcT : c < DB.T) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c DB.T := ...
```

Then Tower line 60 becomes one call.

Verdict: **pure wiring after a small API/signature wrapper.**

## 2. Line 73 — logistic successor

Classification: **mostly wiring, but not a one-liner.**

The useful existing theorem is:

```lean
sourceTimeC1On_succ_of_sourceTimeC1On
```

Its signature is endpoint-inclusive and already designed for this job.  It consumes:

```lean
src : DuhamelSourceTimeC1On a 0 W
hshift : MapsTo (fun s => s - offset) (Icc lo hi) (Icc aτ W)
bc, hbsum, hagree
hpos, hub, hG1, hG2
hrestart
hC2cont
hprofile_joint
```

and returns the successor logistic source package:

```lean
DuhamelSourceTimeC1On
  (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

For Tower line 73, the predecessor package from `ih` is for the **B-form source coefficients** of level `n`.  That is the right source family for the conjugate restart formula, but you have to shift it to a `0 W` source using `DuhamelSourceTimeC1On.shift_zero`, choose the offset (likely `c/2`), prove the interval map facts, and supply the restart representation of `conjugatePicardIter p u₀ (n+1)` over `[c,T]`.

There is existing non-conjugate source tower machinery (`IntervalPicardSourceTower`) that already carries representation/summability/positivity/G1/G2/source packages, and there is conjugate cosine-series infrastructure in `IntervalConjugateCosineSeries.lean`.  So this should be an adapter/wiring task if the conjugate restart representation theorem is already available in the right shape.  If not, the missing piece is a small representation adapter, not new analysis.

Verdict: **wiring + restart-representation adapter.**

## 3. Line 77 — chemDiv successor

Classification: **new infrastructure; this is the main analytic blocker after Level0.**

Closing Level0 only proves the chemDiv source package for

```lean
u := conjugatePicardIter p u₀ 0
```

The successor needs the same type of package for

```lean
u := conjugatePicardIter p u₀ (n + 1)
```

That requires an iterate-level version of the Level0 chemDiv work:

```text
iterate representation / joint regularity of u
resolver value and gradient joint regularity for v = coupledChemicalConcentration p u
joint flux/source regularity
uniform H² / coefficient envelope on [c,T]
time-derivative coefficient data and bounds
```

The existing physical resolver lane gives reusable pieces, but the iterate-level data package has to be built and threaded.  This is not discharged merely by Level0 being clean.

Verdict: **real new infrastructure; hardest Tower item.**

## 4. Line 92 — limit passage

Classification: **existing theorem, but nontrivial new hypotheses; not pure wiring.**

The theorem exists and is sorry-free:

```lean
def duhamelSourceTimeC1On_of_uniform_limit
    {a : ℝ → ℕ → ℝ} {aSeq : ℕ → ℝ → ℕ → ℝ} {lo hi : ℝ}
    (hconv : ∀ s ∈ Icc lo hi, ∀ k,
      Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
    (hderiv_each : ∀ n, ∀ s ∈ Icc lo hi, ∀ k,
      HasDerivWithinAt (fun r => aSeq n r k) (adotSeq n s k) (Icc lo hi) s)
    (hadot_unif : ∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k)
      (fun s => adot s k) atTop (Icc lo hi))
    (hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Icc lo hi))
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |aSeq n s k| ≤ envelope k)
    (hderiv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |adotSeq n s k| ≤ D) :
    DuhamelSourceTimeC1On a lo hi
```

The Tower gives `hderiv_each` for every iterate once the full iterate tower is closed.  But it does **not** automatically give:

```text
coefficient convergence of bFormSourceCoeffs(iter n) → bFormSourceCoeffs(limit)
uniform convergence of adotSeq → adot on [c,T]
a common summable envelope independent of n
a common derivative bound independent of n
continuity of the limiting adot
```

Those are real convergence/uniformity lemmas, presumably from geometric convergence plus Lipschitz estimates for `bFormSourceCoeffs` and its time derivative.  They are not pure API wiring.

Verdict: **use existing theorem, but add convergence/common-bound infrastructure.**

## 5. Line 111 — extension from positive windows to `[0,T]`

Classification: **new endpoint-extension lemma; not pure wiring.**

`DuhamelSourceTimeC1On a 0 T` requires all fields on `Icc 0 T`, including:

```lean
hderiv : ∀ s ∈ Icc 0 T, ∀ n,
  HasDerivWithinAt (fun r => a r n) (adot s n) (Icc 0 T) s
hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc 0 T)
henv_bound : ∀ s ∈ Icc 0 T, ∀ n, |a s n| ≤ envelope n
hderivBound : ∀ s ∈ Icc 0 T, ∀ n, |adot s n| ≤ derivBound
```

Having packages on every `[c,T]`, `c > 0`, does not by itself prove the endpoint `s = 0` derivative or continuity of `adot` at `0`.  The Tower comment says the coefficients are defined to be `0` at `s = 0`, but that only helps the value/envelope field.  The derivative field at `0` still needs a right-derivative proof, or the endpoint-extension lemma must explicitly assume/prove the needed `s → 0+` limits.

So the final theorem should not be attempted until you have a reusable lemma with a shape like:

```lean
theorem DuhamelSourceTimeC1On.extend_zero_of_pos_windows
    (hposWin : ∀ c, 0 < c → c < T, DuhamelSourceTimeC1On a c T)
    (hval0 : ∀ k, a 0 k = 0)
    (hadot0 : ...)
    (hderiv0 : ∀ k, HasDerivWithinAt (fun r => a r k) (adot0 k) (Icc 0 T) 0)
    (hadot_cont_zero : ...)
    (henv0_bound : ...)
    (uniformEnvelopeAndDerivBound : ...) :
    DuhamelSourceTimeC1On a 0 T
```

This is not just `restrict`; `restrict_hi` only shrinks the upper endpoint and `shift_zero` shifts a closed window.  Neither creates the missing lower endpoint from a family of positive lower endpoints.

Verdict: **new endpoint infrastructure; do last.**

## Practical priority order

1. **Patch the Tower assumptions/wrapper layer.** Add `hα1 : 1 ≤ p.α` to the Tower theorem signatures, or prove it from a stronger existing assumption. Add a Level0-from-data wrapper so line 60 is a one-line call.
2. **Close line 60.** This is the quickest visible win once Level0 is clean.
3. **Close line 73.** Use `sourceTimeC1On_succ_of_sourceTimeC1On`; spend time only on interval-shift and conjugate restart-representation adapters.
4. **Build iterate chemDiv package.** Generalize the Level0 chemDiv source data to arbitrary iterates using the existing joint-C²/resolver lanes. This closes line 77.
5. **Build limit convergence package.** Then line 92 is an application of `duhamelSourceTimeC1On_of_uniform_limit`.
6. **Build lower-endpoint extension.** Then line 111 closes.

## Final classification table

| Tower sorry | Pure wiring after Level0? | Needs new infrastructure? | Notes |
|---|---:|---:|---|
| Line 60 zero base | Yes, after wrapper/signature fix | Small API wrapper only | `level0_bFormSource_duhamelSourceTimeC1On_auto` exists but needs many args, incl. `1 ≤ p.α`. |
| Line 73 logistic successor | Mostly | Small adapter if restart representation not in exact shape | Existing `sourceTimeC1On_succ_of_sourceTimeC1On` is the right theorem. |
| Line 77 chemDiv successor | No | Yes, major | Level0 clean does not give chemDiv TimeC1On for arbitrary iterates. |
| Line 92 limit passage | No | Yes, medium/major | The theorem exists; convergence/common-envelope hypotheses still need proof. |
| Line 111 extension to `[0,T]` | No | Yes, endpoint lemma | Positive-window packages do not automatically give derivative/`adot` continuity at `0`. |
