# Q2900 (shen1) — route audit for zero-slice compatibility

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target files: `ShenWork/PDE/P3MoserEnergyContinuity.lean`, `ShenWork/PDE/P3MoserRegularityProducer.lean`  
Source edit requested: none; answer file only.

## Verdict

For the **raw intended B-form Picard representative**

```lean
conjugatePicardLimit p u₀ T
```

there is not an honest upstream proof of

```lean
(conjugatePicardLimit p u₀ T) 0 = u₀
```

or of

```lean
IntervalDomainInitialPowerEnergyCompatibleAtZero u₀
  (conjugatePicardLimit p u₀ T) p0
```

In fact, for the current definition, it is false in general: `conjugatePicardLimit` is explicitly defined by

```lean
def conjugatePicardLimit (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  if 0 < t ∧ t ≤ T then
    atTop.limUnder (fun n => conjugatePicardIter p u₀ n t x)
  else 0
```

So at `t = 0` the stored slice is the zero slice, not `u₀`. For paper-positive `u₀`, the zero-slice power energy is not the initial datum power energy. Therefore the raw Picard-limit compatibility is a genuine residual/false target, not a theorem waiting to be found.

The honest non-circular source is to **change representatives** after construction: re-anchor the trajectory at `t = 0` by defining a zero-compatible wrapper

```lean
def withInitialSlice
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) :
    ℝ → intervalDomain.Point → ℝ :=
  fun t x => if t = 0 then u₀ x else u t x
```

Then prove that all positive-time/classical/global/trace facts transfer from `u` to `withInitialSlice u₀ u`, while compatibility at `0` is immediate. This is the recommended producer route.

## Why the raw Picard limit cannot be the source

The current B-form Picard construction is deliberately positive-time/deleted-right:

* `conjugatePicardLimit` is only the limit on `0 < t ∧ t ≤ T`; outside that interval it is `0`.
* `conjugatePicardLimit_initialTrace_of_conjugate_data` proves only `InitialTrace intervalDomain u₀ (conjugatePicardLimit p u₀ DB.T)`, i.e. convergence for `0 < t` small. It does not and cannot imply anything about the stored value at `t = 0`.
* `conjugateMildSolutionData_of_data` stores

```lean
u := conjugatePicardLimit p u₀ D.T
```

and all its fields (`hmild`, `hbound`, `hnonneg`, `hpos`, `hcont`, `hmeas`) are quantified on `0 < t`; they do not require a zero slice.

So for raw `conjugatePicardLimit`, compatibility should **not** be added as an assumed field or proved by trace. It is false for the present representative.

## Files and search terms to inspect

Use these exact search terms/files to confirm and wire the route.

### Core Picard representative

File:

```text
ShenWork/Paper2/IntervalConjugatePicard.lean
```

Search terms:

```text
conjugatePicardLimit
if 0 < t ∧ t ≤ T then
else 0
conjugateMildSolutionData_of_data
IntervalConjugateMildSolution_of_data
```

Important declarations:

```lean
def conjugatePicardLimit
structure ConjugateMildSolutionData
def conjugateMildSolutionData_of_data
theorem intervalConjugateMildSolution_exists_from_data
```

### Initial trace for the B-form fixed point

File:

```text
ShenWork/Paper2/IntervalBFormInitialTrace.lean
```

Search terms:

```text
intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
conjugatePicardLimit_initialTrace_of_conjugate_data
InitialTrace intervalDomain u₀
```

Important result:

```lean
theorem conjugatePicardLimit_initialTrace_of_conjugate_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (DB : ConjugateMildExistenceData p u₀) :
    InitialTrace intervalDomain u₀ (conjugatePicardLimit p u₀ DB.T)
```

This is the analytic deleted-right source. It is not zero-slice compatibility.

### B-form end-to-end bridge

File:

```text
ShenWork/Paper2/IntervalBFormEndToEnd.lean
```

Search terms:

```text
BFormBankedInputs
conjugateAsGradientMildSolutionData
BFormSpectralFrontier
gradientInitialApproach_of_BForm
```

This file packages the B-form fixed point as the gradient mild solution data and transfers the B-form initial approach. Again, the data are positive-time oriented.

### Local/global existence skeletons

Files:

```text
ShenWork/PDE/IntervalDomainExistence.lean
ShenWork/Paper2/IntervalDomainGlobalWellposed.lean
```

Search terms:

```text
IsMildSolutionData
localExistence_of_isMildSolutionData
localExistence
InitialTrace intervalDomain u₀ u
reachableClassicalHorizonSet
GlobalSolutionGluingFromReachability
```

These currently expose `InitialTrace`, not `u 0 = u₀`.

### Moser regularity consumer

File:

```text
ShenWork/PDE/P3MoserRegularityProducer.lean
```

Search terms:

```text
IntervalDomainIntegratedMoserGlobalClassicalRegularityData
atZero : IntervalDomainInitialPowerEnergyContinuityAtZero
intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
```

This is where the new wrapper should be consumed.

## Recommended non-circular producer route

### Step 1: define zero re-anchoring

Put this in `P3MoserEnergyContinuity.lean` or a small reusable interval-domain utility file.

```lean
def intervalDomainWithInitialSlice
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) :
    ℝ → intervalDomain.Point → ℝ :=
  fun t x => if t = 0 then u₀ x else u t x
```

### Step 2: compatibility is immediate

```lean
theorem intervalDomain_initialPowerEnergyCompatibleAtZero_withInitialSlice
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} {p0 : ℝ} :
    IntervalDomainInitialPowerEnergyCompatibleAtZero u₀
      (intervalDomainWithInitialSlice u₀ u) p0 := by
  intro p hp
  simp [intervalDomainWithInitialSlice]
```

If the local `simp` does not unfold the integral body deeply enough:

```lean
  change intervalDomain.integral
      (fun x => (if (0 : ℝ) = 0 then u₀ x else u 0 x) ^ p) = _
  simp
```

### Step 3: initial trace is preserved

Because `InitialTrace` only quantifies `0 < t`, the re-anchored trajectory agrees with `u` on all traced times.

```lean
theorem intervalDomain_initialTrace_withInitialSlice
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (htrace : InitialTrace intervalDomain u₀ u) :
    InitialTrace intervalDomain u₀ (intervalDomainWithInitialSlice u₀ u) := by
  intro ε hε
  rcases htrace ε hε with ⟨δ, hδ, hsmall⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  simpa [intervalDomainWithInitialSlice, ht_ne] using hsmall t ht0 htδ
```

### Step 4: classical/global solution is preserved

This is the essential non-circular bridge: the classical solution predicates only inspect `0 < t < T`, so the zero-slice replacement is invisible.

Recommended theorem statements:

```lean
theorem intervalDomain_classical_withInitialSlice
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IsPaper2ClassicalSolution intervalDomain params T
      (intervalDomainWithInitialSlice u₀ u) v
```

```lean
theorem intervalDomain_globalClassical_withInitialSlice
    {params : CM2Params}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IsPaper2GlobalClassicalSolution intervalDomain params
      (intervalDomainWithInitialSlice u₀ u) v
```

Proof route for the local theorem:

* Use `IsPaper2ClassicalSolution.of_components`.
* `hT := hsol.T_pos`.
* `positivity`, `v_nonneg`, `pde_u`, `pde_v`, `neumann` transfer by rewriting at strict positive `t`:

```lean
have ht_ne : t ≠ 0 := ne_of_gt ht0
simp [intervalDomainWithInitialSlice, ht_ne]
```

* For `D.classicalRegularity T ...`, because `intervalDomainClassicalRegularity` contains time derivatives of `intervalDomainLift ((intervalDomainWithInitialSlice u₀ u) s)` at strict interior times, the proof needs an eventual equality near each interior time `t`. The pattern is:

```lean
have heq : (fun s : ℝ => intervalDomainWithInitialSlice u₀ u s x) =ᶠ[𝓝 t]
    (fun s : ℝ => u s x) := by
  filter_upwards [Ioi_mem_nhds ht0] with s hs
  have hs_ne : s ≠ 0 := ne_of_gt hs
  simp [intervalDomainWithInitialSlice, hs_ne]
```

For lifted fields:

```lean
have heqLift : (fun s : ℝ => intervalDomainLift ((intervalDomainWithInitialSlice u₀ u) s) y)
    =ᶠ[𝓝 t]
    (fun s : ℝ => intervalDomainLift (u s) y) := by
  filter_upwards [Ioi_mem_nhds ht0] with s hs
  have hs_ne : s ≠ 0 := ne_of_gt hs
  simp [intervalDomainWithInitialSlice, hs_ne]
```

Then use `EventuallyEq.deriv_eq`, `ContinuousOn.congr`, and the fact that all time domains are subsets of `Ioo 0 T`. Spatial regularity at a fixed strict positive `t` is just definitional rewriting with `t ≠ 0`.

This proof is a little tedious but honest and local. It is not new PDE analysis.

### Step 5: endpoint power-energy continuity wrapper

Once re-anchoring exists, the wrapper you want is straightforward:

```lean
theorem intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialPowerEnergyContinuityAtZero
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  have htrace' : InitialTrace intervalDomain u₀ (intervalDomainWithInitialSlice u₀ u) :=
    intervalDomain_initialTrace_withInitialSlice htrace
  have hglobal' : IsPaper2GlobalClassicalSolution intervalDomain params
      (intervalDomainWithInitialSlice u₀ u) v :=
    intervalDomain_globalClassical_withInitialSlice hglobal
  have hlim : IntervalDomainInitialTracePowerEnergyTendsto u₀
      (intervalDomainWithInitialSlice u₀ u) T p0 :=
    intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
      hT htrace' hdatum hglobal'
  have hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀
      (intervalDomainWithInitialSlice u₀ u) p0 :=
    intervalDomain_initialPowerEnergyCompatibleAtZero_withInitialSlice
  exact intervalDomain_initialPowerEnergyContinuityAtZero_of_traceTendsto_compat
    hlim hcompat
```

## How this feeds `P3MoserRegularityProducer.lean`

The current producer data structure

```lean
structure IntervalDomainIntegratedMoserGlobalClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
  gradientTimeIntegrable : ...
```

can remain as-is. Add a constructor/wrapper whose `u` is the re-anchored representative:

```lean
structure IntervalDomainIntegratedMoserGlobalClassicalRegularityDataAnchored
    (u₀ : intervalDomain.Point → ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop where
  hT : 0 < T
  htrace : InitialTrace intervalDomain u₀ u
  hdatum : PaperPositiveInitialDatum intervalDomain u₀
  hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

But since `params` is needed in `hglobal`, the actual structure should include `(params : CM2Params)` as an argument.

A simpler theorem-level producer is preferable:

```lean
theorem intervalDomain_globalClassicalRegularityData_of_trace_paperPositive_anchored
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgrad :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    IntervalDomainIntegratedMoserGlobalClassicalRegularityData
      (intervalDomainWithInitialSlice u₀ u) T p0
```

This keeps gradient integrability as the remaining true analytic field, while endpoint continuity is no longer a residual.

## What not to do

Do not add a field to `ConjugateMildExistenceData` asserting raw `conjugatePicardLimit 0 = u₀`; it contradicts the current definition.

Do not try to derive compatibility from `InitialTrace`; that is the Q2892/Q2893 point and remains false.

Do not change `conjugatePicardLimit` itself unless you are prepared to update all existing proofs that use its `else 0` behavior. Re-anchoring via a wrapper is lower-risk and faithful: classical/PDE/mild statements are positive-time statements, and the Moser endpoint regularity is exactly the place where the stored zero representative matters.

## Concise recommendation

1. Keep `IntervalDomainInitialPowerEnergyCompatibleAtZero` as an honest compatibility notion.
2. Do not expect raw `conjugatePicardLimit` to satisfy it.
3. Add `intervalDomainWithInitialSlice u₀ u` and transfer positive-time/global-classical/trace facts to it.
4. Use the re-anchored trajectory as the `u` argument in the Moser regularity producer whenever closed-time energy continuity is required.

That gives a non-circular producer of `atZero`:

```text
InitialTrace + PaperPositiveInitialDatum + GlobalClassical(raw u)
  + re-anchor u at 0
  ⇒ InitialTrace + GlobalClassical(anchored u) + compatibility by rfl
  ⇒ IntervalDomainInitialPowerEnergyContinuityAtZero(anchored u)
```

The only remaining regularity residual in `P3MoserRegularityProducer.lean` should then be genuine gradient time-integrability/continuity, not initial power-energy continuity.
