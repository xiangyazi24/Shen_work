# Q1532 (cron1) -- consumers of `FlooredSourceTimeData.zerothBound/laplBound`

Repository: `xiangyazi24/Shen_work`  
Committed on branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only inspection. I did not run Lean locally and did not use Python/sandbox.

GitHub code search queries used:

```text
H.zerothBound H.laplBound
zerothBound laplBound FlooredSourceTimeData
```

The default/indexed repo matches the Q1532 premise: `FlooredSourceTimeData` has positive-time fields `∀ t, 0 < t → ...`. The delivery branch `chatgpt-scratch` still has the older all-real-time version from Q1518, so this report focuses on the current indexed/default code surface and notes the branch mismatch.

## Counts

Exact direct reads of `H.zerothBound` / `H.laplBound` are in **2 files**:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

Only **1 file directly reads fields from a `FlooredSourceTimeData` value**:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

`IntervalFlooredSourceTimeDataIterate.lean` reads same-named fields from `IterateSourceTimeData` and forwards them into a `FlooredSourceTimeData`; it is an upstream adapter/producer.

A broader grep for `zerothBound laplBound FlooredSourceTimeData` returns **5 files**:

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
UNDERSTANDING.md
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

Relevant Lean files are the first, third, and fourth. `UNDERSTANDING.md` is documentation. `IntervalHeatSemigroupHighRegularity.lean` is not a field consumer; it imports the heat-semigroup floored-source file and contains positive-time cutoff/window regularity infrastructure.

## Direct / relevant occurrences

### `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean`

Field signatures are positive-time global, not windowed:

```text
IntervalPhysicalSourceTimeC2Concrete.lean:104-107
```

```lean
zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
  |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D
laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
  |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

Direct field read in `builtEs`:

```text
IntervalPhysicalSourceTimeC2Concrete.lean:247-252
```

```lean
if hi : i ≤ 2 then
  (if k = 0 then Classical.choose (H.zerothBound i hi)
   else Classical.choose (H.laplBound i hi) / ((k:ℝ) * Real.pi) ^ 2)
else 0
```

This extracts one time-independent constant for each `(i,k)` envelope. If the bound becomes window-dependent, `builtEs` must also become window-dependent, e.g. `builtEsOn H c T ...`.

Direct field use in `srcTimeCoeff_bound`:

```text
IntervalPhysicalSourceTimeC2Concrete.lean:257-268
```

```lean
theorem srcTimeCoeff_bound ... (t : ℝ) (hi : i ≤ 2) (ht : 0 < t) :
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k := by
...
  · exact (Classical.choose_spec (H.zerothBound i hi)).2 t ht
  · exact (Classical.choose_spec (H.laplBound i hi)).2 t ht k hk
```

This is the decisive direct consumer. It asks for arbitrary positive `t`; it is not tied to a fixed `[c,T]` window.

`physicalSourceTimeC2_of_floored` tries to produce global `PhysicalSourceTimeC2`:

```text
IntervalPhysicalSourceTimeC2Concrete.lean:276-293
```

```lean
PhysicalSourceTimeC2 p u (builtEs H) where
  src_contDiff k := by
    -- positive-time data gives ContDiffAt at every t > 0; global extension is separate
    sorry
  src_bound i k t hi := by
    -- t > 0 uses srcTimeCoeff_bound; t ≤ 0 needs a separate envelope argument
    sorry
```

So the downstream target is still global in `t`, not windowed.

### `ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean`

This file is an adapter from `IterateSourceTimeData` to `FlooredSourceTimeData`.

Upstream same-named fields are currently all-time:

```text
IntervalFlooredSourceTimeDataIterate.lean:139-144
```

```lean
zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ...
laplBound   : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), ...
```

Forwarding site:

```text
IntervalFlooredSourceTimeDataIterate.lean:167-171
```

```lean
zerothBound i hi := by
  obtain ⟨D, hD, hb⟩ := H.zerothBound i hi
  exact ⟨D, hD, fun t _ht => hb t⟩
laplBound i hi := by
  obtain ⟨M, hM, hb⟩ := H.laplBound i hi
  exact ⟨M, hM, fun t _ht k hk => hb t k hk⟩
```

This will need to change if `FlooredSourceTimeData` becomes windowed. Also, unless `IterateSourceTimeData` is weakened/windowed too, the same singular `t → 0+` problem has just moved upstream.

This file also depends on `builtEs (flooredSourceTimeData_of_iterate H)` in summability hypotheses:

```text
IntervalFlooredSourceTimeDataIterate.lean:181-188
```

That is not a direct field read, but it depends on `builtEs`, which currently uses time-independent constants chosen from the Floored fields.

### `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`

This is a heat-semigroup producer of `FlooredSourceTimeData`, not a downstream field reader.

It currently takes positive-time global bound hypotheses:

```text
IntervalHeatSemigroupFlooredSourceTimeData.lean:650-684
```

and assigns them directly:

```text
IntervalHeatSemigroupFlooredSourceTimeData.lean:692-693
```

```lean
zerothBound := hzerothBound
laplBound := hlaplBound
```

This is exactly where the heat-semigroup route asks for the impossible uniform-in-all-positive-time envelopes for `i = 1,2`.

## Downstream time-domain consumers

These files do not directly read `FlooredSourceTimeData.zerothBound/laplBound`, but they determine whether windowing is a safe drop-in replacement.

### `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean`

`PhysicalSourceTimeC2` is global in `t`:

```text
IntervalPhysicalResolverDataConcrete.lean:107-114
```

```lean
src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
```

`resolverTimeCoeff_bound` also expects a global source bound:

```text
IntervalPhysicalResolverDataConcrete.lean:145-156
```

`physicalResolverJointC2Data_of_floor` forwards `H.src_bound` into resolver coefficient bounds:

```text
IntervalPhysicalResolverDataConcrete.lean:165-177
```

### `ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean`

`PhysicalResolverJointC2Data` is global in `t`:

```text
IntervalResolverJointC2PhysicalConcrete.lean:90-94
```

```lean
coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
```

Joint series assemblers consume arbitrary-time coefficient bounds:

```text
IntervalResolverJointC2PhysicalConcrete.lean:122-127
IntervalResolverJointC2PhysicalConcrete.lean:145-149
IntervalResolverJointC2PhysicalConcrete.lean:172-174
```

Examples:

```lean
(fun i k t hi => H.coeff_bound i k t hi)
...
have h0 := H.coeff_bound 0 k q.1 (by norm_num)
```

Again, this is not expressed as a fixed `[c,T]` window.

## Safety verdict for Fix Option A

Changing only `FlooredSourceTimeData.zerothBound/laplBound` to windowed fields is **not safe as a local/drop-in edit**.

Reason: the direct consumer `srcTimeCoeff_bound` is quantified over arbitrary positive time:

```lean
(t : ℝ) (ht : 0 < t)
```

and the downstream structures are global:

```lean
∀ (i k : ℕ) (t : ℝ), i ≤ 2 → ...
```

So the consumers do **not** currently only evaluate at a fixed positive-time window `[c,T]`.

Windowing is mathematically right, but it must be propagated through the API:

```text
FlooredSourceTimeData
  -> builtEs
  -> PhysicalSourceTimeC2
  -> PhysicalResolverJointC2Data
  -> bounded-weight joint series / FAC producers
```

A safe shape would add a windowed envelope, e.g.

```lean
zerothBoundOn : ∀ i, i ≤ 2 → ∀ c T, 0 < c → c ≤ T →
  ∃ D, 0 ≤ D ∧ ∀ t ∈ Icc c T, ...

laplBoundOn : ∀ i, i ≤ 2 → ∀ c T, 0 < c → c ≤ T →
  ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc c T, ∀ k, 1 ≤ k → ...
```

then replace `builtEs` by a windowed `builtEsOn H c T ...`, and replace the global `src_bound`/`coeff_bound` surfaces by windowed or positive-time-local versions.

For local regularity at a positive time `τ`, one can choose a window such as `c = τ / 2` and `T = τ + δ`, but the current structures do not carry this window.

## Final answer

Direct Floored bound consumption is concentrated in one file, but the downstream API is global. Therefore Fix Option A is viable only as an API-wide windowing refactor, not as a field-signature-only patch.
