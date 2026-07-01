# Q2848 shen2: relative-Moser integration route audit

Repo target: `xiangyazi24/Shen_work`, Lean 4, default branch `main`.

Files/APIs inspected directly:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/Paper2/IntervalDomainMoserClosure.lean
```

Scope honored: no proposed edits to Zinan-owned

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
```

## Current state

The pointwise predicate is exactly:

```lean
def RelativeMoserInterpolationBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
    ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u t x) ^ p)
```

So it is **strict interior only**: it gives a pointwise inequality only for

```lean
0 < t ∧ t < T
```

`P3MoserIntegratedClosure.lean` already has the strict interior integration lemma with a **pointwise current-energy bound**:

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
```

and its gradient-bound variant:

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

Those require:

```lean
hab : a ≤ b
ha : 0 < a
hb : b < T
hZ_int : IntervalIntegrable Z volume a b
hG_int : IntervalIntegrable G volume a b
hY_le : ∀ s ∈ Set.Icc a b, Y s ≤ M
```

They are correct for high-excursion windows already encoded in this file, because those windows carry strict fields:

```lean
IntegratedMoserPrecrossingIntervalData.ha_pos : 0 < a
IntegratedMoserPrecrossingIntervalData.hb_lt : b < T
```

The needed new shape is different: it wants a time-integrated lower-order term

```lean
Ceps * ∫ max 1 Y_p(s)
```

rather than `(b-a) * (Ceps * M)`.

## 1. Strongest provable now: strict interior `max 1 Y` version

This is the next small lemma Codex should add to `P3MoserIntegratedClosure.lean`. Insert it after

```lean
intervalIntegrable_max_one_of_intervalIntegrable
```

so that `integratedMoserEnergy`, `integratedMoserGradientEnergy`, and the max-integrability helper are already in scope.

```lean
/-- Strict-interior integrated relative-Moser estimate with the lower-order
current energy kept as `∫ max 1 Y_p`.

This is the strongest direct consequence of
`RelativeMoserInterpolationBefore`: the interval must satisfy `0 < a` and
`b < T`, because the pointwise relative interpolation hypothesis is only stated
for strict interior times. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s)
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s)
        volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s)
        volume a b) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
        eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
        Ceps * (∫ s in a..b,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  have hYmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
        volume a b :=
    intervalIntegrable_max_one_of_intervalIntegrable hY_int
  have hR_int :
      IntervalIntegrable
        (fun s =>
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s)
        volume a b :=
    (hG_int.const_mul eps).add (hY_int.const_mul Ceps)
  have hpoint :
      ∀ s ∈ Set.Icc a b,
        integratedMoserEnergy D u (p + rho) s ≤
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsT : s < T := lt_of_le_of_lt hs.2 hb
    simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
      hrel_eps s hs0 hsT
  have hmono :
      ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
        ∫ s in a..b,
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s :=
    intervalIntegral.integral_mono_on hab hZ_int hR_int hpoint
  have hR_eq :
      (∫ s in a..b,
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s) =
        eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
          Ceps * (∫ s in a..b, integratedMoserEnergy D u p s) := by
    rw [intervalIntegral.integral_add
      (hG_int.const_mul eps) (hY_int.const_mul Ceps)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hY_le_max_point :
      ∀ s ∈ Set.Icc a b,
        integratedMoserEnergy D u p s ≤
          max (1 : ℝ) (integratedMoserEnergy D u p s) := by
    intro s _hs
    exact le_max_right (1 : ℝ) (integratedMoserEnergy D u p s)
  have hY_le_max_int :
      ∫ s in a..b, integratedMoserEnergy D u p s ≤
        ∫ s in a..b,
          max (1 : ℝ) (integratedMoserEnergy D u p s) :=
    intervalIntegral.integral_mono_on hab hY_int hYmax_int hY_le_max_point
  have hscaled :
      Ceps * (∫ s in a..b, integratedMoserEnergy D u p s) ≤
        Ceps * (∫ s in a..b,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) :=
    mul_le_mul_of_nonneg_left hY_le_max_int hCeps_nonneg
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  rw [hR_eq] at hmono
  linarith
```

Notes:

* This theorem is purely a wrapper around `RelativeMoserInterpolationBefore` plus interval integration.
* It does not need `Y ≥ 0`; the pointwise comparison `Y ≤ max 1 Y` is unconditional.
* It still needs `ha : 0 < a` and `hb : b < T`.
* It does not need `hYmax_int` as a user hypothesis because `intervalIntegrable_max_one_of_intervalIntegrable` already derives it from `hY_int`.

## 2. Strict-interior all-window version matching the desired input shape

If the downstream wrapper can be changed to strict interior windows, use this shape:

```lean
/-- Strict-interior all-window version of the integrated relative-Moser estimate.
This is exactly the desired `hrelInt` shape, but only on windows contained in
`(0,T)`. -/
theorem relativeMoser_hrelInt_strictInterior
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hrho_nonneg : 0 ≤ rho) :
    ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
      ∃ Ceps, 0 ≤ Ceps ∧
        ∀ a b, a ≤ b → 0 < a → b < T →
          ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
            eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
            Ceps * (∫ s in a..b,
              max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  intro p hp eps heps
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, _hrel_eps⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  intro a b hab ha hb
  have hT_nonneg : 0 ≤ T := le_trans ha.le (le_of_lt hb)
  have hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T := by
    intro s hs
    rw [Set.uIcc_of_le hT_nonneg]
    exact ⟨le_trans ha.le hs.1, le_trans hs.2 (le_of_lt hb)⟩
  have hp_rho : p0 ≤ p + rho := by linarith
  have hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume a b :=
    hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
  have hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume a b :=
    hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
  have hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s) volume a b :=
    hreg.power_intervalIntegrable_of_Icc hp hab hsub
  exact
    (relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (eps := eps)
      hrel hp heps hab ha hb hZ_int hG_int hY_int).choose_spec.2
```

The last line above is skeleton-level; in a real proof, avoid `choose_spec.2` directly by `rcases` on the previous lemma and reuse the resulting `Ceps`. Since this theorem chooses `Ceps` before `a b`, the constant must be the same for all windows. That is okay: `Ceps` comes from `hrel p hp eps heps`, independent of the window.

A more compile-oriented implementation would inline the proof of the first lemma after choosing `Ceps`, rather than calling the existential-returning lemma for each window and then needing proof that the chosen constant is the same.

## 3. Closed-window version: not available from current pointwise API without an endpoint/a.e. bridge

The desired input shape quantifies closed windows:

```lean
∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T, ...
```

This includes windows with `t1 = 0` and/or `t2 = T`. But `RelativeMoserInterpolationBefore` only applies at times satisfying `0 < s` and `s < T`.

Mathematically, endpoint failure should be harmless for interval integrals: the endpoint set `{0,T}` is null. In Lean, however, the current repository integration lemma

```lean
intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
```

and the existing relative-Moser integration lemma use

```lean
intervalIntegral.integral_mono_on
```

which asks for pointwise comparison on `Set.Icc a b`. That is why the current in-repo relative integration lemmas require strict window hypotheses:

```lean
ha : 0 < a
hb : b < T
```

So the closed-window version is not a direct consequence of the currently packaged repository APIs. The missing piece is not a PDE estimate; it is an endpoint/a.e. transport layer.

## 4. Exact endpoint/a.e. frontier to add for closed windows

If the compiled wrapper really requires closed windows, introduce this a.e. version in `P3MoserIntegratedClosure.lean`:

```lean
/-- A.e. relative-Moser interpolation on closed time windows.

This is the exact endpoint bridge missing between the pointwise strict-interior
`RelativeMoserInterpolationBefore` and closed-window time integration. -/
def RelativeMoserInterpolationBeforeClosedWindowAE
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
    ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        (∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)),
          integratedMoserEnergy D u (p + rho) s ≤
            eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s)
```

Then add the closed-window integration theorem:

```lean
/-- Closed-window integrated relative-Moser estimate from an a.e. closed-window
relative interpolation frontier. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_closedWindow_currentEnergy_maxOne_of_ae
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p t1 t2 eps : ℝ}
    (hrelAE : RelativeMoserInterpolationBeforeClosedWindowAE D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s)
        volume t1 t2)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s)
        volume t1 t2)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s)
        volume t1 t2) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s ≤
        eps * (∫ s in t1..t2, integratedMoserGradientEnergy D u p s) +
        Ceps * (∫ s in t1..t2,
          max (1 : ℝ) (integratedMoserEnergy D u p s))
```

Proof strategy:

1. `rcases hrelAE p hp eps heps with ⟨Ceps, hCeps_nonneg, hAE⟩`.
2. Set `Y`, `G`, `Z`, `R := fun s => eps * G s + Ceps * Y s`.
3. Prove `R` interval-integrable from `hG_int` and `hY_int`.
4. Use an a.e. interval-integral monotonicity lemma to get
   ```lean
   ∫ Z ≤ ∫ R
   ```
   from `hAE t1 ht1 t2 ht2`.
5. Rewrite `∫ R = eps * ∫ G + Ceps * ∫ Y`.
6. Use `Y ≤ max 1 Y` pointwise and `Ceps ≥ 0` to replace `∫Y` by `∫max 1 Y`.

The only nontrivial library/API point is step 4. If Mathlib exposes a usable name such as `intervalIntegral.integral_mono_ae`, use it. If not, add a local helper in this file:

```lean
/-- A.e. version of interval-integral monotonicity over a non-reversed interval. -/
theorem intervalIntegral_integral_mono_on_ae
    {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hle : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), f s ≤ g s) :
    ∫ s in a..b, f s ≤ ∫ s in a..b, g s := by
  -- proof should unfold `intervalIntegrable_iff_integrableOn_Ioc_of_le hab`
  -- and use the Lebesgue integral monotonicity theorem on
  -- `volume.restrict (Set.Ioc a b)`, then rewrite interval integrals by the
  -- usual `intervalIntegral.integral_of_le` / Ioc representation.
  ...
```

This helper is pure measure theory, not a PDE frontier.

## 5. Can `RelativeMoserInterpolationBeforeClosedWindowAE` be derived from `RelativeMoserInterpolationBefore`?

Mathematically yes, from endpoint-null facts. For each closed window `t1..t2` with

```lean
t1 ∈ Set.Icc 0 T, t2 ∈ Set.Icc t1 T
```

we need the strict-interior condition a.e. on `Set.Ioc t1 t2`:

```lean
∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), 0 < s ∧ s < T
```

The lower bound is easy because `s ∈ Ioc t1 t2` gives `t1 < s` and `0 ≤ t1`.
The upper bound fails only at `s = T` when `t2 = T`, a singleton null set.

A useful bridge theorem would be:

```lean
/-- The pointwise strict-interior relative-Moser predicate implies its a.e.
closed-window version, after discarding endpoint singletons. -/
theorem relativeMoserInterpolationBeforeClosedWindowAE_of_strictInterior
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    RelativeMoserInterpolationBeforeClosedWindowAE D u T rho p0 := by
  intro p hp eps heps
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hpoint⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  intro t1 ht1 t2 ht2
  -- Need to prove that almost every `s` in `volume.restrict (Set.Ioc t1 t2)`
  -- satisfies `0 < s ∧ s < T`, then apply `hpoint s` and simp through
  -- `integratedMoserEnergy` / `integratedMoserGradientEnergy`.
  ...
```

This should be provable with standard singleton-null lemmas, but it is not currently packaged in the repository. If Codex wants a low-risk step, add the strict-interior theorem first; then add this AE bridge and closed-window integration theorem separately.

## 6. Regularity-fed closed-window `hrelInt` skeleton

Once the a.e. bridge exists, the final wrapper matching the compiled input shape should be:

```lean
/-- Produce the closed-window `hrelInt` shape from first-crossing regularity and
the a.e. closed-window relative-Moser frontier. -/
theorem relativeMoser_hrelInt_closedWindow_of_regular_AE
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hrelAE : RelativeMoserInterpolationBeforeClosedWindowAE D u T rho p0)
    (hrho_nonneg : 0 ≤ rho) :
    ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
      ∃ Ceps, 0 ≤ Ceps ∧
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s ≤
            eps * (∫ s in t1..t2, integratedMoserGradientEnergy D u p s) +
            Ceps * (∫ s in t1..t2,
              max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  intro p hp eps heps
  rcases hrelAE p hp eps heps with ⟨Ceps, hCeps_nonneg, hAE⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  intro t1 ht1 t2 ht2
  have hab : t1 ≤ t2 := ht2.1
  have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
    Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
  have hp_rho : p0 ≤ p + rho := by linarith
  have hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume t1 t2 :=
    hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
  have hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2 :=
    hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
  have hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s) volume t1 t2 :=
    hreg.power_intervalIntegrable_of_Icc hp hab hsub
  -- apply `relativeMoser_higherPower_timeIntegral_le_of_closedWindow_currentEnergy_maxOne_of_ae`
  -- with the same `Ceps` from `hAE`; or inline the proof to avoid existential
  -- mismatch.
  ...
```

Again, the only missing implementation detail is the a.e. interval-integral monotonicity/endpoint bridge, not PDE analysis.

## Recommendation

For immediate Codex work in `P3MoserIntegratedClosure.lean`:

1. Land `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne` first. It is strict interior and should compile with only existing APIs.
2. Do **not** pretend this proves the closed-window `hrelInt` shape. It does not cover `t1 = 0` or `t2 = T` because `RelativeMoserInterpolationBefore` is strict interior.
3. For closed windows, add the explicit a.e. bridge:
   ```lean
   RelativeMoserInterpolationBeforeClosedWindowAE
   relativeMoserInterpolationBeforeClosedWindowAE_of_strictInterior
   intervalIntegral_integral_mono_on_ae
   relativeMoser_higherPower_timeIntegral_le_of_closedWindow_currentEnergy_maxOne_of_ae
   ```
4. Then add `relativeMoser_hrelInt_closedWindow_of_regular_AE` to feed the already-compiled closed-window wrapper.

This sequence cleanly separates the already-provable strict-window integration from the endpoint/a.e. transport needed by the closed-window wrapper.
