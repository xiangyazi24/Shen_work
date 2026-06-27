# Q1228 / cron1 — `heatSemigroup_flooredSourceTimeData`: filling `d0` and planning `d1`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Files inspected

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/PDE/IntervalDomainRegularityBootstrap.lean
ShenWork/PDE/RegularityBootstrap.lean
ShenWork/Wiener/EWA/HeatFloorIcc.lean
ShenWork/Paper2/Defs.lean
```

## Short answer

You should add a **floor / positivity input**.  The current file has already moved in the right direction: `heatSemigroup_flooredSourceTimeData` now has

```lean
(hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
```

This is the best local hypothesis for this producer.  Derive it upstream from a positive initial datum / closed-domain floor in a wrapper theorem.  Do **not** try to derive it inside this theorem from the existing `_hu₀_bound` and `_hu₀_cont`; those hypotheses are not enough.  A mere nonnegativity hypothesis is also not quite the right local input unless you additionally prove strict heat-kernel positivity plus a nontrivial-mass condition.  For the `Real.rpow` chain rule used by `hasDerivAt_srcSlice` and `hasDerivAt_srcSlice1`, the local producer needs strict positivity at every positive time and every spatial point in the slice.

The `heatDu` / `unitIntervalCosineHeatSecondValue` bridge is already present in the current file and is the right bridge:

```lean
private theorem heatDu_eq_secondValue
    (u₀ : intervalDomainPoint → ℝ) {t x : ℝ} (ht : 0 < t) :
    heatDu u₀ t x =
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        t (cosineCoeffs (intervalDomainLift u₀)) x := by
  simp only [heatDu, if_pos ht]
  simp only [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue,
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue]
  congr 1; ext n
  simp only [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight,
    unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
    unitIntervalCosineEigenvalue]
  ring
```

This is correct: `RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight` is `-λₙ * heatPointWeight`, while `IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight` is `exp(-tλₙ) * (-(nπ)^2 * cos(nπx))`; since `λₙ = (nπ)^2`, the terms are pointwise equal.

## One import/open change for `d1`

At the top, add `hasDerivAt_srcSlice1` to the open list:

```lean
open ShenWork.IntervalFlooredSourceTimeDataIterate
  (srcSlice1 srcSlice2 hasDerivAt_srcSlice hasDerivAt_srcSlice1)
```

## Fill the two remaining holes in current `d0`

Your current `d0` already proves the ball geometry and the derivative subgoal `(b)`.  Replace the two `sorry`s in `(a)` and `(c)` with the following code.

```lean
    refine ⟨δ, hδ, ?_, ?_, ?_⟩
    · -- (a) ContinuousOn of srcSlice near τ
      have hprofile0 := heatSlice_profile_jointContinuousOn
        (p := p) (u₀ := u₀) (c := τ - δ) (T := τ + δ)
        (M₀ := M₀) hleft _hu₀_cont _hu₀_bound
      have hprofile : ContinuousOn
          (fun q : ℝ × ℝ =>
            intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
        -- `picardIter` level 0 and `conjugatePicardIter` level 0 are both the
        -- same heat semigroup slice, so this should be definitional.
        simpa [Function.uncurry] using hprofile0
      have hpow : ContinuousOn
          (fun q : ℝ × ℝ =>
            (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ p.γ)
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
        apply ContinuousOn.rpow_const hprofile
        intro q hq
        obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
        have hσpos : 0 < q.1 := lt_of_lt_of_le hleft hσ.1
        exact Or.inl (ne_of_gt (hfloor q.1 hσpos q.2 hx))
      have hsrc_joint : ContinuousOn
          (Function.uncurry (srcSlice p (conjugatePicardIter p u₀ 0)))
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
        simpa [srcSlice, Function.uncurry] using continuousOn_const.mul hpow
      filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
      have hsIcc := hball_Icc s hs
      exact hsrc_joint.comp
        (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hsIcc, hx⟩)

    · -- (b) HasDerivAt of srcSlice = srcSlice1
      intro x hx s hs
      have hs_pos := hball_pos s hs
      have hxIcc : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
      have hsIcc := hball_Icc s hs
      have hderiv_within := heatSlice_field_hasDerivWithinAt p
        (c := τ - δ) (T := τ + δ) hleft hsIcc _hu₀_cont _hu₀_bound hxIcc
      have hsIoo := hball_Ioo s hs
      have hderiv := hderiv_within.hasDerivAt (Icc_mem_nhds hsIoo.1 hsIoo.2)
      rw [← heatDu_eq_secondValue u₀ hs_pos] at hderiv
      exact hasDerivAt_srcSlice (hfloor s hs_pos x hxIcc) hderiv

    · -- (c) Joint ContinuousOn of srcSlice1 on slab
      have hprofile0 := heatSlice_profile_jointContinuousOn
        (p := p) (u₀ := u₀) (c := τ - δ) (T := τ + δ)
        (M₀ := M₀) hleft _hu₀_cont _hu₀_bound
      have hprofile : ContinuousOn
          (fun q : ℝ × ℝ =>
            intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
        simpa [Function.uncurry] using hprofile0
      have hsecond0 := heatSlice_secondValue_jointContinuousOn
        (u₀ := u₀) (c := τ - δ) (T := τ + δ) (M₀ := M₀)
        hleft _hu₀_bound
      have hdu_joint : ContinuousOn
          (Function.uncurry (heatDu u₀))
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
        refine hsecond0.congr ?_
        intro q hq
        obtain ⟨hσ, _hx⟩ := Set.mem_prod.mp hq
        have hqpos : 0 < q.1 := lt_of_lt_of_le hleft hσ.1
        simp [Function.uncurry, heatDu_eq_secondValue u₀ (t := q.1) (x := q.2) hqpos]
      have hpow1 : ContinuousOn
          (fun q : ℝ × ℝ =>
            (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1))
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
        apply ContinuousOn.rpow_const hprofile
        intro q hq
        obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
        have hσpos : 0 < q.1 := lt_of_lt_of_le hleft hσ.1
        exact Or.inl (ne_of_gt (hfloor q.1 hσpos q.2 hx))
      simpa [srcSlice1, Function.uncurry] using
        ((continuousOn_const.mul continuousOn_const).mul hpow1).mul hdu_joint
```

This is the right local structure because `IntervalPicardLevel0SourceTimeC1On` already supplies:

```lean
heatSlice_field_hasDerivWithinAt
heatSlice_profile_jointContinuousOn
heatSlice_secondValue_jointContinuousOn
```

and `IntervalFlooredSourceTimeDataIterate` already supplies the nonlinear chain rule:

```lean
hasDerivAt_srcSlice
```

## For `d1`: what is genuinely missing

`d1` has the same shape, but it needs one more heat-time derivative:

```lean
HasDerivAt (fun r => heatDu u₀ r x) (heatD2u u₀ s x) s
```

and joint continuity of the second derivative slice:

```lean
ContinuousOn
  (Function.uncurry (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
```

I did not find an existing project lemma in `IntervalPicardLevel0SourceTimeC1On.lean` that proves the derivative of `heatDu`; that file stops at the first heat time derivative.  So `d1` needs two new helper lemmas.  Add them above the theorem, with honest proofs later:

```lean
/-- Positive-time derivative of the heat Laplacian value.
This is the second time derivative of the heat semigroup. -/
private theorem heatDu_hasDerivAt
    (u₀ : intervalDomainPoint → ℝ) {M₀ s x : ℝ}
    (hs : 0 < s)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    HasDerivAt (fun r : ℝ => heatDu u₀ r x) (heatD2u u₀ s x) s := by
  -- Prove by termwise differentiation on an `Ioi (s/2)` neighborhood.
  -- Mode derivative:
  --   d/dt [-λ * exp(-tλ) * âₙ * cos(nπx)]
  --     = λ^2 * exp(-tλ) * âₙ * cos(nπx)
  -- Use the same exponential-polynomial summability pattern as
  -- `unitIntervalCosineHeatValue_hasDerivAt_time` /
  -- `unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2`.
  sorry

/-- Joint continuity of the second heat time derivative on a positive closed slab. -/
private theorem heatD2u_jointContinuousOn
    (u₀ : intervalDomainPoint → ℝ) {M₀ c T : ℝ}
    (hc : 0 < c)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn
      (Function.uncurry (heatD2u u₀))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  -- Prove by uniform convergence of the λ² exp(-tλ) cosine series on `t ≥ c`.
  -- The majorant is `λ² * |âₙ| * exp(-c λ)`, summable from bounded coefficients
  -- and exponential decay.  This is analogous to the heat high-regularity cutoff
  -- estimates, but on a compact positive-time slab.
  sorry
```

Then define a local `srcSlice2` joint continuity helper:

```lean
private theorem heatLevel0_srcSlice2_jointContinuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ContinuousOn
      (Function.uncurry
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  have hprofile0 := heatSlice_profile_jointContinuousOn
    (p := p) (u₀ := u₀) (c := c) (T := T) (M₀ := M₀)
    hc hu₀_cont hu₀_bound
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hprofile0
  have hsecond0 := heatSlice_secondValue_jointContinuousOn
    (u₀ := u₀) (c := c) (T := T) (M₀ := M₀) hc hu₀_bound
  have hdu_joint : ContinuousOn
      (Function.uncurry (heatDu u₀))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    refine hsecond0.congr ?_
    intro q hq
    obtain ⟨hσ, _hx⟩ := Set.mem_prod.mp hq
    have hqpos : 0 < q.1 := lt_of_lt_of_le hc hσ.1
    simp [Function.uncurry, heatDu_eq_secondValue u₀ (t := q.1) (x := q.2) hqpos]
  have hd2u_joint := heatD2u_jointContinuousOn
    (u₀ := u₀) (M₀ := M₀) (c := c) (T := T) hc hu₀_bound
  have hpowγm1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hprofile
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hc hσ.1) q.2 hx))
  have hpowγm2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1 - 1))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hprofile
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hc hσ.1) q.2 hx))
  simpa [srcSlice2, Function.uncurry] using
    ((((continuousOn_const.mul continuousOn_const).mul continuousOn_const).mul hpowγm2).mul
        (hdu_joint.pow 2)).add
      (((continuousOn_const.mul continuousOn_const).mul hpowγm1).mul hd2u_joint)
```

With those helpers, the `d1` body is almost the same as `d0`:

```lean
  d1 := by
    intro τ hτ
    set δ : ℝ := min 1 (τ / 2)
    have hδ : 0 < δ := lt_min one_pos (half_pos hτ)
    have hleft : 0 < τ - δ := by linarith [min_le_right (1 : ℝ) (τ / 2)]
    have hball_pos : ∀ s, s ∈ Metric.ball τ δ → 0 < s := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      linarith [(abs_lt.mp hs).1, min_le_right (1 : ℝ) (τ / 2)]
    have hball_Icc : ∀ s, s ∈ Metric.ball τ δ → s ∈ Icc (τ - δ) (τ + δ) := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    have hball_Ioo : ∀ s, s ∈ Metric.ball τ δ → s ∈ Ioo (τ - δ) (τ + δ) := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩

    have hsrc1_joint : ContinuousOn
        (Function.uncurry
          (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
      -- Use the same proof as d0(c).  Factor it as a helper if it gets duplicated.
      sorry

    have hsrc2_joint := heatLevel0_srcSlice2_jointContinuousOn
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := τ - δ) (T := τ + δ)
      hleft _hu₀_bound _hu₀_cont hfloor

    refine ⟨δ, hδ, ?_, ?_, ?_⟩
    · filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
      have hsIcc := hball_Icc s hs
      exact hsrc1_joint.comp
        (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hsIcc, hx⟩)
    · intro x hx s hs
      have hs_pos := hball_pos s hs
      have hxIcc : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
      have hsIcc := hball_Icc s hs
      have hderiv_within := heatSlice_field_hasDerivWithinAt p
        (c := τ - δ) (T := τ + δ) hleft hsIcc _hu₀_cont _hu₀_bound hxIcc
      have hsIoo := hball_Ioo s hs
      have hderiv := hderiv_within.hasDerivAt (Icc_mem_nhds hsIoo.1 hsIoo.2)
      rw [← heatDu_eq_secondValue u₀ hs_pos] at hderiv
      have hd2u := heatDu_hasDerivAt
        (u₀ := u₀) (M₀ := M₀) (s := s) (x := x) hs_pos _hu₀_bound
      exact hasDerivAt_srcSlice1
        (p := p) (u := conjugatePicardIter p u₀ 0)
        (du := heatDu u₀) (d2u := heatD2u u₀)
        (hfloor s hs_pos x hxIcc) hderiv hd2u
    · exact hsrc2_joint
```

## Direct floor or derived floor?

For this theorem, keep the direct heat-profile floor:

```lean
hfloor : ∀ t > 0, ∀ x ∈ Icc (0:ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

This matches exactly what `hasDerivAt_srcSlice` / `hasDerivAt_srcSlice1` need and keeps `FlooredSourceTimeData` independent of how the floor is produced.

Then make a separate wrapper theorem later, for example:

```lean
theorem heatSemigroup_flooredSourceTimeData_of_initial_floor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ η : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hη : 0 < η)
    (hu₀_floor : ∀ x : intervalDomainPoint, η ≤ u₀ x) :
    FlooredSourceTimeData p (conjugatePicardIter p u₀ 0)
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) := by
  refine heatSemigroup_flooredSourceTimeData hu₀_bound hu₀_cont ?_
  intro t ht x hx
  -- derive `η ≤ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x`, then `0 < ...`.
  -- Use the interval heat-kernel floor theorem or a variant adapted to
  -- `intervalDomainLift u₀`.  Existing `intervalFullSemigroupOperator_ge_floor_Icc`
  -- expects a globally continuous `ℝ → ℝ`, so either use a compatible continuous
  -- extension or prove a subtype-continuity version.
  sorry
```

Do not use only `hu₀_nonneg` unless you also add hypotheses ensuring nontrivial positive mass and prove strict positivity of the Neumann heat kernel convolution.  A closed positive lower bound is much cleaner and already matches the `FlooredSourceTimeData` design.

## Implementation order

1. Keep the existing `hfloor` heat-profile hypothesis in `heatSemigroup_flooredSourceTimeData`.
2. Fill `d0(a)` and `d0(c)` with the code above; `d0(b)` is already the right proof.
3. Add `hasDerivAt_srcSlice1` to the open list.
4. Add `heatDu_hasDerivAt` and `heatD2u_jointContinuousOn` as named heat-specific helper lemmas.
5. Fill `d1` using `hasDerivAt_srcSlice1` and those helpers.
6. Later add a wrapper that derives `hfloor` from a closed-domain initial floor, not from bare nonnegativity.
