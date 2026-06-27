# Q1160 / cron1 — filling `FlooredSourceTimeData.d0` for heat level 0

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Files inspected

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean
ShenWork/PDE/IntervalDuhamelClosedC2.lean
ShenWork/PDE/RegularityBootstrap.lean
ShenWork/PDE/IntervalDomainRegularityBootstrap.lean
ShenWork/Wiener/EWA/HeatFloorIcc.lean
ShenWork/Paper2/Defs.lean
```

## Main finding

There is a real missing hypothesis/infrastructure boundary: the theorem currently has only

```lean
(_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
(_hu₀_cont : Continuous u₀)
```

but `d0` for `srcSlice p u t x = p.ν * (intervalDomainLift (u t) x) ^ p.γ` uses the repo lemma

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.hasDerivAt_srcSlice
```

which requires

```lean
0 < intervalDomainLift (u t) x
```

at the differentiation point.  The current theorem statement does not supply positivity of `u₀`, a closed-domain floor, or heat-profile positivity.  This is not just a Lean API inconvenience: with arbitrary continuous initial data, the positive-power `Real.rpow` chain rule under the floor cannot be invoked from the current hypotheses.  The file name says `FlooredSourceTimeData`, and the existing producer `flooredSourceTimeData_of_iterate` confirms that the intended input includes a floor/positivity field.

So the exact `d0` proof can be written once you provide a heat-level-0 positivity lemma on the local positive-time slab.  Below I isolate the required nontrivial heat facts as private helper lemmas, then give the concrete `d0` body.

## Add this import

`IntervalHeatSemigroupFlooredSourceTimeData.lean` should import the level-0 heat-slice infrastructure:

```lean
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
```

That file already exposes the three facts you want to reuse:

```lean
heatSlice_field_hasDerivWithinAt
heatSlice_profile_jointContinuousOn
heatSlice_secondValue_jointContinuousOn
```

The first gives the heat-equation time derivative on a closed positive window, but as a `HasDerivWithinAt`; inside an open slab, convert it to `HasDerivAt` with `.hasDerivAt` and `Icc_mem_nhds`.

## Helper lemmas to put above `heatSemigroup_flooredSourceTimeData`

These helpers are the cleanest way to keep the `d0` body short.  Two are routine transport/congruence lemmas; one is the genuine missing positivity/floor input.

```lean
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 hasDerivAt_srcSlice)
open ShenWork.IntervalPicardLevel0SourceTimeC1On
  (heatCoeff heatSlice_field_hasDerivWithinAt heatSlice_profile_jointContinuousOn
   heatSlice_secondValue_jointContinuousOn)
open ShenWork.IntervalDomainRegularityBootstrap (unitIntervalCosineHeatSecondValue)

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

/-- The `heatDu` definition is the same spectral Laplacian as the old
`unitIntervalCosineHeatSecondValue` used by `IntervalPicardLevel0SourceTimeC1On`.
This is a pointwise definitional/algebraic bridge between the two namespaces. -/
private lemma heatDu_eq_secondValue
    (u₀ : intervalDomainPoint → ℝ) {t x : ℝ} (ht : 0 < t) :
    heatDu u₀ t x =
      unitIntervalCosineHeatSecondValue t
        (cosineCoeffs (intervalDomainLift u₀)) x := by
  -- This should close by unfolding both spectral Laplacian definitions.
  -- `heatDu` unfolds to `RegularityBootstrap.unitIntervalCosineHeatLaplacianValue`;
  -- `unitIntervalCosineHeatSecondValue` unfolds to the older
  -- `IntervalDomainRegularityBootstrap` series.  The per-mode terms are equal by
  -- `unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi)^2` and ring algebra.
  rw [heatDu, if_pos ht]
  -- Usually enough after imports:
  --   simp [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue,
  --     ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
  --     unitIntervalCosineHeatSecondValue,
  --     ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight,
  --     ShenWork.RegularityBootstrap.unitIntervalCosineHeatPointWeight,
  --     unitIntervalCosineHeatPointWeight, unitIntervalCosineEigenvalue,
  --     unitIntervalCosineMode]
  -- If `simp` does not unfold through `tsum`, use `congr 1; ext n; ring`.
  sorry

/-- Heat level-0 field time derivative, upgraded from the existing closed-window
`HasDerivWithinAt` lemma to `HasDerivAt` at an interior point of the window. -/
private lemma heatLevel0_field_hasDerivAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M₀ c T s x : ℝ}
    (hc : 0 < c) (hsIcc : s ∈ Icc c T)
    (hs_int : c < s ∧ s < T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 r) x)
      (heatDu u₀ s x) s := by
  have hWithin := heatSlice_field_hasDerivWithinAt
    (p := p) (u₀ := u₀) (c := c) (T := T) (σ := s) (x := x) (M₀ := M₀)
    hc hsIcc hu₀_cont hu₀_bound hx
  have hnhds : Icc c T ∈ 𝓝 s := by
    apply Icc_mem_nhds <;> exact hs_int.1 <;> exact hs_int.2
  have hAt := hWithin.hasDerivAt hnhds
  have hdu : unitIntervalCosineHeatSecondValue s
        (cosineCoeffs (intervalDomainLift u₀)) x = heatDu u₀ s x :=
    (heatDu_eq_secondValue u₀ (t := s) (x := x) (lt_of_lt_of_le hc hsIcc.1)).symm
  -- `picardIter` and `conjugatePicardIter` are definitionally the same heat slice at level 0.
  convert hAt using 1
  · ext r
    rfl
  · exact hdu

/-- ContinuousOn of the concrete source slice on a positive-time closed window.
This is the zeroth-slice analogue of `heatSourceDot_jointContinuousOn`, but for
`srcSlice p u t x = ν * u(t,x)^γ`. -/
private lemma heatLevel0_srcSlice_jointContinuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (hc : 0 < c) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x) :
    ContinuousOn
      (Function.uncurry (srcSlice p (conjugatePicardIter p u₀ 0)))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  have hprofile_picard := heatSlice_profile_jointContinuousOn
    (p := p) (u₀ := u₀) (c := c) (T := T) (M₀ := M₀)
    hc hu₀_cont hu₀_bound
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hprofile_picard
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ p.γ)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hprofile
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hpos q.1 hσ q.2 hx))
  simpa [srcSlice, Function.uncurry] using (continuousOn_const.mul hpow)

/-- Joint continuity of `srcSlice1` on a positive-time closed window. -/
private lemma heatLevel0_srcSlice1_jointContinuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (hc : 0 < c) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x) :
    ContinuousOn
      (Function.uncurry
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  have hprofile_picard := heatSlice_profile_jointContinuousOn
    (p := p) (u₀ := u₀) (c := c) (T := T) (M₀ := M₀)
    hc hu₀_cont hu₀_bound
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hprofile_picard
  have hdu_second := heatSlice_secondValue_jointContinuousOn
    (u₀ := u₀) (c := c) (T := T) (M₀ := M₀) hc hu₀_bound
  have hdu : ContinuousOn
      (Function.uncurry (heatDu u₀))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    refine hdu_second.congr ?_
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    have hqpos : 0 < q.1 := lt_of_lt_of_le hc hσ.1
    simp [Function.uncurry, heatDu_eq_secondValue u₀ (t := q.1) (x := q.2) hqpos]
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hprofile
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hpos q.1 hσ q.2 hx))
  simpa [srcSlice1, Function.uncurry] using
    ((continuousOn_const.mul continuousOn_const).mul hpow).mul hdu

/-- This is the missing floor/positivity input.  It is not derivable from the
current theorem hypotheses `hu₀_cont` and `hu₀_bound` alone.  Fill this from a
positive initial datum / closed-domain floor theorem, or add it as an argument to
`heatSemigroup_flooredSourceTimeData`. -/
private lemma heatLevel0_profile_pos_on_slab
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (_hc : 0 < c) (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x := by
  -- Cannot be proved from the current theorem hypotheses.
  -- Use a real heat-floor theorem here, e.g. a closed-domain floor on `u₀` plus
  -- `intervalFullSemigroupOperator_ge_floor_Icc` / `heatEWA_uniformFloor_Icc`,
  -- or strengthen `heatSemigroup_flooredSourceTimeData` to take this as input.
  sorry
```

### Note on `Icc_mem_nhds`

If the `apply Icc_mem_nhds` line in `heatLevel0_field_hasDerivAt` produces two goals in the opposite order, replace it with:

```lean
  have hnhds : Icc c T ∈ 𝓝 s := by
    exact Icc_mem_nhds hs_int.1 hs_int.2
```

or the local project’s preferred spelling.  The point is just `c < s` and `s < T`.

## The concrete `d0` body

After the helper lemmas above, replace the `d0 := by ... sorry` block with this:

```lean
  d0 := by
    intro τ hτ
    let δ : ℝ := τ / 4
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let c : ℝ := τ / 2
    let T : ℝ := 3 * τ / 2
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hcT : c < T := by
      dsimp [c, T]
      linarith

    -- Points in `ball τ δ` lie in the positive closed slab `[c,T]`, actually in its interior.
    have hball_sub_Icc : ∀ s ∈ Metric.ball τ δ, s ∈ Icc c T := by
      intro s hs
      have hdist : |s - τ| < δ := by
        simpa [Metric.mem_ball, Real.dist_eq] using hs
      have hlt_left : τ - δ < s := by
        have := (abs_lt.mp hdist).1
        linarith
      have hlt_right : s < τ + δ := by
        have := (abs_lt.mp hdist).2
        linarith
      constructor <;> dsimp [c, T, δ] <;> linarith

    have hball_int : ∀ s ∈ Metric.ball τ δ, c < s ∧ s < T := by
      intro s hs
      have hdist : |s - τ| < δ := by
        simpa [Metric.mem_ball, Real.dist_eq] using hs
      have hlt_left : τ - δ < s := by
        have := (abs_lt.mp hdist).1
        linarith
      have hlt_right : s < τ + δ := by
        have := (abs_lt.mp hdist).2
        linarith
      constructor <;> dsimp [c, T, δ] <;> linarith

    have hslab_eq : Icc (τ - δ) (τ + δ) = Icc c T := by
      dsimp [δ, c, T]
      ext s
      constructor <;> intro hs <;> constructor <;> linarith [hs.1, hs.2]

    -- The required floor on this positive slab.  This is the missing nontrivial input.
    have hpos_slab : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x :=
      heatLevel0_profile_pos_on_slab
        (p := p) (u₀ := u₀) (M₀ := M₀) (c := c) (T := T)
        hc _hu₀_cont _hu₀_bound

    have hsrc_joint := heatLevel0_srcSlice_jointContinuousOn
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c) (T := T)
      hc _hu₀_cont _hu₀_bound hpos_slab

    have hsrc1_joint := heatLevel0_srcSlice1_jointContinuousOn
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c) (T := T)
      hc _hu₀_cont _hu₀_bound hpos_slab

    refine ⟨δ, hδ, ?_, ?_, ?_⟩
    · -- (a) eventual `ContinuousOn` of the source slice.
      filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
      have hsIcc : s ∈ Icc c T := hball_sub_Icc s hs
      exact hsrc_joint.comp
        (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hsIcc, hx⟩)
    · -- (b) pointwise time derivative of the source slice.
      intro x hx s hs
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
      have hsIcc : s ∈ Icc c T := hball_sub_Icc s hs
      have hsint : c < s ∧ s < T := hball_int s hs
      have hfield :
          HasDerivAt
            (fun r : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 r) x)
            (heatDu u₀ s x) s :=
        heatLevel0_field_hasDerivAt
          (p := p) (u₀ := u₀) (M₀ := M₀) (c := c) (T := T)
          hc hsIcc hsint _hu₀_cont _hu₀_bound hxIcc
      exact hasDerivAt_srcSlice
        (p := p) (u := conjugatePicardIter p u₀ 0) (du := heatDu u₀)
        (hpos_slab s hsIcc x hxIcc) hfield
    · -- (c) joint continuity of `srcSlice1` on `[τ-δ,τ+δ] × [0,1]`.
      simpa [hslab_eq] using hsrc1_joint
```

### Small tactic adjustment

If the `simpa [Metric.mem_ball, Real.dist_eq] using hs` lines fail because Mathlib normalizes `dist τ s` rather than `dist s τ`, use this variant:

```lean
      have hdist' : dist s τ < δ := by simpa [Metric.mem_ball] using hs
      have hdist : |s - τ| < δ := by simpa [Real.dist_eq] using hdist'
```

or, if it gives `|τ - s|`, add `abs_sub_comm`:

```lean
      have hdist : |s - τ| < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using hdist'
```

## Why this is the right proof shape

The repo already contains the nonlinear rpow chain rule in the exact source shape:

```lean
hasDerivAt_srcSlice
```

so `d0` should not reprove the derivative of `ν * u^γ`.  The proof should only supply:

1. heat field derivative: `∂t S(t)u₀ = heatDu u₀ t`,
2. positivity/floor on the slab,
3. source slice continuity and `srcSlice1` joint continuity.

The older file `IntervalPicardLevel0SourceTimeC1On.lean` gives exactly the heat-slice pattern for the logistic source: it builds closed-window profile continuity, heat time derivative, and derivative-slice joint continuity.  The code above copies that shape for `srcSlice`/`srcSlice1`.

## Better structural alternative

Instead of filling only `d0` inside `FlooredSourceTimeData`, you can build an

```lean
IterateSourceTimeData p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)
```

and then close the whole source-time package with:

```lean
exact ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate H
```

This is cleaner long-term because `flooredSourceTimeData_of_iterate` already wires `d0` and `d1` via `hasDerivAt_srcSlice` and `hasDerivAt_srcSlice1`.  But for the requested `d0` line, the concrete block above is the direct replacement.

## Bottom line

The `d0` body is straightforward once these helpers exist.  The only non-routine blocker is not `ContDiff` API or the rpow chain rule; it is that `heatSemigroup_flooredSourceTimeData` currently lacks a positivity/floor input.  Either prove `heatLevel0_profile_pos_on_slab` from an added positive initial datum/floor hypothesis, or strengthen the theorem statement to accept exactly that slab positivity as a hypothesis.
