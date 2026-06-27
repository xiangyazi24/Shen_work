/-
# `FlooredSourceTimeData` for the heat semigroup base iterate (level 0)

This file builds the `FlooredSourceTimeData p u s₁ s₂` for the heat semigroup
base iterate `u = conjugatePicardIter p u₀ 0 = S(t)u₀`, the SINGLE
infrastructure piece that gates 7 of 12 remaining sorry.

## Source slice and time derivatives

The source slice is `srcSlice p u t x = ν · (S(t)u₀(x))^γ`.

Time derivatives via the chain rule through the heat equation `∂_t S(t) = ΔS(t)`:

  `s₁(t,x) = ν · γ · (S(t)u₀(x))^{γ-1} · ΔS(t)u₀(x)`
  `s₂(t,x) = ν · γ · (γ-1) · (S(t)u₀(x))^{γ-2} · (ΔS(t)u₀(x))² + ν · γ · (S(t)u₀(x))^{γ-1} · Δ²S(t)u₀(x)`

where `du(t,x) = ΔS(t)u₀(x)` and `d2u(t,x) = Δ²S(t)u₀(x)`.

## The τ > 0 weakening

`FlooredSourceTimeData` now requires only `∀ τ : ℝ, 0 < τ → ...` (weakened
from `∀ τ : ℝ`).  For τ > 0: the heat semigroup is smooth and everything works.
The τ ≤ 0 case is no longer required, eliminating the fundamental obstruction
(S(0) discontinuity) that made the old all-ℝ fields unfillable.

The time-derivative functions `du` and `d2u` are still defined as 0 at t ≤ 0
for completeness, but they are only used at t > 0.

## Sorry budget

Each field of `FlooredSourceTimeData` is sorry'd with a named obligation.
These are finite, non-circular, and independently attackable.  All fields
now quantify over **positive time only** (`0 < τ` / `0 < t`), which makes
them fillable from the heat semigroup smoothing data:

1. `d0` — HasDerivAt of srcSlice = s₁ + joint continuity of s₁ (for τ > 0)
2. `d1` — HasDerivAt of s₁ = s₂ + joint continuity of s₂ (for τ > 0)
3. `sliceC2` — ContDiffOn ℝ 2 of each time-derivative slice on [0,1] (for t > 0)
4. `sliceNeumann` — Neumann BC (deriv = 0 at endpoints) (for t > 0)
5. `zerothBound` — uniform zeroth-mode bound (for t > 0)
6. `laplBound` — uniform Laplacian bound (kπ)⁻² (for t > 0)

Once built, this feeds into the committed chain:
  FlooredSourceTimeData → physicalSourceTimeC2_of_floored → PhysicalSourceTimeC2
  → physicalResolverJointC2Data_of_floor → PhysicalResolverJointC2Data
  → coupledChemical_jointContDiffAt_two

which closes `heatSemigroup_level0_resolverJointC2Data` (previously 4 unstructured sorry).
-/
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam FlooredSourceTimeData)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2 hasDerivAt_srcSlice hasDerivAt_srcSlice1)
open ShenWork.IntervalPicardLevel0SourceTimeC1On
  (heatCoeff heatSlice_field_hasDerivWithinAt heatSlice_profile_jointContinuousOn
   heatSlice_secondValue_jointContinuousOn)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

/-! ## Time derivatives of the heat semigroup iterate

For the heat semigroup `u t x = S(t)u₀(x.1)`, the time derivative is the
spectral Laplacian `∂_t S(t) = ΔS(t)`.  We define `du` and `d2u` using the
spectral Laplacian values from `RegularityBootstrap`. -/

/-- The first time-derivative of the lifted heat semigroup iterate at `(t, x)`,
defined as the spectral Laplacian value `∑' k, -λ_k · exp(-tλ_k) · â_k · cos(kπx)`
for `t > 0`, and `0` for `t ≤ 0`. -/
def heatDu (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
      t (cosineCoeffs (intervalDomainLift u₀)) x
  else 0

/-- The second time-derivative of the lifted heat semigroup iterate, defined as
the iterated spectral Laplacian `∑' k, λ_k² · exp(-tλ_k) · â_k · cos(kπx)`
for `t > 0`, and `0` for `t ≤ 0`. -/
def heatD2u (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    -- The second time derivative of S(t)u₀ = Δ²S(t)u₀ = ∑ λ_k² exp(-tλ_k) â_k cos(kπx)
    ∑' k : ℕ, unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) *
      ShenWork.CosineSpectrum.cosineMode k x
  else 0

/-! ## Bridge: `heatDu` = `unitIntervalCosineHeatSecondValue` at positive time -/

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

/-! ## Helper: d0 proof body (extracted to avoid where-syntax elaboration issues) -/

private theorem heatSemigroup_d0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ, ContinuousOn
        (srcSlice p (conjugatePicardIter p u₀ 0) s) (Icc (0:ℝ) 1)) ∧
      (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => srcSlice p (conjugatePicardIter p u₀ 0) r x)
          (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) s x) s) ∧
      ContinuousOn
        (Function.uncurry (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1) := by
  set δ : ℝ := min 1 (τ / 2) with hδdef
  have hδ : 0 < δ := lt_min one_pos (half_pos hτ)
  have hleft : 0 < τ - δ := by
    have := min_le_right (1 : ℝ) (τ / 2); linarith
  have hball_pos : ∀ s, s ∈ Metric.ball τ δ → 0 < s := by
    intro s hs; rw [Metric.mem_ball, Real.dist_eq] at hs
    linarith [(abs_lt.mp hs).1, min_le_right (1 : ℝ) (τ / 2)]
  have hball_Icc : ∀ s, s ∈ Metric.ball τ δ → s ∈ Icc (τ - δ) (τ + δ) := by
    intro s hs; rw [Metric.mem_ball, Real.dist_eq] at hs
    exact ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
  have hball_Ioo : ∀ s, s ∈ Metric.ball τ δ → s ∈ Ioo (τ - δ) (τ + δ) := by
    intro s hs; rw [Metric.mem_ball, Real.dist_eq] at hs
    exact ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using heatSlice_profile_jointContinuousOn p
      (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft _hu₀_cont _hu₀_bound
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ p.γ)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    hprofile.rpow_const (fun q hq => by
      obtain ⟨hσ, hx⟩ := mem_prod.mp hq
      exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
  have hsrc_joint : ContinuousOn
      (Function.uncurry (srcSlice p (conjugatePicardIter p u₀ 0)))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    simpa [srcSlice, Function.uncurry] using continuousOn_const.mul hpow
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · -- (a) ContinuousOn of srcSlice near τ
    filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
    exact hsrc_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => mem_prod.mpr ⟨hball_Icc s hs, hx⟩)
  · -- (b) HasDerivAt of srcSlice = srcSlice1
    intro x hx s hs
    have hs_pos := hball_pos s hs
    have hxIcc : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
    have hderiv_within := heatSlice_field_hasDerivWithinAt p
      (c := τ - δ) (T := τ + δ) hleft (hball_Icc s hs) _hu₀_cont _hu₀_bound hxIcc
    have hderiv := hderiv_within.hasDerivAt
      (Icc_mem_nhds (hball_Ioo s hs).1 (hball_Ioo s hs).2)
    rw [← heatDu_eq_secondValue u₀ hs_pos] at hderiv
    exact hasDerivAt_srcSlice (hfloor s hs_pos x hxIcc) hderiv
  · -- (c) Joint ContinuousOn of srcSlice1 on slab
    have hpow1 : ContinuousOn
        (fun q : ℝ × ℝ =>
          (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
      hprofile.rpow_const (fun q hq => by
        obtain ⟨hσ, hx⟩ := mem_prod.mp hq
        exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
    have hdu_joint : ContinuousOn
        (fun q : ℝ × ℝ => heatDu u₀ q.1 q.2)
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
      have hsecond := heatSlice_secondValue_jointContinuousOn
        (u₀ := u₀) (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft _hu₀_bound
      exact hsecond.congr (fun q hq => by
        obtain ⟨hσ, _hx⟩ := mem_prod.mp hq
        exact (heatDu_eq_secondValue u₀ (lt_of_lt_of_le hleft hσ.1)).symm)
    simpa [srcSlice1, Function.uncurry] using
      (continuousOn_const.mul continuousOn_const).mul (hpow1.mul hdu_joint)

/-! ## Helper: HasDerivAt of heatDu in time (needed for d1) -/

private theorem heatDu_hasDerivAt
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => heatDu u₀ r x) (heatD2u u₀ t x) t := by
  sorry

/-! ## Helper: joint continuity of heatD2u on a positive slab -/

private theorem heatD2u_jointContinuousOn
    {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ} (hc : 0 < c)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn (fun q : ℝ × ℝ => heatD2u u₀ q.1 q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  sorry

/-! ## Helper: d1 proof body -/

private theorem heatSemigroup_d1
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ, ContinuousOn
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) s) (Icc (0:ℝ) 1)) ∧
      (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r x)
          (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) s x) s) ∧
      ContinuousOn
        (Function.uncurry (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1) := by
  set δ : ℝ := min 1 (τ / 2) with hδdef
  have hδ : 0 < δ := lt_min one_pos (half_pos hτ)
  have hleft : 0 < τ - δ := by
    have := min_le_right (1 : ℝ) (τ / 2); linarith
  have hball_pos : ∀ s, s ∈ Metric.ball τ δ → 0 < s := by
    intro s hs; rw [Metric.mem_ball, Real.dist_eq] at hs
    linarith [(abs_lt.mp hs).1, min_le_right (1 : ℝ) (τ / 2)]
  have hball_Icc : ∀ s, s ∈ Metric.ball τ δ → s ∈ Icc (τ - δ) (τ + δ) := by
    intro s hs; rw [Metric.mem_ball, Real.dist_eq] at hs
    exact ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
  have hball_Ioo : ∀ s, s ∈ Metric.ball τ δ → s ∈ Ioo (τ - δ) (τ + δ) := by
    intro s hs; rw [Metric.mem_ball, Real.dist_eq] at hs
    exact ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
  -- Reuse d0's joint continuity proof for srcSlice1 as part (a)
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using heatSlice_profile_jointContinuousOn p
      (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft _hu₀_cont _hu₀_bound
  have hpow1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    hprofile.rpow_const (fun q hq => by
      obtain ⟨hσ, hx⟩ := mem_prod.mp hq
      exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
  have hdu_joint : ContinuousOn
      (fun q : ℝ × ℝ => heatDu u₀ q.1 q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    have hsecond := heatSlice_secondValue_jointContinuousOn
      (u₀ := u₀) (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft _hu₀_bound
    exact hsecond.congr (fun q hq => by
      obtain ⟨hσ, _hx⟩ := mem_prod.mp hq
      exact (heatDu_eq_secondValue u₀ (lt_of_lt_of_le hleft hσ.1)).symm)
  have hsrc1_joint : ContinuousOn
      (Function.uncurry (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    simpa [srcSlice1, Function.uncurry] using
      (continuousOn_const.mul continuousOn_const).mul (hpow1.mul hdu_joint)
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · -- (a) ContinuousOn of srcSlice1 near τ
    filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
    exact hsrc1_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => mem_prod.mpr ⟨hball_Icc s hs, hx⟩)
  · -- (b) HasDerivAt of srcSlice1 = srcSlice2
    intro x hx s hs
    have hs_pos := hball_pos s hs
    have hxIcc : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
    have hderiv_within := heatSlice_field_hasDerivWithinAt p
      (c := τ - δ) (T := τ + δ) hleft (hball_Icc s hs) _hu₀_cont _hu₀_bound hxIcc
    have hderiv := hderiv_within.hasDerivAt
      (Icc_mem_nhds (hball_Ioo s hs).1 (hball_Ioo s hs).2)
    rw [← heatDu_eq_secondValue u₀ hs_pos] at hderiv
    exact ShenWork.IntervalFlooredSourceTimeDataIterate.hasDerivAt_srcSlice1
      (hfloor s hs_pos x hxIcc) hderiv (heatDu_hasDerivAt _hu₀_bound hs_pos)
  · -- (c) Joint ContinuousOn of srcSlice2 on slab
    sorry

/-! ## The main construction -/

/-- **`FlooredSourceTimeData` for the heat semigroup base iterate.**

For `u = conjugatePicardIter p u₀ 0 = S(t)u₀`, this packages the three
time-derivative slices of the source `srcSlice p u t x = ν·(S(t)u₀(x))^γ`
with the six `FlooredSourceTimeData` fields.

Each field is sorry'd as a named atomic obligation; once all 6 are discharged,
the entire `heatSemigroup_level0_resolverJointC2Data` follows by the committed
chain `FlooredSourceTimeData → physicalSourceTimeC2_of_floored →
physicalResolverJointC2Data_of_floor`. -/
theorem heatSemigroup_flooredSourceTimeData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    FlooredSourceTimeData p (conjugatePicardIter p u₀ 0)
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) where
  d0 τ hτ := heatSemigroup_d0 _hu₀_bound _hu₀_cont hfloor τ hτ
  d1 τ hτ := heatSemigroup_d1 _hu₀_bound _hu₀_cont hfloor τ hτ
  sliceC2 i hi t ht := by
    -- OBLIGATION: ∀ i ≤ 2, ∀ t > 0, ContDiffOn ℝ 2 (slice_i t) [0,1]
    -- For t > 0 and i = 0: srcSlice = ν·(S(t)u₀)^γ.  The heat semigroup gives C⁴
    --   in space for t > 0 (from heatSemigroup_contDiff_four), and S(t)u₀ > 0 on (0,1)
    --   (heat floor), so rpow is C² on [0,1].
    -- For t > 0 and i = 1: srcSlice1 = ν·γ·u^{γ-1}·du where du is the spectral
    --   Laplacian (also C² in space for t > 0).
    -- For t > 0 and i = 2: srcSlice2 is a combination of u^{γ-2}·du² + u^{γ-1}·d2u,
    --   both C² under the floor.
    -- The old t ≤ 0 case is eliminated by the weakening.
    sorry
  sliceNeumann i hi t ht := by
    -- OBLIGATION: ∀ i ≤ 2, ∀ t > 0, deriv (slice_i t) vanishes at 0 and 1
    -- For the heat semigroup, the Neumann eigenfunction expansion guarantees
    -- that the spatial derivatives of S(t)u₀ satisfy Neumann BCs (deriv cos(kπx)
    -- vanishes at 0 and 1).  The chain/product rule through rpow preserves this
    -- because deriv(u^γ) = γ·u^{γ-1}·u' and u' = 0 at the boundary.
    sorry
  zerothBound i hi := by
    -- OBLIGATION: ∀ i ≤ 2, ∃ D ≥ 0, ∀ t > 0, |cosineCoeffs (slice_i t) 0| ≤ D
    -- The zeroth cosine coefficient is the integral ∫₀¹ f(x) dx.
    -- For the heat semigroup: S(t)u₀ is bounded by M₀ (coefficient bound gives
    -- sup-norm bound via the cosine series), so srcSlice = ν·u^γ is bounded by
    -- ν·M₀^γ.  Similarly for s₁ and s₂ (their integrals are bounded by products
    -- of sup-norm bounds of u, du, d2u on [0,1]).
    sorry
  laplBound i hi := by
    -- OBLIGATION: ∀ i ≤ 2, ∃ M ≥ 0, ∀ t > 0, ∀ k, 1 ≤ k →
    --   |cosineCoeffs (slice_i t) k| ≤ M / (kπ)²
    -- This is the IBP decay from the committed `cosineCoeff_decay`: when the
    -- slice is C² on [0,1] with Neumann BCs, integration by parts twice gives
    --   |â_k| ≤ (1/(kπ)²) · sup |Δ(slice)|
    -- The uniform-in-positive-t Laplacian bound follows from the spatial C² data
    -- and the uniform sup-norm bounds of the iterated Laplacian.
    sorry

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
