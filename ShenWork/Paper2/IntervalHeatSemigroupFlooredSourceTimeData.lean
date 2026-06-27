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
import ShenWork.PDE.HasDerivWithinAtTsum
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.Paper2.IntervalDuhamelIntegrability

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam FlooredSourceTimeData)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2 hasDerivAt_srcSlice hasDerivAt_srcSlice1)
open ShenWork.IntervalPicardLevel0SourceTimeC1On
  (heatCoeff heatSlice_field_hasDerivWithinAt heatSlice_profile_jointContinuousOn
   heatSlice_secondValue_jointContinuousOn)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

/-! ## Heat semigroup positivity from positive initial data -/

/-- The heat semigroup applied to strictly positive continuous initial data is
strictly positive for all `t > 0` and `x ∈ [0,1]`.

Proof: continuous `u₀ > 0` on compact `intervalDomainPoint` has `inf u₀ > 0`,
so `intervalDomainLift u₀ ≥ inf u₀` on `[0,1]`; the semigroup lower bound
`intervalFullSemigroupOperator_lower_bound` then gives `S(t)(lift u₀)(x) ≥ inf u₀ > 0`. -/
theorem heatSemigroup_pos_of_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
  haveI : CompactSpace intervalDomainPoint := isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : Nonempty intervalDomainPoint := ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩⟩
  obtain ⟨xmin, _, hmin⟩ := IsCompact.exists_isMinOn isCompact_univ
    Set.univ_nonempty hu₀_cont.continuousOn
  set c := u₀ xmin
  have hc_pos : 0 < c := hu₀_pos xmin
  obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
    Set.univ_nonempty hu₀_cont.abs.continuousOn
  set B := |u₀ xmax|
  have hlift_lower : ∀ y, y ∈ Icc (0 : ℝ) 1 → c ≤ intervalDomainLift u₀ y := by
    intro y hy
    let ypt : intervalDomainPoint := ⟨y, hy⟩
    unfold intervalDomainLift
    rw [dif_pos hy]
    exact hmin (Set.mem_univ ypt)
  have hlift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ B := by
    intro y; unfold intervalDomainLift
    split_ifs with hy
    · let ypt : intervalDomainPoint := ⟨y, hy⟩
      exact hmax (Set.mem_univ ypt)
    · simpa [B] using (abs_nonneg (u₀ xmax))
  have hcB : c ≤ B := by
    have hxmin_lift : intervalDomainLift u₀ xmin.1 = u₀ xmin := by
      simp [intervalDomainLift, xmin.2]
    calc c = intervalDomainLift u₀ xmin.1 := by
          rw [hxmin_lift]
      _ ≤ |intervalDomainLift u₀ xmin.1| := le_abs_self _
      _ ≤ B := hlift_bound xmin.1
  have hlift_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont
  simp only [conjugatePicardIter]; unfold intervalDomainLift; rw [dif_pos hx]
  calc (0 : ℝ) < c := hc_pos
    _ ≤ intervalFullSemigroupOperator t (intervalDomainLift u₀) x :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
          ht hc_pos.le hcB hlift_meas hlift_lower hlift_bound x

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

set_option maxHeartbeats 8000000 in
theorem heatSemigroup_d0
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

/-! ## Helper: HasDerivAt of heatDu in time (needed for d1)

Termwise differentiation of the Laplacian cosine series via
`hasDerivWithinAt_tsum` on `Ioi(t/2)`, then convert to `HasDerivAt`.
Proof body from ChatGPT Q1249 (cron1). -/

local notation "λ_" n => unitIntervalCosineEigenvalue n

private theorem unitIntervalCosineEigenvalue_sq_exp_summable
    {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => (λ_ n) ^ 2 * Real.exp (-r * (λ_ n)) := by
  set ρ : ℝ := r * Real.pi ^ 2
  have hρ : 0 < ρ := by positivity
  have hbase : Summable fun n : ℕ =>
      Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 4 (r := ρ) hρ).mul_left (Real.pi ^ 4)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      by_cases hn : n = 0
      · subst n; norm_num
      · nlinarith [Nat.pos_of_ne_zero hn, show (1 : ℝ) ≤ (n : ℝ) from
          by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)]
    have hlam_eq : (λ_ n) = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue; ring
    have hlam_sq_eq : (λ_ n) ^ 2 = (n : ℝ) ^ 4 * Real.pi ^ 4 := by
      rw [hlam_eq]; ring
    have hexp_le : Real.exp (-r * (λ_ n)) ≤ Real.exp (-ρ * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hn_sq_ge hρ.le]
    calc (λ_ n) ^ 2 * Real.exp (-r * (λ_ n))
        = ((n : ℝ) ^ 4 * Real.pi ^ 4) * Real.exp (-r * (λ_ n)) := by rw [hlam_sq_eq]
      _ ≤ ((n : ℝ) ^ 4 * Real.pi ^ 4) * Real.exp (-ρ * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by ring

private theorem heatLaplacianTerm_hasDerivAt_time
    (a : ℕ → ℝ) (x t : ℝ) (n : ℕ) :
    HasDerivAt
      (fun τ : ℝ =>
        ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight τ x n * a n)
      ((λ_ n) ^ 2 * (Real.exp (-t * (λ_ n)) * a n) * ShenWork.CosineSpectrum.cosineMode n x) t := by
  have hlin : HasDerivAt (fun τ : ℝ => -τ * (λ_ n)) (-(λ_ n)) t := by
    simpa [mul_comm] using (hasDerivAt_id t).neg.mul_const (λ_ n)
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-τ * (λ_ n)))
      (-(λ_ n) * Real.exp (-t * (λ_ n))) t := by
    simpa [mul_comm] using hlin.exp
  have h := ((hexp.mul_const (ShenWork.CosineSpectrum.cosineMode n x)).const_mul
    (-(λ_ n))).mul_const (a n)
  have h' : HasDerivAt
      (fun y => -(a n * ((λ_ n) *
        (Real.cos (x * (Real.pi * (n : ℝ))) * Real.exp (-(y * (λ_ n)))))))
      (a n * ((λ_ n) * ((λ_ n) *
        (Real.cos (x * (Real.pi * (n : ℝ))) * Real.exp (-(t * (λ_ n))))))) t := by
    simpa [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
      unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
      ShenWork.CosineSpectrum.cosineMode, mul_assoc, mul_left_comm, mul_comm] using h
  convert h' using 1
  · funext y
    ring
  · ring

private theorem summable_heatLaplacian_terms_of_bound
    {a : ℕ → ℝ} {M t x : ℝ} (ht : 0 < t)
    (ha : ∀ n, |a n| ≤ M) :
    Summable fun n : ℕ =>
      ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n * a n := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  have hmajor : Summable fun n : ℕ =>
      M * ((λ_ n) * Real.exp (-t * (λ_ n))) :=
    (unitIntervalCosineEigenvalue_mul_exp_summable ht).mul_left M
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => M * ((λ_ n) * Real.exp (-t * (λ_ n)))) hmajor ?_
  intro n
  have hlam_nn : 0 ≤ λ_ n := by unfold unitIntervalCosineEigenvalue; positivity
  have hcos : |Real.cos ((n : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
  have hA_nonneg : 0 ≤ (λ_ n) * Real.exp (-t * (λ_ n)) :=
    mul_nonneg hlam_nn (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_mul]
  calc |ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n| * |a n|
      = ((λ_ n) * Real.exp (-t * (λ_ n)) * |Real.cos ((n : ℝ) * Real.pi * x)|) *
          |a n| := by
        simp only [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
          unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, abs_mul,
          abs_of_nonneg hlam_nn, abs_of_nonneg (Real.exp_nonneg _), abs_neg]
        ring
      _ ≤ ((λ_ n) * Real.exp (-t * (λ_ n)) * 1) * M := by
        calc ((λ_ n) * Real.exp (-t * (λ_ n)) * |Real.cos ((n : ℝ) * Real.pi * x)|) *
              |a n|
            ≤ ((λ_ n) * Real.exp (-t * (λ_ n)) * 1) * |a n| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcos hA_nonneg) (abs_nonneg _)
          _ ≤ ((λ_ n) * Real.exp (-t * (λ_ n)) * 1) * M := by
              exact mul_le_mul_of_nonneg_left (ha n)
                (mul_nonneg hA_nonneg zero_le_one)
    _ = M * ((λ_ n) * Real.exp (-t * (λ_ n))) := by ring

private theorem heatD2Term_abs_le_majorant
    {a : ℕ → ℝ} {M r τ x : ℝ}
    (ha : ∀ n, |a n| ≤ M) (hτ : τ ∈ Ioi r) (n : ℕ) :
    |(λ_ n) ^ 2 * (Real.exp (-τ * (λ_ n)) * a n) * ShenWork.CosineSpectrum.cosineMode n x|
      ≤ M * ((λ_ n) ^ 2 * Real.exp (-r * (λ_ n))) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  have hlam_nn : 0 ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
  have hcos : |ShenWork.CosineSpectrum.cosineMode n x| ≤ 1 := by
    simp only [ShenWork.CosineSpectrum.cosineMode]; exact Real.abs_cos_le_one _
  have hexp_mono : Real.exp (-τ * (λ_ n)) ≤ Real.exp (-r * (λ_ n)) := by
    have hmul : r * (λ_ n) ≤ τ * (λ_ n) :=
      mul_le_mul_of_nonneg_right (le_of_lt (mem_Ioi.mp hτ)) hlam_nn
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc |(λ_ n) ^ 2 * (Real.exp (-τ * (λ_ n)) * a n) * ShenWork.CosineSpectrum.cosineMode n x|
      = (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * |a n| * |ShenWork.CosineSpectrum.cosineMode n x| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
          abs_of_nonneg (Real.exp_nonneg _)]; ring
    _ ≤ (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * M * 1 := by
        have hA_nonneg : 0 ≤ (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) :=
          mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
        calc (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * |a n| *
                |ShenWork.CosineSpectrum.cosineMode n x|
            ≤ (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * M *
                |ShenWork.CosineSpectrum.cosineMode n x| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (ha n) hA_nonneg) (abs_nonneg _)
          _ ≤ (λ_ n) ^ 2 * Real.exp (-τ * (λ_ n)) * M * 1 := by
              exact mul_le_mul_of_nonneg_left hcos
                (mul_nonneg hA_nonneg hM)
    _ ≤ (λ_ n) ^ 2 * Real.exp (-r * (λ_ n)) * M := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp_mono (sq_nonneg _)) hM
    _ = M * ((λ_ n) ^ 2 * Real.exp (-r * (λ_ n))) := by ring

private theorem heatDu_hasDerivAt
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => heatDu u₀ r x) (heatD2u u₀ t x) t := by
  let a : ℕ → ℝ := cosineCoeffs (intervalDomainLift u₀)
  let r : ℝ := t / 2
  have hr : 0 < r := by positivity
  have hrt : t ∈ Ioi r := by
    show r < t
    dsimp [r]
    linarith
  let F : ℕ → ℝ → ℝ := fun n τ =>
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight τ x n * a n
  let F' : ℕ → ℝ → ℝ := fun n τ =>
    (λ_ n) ^ 2 * (Real.exp (-τ * (λ_ n)) * a n) * ShenWork.CosineSpectrum.cosineMode n x
  let u : ℕ → ℝ := fun n => M₀ * ((λ_ n) ^ 2 * Real.exp (-r * (λ_ n)))
  have hu : Summable u := by
    simpa [u] using (unitIntervalCosineEigenvalue_sq_exp_summable hr).mul_left M₀
  have hF : ∀ n, ∀ τ ∈ Ioi r, HasDerivWithinAt (F n) (F' n τ) (Ioi r) τ := by
    intro n τ _hτ
    exact (heatLaplacianTerm_hasDerivAt_time a x τ n).hasDerivWithinAt
  have hbound : ∀ n, ∀ τ ∈ Ioi r, |F' n τ| ≤ u n := by
    intro n τ hτ
    exact heatD2Term_abs_le_majorant hu₀_bound hτ n
  have hF0 : Summable fun n => F n t := by
    exact summable_heatLaplacian_terms_of_bound ht hu₀_bound
  have hwithin := ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum
    (convex_Ioi r) hu hF hbound hrt hF0 hrt
  have hAtSum := hwithin.hasDerivAt (isOpen_Ioi.mem_nhds hrt)
  have hbranch : (fun τ => heatDu u₀ τ x) =ᶠ[𝓝 t] (fun τ => ∑' n, F n τ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hrt] with τ hτ
    have hτpos : 0 < τ := lt_trans hr hτ
    simp only [heatDu, if_pos hτpos, F, a,
      ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue]
  have hvalue : (∑' n, F' n t) = heatD2u u₀ t x := by
    simp only [heatD2u, if_pos ht, F', ShenWork.CosineSpectrum.cosineMode]
  rw [← hvalue]
  exact hAtSum.congr_of_eventuallyEq hbranch

/-! ## Helper: joint continuity of heatD2u on a positive slab -/

private theorem heatD2u_jointContinuousOn
    {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn (fun q : ℝ × ℝ => heatD2u u₀ q.1 q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  have hM₀ : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  -- On the slab, all times are positive, so the if-branch of heatD2u is active
  have hcongr : ∀ q ∈ Icc c T ×ˢ Icc (0 : ℝ) 1,
      heatD2u u₀ q.1 q.2 =
        ∑' k : ℕ, unitIntervalCosineEigenvalue k ^ 2 *
          (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
            cosineCoeffs (intervalDomainLift u₀) k) *
          ShenWork.CosineSpectrum.cosineMode k q.2 := by
    intro q hq
    have hpos : 0 < q.1 := lt_of_lt_of_le hc (mem_prod.mp hq).1.1
    simp only [heatD2u, if_pos hpos]
  refine (ContinuousOn.congr ?_ hcongr)
  apply continuousOn_tsum
  · intro k
    have hcos : Continuous (fun y : ℝ => ShenWork.CosineSpectrum.cosineMode k y) := by
      unfold ShenWork.CosineSpectrum.cosineMode
      fun_prop
    exact ((((Real.continuous_exp.comp
      (continuous_id.neg.mul continuous_const)).mul continuous_const).const_mul _).comp
        continuous_fst).mul
      (hcos.comp continuous_snd)
      |>.continuousOn
  · exact (unitIntervalCosineEigenvalue_sq_exp_summable hc).mul_left M₀
  · intro k q hq
    have hpos : 0 < q.1 := lt_of_lt_of_le hc (mem_prod.mp hq).1.1
    have hlam_nn : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
    have hexp_mono : Real.exp (-q.1 * (λ_ k)) ≤ Real.exp (-c * (λ_ k)) := by
      have hmul : c * (λ_ k) ≤ q.1 * (λ_ k) :=
        mul_le_mul_of_nonneg_right (mem_prod.mp hq).1.1 hlam_nn
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hcos : |ShenWork.CosineSpectrum.cosineMode k q.2| ≤ 1 := by
      unfold ShenWork.CosineSpectrum.cosineMode
      exact Real.abs_cos_le_one _
    have hA_nonneg :
        0 ≤ (λ_ k) ^ 2 * Real.exp (-q.1 * (λ_ k)) :=
      mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
    rw [Real.norm_eq_abs]
    calc |(λ_ k) ^ 2 * (Real.exp (-q.1 * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k) *
            ShenWork.CosineSpectrum.cosineMode k q.2|
        = (λ_ k) ^ 2 * Real.exp (-q.1 * (λ_ k)) *
            |cosineCoeffs (intervalDomainLift u₀) k| *
            |ShenWork.CosineSpectrum.cosineMode k q.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
            abs_of_nonneg (Real.exp_nonneg _)]; ring
      _ ≤ (λ_ k) ^ 2 * Real.exp (-c * (λ_ k)) * M₀ * 1 := by
          calc (λ_ k) ^ 2 * Real.exp (-q.1 * (λ_ k)) *
                  |cosineCoeffs (intervalDomainLift u₀) k| *
                  |ShenWork.CosineSpectrum.cosineMode k q.2|
              ≤ (λ_ k) ^ 2 * Real.exp (-q.1 * (λ_ k)) * M₀ *
                  |ShenWork.CosineSpectrum.cosineMode k q.2| := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hu₀_bound k) hA_nonneg)
                  (abs_nonneg _)
            _ ≤ (λ_ k) ^ 2 * Real.exp (-q.1 * (λ_ k)) * M₀ * 1 := by
                exact mul_le_mul_of_nonneg_left hcos
                  (mul_nonneg hA_nonneg hM₀)
            _ ≤ (λ_ k) ^ 2 * Real.exp (-c * (λ_ k)) * M₀ * 1 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hexp_mono (sq_nonneg _)) hM₀)
                  zero_le_one
      _ = M₀ * ((λ_ k) ^ 2 * Real.exp (-c * (λ_ k))) := by ring

/-! ## Helper lemmas for d1 (split for heartbeat budget) -/

set_option maxHeartbeats 800000 in
private theorem heatSemigroup_d1_partA
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {τ δ : ℝ} (hδ : 0 < δ) (hleft : 0 < τ - δ)
    (hball_Icc : ∀ s, s ∈ Metric.ball τ δ → s ∈ Icc (τ - δ) (τ + δ)) :
    ∀ᶠ s in 𝓝 τ, ContinuousOn
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) s) (Icc (0:ℝ) 1) := by
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using heatSlice_profile_jointContinuousOn p
      (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft hu₀_cont hu₀_bound
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
      (u₀ := u₀) (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft hu₀_bound
    exact hsecond.congr (fun q hq => by
      obtain ⟨hσ, _hx⟩ := mem_prod.mp hq
      simpa [heatCoeff] using
        (heatDu_eq_secondValue u₀ (lt_of_lt_of_le hleft hσ.1)).symm)
  have hsrc1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ * (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1)
        * heatDu u₀ q.1 q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    ((continuousOn_const.mul continuousOn_const).mul hpow1).mul hdu_joint
  filter_upwards [Metric.ball_mem_nhds τ hδ] with s hs
  exact hsrc1.comp (continuousOn_const.prodMk continuousOn_id)
    (fun x hx => mem_prod.mpr ⟨hball_Icc s hs, hx⟩)

set_option maxHeartbeats 1600000 in
private theorem heatSemigroup_d1_partB
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {τ δ : ℝ} (hleft : 0 < τ - δ)
    (hball_pos : ∀ s, s ∈ Metric.ball τ δ → 0 < s)
    (hball_Icc : ∀ s, s ∈ Metric.ball τ δ → s ∈ Icc (τ - δ) (τ + δ))
    (hball_Ioo : ∀ s, s ∈ Metric.ball τ δ → s ∈ Ioo (τ - δ) (τ + δ)) :
    ∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r x)
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) s x) s := by
  intro x hx s hs
  have hs_pos := hball_pos s hs
  have hxIcc : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
  have hderiv_within := heatSlice_field_hasDerivWithinAt p
    (c := τ - δ) (T := τ + δ) hleft (hball_Icc s hs) hu₀_cont hu₀_bound hxIcc
  have hderiv := hderiv_within.hasDerivAt
    (Icc_mem_nhds (hball_Ioo s hs).1 (hball_Ioo s hs).2)
  rw [← heatDu_eq_secondValue u₀ hs_pos] at hderiv
  exact ShenWork.IntervalFlooredSourceTimeDataIterate.hasDerivAt_srcSlice1
    (hfloor s hs_pos x hxIcc) hderiv (heatDu_hasDerivAt hu₀_bound hs_pos)

set_option maxHeartbeats 1600000 in
private theorem heatSemigroup_d1_partC
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {τ δ : ℝ} (hleft : 0 < τ - δ) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ * (p.γ - 1) *
          (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1 - 1) *
          (heatDu u₀ q.1 q.2) ^ (2 : ℕ) +
        p.ν * p.γ *
          (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1) *
          heatD2u u₀ q.1 q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  have hprofile : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using heatSlice_profile_jointContinuousOn p
      (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft hu₀_cont hu₀_bound
  have hpow1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    hprofile.rpow_const (fun q hq => by
      obtain ⟨hσ, hx⟩ := mem_prod.mp hq
      exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
  have hpow2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1 - 1))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    hprofile.rpow_const (fun q hq => by
      obtain ⟨hσ, hx⟩ := mem_prod.mp hq
      exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
  have hdu_joint : ContinuousOn
      (fun q : ℝ × ℝ => heatDu u₀ q.1 q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
    have hsecond := heatSlice_secondValue_jointContinuousOn
      (u₀ := u₀) (c := τ - δ) (T := τ + δ) (M₀ := M₀) hleft hu₀_bound
    exact hsecond.congr (fun q hq => by
      obtain ⟨hσ, _hx⟩ := mem_prod.mp hq
      simpa [heatCoeff] using
        (heatDu_eq_secondValue u₀ (lt_of_lt_of_le hleft hσ.1)).symm)
  exact ((((continuousOn_const.mul continuousOn_const).mul continuousOn_const).mul
      hpow2).mul (hdu_joint.pow 2)).add
    (((continuousOn_const.mul continuousOn_const).mul hpow1).mul
      (heatD2u_jointContinuousOn hleft hu₀_bound))

/-! ## d1: assembly from parts -/

theorem heatSemigroup_d1
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
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
  set δ : ℝ := min 1 (τ / 2)
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
  exact ⟨δ, hδ,
    heatSemigroup_d1_partA hu₀_bound hu₀_cont hfloor hδ hleft hball_Icc,
    heatSemigroup_d1_partB hu₀_bound hu₀_cont hfloor hleft hball_pos hball_Icc hball_Ioo,
    heatSemigroup_d1_partC hu₀_bound hu₀_cont hfloor hleft⟩

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
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hsliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
      ContDiffOn ℝ 2 ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t)
        (Icc (0:ℝ) 1))
    (hsliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
      Tendsto (deriv ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t))
        (𝓝[Ioi 0] 0) (𝓝 0) ∧
      Tendsto (deriv ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t))
        (𝓝[Iio 1] 1) (𝓝 0) ∧
      deriv ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t) 0 = 0 ∧
      deriv ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t) 1 = 0)
    (hzerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
      |cosineCoeffs ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t) 0| ≤ D)
    (hlaplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
      |cosineCoeffs ((sliceFam (srcSlice p (conjugatePicardIter p u₀ 0))
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) i) t) k|
        ≤ M / ((k:ℝ) * Real.pi) ^ 2) :
    FlooredSourceTimeData p (conjugatePicardIter p u₀ 0)
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) where
  d0 τ hτ := heatSemigroup_d0 _hu₀_bound _hu₀_cont hfloor τ hτ
  d1 τ hτ := heatSemigroup_d1 _hu₀_bound _hu₀_cont hfloor τ hτ
  sliceC2 := hsliceC2
  sliceNeumann := hsliceNeumann
  zerothBound := hzerothBound
  laplBound := hlaplBound

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
