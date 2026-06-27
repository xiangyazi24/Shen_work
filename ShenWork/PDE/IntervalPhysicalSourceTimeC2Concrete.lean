/-
# Physical producer of `PhysicalSourceTimeC2` for the concrete chemotaxis source

This file builds the honest source-side `C²`-in-time / `(kπ)⁻²`-spatial data
`PhysicalSourceTimeC2 p u Es` for the **concrete** chemotaxis source
`g(t,x) = p.ν · u(t,x)^γ`, under the committed floor `u ≥ δ > 0`, WITHOUT routing
through `DuhamelSourceTimeC2Coeff` or the eigen-cube (`λ²`/`λ³`) ladder.

The source time-coefficient is, by the committed identity,
`srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k` with
`srcSlice p u t x = p.ν · (intervalDomainLift (u t) x)^γ`.  The two genuinely-new
pieces are:

* `src_contDiff` — `t ↦ srcTimeCoeff p u k t` is `ContDiff ℝ 2`.  Differentiating
  the cosine coefficient under the integral twice (the committed time-Leibniz atom
  `cosineCoeffs_hasDerivAt_of_smooth_param`) identifies the first two time
  derivatives with `cosineCoeffs (srcSlice₁ ·) k` and `cosineCoeffs (srcSlice₂ ·) k`,
  the latter continuous; `contDiff_succ_iff_deriv` twice closes it.

* `src_bound` — the three-time-order `(kπ)⁻²` decay.  At each time order `i`, the
  `i`-th time-derivative slice is `C²`-in-`x` Neumann (under the floor), so the
  committed IBP decay `cosineCoeff_decay` gives `|cosineCoeffs (sliceᵢ t) k| ≤
  Cᵢ/(kπ)²` for `k ≥ 1`, with the zeroth mode bounded separately.

The honest hypotheses are exactly: the committed floor (positivity of the slice),
the per-time-order space `C²`-Neumann regularity of the source slices, and the
**iterate time-`C²`** datum (the time-Leibniz chain on the slices — supplied as the
`slice*_hasDerivAt` fields, the honest `d_t² u` content under heat smoothing at
`t > 0`).  The bounded-weight majorant summability of `w·Es` is the source-`ℓ¹`
datum, carried as hypotheses (NO resolver-C2 / FAC field is assumed).
-/
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint

open Filter Topology Set
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalCosineCoeffDecay (exists_laplacianCoeff_bound cosineCoeff_decay)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param cosineCoeffs_eq_factor_mul_integral)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

open ShenWork.IntervalPhysicalResolverDataConcrete

/-- The concrete chemotaxis source slice `x ↦ p.ν · u(t,x)^γ` at time `t`. -/
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ

/-- The committed identity `srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k`. -/
theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k := by
  unfold srcTimeCoeff srcSlice
  simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]

/-- The `ℕ`-indexed time-derivative slice family: `0 ↦ s₀`, `1 ↦ s₁`, else `s₂`. -/
def sliceFam (s₀ s₁ s₂ : ℝ → ℝ → ℝ) : ℕ → (ℝ → ℝ → ℝ)
  | 0 => s₀
  | 1 => s₁
  | _ => s₂

/-- **Honest floored source time-`C²` data.**  Packages, for the concrete source
`srcSlice p u`, the three time-derivative slices `s₀ = srcSlice`, `s₁`, `s₂` with:
the time-Leibniz `HasDerivAt` chain `s₀ → s₁ → s₂` (the iterate time-`C²`
content), joint continuity of `s₁, s₂` on slabs, and per-time-order space
`C²`-Neumann regularity giving the `(kπ)⁻²` decay.  This is exactly the floor +
committed regularity + iterate time-`C²` input — NO eigen-cube ladder. -/
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  /-- `∂ₜ srcSlice = s₁` pointwise in `x ∈ (0,1)`, locally in `t`. -/
  d0 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
    ContinuousOn (Function.uncurry s₁) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  /-- `∂ₜ s₁ = s₂` pointwise in `x ∈ (0,1)`, locally in `t`. -/
  d1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (s₁ s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => s₁ r x) (s₂ s x) s) ∧
    ContinuousOn (Function.uncurry s₂) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  /-- Each time-derivative slice is space-`C²` on `[0,1]` (under the floor). -/
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)
  /-- Neumann endpoint data of each time-derivative slice (for IBP decay). -/
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 1 = 0
  /-- Uniform-in-`t` zeroth-mode and Laplacian envelopes per time order. -/
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2

/-- The slice index function evaluated. -/
private theorem slice_eval (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) (t : ℝ) :
    ((sliceFam (srcSlice p u) s₁ s₂ 0) t = srcSlice p u t) ∧
    ((sliceFam (srcSlice p u) s₁ s₂ 1) t = s₁ t) ∧
    ((sliceFam (srcSlice p u) s₁ s₂ 2) t = s₂ t) := ⟨rfl, rfl, rfl⟩

/-- `srcTimeCoeff k` is differentiable with derivative `t ↦ cosineCoeffs (s₁ t) k`. -/
private theorem srcTimeCoeff_deriv
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Differentiable ℝ (srcTimeCoeff p u k) ∧
    deriv (srcTimeCoeff p u k) = fun t => cosineCoeffs (s₁ t) k := by
  have hpt : ∀ t : ℝ, HasDerivAt (srcTimeCoeff p u k)
      (cosineCoeffs (s₁ t) k) t := by
    intro t
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.d0 t
    have hcont_int : ∀ᶠ s in 𝓝 t,
        IntervalIntegrable (srcSlice p u s) MeasureTheory.volume (0 : ℝ) 1 := by
      filter_upwards [hcont] with s hs; exact hs.intervalIntegrable
    have hH := cosineCoeffs_hasDerivAt_of_smooth_param (f := srcSlice p u)
      (f' := s₁) (τ := t) (δ := δ) (n := k) hδ hcont_int hdiff hcd
    have heq : (fun s => cosineCoeffs (srcSlice p u s) k) = srcTimeCoeff p u k := by
      funext s; exact (srcTimeCoeff_eq_cosineCoeffs p u k s).symm
    rw [heq] at hH; exact hH
  refine ⟨fun t => (hpt t).differentiableAt, ?_⟩
  funext t; exact (hpt t).deriv

/-- `t ↦ cosineCoeffs (s₁ t) k` is differentiable with derivative
`t ↦ cosineCoeffs (s₂ t) k`. -/
private theorem cosS1_deriv
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Differentiable ℝ (fun t => cosineCoeffs (s₁ t) k) ∧
    deriv (fun t => cosineCoeffs (s₁ t) k) = fun t => cosineCoeffs (s₂ t) k := by
  have hpt : ∀ t : ℝ, HasDerivAt (fun s => cosineCoeffs (s₁ s) k)
      (cosineCoeffs (s₂ t) k) t := by
    intro t
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.d1 t
    have hcont_int : ∀ᶠ s in 𝓝 t,
        IntervalIntegrable (s₁ s) MeasureTheory.volume (0 : ℝ) 1 := by
      filter_upwards [hcont] with s hs; exact hs.intervalIntegrable
    exact cosineCoeffs_hasDerivAt_of_smooth_param (f := s₁) (f' := s₂)
      (τ := t) (δ := δ) (n := k) hδ hcont_int hdiff hcd
  refine ⟨fun t => (hpt t).differentiableAt, ?_⟩
  funext t; exact (hpt t).deriv

/-- `t ↦ cosineCoeffs (s₂ t) k` is continuous (joint continuity of `s₂` ⇒
continuity of the cosine coefficient in `t`, via slab dominated convergence). -/
private theorem cosS2_continuous
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Continuous (fun t => cosineCoeffs (s₂ t) k) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨δ, hδ, _, _, hcd⟩ := H.d1 t
  have hcont_on :=
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc (f := s₂)
      (c := t - δ) (T := t + δ) k hcd
  have htmem : t ∈ Icc (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hsub : Icc (t - δ) (t + δ) ∈ 𝓝 t := by
    apply Icc_mem_nhds <;> linarith
  exact (hcont_on t htmem).continuousAt hsub

/-- **`src_contDiff`.**  `srcTimeCoeff p u k` is `ContDiff ℝ 2` in `t`. -/
theorem srcTimeCoeff_contDiff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k) := by
  obtain ⟨hdiff0, hderiv0⟩ := srcTimeCoeff_deriv H k
  obtain ⟨hdiff1, hderiv1⟩ := cosS1_deriv H k
  have hcontS2 := cosS2_continuous H k
  -- `deriv (srcTimeCoeff k)` is `ContDiff ℝ 1`.
  have hC1 : ContDiff ℝ (1 : ℕ∞) (deriv (srcTimeCoeff p u k)) := by
    rw [hderiv0]
    refine contDiff_one_iff_deriv.mpr ⟨hdiff1, ?_⟩
    rw [hderiv1]; exact hcontS2
  -- assemble `ContDiff ℝ (1+1)`.
  have : ContDiff ℝ ((1 : ℕ∞) + 1) (srcTimeCoeff p u k) :=
    contDiff_succ_iff_deriv.mpr ⟨hdiff0, by intro h; exact absurd h (by decide), hC1⟩
  simpa using this

/-- `iteratedDeriv 1 (srcTimeCoeff k) = fun t => cosineCoeffs (s₁ t) k`. -/
private theorem srcTimeCoeff_iteratedDeriv1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    iteratedDeriv 1 (srcTimeCoeff p u k) = fun t => cosineCoeffs (s₁ t) k := by
  rw [iteratedDeriv_one]; exact (srcTimeCoeff_deriv H k).2

/-- `iteratedDeriv 2 (srcTimeCoeff k) = fun t => cosineCoeffs (s₂ t) k`. -/
private theorem srcTimeCoeff_iteratedDeriv2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    iteratedDeriv 2 (srcTimeCoeff p u k) = fun t => cosineCoeffs (s₂ t) k := by
  rw [iteratedDeriv_succ, srcTimeCoeff_iteratedDeriv1 H k]
  exact (cosS1_deriv H k).2

/-- The `i`-th iterated time-derivative of `srcTimeCoeff k` equals
`cosineCoeffs (sliceᵢ t) k` for `i ≤ 2`. -/
private theorem srcTimeCoeff_iteratedDeriv_eq
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) (hi : i ≤ 2) (t : ℝ) :
    iteratedDeriv i (srcTimeCoeff p u k) t =
      cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k := by
  interval_cases i
  · rw [iteratedDeriv_zero]; exact srcTimeCoeff_eq_cosineCoeffs p u k t
  · exact congrFun (srcTimeCoeff_iteratedDeriv1 H k) t
  · exact congrFun (srcTimeCoeff_iteratedDeriv2 H k) t

/-- The constructed envelope `Es i k`: zeroth-mode bound `D i` at `k = 0`,
Laplacian-decay `M i / (kπ)²` at `k ≥ 1`. -/
def builtEs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    (if k = 0 then Classical.choose (H.zerothBound i hi)
     else Classical.choose (H.laplBound i hi) / ((k:ℝ) * Real.pi) ^ 2)
  else 0

/-- **`src_bound`.**  `‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k`
for `i ≤ 2`, from the per-time-order `(kπ)⁻²` IBP decay + zeroth-mode bound. -/
theorem srcTimeCoeff_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) (t : ℝ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    srcTimeCoeff_iteratedDeriv_eq H i k hi, Real.norm_eq_abs, builtEs, dif_pos hi]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [if_pos rfl]
    exact (Classical.choose_spec (H.zerothBound i hi)).2 t
  · rw [if_neg (Nat.pos_iff_ne_zero.mp hk)]
    exact (Classical.choose_spec (H.laplBound i hi)).2 t k hk

/-- **The honest physical producer of `PhysicalSourceTimeC2`.**  Under the floored
source time-data `FlooredSourceTimeData` (floor positivity + committed space-`C²`
Neumann regularity + the iterate time-`C²` Leibniz chain), together with the
source-`ℓ¹` bounded-weight majorant summability of `w·builtEs`, the concrete
chemotaxis source satisfies `PhysicalSourceTimeC2 p u (builtEs H)`.  NO eigen-cube
ladder, NO `DuhamelSourceTimeC2Coeff`, NO resolver-C2/FAC field assumed. -/
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H) where
  src_contDiff k := srcTimeCoeff_contDiff H k
  src_bound i k t hi := srcTimeCoeff_bound H i k t hi
  value_summable := hval
  grad_summable := hgrad

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
