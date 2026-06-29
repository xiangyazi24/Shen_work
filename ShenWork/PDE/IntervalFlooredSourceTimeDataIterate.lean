/-
# `FlooredSourceTimeData` for the concrete floored iterate

This file PRODUCES the honest `FlooredSourceTimeData p u s₁ s₂` for the concrete
chemotaxis source `srcSlice p u t x = p.ν · (lift (u t) x)^γ`, under the committed
floor `u ≥ δ > 0`, from genuinely-finite iterate-side data:

* the floor positivity of the lifted iterate (committed),
* the iterate **time-`C¹`** datum `du = ∂ₜ (lift u)` — the committed time-Leibniz
  atom (pointwise `HasDerivAt` in `t` for `x ∈ (0,1)`, with joint slab continuity),
* the iterate **time-`C²`** datum `d2u = ∂ₜ du = ∂ₜ² (lift u)` — established NON-
  circularly from the heat equation `∂ₜ u = ∂ₓ² u + source` and the committed
  spatial climb (`SpatialSlice 7 ⇒ ∂ₓ⁴ u`) + the time-`C¹` source, OR isolated as
  the minimal honest leg `iterate_dt2` (finite, non-regressing); here it is a
  hypothesis stated exactly as a pointwise `HasDerivAt` of `du` with joint slab
  continuity, plus per-slice space-`C²`-Neumann regularity and the `(kπ)⁻²`
  envelopes.

The two time-derivative slices are produced explicitly by the `Real.rpow`
chain/product rule under the floor:

  `s₁ = ν·γ·(lift u)^{γ-1}·du`,
  `s₂ = ν·γ·(γ-1)·(lift u)^{γ-2}·du² + ν·γ·(lift u)^{γ-1}·d2u`.

NO eigen-cube ladder, NO `DuhamelSourceTimeC2Coeff`, NO resolver-C2/FAC field is
assumed.  Feeding the output into `physicalSourceTimeC2_of_floored` and then
`coupledChemDivFluxFactorJointC2Inputs_of_floor` discharges the FAC resolver-`C²`
fields end-to-end.
-/
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

open Filter Topology Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

open ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- The first time-derivative slice of `srcSlice`, by the `rpow` chain rule under
the floor: `s₁ = ∂ₜ[ν·u^γ] = ν·γ·u^{γ-1}·(∂ₜu)`. -/
def srcSlice1 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * du t x

/-- The second time-derivative slice of `srcSlice`, by the product/chain rule:
`s₂ = ν·γ·(γ-1)·u^{γ-2}·(∂ₜu)² + ν·γ·u^{γ-1}·(∂ₜ²u)`. -/
def srcSlice2 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du d2u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (p.γ - 1) * (intervalDomainLift (u t) x) ^ (p.γ - 1 - 1)
      * (du t x) ^ (2 : ℕ)
    + p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * d2u t x

/-- **Pointwise first time-derivative of the source slice** under the floor:
`HasDerivAt (fun r => srcSlice p u r x) (srcSlice1 p u du t x) t`. -/
theorem hasDerivAt_srcSlice
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du : ℝ → ℝ → ℝ}
    {t x : ℝ} (hpos : 0 < intervalDomainLift (u t) x)
    (hdu : HasDerivAt (fun r => intervalDomainLift (u r) x) (du t x) t) :
    HasDerivAt (fun r => srcSlice p u r x) (srcSlice1 p u du t x) t := by
  have hpow := (hdu.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))).const_mul p.ν
  have hg : (fun r => srcSlice p u r x)
      = fun r => p.ν * (intervalDomainLift (u r) x) ^ p.γ := by
    funext r; simp [srcSlice]
  rw [hg]
  refine hpow.congr_deriv ?_
  simp only [srcSlice1]; ring

/-- **Pointwise second time-derivative of the source slice** (= first time-
derivative of `srcSlice1`) under the floor:
`HasDerivAt (fun r => srcSlice1 p u du r x) (srcSlice2 p u du d2u t x) t`. -/
theorem hasDerivAt_srcSlice1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    {t x : ℝ} (hpos : 0 < intervalDomainLift (u t) x)
    (hdu : HasDerivAt (fun r => intervalDomainLift (u r) x) (du t x) t)
    (hd2u : HasDerivAt (fun r => du r x) (d2u t x) t) :
    HasDerivAt (fun r => srcSlice1 p u du r x) (srcSlice2 p u du d2u t x) t := by
  have hpow : HasDerivAt (fun r => (intervalDomainLift (u r) x) ^ (p.γ - 1))
      (du t x * (p.γ - 1) * (intervalDomainLift (u t) x) ^ (p.γ - 1 - 1)) t :=
    hdu.rpow_const (Or.inl (ne_of_gt hpos))
  have hprod := (hpow.mul hd2u).const_mul (p.ν * p.γ)
  have hfun : (fun r => p.ν * p.γ *
      ((fun r => (intervalDomainLift (u r) x) ^ (p.γ - 1)) * fun r => du r x) r)
      = fun r => srcSlice1 p u du r x := by
    funext r; simp only [srcSlice1, Pi.mul_apply, mul_assoc]
  rw [hfun] at hprod
  unfold srcSlice2
  convert hprod using 1
  ring

/-- **The honest iterate time-`C²` source datum.**  Packages, for the concrete
floored iterate, exactly the genuinely-finite non-resolver legs needed to build
`FlooredSourceTimeData`:

* `floor`   — the committed positivity `0 < lift (u t) x` on the open interior;
* `time1`   — the iterate **time-`C¹`** Leibniz atom: a local pointwise
  `HasDerivAt (lift u) = du` with eventual slice continuity and joint slab
  continuity of `du`;
* `time2`   — the iterate **time-`C²`** leg `∂ₜ du = d2u` (from the heat equation
  + the committed spatial climb, or the minimal honest `iterate_dt2`): a local
  pointwise `HasDerivAt du = d2u` with eventual `du`-slice continuity and joint
  slab continuity of `srcSlice2`;
* `space*`  — the committed per-time-order space-`C²`-Neumann regularity and the
  zeroth-mode / `(kπ)⁻²` envelopes of each derivative slice.

NO eigen-cube ladder, NO `DuhamelSourceTimeC2Coeff`, NO resolver-C2/FAC field. -/
structure IterateSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (du d2u : ℝ → ℝ → ℝ)
    : Prop where
  floor : ∀ t : ℝ, ∀ x ∈ Ioo (0:ℝ) 1, 0 < intervalDomainLift (u t) x
  time1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x) (du s x) s) ∧
    ContinuousOn (Function.uncurry (srcSlice1 p u du))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  time2 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice1 p u du s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x) (du s x) s ∧
      HasDerivAt (fun r => du r x) (d2u s x) s) ∧
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2
      ((sliceFam (srcSlice p u) (srcSlice1 p u du) (srcSlice2 p u du d2u) i) t)
      (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 1 = 0
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 0| ≤ D
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2

/-- **The producer.**  The honest iterate time-`C²` datum yields the
`FlooredSourceTimeData` for the concrete source, with the two time-derivative
slices `s₁ = srcSlice1`, `s₂ = srcSlice2` supplied by the `rpow` chain/product
rule under the floor. -/
theorem flooredSourceTimeData_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u) where
  d0 τ _hτ := by
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.time1 τ
    refine ⟨δ, hδ, hcont, ?_, hcd⟩
    intro x hx s hs
    exact hasDerivAt_srcSlice (H.floor s x hx) (hdiff x hx s hs)
  d1 τ _hτ := by
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ := H.time2 τ
    refine ⟨δ, hδ, hcont, ?_, hcd⟩
    intro x hx s hs
    obtain ⟨h1, h2⟩ := hdiff x hx s hs
    exact hasDerivAt_srcSlice1 (H.floor s x hx) h1 h2
  sliceC2 i hi t _ht := H.sliceC2 i hi t
  sliceNeumann i hi t _ht := H.sliceNeumann i hi t
  zerothBound i hi := by
    obtain ⟨D, hD, hb⟩ := H.zerothBound i hi
    exact ⟨D, hD, fun t _ht => hb t⟩
  laplBound i hi := by
    obtain ⟨M, hM, hb⟩ := H.laplBound i hi
    exact ⟨M, hM, fun t _ht k hk => hb t k hk⟩

/-- **End-to-end FAC resolver-`C²` discharge for the concrete iterate.**  The
honest iterate datum + the source-`ℓ¹` bounded-weight summability + the committed
slab `other` field discharge the FAC resolver-`C²` inputs physically — NO eigen-
cube ladder, NO `DuhamelSourceTimeC2Coeff`, NO resolver-C2/FAC field assumed. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u)
    (hsrc_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞)
      (ShenWork.IntervalPhysicalResolverDataConcrete.srcTimeCoeff p u k))
    (hsrc_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i
        (ShenWork.IntervalPhysicalResolverDataConcrete.srcTimeCoeff p u k) t‖ ≤
        builtEs (flooredSourceTimeData_of_iterate H) i k)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointMajorant
        (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
          builtEs (flooredSourceTimeData_of_iterate H) i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
        (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
          builtEs (flooredSourceTimeData_of_iterate H) i k) m))
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSourceLift
            p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            ShenWork.IntervalDomain.intervalDomainLift (u q.1) q.2) (s, x)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        0 < 1 + ShenWork.IntervalDomain.intervalDomainLift
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p u s) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        (fun y : ℝ =>
            ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxTimeDerivativeLift
              p u s y) =ᶠ[𝓝 x]
          (fun y : ℝ => fderiv ℝ
            (Function.uncurry
              (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
      ContinuousOn
        (Function.uncurry
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
            p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)) :
    ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivFluxFactorJointC2Inputs
      p u :=
  ShenWork.IntervalPhysicalResolverDataConcrete.coupledChemDivFluxFactorJointC2Inputs_of_floor
    (physicalSourceTimeC2_of_floored (flooredSourceTimeData_of_iterate H)
      hsrc_contDiff hsrc_bound hval hgrad)
    other

end ShenWork.IntervalFlooredSourceTimeDataIterate
