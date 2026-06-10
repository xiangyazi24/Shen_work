/-
  Assembly of regularity frontier fields from G4 + F2 infrastructure.

  Maps the time-regularity fields of `GradientMildClassicalRegularityFrontierData`
  to proved theorems:
  - u-side: from `HasTimeNeighborhoodSpectralAgreement` (G4)
  - v-side: from `HasResolverDirectSpectralData` (F2)

  Also contains the packaging theorem:
  `hasResolverDirectSpectralData_of_sourceCoeffTimeC1` — given
  `DuhamelSourceTimeC1` of the resolver source coefficients
  `s ↦ (intervalNeumannResolverSourceCoeff p (u s) k).re`, construct
  `HasResolverDirectSpectralData T (mildChemicalConcentration p u) p`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.PDE.IntervalMildTimeDerivContinuity
import ShenWork.PDE.IntervalMildFrontierFromSpectral
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement
   mildSolution_hasDerivAt_time
   mildSolution_timeDeriv_continuousOn_fixed_x
   mildSolution_timeDeriv_jointContinuousOn)
open ShenWork.IntervalMildFrontierFromSpectral
  (mildSolution_timeDeriv_jointContinuousOn_closed
   mildSolution_jointContinuousOn_closed)
open ShenWork.Paper2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData
   resolver_direct_differentiableAt_time
   resolver_direct_timeDeriv_continuousOn
   resolver_direct_jointTimeDerivInterior
   resolver_direct_jointTimeDerivClosed
   resolver_direct_jointSolutionClosed)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff intervalNeumannResolverWeight
  intervalNeumannResolverCoeff)
open ShenWork.IntervalResolverGradientBridge (resolverCoeff_re_eq resolverR_apply_eq)
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.RegularityFrontierAssembly

/-- **timeSlices (u-side)**: DifferentiableAt + continuous time derivative
for each fixed x, from `HasTimeNeighborhoodSpectralAgreement`. -/
theorem timeSlices_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u)
    (x : intervalDomainPoint) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s => u s x) t) ∧
    ContinuousOn (fun s => deriv (fun r => u r x) s) (Ioo (0 : ℝ) T) := by
  constructor
  · intro t ht
    obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree⟩ :=
      H.exists_data t ht.1 ht.2
    exact (mildSolution_hasDerivAt_time hM ha₀ src hτ₀ hagree x).differentiableAt
  · exact mildSolution_timeDeriv_continuousOn_fixed_x H x

/-- **jointTimeDerivInterior (u-side)**: joint (t,x) continuity of the time
derivative on the open slab (0,T) × (0,1). -/
theorem jointTimeDerivInterior_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (u s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  mildSolution_timeDeriv_jointContinuousOn H

/-- **jointTimeDerivClosed (u-side)**: joint (t,x) continuity of ∂ₜ(lift(u t))(x)
on `Ioo 0 T ×ˢ Icc 0 1` (closed in x).

Extends `jointTimeDerivInterior_u_of_spectralAgreement` from `Ioo 0 1` to `Icc 0 1`
using uniform convergence of the cosine derivative series on all of `[0,1]`
(|cos(nπx)| ≤ 1 for all x), via `mildSolution_timeDeriv_jointContinuousOn_closed`. -/
theorem jointTimeDerivClosed_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (u s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  mildSolution_timeDeriv_jointContinuousOn_closed H

/-- **jointSolutionClosed (u-side)**: joint (t,x) continuity of `lift(u t)(x)`
on `Ioo 0 T ×ˢ Icc 0 1` (closed in x).

The restart cosine series is jointly continuous on all of `Ioi 0 × ℝ`; this
restricts to `Ioo 0 T × Icc 0 1` via `mildSolution_jointContinuousOn_closed`. -/
theorem jointSolutionClosed_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  mildSolution_jointContinuousOn_closed H

/-! ## V-side time regularity fields (from F2: resolver spectral data) -/

/-- **timeSlices (v-side)**: DifferentiableAt + continuous time derivative
for the resolver v at each fixed x, from `HasResolverDirectSpectralData`. -/
theorem timeSlices_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p)
    (x : intervalDomainPoint) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s => v s x) t) ∧
    ContinuousOn (fun s => deriv (fun r => v r x) s) (Ioo (0 : ℝ) T) := by
  constructor
  · intro t ht
    exact resolver_direct_differentiableAt_time H ht.1 ht.2 x
  · exact resolver_direct_timeDeriv_continuousOn H x

/-- **jointTimeDerivInterior (v-side)**: joint (t,x) continuity of the
resolver time derivative on the open slab (0,T) × (0,1). -/
theorem jointTimeDerivInterior_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  resolver_direct_jointTimeDerivInterior H

/-- **jointTimeDerivClosed (v-side)**: joint (t,x) continuity of ∂ₜv on
the closed spatial slab Ioo 0 T ×ˢ Icc 0 1. -/
theorem jointTimeDerivClosed_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  resolver_direct_jointTimeDerivClosed H

/-- **jointSolutionClosed (v-side)**: joint (t,x) continuity of the resolver
v(t,x) on the closed spatial slab Ioo 0 T ×ˢ Icc 0 1. -/
theorem jointSolutionClosed_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  resolver_direct_jointSolutionClosed H

/-! ## V-side spectral packaging from resolver algebra -/

/-- **Algebraic identity**: the resolver value equals the weighted
source-coefficient cosine series.

For every time `s` and every `x : intervalDomainPoint`:
```
mildChemicalConcentration p u s x
  = ∑' k, (intervalNeumannResolverSourceCoeff p (u s) k).re
           · intervalNeumannResolverWeight p k · cos(kπ x)
```

Proof is purely algebraic:
1. `mildChemicalConcentration p u s = intervalNeumannResolverR p (u s)`
2. `resolverR_apply_eq` gives the cosine series `∑ resolverCoeff.re · cos`
3. `resolverCoeff_re_eq` rewrites each mode:
   `resolverCoeff.re = sourceCoeff.re / (μ + λ_k) = sourceCoeff.re · w_k`

No `sorry`. -/
theorem mildChemicalConcentration_eq_sourceWeight_series
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ)
    (x : intervalDomainPoint) :
    mildChemicalConcentration p u s x =
      ∑' k, (intervalNeumannResolverSourceCoeff p (u s) k).re *
        intervalNeumannResolverWeight p k * cosineMode k x.1 := by
  -- Unfold to `intervalNeumannResolverR p (u s) x` and apply the series identity.
  simp only [mildChemicalConcentration, resolverR_apply_eq, cosineMode]
  refine tsum_congr (fun k => ?_)
  -- Per-mode: resolverCoeff.re = sourceCoeff.re / (μ + λ_k), w_k = 1 / (μ + λ_k).
  rw [resolverCoeff_re_eq, intervalNeumannResolverWeight]
  ring

/-- **Packaging theorem**: given `DuhamelSourceTimeC1` of the resolver source
coefficients `(s, k) ↦ (intervalNeumannResolverSourceCoeff p (u s) k).re`,
construct `HasResolverDirectSpectralData T (mildChemicalConcentration p u) p`.

The series identity `v s x = ∑ sourceCoeff.re · w_k · cos` holds for **all** `s`
(not just eventually), so the `∀ᶠ s in 𝓝 t₀` condition is discharged by
`eventually_of_forall`.

**Residual**: the hypothesis `hsrc` is an honest remaining gap.  To instantiate it:
- The summable envelope requires `|sourceCoeff k| ≤ C/(kπ)²` for k ≥ 1
  (from `SourceCoeffQuadraticDecay p (u s)` at each `s`, which in turn follows
  from C²-Neumann regularity of `s ↦ p.ν · (u s)^γ` via
  `powerSource_cosineCoeff_quadratic_decay_of_chain_rule`).
- The time derivative of the source coefficient at each mode `k` comes from
  the Leibniz rule (`hasDerivAt_intervalIntegral_of_dominated`) applied to
  `∂ₛ [∫₀¹ p.ν (u s x)^γ cos(kπx) dx]`, using the time differentiability
  of `u s x` from `HasTimeNeighborhoodSpectralAgreement`.

No `sorry`. -/
theorem hasResolverDirectSpectralData_of_sourceCoeffTimeC1
    {T : ℝ} {p : CM2Params} (u : ℝ → intervalDomainPoint → ℝ)
    (hsrc : DuhamelSourceTimeC1
      (fun s k => (intervalNeumannResolverSourceCoeff p (u s) k).re)) :
    HasResolverDirectSpectralData T (mildChemicalConcentration p u) p := by
  unfold HasResolverDirectSpectralData
  intro _t₀ _ht₀ _ht₀T
  exact ⟨fun s k => (intervalNeumannResolverSourceCoeff p (u s) k).re, hsrc,
     Eventually.of_forall (fun s x =>
       mildChemicalConcentration_eq_sourceWeight_series p u s x)⟩

/-- **Per-`t₀` packaging theorem (clamped-witness form).**

Given, for each interior time `t₀ ∈ (0,T)`, a spectral family `aC` together with a
`DuhamelSourceTimeC1 aC` package and a time NEIGHBORHOOD `W ∈ 𝓝 t₀` on which `aC`
agrees with the canonical resolver source coefficients
`(s,k) ↦ (intervalNeumannResolverSourceCoeff p (u s) k).re`, construct
`HasResolverDirectSpectralData T (mildChemicalConcentration p u) p`.

This is the consumer-facing entry point for the soft-clamped witness: the canonical
`DuhamelSourceTimeC1` is unsatisfiable globally (the source jumps at `s = T`), but a
clamped family agreeing with it on a window around each interior `t₀` IS satisfiable,
and the per-`t₀` retyped `HasResolverDirectSpectralData` consumes exactly that.

The agreement on `𝓝 t₀` follows because the resolver value equals the canonical
weighted source series for ALL `s` (`mildChemicalConcentration_eq_sourceWeight_series`,
purely algebraic), and on `W` the clamped `aC` equals the canonical coefficient.

No `sorry`. -/
theorem hasResolverDirectSpectralData_of_clamped_perT0
    {T : ℝ} {p : CM2Params} (u : ℝ → intervalDomainPoint → ℝ)
    (H : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k, aC s k = (intervalNeumannResolverSourceCoeff p (u s) k).re)) :
    HasResolverDirectSpectralData T (mildChemicalConcentration p u) p := by
  unfold HasResolverDirectSpectralData
  intro t₀ ht₀ ht₀T
  obtain ⟨aC, src, W, hW_nhds, hW_agree⟩ := H t₀ ht₀ ht₀T
  refine ⟨aC, src, ?_⟩
  filter_upwards [hW_nhds] with s hs x
  rw [mildChemicalConcentration_eq_sourceWeight_series p u s x]
  refine tsum_congr (fun k => ?_)
  rw [hW_agree s hs k]

end ShenWork.Paper2.RegularityFrontierAssembly
