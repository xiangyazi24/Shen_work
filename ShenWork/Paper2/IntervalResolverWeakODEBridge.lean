/-
Green/ODE regularity bridge: continuous source → R' has derivative μR - ρ(u).

Uses the integrated weak ODE identity (spectral weak equation + Parseval) and
Mathlib's FTC (integral_hasDerivAt_right) to bypass termwise differentiation
of the gradient series (which would require ∑|c_k|(kπ)² < ∞).

Source: ChatGPT Q3970 (green_ode_bridge) + Q3971 (continuity).
-/
import ShenWork.Paper2.IntervalResolverWeakLapBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Group.FunctionSeries

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.IntervalResolverWeakBounds

/-! ### Continuity infrastructure (from IntervalResolverContinuity, inlined) -/

def resolverValueSeriesReal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun z => ∑' k : ℕ,
    (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k z

def resolverPhysicalSourceReal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun z => p.ν * (positivePart (intervalDomainLift u z)) ^ p.γ

def resolverLapPhysicalPlain (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun z => p.μ * resolverValueSeriesReal p u z - resolverPhysicalSourceReal p u z

private theorem resolverPhysicalSourceReal_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (resolverPhysicalSourceReal p u) (Set.Icc (0 : ℝ) 1) := by
  have hpp :
      ContinuousOn (fun z : ℝ => positivePart (intervalDomainLift u z))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [positivePart] using
      ContinuousOn.sup hUcont
        (continuousOn_const :
          ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 1))
  have hpow :
      ContinuousOn
        (fun z : ℝ => (positivePart (intervalDomainLift u z)) ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hpp.rpow_const (fun z hz => Or.inr p.hγ.le)
  simpa [resolverPhysicalSourceReal] using continuousOn_const.mul hpow

private theorem resolverCoeff_re_abs_summable_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1)) :
    Summable fun k : ℕ => |(intervalNeumannResolverCoeff p u k).re| := by
  have hsrcL2 :
      Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hseries0 :
      Summable fun k : ℕ =>
        (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k (0 : ℝ) :=
    resolver_cosineSeries_summable_of_sourceL2 p hsrcL2 0
  simpa [unitIntervalCosineMode, Real.norm_eq_abs] using hseries0.norm

private theorem resolverValueSeriesReal_continuous_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1)) :
    Continuous (resolverValueSeriesReal p u) := by
  classical
  let c : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p u k).re
  let f : ℕ → ℝ → ℝ := fun k z => c k * unitIntervalCosineMode k z
  let M' : ℕ → ℝ := fun k => |c k|
  have hM : Summable M' :=
    resolverCoeff_re_abs_summable_of_continuousOn p hUcont
  have hf : ∀ k : ℕ, Continuous (f k) := by
    intro k; dsimp [f, c]
    unfold unitIntervalCosineMode; fun_prop
  have hbound : ∀ k z, ‖f k z‖ ≤ M' k := by
    intro k z; dsimp [f, M', c]
    have hcos : |unitIntervalCosineMode k z| ≤ 1 := by
      unfold unitIntervalCosineMode; exact Real.abs_cos_le_one _
    calc ‖(intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k z‖
        = |(intervalNeumannResolverCoeff p u k).re| * |unitIntervalCosineMode k z| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |(intervalNeumannResolverCoeff p u k).re| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |(intervalNeumannResolverCoeff p u k).re| := by ring
  simpa [resolverValueSeriesReal, f, c] using continuous_tsum hf hM hbound

private theorem resolverLapPhysicalPlain_continuousAt_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (resolverLapPhysicalPlain p u) x := by
  have hR : ContinuousAt (resolverValueSeriesReal p u) x :=
    (resolverValueSeriesReal_continuous_of_continuousOn p hUcont).continuousAt
  have hS : ContinuousAt (resolverPhysicalSourceReal p u) x := by
    have hsrc_on := resolverPhysicalSourceReal_continuousOn p hUcont
    have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx) Set.Ioo_subset_Icc_self
    exact hsrc_on.continuousAt hIcc_nhds
  simpa [resolverLapPhysicalPlain] using (hR.const_mul p.μ).sub hS

/-! ### Physical Laplacian (piecewise) and its continuity -/

def resolverLapPhysicalReal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then
    resolverLapPhysical p u ⟨x, hx⟩
  else
    0

theorem resolverLapPhysicalReal_continuousAt_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (resolverLapPhysicalReal p u) x := by
  have hplain : ContinuousAt (resolverLapPhysicalPlain p u) x :=
    resolverLapPhysicalPlain_continuousAt_of_continuousOn p hUcont hx
  have hIoo_nhds : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_Ioo hx
  have hlocal :
      resolverLapPhysicalReal p u =ᶠ[𝓝 x] resolverLapPhysicalPlain p u := by
    filter_upwards [hIoo_nhds] with z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    simp [resolverLapPhysicalReal, resolverLapPhysicalPlain, resolverLapPhysical,
      resolverValueSeriesReal, resolverPhysicalSourceReal, resolverPositiveSourceLifted,
      intervalNeumannResolverR, unitIntervalCosineMode, hzIcc]
  exact hplain.congr_of_eventuallyEq hlocal.symm

/-! ### Integrated weak ODE and FTC bridge -/

theorem resolverGradReal_sub_eq_integral_lapPhysicalReal
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    resolverGradReal p u b - resolverGradReal p u a
      = ∫ t in a..b, resolverLapPhysicalReal p u t := by
  sorry

theorem resolverGradReal_eventually_eq_primitive
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (fun z : ℝ => resolverGradReal p u z)
      =ᶠ[𝓝 x]
    (fun z : ℝ => resolverGradReal p u x
      + ∫ t in x..z, resolverLapPhysicalReal p u t) := by
  have hIoo_mem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_Ioo hx
  filter_upwards [hIoo_mem] with z hz
  have h := resolverGradReal_sub_eq_integral_lapPhysicalReal
    p hUcont hx hz
  linarith

theorem resolverGradReal_hasDerivAt_physicalLap_of_continuousOn_via_FTC
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z : ℝ => resolverGradReal p u z)
      (resolverLapPhysical p u ⟨x, Set.Ioo_subset_Icc_self hx⟩) x := by
  let q : ℝ → ℝ := resolverLapPhysicalReal p u
  have hq_cont : ContinuousAt q x :=
    resolverLapPhysicalReal_continuousAt_of_continuousOn p hUcont hx
  have hq_int : IntervalIntegrable q volume x x :=
    intervalIntegrable_const.congr (Filter.EventuallyEq.refl _ _)
  have hq_meas : StronglyMeasurableAtFilter q (𝓝 x) :=
    hq_cont.stronglyMeasurableAtFilter
  have hFTC :
      HasDerivAt (fun z : ℝ => ∫ t in x..z, q t) (q x) x :=
    intervalIntegral.integral_hasDerivAt_right hq_int hq_meas hq_cont
  have hprim :
      HasDerivAt
        (fun z : ℝ => resolverGradReal p u x + ∫ t in x..z, q t)
        (q x) x := by
    simpa using hFTC.const_add (resolverGradReal p u x)
  have hev :
      (fun z : ℝ => resolverGradReal p u z)
        =ᶠ[𝓝 x]
      (fun z : ℝ => resolverGradReal p u x + ∫ t in x..z, q t) :=
    resolverGradReal_eventually_eq_primitive p hUcont hx
  have hq_x : q x = resolverLapPhysical p u ⟨x, Set.Ioo_subset_Icc_self hx⟩ := by
    simp [q, resolverLapPhysicalReal, Set.Ioo_subset_Icc_self hx]
  rw [← hq_x]
  exact hprim.congr_of_eventuallyEq hev.symm

end ShenWork.IntervalResolverWeakBounds
