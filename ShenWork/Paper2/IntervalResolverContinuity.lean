/-
Continuity of the physical Laplacian μR - source for the Neumann resolver.

Source: ChatGPT Q3971 (ODE bridge continuity).
Architecture: Weierstrass M-test for the resolver value series,
plus standard ContinuousOn composition for the source term.
-/
import ShenWork.Paper2.IntervalResolverWeakBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries

open MeasureTheory
open ShenWork.IntervalDomain ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.IntervalResolverWeakBounds

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

theorem resolverPhysicalSourceReal_continuousOn
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

theorem resolverPhysicalSourceReal_continuousAt_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (resolverPhysicalSourceReal p u) x := by
  have hsrc_on := resolverPhysicalSourceReal_continuousOn p hUcont
  have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x :=
    Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx) Set.Ioo_subset_Icc_self
  exact hsrc_on.continuousAt hIcc_nhds

theorem resolverCoeff_re_abs_summable_of_continuousOn
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

theorem resolverValueSeriesReal_continuous_of_continuousOn
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

theorem resolverLapPhysicalPlain_continuousAt_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (resolverLapPhysicalPlain p u) x := by
  have hR : ContinuousAt (resolverValueSeriesReal p u) x :=
    (resolverValueSeriesReal_continuous_of_continuousOn p hUcont).continuousAt
  have hS : ContinuousAt (resolverPhysicalSourceReal p u) x :=
    resolverPhysicalSourceReal_continuousAt_of_continuousOn p hUcont hx
  simpa [resolverLapPhysicalPlain] using (hR.const_mul p.μ).sub hS

end ShenWork.IntervalResolverWeakBounds
