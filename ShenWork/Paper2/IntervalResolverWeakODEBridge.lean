/-
Green/ODE regularity bridge: continuous source → R' has derivative μR - ρ(u).

Uses the integrated weak ODE identity (spectral weak equation + Parseval) and
Mathlib's FTC (integral_hasDerivAt_right) to bypass termwise differentiation
of the gradient series (which would require ∑|c_k|(kπ)² < ∞).

Source: ChatGPT Q3970 (green_ode_bridge), architecture verified.
-/
import ShenWork.Paper2.IntervalResolverWeakLapBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.IntervalResolverWeakBounds

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
  sorry

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
