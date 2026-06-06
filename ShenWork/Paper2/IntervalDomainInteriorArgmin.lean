/-
  B2 (MinPersistence): vanishing spatial derivative at an interior argmin.

  If `x*` is a spatial argmin of `u` (`u x* ≤ u y` for all `y`) and lies in the
  open interior `(0,1)`, then the zero-extension lift has a vanishing derivative
  there: `HasDerivAt (intervalDomainLift u) 0 x*`.  This is the `hux` input of
  `min_point_estimate_interior` (the `u_x = 0` critical-point fact).

  Fermat's interior-extremum theorem: the lift agrees with `u` on the open
  interior, so `x*` is a genuine local min of the lift, hence its derivative
  vanishes (`IsLocalMin.deriv_eq_zero`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalDomain
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open ShenWork.IntervalDomain Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- The zero-extension lift attains a local minimum (over `ℝ`) at an interior
spatial argmin. -/
theorem intervalDomainLift_isLocalMin_of_argmin
    {u : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hmin : ∀ y, u x ≤ u y) (hint : x.1 ∈ Set.Ioo (0:ℝ) 1) :
    IsLocalMin (intervalDomainLift u) x.1 := by
  -- `x.1 ∈ Icc`, so `lift u x.1 = u x`.
  have hxIcc : x.1 ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hint
  have hlift_x : intervalDomainLift u x.1 = u x := by
    rw [intervalDomainLift, dif_pos hxIcc]
    congr
  -- On the open interior `(0,1) ∈ 𝓝 x.1`, the lift dominates its value at `x.1`.
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Set.Ioo (0:ℝ) 1, isOpen_Ioo.mem_nhds hint, fun y hy => ?_⟩
  have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
  rw [hlift_x, intervalDomainLift, dif_pos hyIcc]
  exact hmin ⟨y, hyIcc⟩

/-- **Vanishing spatial derivative at an interior argmin.** -/
theorem interior_argmin_deriv_zero
    {u : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hmin : ∀ y, u x ≤ u y) (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hdiff : DifferentiableAt ℝ (intervalDomainLift u) x.1) :
    HasDerivAt (intervalDomainLift u) 0 x.1 := by
  have hlm := intervalDomainLift_isLocalMin_of_argmin hmin hint
  have hz : deriv (intervalDomainLift u) x.1 = 0 := hlm.deriv_eq_zero
  have := hdiff.hasDerivAt
  rwa [hz] at this

end ShenWork.MinPersistenceAtoms
