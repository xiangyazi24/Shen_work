/-
  Phase C (MinPersistence): per-solution persistence core.

  Applies the packaged Hamilton bound (`sliceMin_hamilton_bound`) to a classical
  solution's spatial slices `F t y := lift (u t) y`, then bounds each pointwise
  value below by the spatial minimum:
    `u(t,x) ≥ m_u(t) ≥ m_u(a)·e^{−Kp·(t−a)}`  on `[a,b] × [0,1]`.
  This is the per-solution form of `ClassicalMinPersistence`; the regularity
  facts (joint continuity of the field and its time-derivative, time slices
  differentiable) come from the classical-solution conjuncts, and the min-point
  bound `hbound` from `interior_min_point_of_solution` ∪ the boundary assembly.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainHamiltonBound
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Per-solution minimum persistence.**  Under the regularity facts and the
min-point bound, every pointwise value stays above the Hamilton lower bound. -/
theorem solution_minPersist_core
    {u : ℝ → intervalDomainPoint → ℝ} {a b Kp : ℝ}
    (hF : ContinuousOn
      (Function.uncurry (fun t y => intervalDomainLift (u t) y))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => intervalDomainLift (u r) y) (Set.Icc a b))
    (hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => intervalDomainLift (u r) y)
        (deriv (fun r => intervalDomainLift (u r) y) s) s)
    (hdF_cont : ContinuousOn
      (Function.uncurry
        (fun s y => deriv (fun r => intervalDomainLift (u r) y) s))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hbound : ∀ s ∈ Set.Icc a b, ∀ ys ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -Kp * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∀ t ∈ Set.Icc a b, ∀ x : intervalDomainPoint,
      sInf (intervalDomainLift (u a) '' Set.Icc (0:ℝ) 1)
          * Real.exp (-Kp * (t - a))
        ≤ u t x := by
  set F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y with hF_def
  have hm_cont : ContinuousOn (fun t => sInf (F t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b) := sliceMin_continuousOn hF
  -- Hamilton lower bound on the minimum trajectory.
  have hham := sliceMin_hamilton_bound hF hslice_cont hslice_diff hm_cont
    hdF_cont hbound
  intro t ht x
  -- `u t x = F t x.1 ≥ m_u(t)` (pointwise ≥ minimum).
  have hxIcc : (x.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := x.2
  have hux : F t x.1 = u t x := by
    simp only [hF_def, intervalDomainLift, dif_pos hxIcc]
    exact congrArg (u t) (Subtype.ext rfl)
  -- `sInf (F t '' [0,1]) ≤ F t x.1` (bdd below via compact image).
  have hslice_t : ContinuousOn (F t) (Set.Icc (0:ℝ) 1) := by
    intro y hy
    have := hF (t, y) ⟨ht, hy⟩
    exact (this.comp (Continuous.continuousWithinAt (by fun_prop))
      (fun w hw => ⟨ht, hw⟩) : ContinuousWithinAt (fun w => F t w) _ y)
  have hbdd : BddBelow (F t '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hslice_t).bddBelow
  have hmin_le : sInf (F t '' Set.Icc (0:ℝ) 1) ≤ F t x.1 :=
    csInf_le hbdd (Set.mem_image_of_mem _ hxIcc)
  -- Chain: `m_u(a)·e^{…} ≤ m_u(t) ≤ F t x.1 = u t x`.
  calc sInf (intervalDomainLift (u a) '' Set.Icc (0:ℝ) 1)
        * Real.exp (-Kp * (t - a))
      ≤ sInf (F t '' Set.Icc (0:ℝ) 1) := hham t ht
    _ ≤ F t x.1 := hmin_le
    _ = u t x := hux

end ShenWork.MinPersistenceAtoms
