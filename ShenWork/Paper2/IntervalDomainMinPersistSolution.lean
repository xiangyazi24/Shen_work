/-
  Phase C (MinPersistence): per-solution persistence from the conjuncts.

  Wraps `solution_minPersist_core` by extracting its regularity inputs from the
  `IsPaper2ClassicalSolution` regularity conjuncts (9: closed-slab solution
  continuity; 8: closed-slab ∂ₜ continuity; 4: time slices differentiable),
  on a compact interior time window `[a,b] ⊆ (0,T)`.  Given the min-point bound
  `hbound` at the solution's argmins, every value persists above the Hamilton
  lower bound `m_u(a)·e^{−Kp·(t−a)}`.

  The only remaining inputs are `hbound` (interior:
  `interior_min_point_of_solution`; boundary: the boundary assembly) and the
  positivity of `m_u(a)` — the rest is the classical-solution regularity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistCore
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Per-solution persistence from the conjuncts.** -/
theorem solution_minPersist_of_conjuncts
    {p : CM2Params} {T a b Kp : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha0 : 0 < a) (hbT : b < T) (hab : a ≤ b)
    (hbound : ∀ s ∈ Set.Icc a b, ∀ ys ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -Kp * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∀ t ∈ Set.Icc a b, ∀ x : intervalDomainPoint,
      sInf (intervalDomainLift (u a) '' Set.Icc (0:ℝ) 1)
          * Real.exp (-Kp * (t - a))
        ≤ u t x := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0:ℝ) T := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hsubprod : Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1
      ⊆ Set.Ioo (0:ℝ) T ×ˢ Set.Icc (0:ℝ) 1 :=
    Set.prod_mono hsub (le_refl _)
  obtain ⟨_, _, _, h4, _, _, _, h8, h9⟩ := hsol.regularity
  -- Conjunct 9: closed-slab solution-field continuity → `hF`.
  have hF : ContinuousOn
      (Function.uncurry (fun t y => intervalDomainLift (u t) y))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := h9.1.mono hsubprod
  -- Conjunct 8: closed-slab ∂ₜ continuity → `hdF_cont`.
  have hdF_cont : ContinuousOn
      (Function.uncurry
        (fun s y => deriv (fun r => intervalDomainLift (u r) y) s))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := h8.1.mono hsubprod
  -- Slice-in-time continuity from `hF`.
  have hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => intervalDomainLift (u r) y) (Set.Icc a b) := by
    intro y hy
    have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc a b)
        (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := fun w hw => ⟨hw, hy⟩
    exact hF.comp (Continuous.continuousOn (by fun_prop)) hmaps
  -- Conjunct 4: time slices differentiable → `hslice_diff`.
  have hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => intervalDomainLift (u r) y)
        (deriv (fun r => intervalDomainLift (u r) y) s) s := by
    intro y hy s hs
    have hsInt : s ∈ Set.Ioo (0:ℝ) T :=
      ⟨lt_of_lt_of_le ha0 hs.1.le, lt_of_lt_of_le hs.2 hbT.le⟩
    -- `lift (u r) y = u r ⟨y,_⟩` as functions of `r`.
    have hfun : (fun r => intervalDomainLift (u r) y)
        = fun r => u r ⟨y, hy⟩ := by
      funext r; rw [intervalDomainLift, dif_pos hy]
    rw [hfun]
    obtain ⟨⟨hdU, _⟩, _, _⟩ := h4 ⟨y, hy⟩ s hsInt
    exact hdU.hasDerivAt
  exact solution_minPersist_core hF hslice_cont hslice_diff hdF_cont hbound

end ShenWork.MinPersistenceAtoms
