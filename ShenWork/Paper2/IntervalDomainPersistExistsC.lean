/-
  Phase C (MinPersistence): per-solution existence of the persistence floor.

  Combines the Hamilton lower bound (`solution_minPersist_of_conjuncts`) with
  positivity of the initial spatial minimum (`sliceMin_pos_of_solution`) into
  the per-solution form of `ClassicalMinPersistence`:

    ∃ c > 0, ∀ t ∈ [t₁, T), ∀ x, c ≤ u(t,x),
    c := m_u(t₁/2) · e^{−Kp·(δ−t₁/2)}.

  The full `ClassicalMinPersistence` (one `c` for ALL solutions with the same
  trace) then follows by the proved overlap uniqueness (all such solutions
  agree at `t₁/2`, so share `m_u(t₁/2)`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistSolution
import ShenWork.Paper2.IntervalDomainSliceMinPos

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Per-solution persistence floor.**  Under the min-point bound on
`[t₁/2, T)`, the solution stays above a positive constant on `[t₁, T)`. -/
theorem solution_persist_exists_c
    {p : CM2Params} {T δ t₁ Kp : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hKp : 0 ≤ Kp) (ht₁ : 0 < t₁) (ht₁T : t₁ < T) (hTδ : T ≤ δ)
    (hbound : ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -Kp * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, t₁ ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x := by
  have ha0 : 0 < t₁ / 2 := by linarith
  have hahalf : t₁ / 2 < t₁ := by linarith
  -- `m_u(t₁/2) > 0`.
  have hm_pos : 0 < sInf (intervalDomainLift (u (t₁/2)) '' Set.Icc (0:ℝ) 1) :=
    sliceMin_pos_of_solution hsol ha0 (lt_trans hahalf ht₁T)
  refine ⟨sInf (intervalDomainLift (u (t₁/2)) '' Set.Icc (0:ℝ) 1)
      * Real.exp (-Kp * (δ - t₁/2)), by positivity, ?_⟩
  intro t ht₁t htT x
  -- Hamilton bound on `[t₁/2, t]`.
  have hbnd := solution_minPersist_of_conjuncts (a := t₁/2) (b := t) (Kp := Kp)
    hsol ha0 htT (by linarith)
    (fun s hs => hbound s ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩)
    t (Set.right_mem_Icc.mpr (by linarith)) x
  -- `m_u(t₁/2)·e^{−Kp(t−t₁/2)} ≥ m_u(t₁/2)·e^{−Kp(δ−t₁/2)} = c`  (t ≤ δ, Kp ≥ 0).
  refine le_trans ?_ hbnd
  refine mul_le_mul_of_nonneg_left ?_ hm_pos.le
  refine Real.exp_le_exp.mpr ?_
  have ht_le_δ : t ≤ δ := le_trans htT.le hTδ
  nlinarith [hKp, ht_le_δ]

end ShenWork.MinPersistenceAtoms
