/-
  Phase C (MinPersistence): positivity of the spatial minimum at interior times.

  At an interior time `t ∈ (0,T)` of a classical solution, the spatial minimum
  `m_u(t) := sInf (lift (u t) '' [0,1])` is strictly positive: the slice is
  continuous and pointwise positive on the compact `[0,1]`, so its minimum is
  attained at a positive value.  This is the `m_u(a) > 0` ingredient of the
  Hamilton `c`-construction (`c := m_u(t₁/2)·e^{−Kp(δ−t₁/2)} > 0`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistCore
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Positivity of the spatial minimum at an interior time.** -/
theorem sliceMin_pos_of_solution
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 < sInf (intervalDomainLift (u t) '' Set.Icc (0:ℝ) 1) := by
  -- The lifted slice is continuous on `[0,1]`.
  have hslice_cont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0:ℝ) 1) := by
    obtain ⟨_, _, _, _, h7, _, _⟩ := hsol.regularity
    exact (h7 t ⟨ht0, htT⟩).1.1.continuousOn
  -- The image is compact and nonempty; its inf is attained.
  have himg : IsCompact (intervalDomainLift (u t) '' Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice_cont
  have hne : (intervalDomainLift (u t) '' Set.Icc (0:ℝ) 1).Nonempty :=
    ⟨intervalDomainLift (u t) 0,
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  obtain ⟨x0, hx0_mem, hx0_eq⟩ := himg.sInf_mem hne
  rw [← hx0_eq]
  -- The attained value is a positive interior value.
  rw [intervalDomainLift, dif_pos hx0_mem]
  exact hsol.u_pos' ht0 htT

end ShenWork.MinPersistenceAtoms
