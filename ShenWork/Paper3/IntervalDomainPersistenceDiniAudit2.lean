import ShenWork.Paper3.IntervalDomainPersistenceDiniFrontier

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

private theorem intervalDomain_range_eq_lift_image
    (f : intervalDomain.Point → ℝ) :
    Set.range f = intervalDomainLift f '' Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.1, x.2, ?_⟩
    simp [intervalDomainLift]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp [intervalDomainLift, hx]

/-- The `sInf (range (u t))` spatial minimum used by the P3 Dini frontier is
the compact-slice infimum over `[0,1]`. -/
theorem intervalDomainSpatialMin_eq_lift_sInf
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainSpatialMin u t =
      sInf (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1) := by
  unfold intervalDomainSpatialMin
  rw [intervalDomain_range_eq_lift_image]

/-- For continuous interval slices, the spatial infimum is attained. -/
theorem intervalDomainSpatialMin_attained
    {u : ℝ → intervalDomain.Point → ℝ} {t : ℝ}
    (hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1)) :
    ∃ x : intervalDomain.Point, u t x = intervalDomainSpatialMin u t := by
  have himg : IsCompact (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hcont
  have hne : (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨intervalDomainLift (u t) 0,
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  obtain ⟨x, hx, hxsInf⟩ := himg.sInf_mem hne
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [intervalDomainSpatialMin_eq_lift_sInf, ← hxsInf]
  simp [intervalDomainLift, hx]

/-- The committed concrete interval chemotaxis divergence is unchanged when
only the parameter `m` is replaced. -/
theorem intervalDomainChemotaxisDiv_eq_with_replaced_m_frontier
    (p : CM2Params) {m' : ℝ} (hm' : 0 < m')
    (u v : intervalDomain.Point → ℝ) (x : intervalDomain.Point) :
    intervalDomainChemotaxisDiv { p with m := m', hm := hm' } u v x =
      intervalDomainChemotaxisDiv p u v x := by
  unfold intervalDomainChemotaxisDiv
  rfl

/-- At a spatial critical point, the committed chemotaxis divergence has a
linear `u(x*)` factor, not the `u(x*) ^ p.m` factor required by the requested
superlinear spatial-minimum Dini loss. -/
theorem intervalDomainChemotaxisDiv_critical_linear_frontier
    {p : CM2Params} {u v : intervalDomain.Point → ℝ} {x : intervalDomain.Point}
    {vx vxx : ℝ}
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y) :
    intervalDomainChemotaxisDiv p u v x =
      intervalDomainLift u x.1 *
        (-p.β * (1 + intervalDomainLift v x.1) ^ (-p.β - 1) * vx ^ 2
          + (1 + intervalDomainLift v x.1) ^ (-p.β) * vxx) :=
  intervalDomain_chemDiv_critical_linear_factor hux hv hvxx hvnn

/-- A limit at a threshold does not imply eventual domination by that same
threshold.  This is the scalar-interface obstruction for replacing an exact
eventual lower-bound field by a bare `liminf ≥ threshold` statement. -/
theorem tendsto_zero_not_eventually_nonneg_frontier :
    Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (𝓝 0) ∧
      ¬ (∀ᶠ t in atTop, 0 ≤ -Real.exp (-t)) := by
  constructor
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  · intro h
    rcases eventually_atTop.1 h with ⟨T, hT⟩
    linarith [hT T le_rfl, Real.exp_pos (-T)]

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainSpatialMin_eq_lift_sInf
#print axioms ShenWork.Paper3.intervalDomainSpatialMin_attained
#print axioms ShenWork.Paper3.intervalDomainChemotaxisDiv_eq_with_replaced_m_frontier
#print axioms ShenWork.Paper3.intervalDomainChemotaxisDiv_critical_linear_frontier
#print axioms ShenWork.Paper3.tendsto_zero_not_eventually_nonneg_frontier
