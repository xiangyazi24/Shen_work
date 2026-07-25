import ShenWork.Paper1.WholeLineFarLeftDirect
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge

/-!
# Scope audit for the direct global barrier route

`far_left_convergence_direct` is a sound abstract theorem, but its conclusion
is uniform convergence to one over the entire spatial line.  That conclusion
cannot be specialized to a traveling front, whose right spatial tail tends to
zero.  The regression theorems below record the obstruction directly.

The canonical front proof already uses buffered left-half-line rectangles and
approximate maxima.  This file deliberately adds no exact-extremum wrapper for
that route.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- A right spatial tail at zero rules out uniform whole-line convergence to
the constant equilibrium one. -/
theorem not_uniform_global_one_of_rightTail_zero
    {u : ℝ → ℝ → ℝ}
    (hright : ∀ t, Tendsto (u t) atTop (𝓝 0)) :
    ¬ (∀ ε > 0, ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t → |u t z - 1| < ε) := by
  intro hglobal
  obtain ⟨T, hT⟩ := hglobal (1 / 2 : ℝ) (by norm_num)
  set t := max T 0 with ht
  have htT : T ≤ t := by simp [ht]
  have ht0 : 0 ≤ t := by simp [ht]
  have hev : ∀ᶠ z in atTop, |u t z| < (1 / 4 : ℝ) := by
    have hball : Metric.ball (0 : ℝ) (1 / 4 : ℝ) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    simpa [Metric.mem_ball, Real.dist_eq] using (hright t) hball
  obtain ⟨z, hz⟩ := hev.exists
  have hclose := hT t z htT ht0
  have htriangle : (1 : ℝ) ≤ |u t z| + |u t z - 1| := by
    calc
      (1 : ℝ) = |u t z - (u t z - 1)| := by
        rw [show u t z - (u t z - 1) = 1 by ring]
        norm_num
      _ ≤ |u t z| + |u t z - 1| := abs_sub _ _
  linarith

/-- The no-go result is invariant under passage to the co-moving coordinate. -/
theorem not_uniform_global_one_coMoving_of_rightTail_zero
    {c : ℝ} {u : ℝ → ℝ → ℝ}
    (hright : ∀ t, Tendsto (u t) atTop (𝓝 0)) :
    ¬ (∀ ε > 0, ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t →
      |coMovingPath c u t z - 1| < ε) := by
  apply not_uniform_global_one_of_rightTail_zero
  intro t
  exact (hright t).comp
    (tendsto_atTop_add_const_right atTop (c * t) tendsto_id)

/-- A front with right tail zero cannot eventually lie above a positive
whole-line exponential barrier. -/
theorem not_eventually_global_lower_expBarrier_of_rightTail_zero
    {u : ℝ → ℝ → ℝ}
    (hright : ∀ t, Tendsto (u t) atTop (𝓝 0))
    {D lam : ℝ} (hlam : 0 < lam) :
    ¬ ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t →
      1 - D * Real.exp (-lam * t) ≤ u t z := by
  rintro ⟨T, hbarrier⟩
  have hevent :
      ∀ᶠ t in atTop, D * Real.exp (-lam * t) < (1 / 2 : ℝ) := by
    have hnhds : Set.Iio (1 / 2 : ℝ) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    simpa only [Set.mem_Iio] using (expBarrier_tendsto_zero hlam) hnhds
  have hall : ∀ᶠ t in atTop,
      D * Real.exp (-lam * t) < (1 / 2 : ℝ) ∧ T ≤ t ∧ 0 ≤ t := by
    filter_upwards [hevent, eventually_ge_atTop T, eventually_ge_atTop 0] with
      t hdecay htT ht0
    exact ⟨hdecay, htT, ht0⟩
  obtain ⟨t, hdecay, htT, ht0⟩ := hall.exists
  have htail : ∀ᶠ z in atTop, u t z < (1 / 4 : ℝ) := by
    have hnhds : Set.Iio (1 / 4 : ℝ) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    simpa only [Set.mem_Iio] using (hright t) hnhds
  obtain ⟨z, hz⟩ := htail.exists
  linarith [hbarrier t z htT ht0]

/-- A traveling-wave profile has no attained global minimum: its values are
strictly positive, while its right tail tends to zero. -/
theorem IsTravelingWave.not_exists_global_min
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) :
    ¬ ∃ z0, ∀ z, U z0 ≤ U z := by
  rintro ⟨z0, hz0⟩
  have hev : ∀ᶠ z in atTop, U z < U z0 :=
    U_eventually_le_eps_at_top hTW (U z0) (hTW.U_pos z0)
  obtain ⟨z, hz⟩ := hev.exists
  exact (not_lt_of_ge (hz0 z)) hz

/-- The exact traveling-wave solution is a concrete regression witness against
the global-uniform conclusion of the direct route. -/
theorem IsTravelingWave.not_uniformConvergesToConstant_one_coMoving_self
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) :
    ¬ UniformConvergesToConstant
      (coMovingPath c (fun t x => U (x - c * t))) 1 := by
  intro hconv
  apply not_uniform_global_one_coMoving_of_rightTail_zero
    (c := c) (u := fun t x => U (x - c * t))
  · intro t
    exact hTW.lim_pos_inf.1.comp
      (tendsto_atTop_add_const_right atTop (-(c * t)) tendsto_id)
  · intro ε hε
    obtain ⟨T, hT⟩ := hconv ε hε
    exact ⟨T, fun t z ht _ht0 => hT t z ht⟩

section AxiomAudit

#print axioms not_uniform_global_one_of_rightTail_zero
#print axioms not_uniform_global_one_coMoving_of_rightTail_zero
#print axioms not_eventually_global_lower_expBarrier_of_rightTail_zero
#print axioms IsTravelingWave.not_exists_global_min
#print axioms IsTravelingWave.not_uniformConvergesToConstant_one_coMoving_self

end AxiomAudit

end ShenWork.Paper1
