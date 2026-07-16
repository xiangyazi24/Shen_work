import ShenWork.Paper1.WholeLineWeightedRegularityDuhamelHolder

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# The fresh Duhamel interval has derivative equal to the current forcing

This is the zero-length endpoint needed after the state has been placed in
the generator domain.  It is deliberately separate from the singular
generator-history cancellation: only strong continuity of the heat
semigroup and continuity of the forcing enter here.
-/

/-- A uniform error bound on a fresh Duhamel interval passes unchanged to
its normalized average. -/
theorem weightedMovingHeatL2_freshDuhamel_slope_norm_sub_le
    {eta c t h E : ℝ} (hh : 0 < h)
    {F : ℝ → WholeLineRealL2}
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume t (t + h))
    (hpoint : ∀ q ∈ Set.Icc t (t + h),
      ‖weightedMovingHeatL2Semigroup eta c (t + h - q) (F q) - F t‖ ≤ E) :
    ‖h⁻¹ • (∫ q in t..t + h,
        weightedMovingHeatL2Semigroup eta c (t + h - q) (F q)) - F t‖ ≤ E := by
  let G : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (t + h - q) (F q)
  have hhistG : IntervalIntegrable G volume t (t + h) := by
    simpa only [G] using hhist
  have hconst : IntervalIntegrable (fun _ : ℝ => F t) volume t (t + h) :=
    intervalIntegrable_const
  have hsub : IntervalIntegrable (fun q => G q - F t) volume t (t + h) :=
    hhistG.sub hconst
  have heq :
      h⁻¹ • (∫ q in t..t + h, G q) - F t =
        h⁻¹ • (∫ q in t..t + h, G q - F t) := by
    rw [intervalIntegral.integral_sub hhistG hconst,
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_sub, smul_smul,
      inv_mul_cancel₀ hh.ne', one_smul]
  rw [show (fun q => weightedMovingHeatL2Semigroup eta c
      (t + h - q) (F q)) = G from rfl, heq, norm_smul]
  have hint := intervalIntegral_norm_le_const_mul_sub
    (a := t) (b := t + h) (C := E)
    (le_add_of_nonneg_right hh.le)
    (G := fun q => G q - F t) (by
      intro q hq
      exact hpoint q hq)
  have hint' : ‖∫ q in t..t + h, G q - F t‖ ≤ E * h := by
    simpa only [add_sub_cancel_left] using hint
  calc
    ‖h⁻¹‖ * ‖∫ q in t..t + h, G q - F t‖ ≤
        ‖h⁻¹‖ * (E * h) := by
      exact mul_le_mul_of_nonneg_left hint' (norm_nonneg _)
    _ = E := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos hh]
      field_simp [hh.ne']

/-- On every sufficiently short positive interval, the complete fresh heat
history is uniformly close to the current forcing value. -/
theorem weightedMovingHeatL2_freshDuhamel_eventually_uniform
    {eta c t : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : ContinuousAt F t) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ q ∈ Set.Icc t (t + h),
        ‖weightedMovingHeatL2Semigroup eta c (t + h - q) (F q) - F t‖ < eps := by
  let M : ℝ := Real.exp (|eta ^ 2 - c * eta|)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hMone : 1 ≤ M := by
    dsimp only [M]
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (abs_nonneg (eta ^ 2 - c * eta)))
  have hFeps : 0 < eps / (2 * M) := by positivity
  have hFnear : {q : ℝ | dist (F q) (F t) < eps / (2 * M)} ∈ 𝓝 t :=
    (Metric.tendsto_nhds.1 hF) _ hFeps
  obtain ⟨dF, hdF, hballF⟩ := Metric.mem_nhds_iff.mp hFnear
  have hSzero := weightedMovingHeatL2Semigroup_tendsto_zero eta c (F t)
  have hSnear : {r : ℝ |
      dist (weightedMovingHeatL2Semigroup eta c r (F t)) (F t) < eps / 2} ∈
      nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    (Metric.tendsto_nhds.1 hSzero) _ (half_pos heps)
  obtain ⟨dS, hdS, hballS⟩ := Metric.mem_nhdsWithin_iff.mp hSnear
  let d : ℝ := min (min dF dS) 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hsmall : Set.Iio d ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hd
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds hsmall] with h hh hhd
  intro q hq
  have hhpos : 0 < h := hh
  have hqdist : dist q t < dF := by
    have hqt : 0 ≤ q - t := sub_nonneg.mpr hq.1
    have hqt_le : q - t ≤ h := by linarith [hq.2]
    rw [Real.dist_eq, abs_of_nonneg hqt]
    exact hqt_le.trans_lt (hhd.trans_le (by
      dsimp only [d]
      exact min_le_left _ _ |>.trans (min_le_left _ _)))
  have hFqt : ‖F q - F t‖ < eps / (2 * M) := by
    have := hballF (Metric.mem_ball.mpr hqdist)
    simpa only [mem_setOf_eq, dist_eq_norm] using this
  let lag : ℝ := t + h - q
  have hlag0 : 0 ≤ lag := by dsimp only [lag]; linarith [hq.2]
  have hlagh : lag ≤ h := by dsimp only [lag]; linarith [hq.1]
  have hlag1 : lag ≤ 1 := hlagh.trans (hhd.le.trans (by
    dsimp only [d]
    exact min_le_right _ _))
  have hmap :
      ‖weightedMovingHeatL2Semigroup eta c lag (F q - F t)‖ < eps / 2 := by
    have hop := weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
      (eta := eta) (c := c) (H := (1 : ℝ)) ⟨hlag0, hlag1⟩ (F q - F t)
    have hMdef : Real.exp (|eta ^ 2 - c * eta| * (1 : ℝ)) = M := by
      simp only [mul_one, M]
    rw [hMdef] at hop
    calc
      ‖weightedMovingHeatL2Semigroup eta c lag (F q - F t)‖ ≤
          M * ‖F q - F t‖ := hop
      _ < M * (eps / (2 * M)) := mul_lt_mul_of_pos_left hFqt hM
      _ = eps / 2 := by field_simp [hM.ne']
  by_cases hlagpos : 0 < lag
  · have hlagdS : dist lag (0 : ℝ) < dS := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hlagpos]
      exact hlagh.trans_lt (hhd.trans_le (by
        dsimp only [d]
        exact min_le_left _ _ |>.trans (min_le_right _ _)))
    have hSft :
        ‖weightedMovingHeatL2Semigroup eta c lag (F t) - F t‖ < eps / 2 := by
      have := hballS ⟨Metric.mem_ball.mpr hlagdS, hlagpos⟩
      simpa only [mem_setOf_eq, dist_eq_norm] using this
    have hdecomp :
        weightedMovingHeatL2Semigroup eta c lag (F q) - F t =
          weightedMovingHeatL2Semigroup eta c lag (F q - F t) +
            (weightedMovingHeatL2Semigroup eta c lag (F t) - F t) := by
      rw [map_sub]
      abel
    rw [hdecomp]
    exact (norm_add_le _ _).trans_lt (add_lt_add hmap hSft) |>.trans_eq (by ring)
  · have hlagzero : lag = 0 := le_antisymm (le_of_not_gt hlagpos) hlag0
    change
      ‖weightedMovingHeatL2Semigroup eta c lag (F q) - F t‖ < eps
    rw [hlagzero, weightedMovingHeatL2Semigroup_zero,
      ContinuousLinearMap.one_apply]
    exact hFqt.trans (by
      rw [div_lt_iff₀ (mul_pos (by norm_num) hM)]
      nlinarith)

/-- The normalized fresh Duhamel interval converges strongly to the current
forcing value.  Integrability is kept explicit because it is supplied by
the natural bounded forcing history in applications. -/
theorem weightedMovingHeatL2_freshDuhamel_slope_tendsto
    {eta c t : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : ContinuousAt F t)
    (hhist : ∀ h, 0 < h → IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume t (t + h)) :
    Tendsto (fun h : ℝ => h⁻¹ • (∫ q in t..t + h,
      weightedMovingHeatL2Semigroup eta c (t + h - q) (F q)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (F t)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [self_mem_nhdsWithin,
    weightedMovingHeatL2_freshDuhamel_eventually_uniform hF (eps / 2)
      (half_pos heps)]
      with h hh hpoint
  rw [dist_eq_norm]
  exact (weightedMovingHeatL2_freshDuhamel_slope_norm_sub_le hh
    (hhist h hh) (fun q hq => (hpoint q hq).le)).trans_lt (half_lt_self heps)

section AxiomAudit

#print axioms weightedMovingHeatL2_freshDuhamel_slope_norm_sub_le
#print axioms weightedMovingHeatL2_freshDuhamel_eventually_uniform
#print axioms weightedMovingHeatL2_freshDuhamel_slope_tendsto

end AxiomAudit

end ShenWork.Paper1
