import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartActual

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Automatic positive-time windows for the full weighted generator

The damping-removal argument for the full weighted generator is local in
time.  This file chooses its four nested endpoints around an arbitrary
positive target time.  In particular, the small-window condition is a
consequence of `0 < t < T`, rather than an extra analytic hypothesis.
-/

/-- Around every interior positive time there is a four-endpoint window on
which the damping-removal Volterra mass is strictly smaller than one. -/
theorem exists_paper5WeightedGeneratorShortWindow
    {eta c t T : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ∃ L a r R : ℝ,
      0 < L ∧ L < a ∧ a < t ∧ t < r ∧ r < R ∧ R < T ∧
        R - L ≤ 1 ∧
        Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1 := by
  let K : ℝ := |eta ^ 2 - c * eta|
  let mass : ℝ → ℝ := fun q => Real.exp (K * q) * q
  have hmass_cont : ContinuousAt mass 0 := by
    dsimp only [mass]
    fun_prop
  rw [Metric.continuousAt_iff] at hmass_cont
  obtain ⟨e, he, hclose⟩ := hmass_cont 1 (by norm_num)
  let d : ℝ := min (e / 8)
    (min (t / 8) (min ((T - t) / 8) (1 / 8)))
  have hTt : 0 < T - t := sub_pos.mpr htT
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by norm_num)))
  have hde : d ≤ e / 8 := by
    dsimp only [d]
    exact min_le_left _ _
  have hdt : d ≤ t / 8 := by
    dsimp only [d]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdT : d ≤ (T - t) / 8 := by
    dsimp only [d]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hd1 : d ≤ 1 / 8 := by
    dsimp only [d]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hfour_e : dist (4 * d) 0 < e := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos (by norm_num) hd)]
    nlinarith
  have hmass_close := hclose hfour_e
  have hmass_zero : mass 0 = 0 := by simp [mass]
  have hmass_nonneg : 0 ≤ mass (4 * d) := by
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (by norm_num) hd.le)
  rw [hmass_zero, Real.dist_eq, sub_zero,
    abs_of_nonneg hmass_nonneg] at hmass_close
  refine ⟨t - 3 * d, t - 2 * d, t + 2 * d, t + 3 * d,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · have hgap : (t + 2 * d) - (t - 2 * d) = 4 * d := by ring
    rw [hgap]
    simpa only [K, mass] using hmass_close

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_paper5WeightedGeneratorShortWindow
