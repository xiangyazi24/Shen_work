import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Bounded short-window Volterra uniqueness

The damping-removal argument needs only a uniform bound for the two Hilbert
trajectories.  Continuity was previously used solely to attain a maximum of
the norm.  Taking the supremum of the bounded norm range gives the same
contraction argument without assuming the exact-weight state is continuous.
-/

/-- A uniformly bounded solution of the homogeneous damped Volterra
equation vanishes on a sufficiently short window. -/
theorem weightedMovingHeat_dampedVolterra_eq_zero_of_bounded_short
    {eta c a r B : ℝ} {D : ℝ → WholeLineRealL2}
    (har : a ≤ r)
    (hDbound : ∀ t ∈ Set.Icc a r, ‖D t‖ ≤ B)
    (hvolterra : ∀ t ∈ Set.Icc a r,
      D t = ∫ q in a..t,
        Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (D q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r, D t = 0 := by
  let E : Set ℝ := {y | ∃ t ∈ Set.Icc a r, y = ‖D t‖}
  have hEne : E.Nonempty := ⟨‖D a‖, a, ⟨le_rfl, har⟩, rfl⟩
  have hEbdd : BddAbove E := by
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact hDbound t ht
  let M : ℝ := sSup E
  have hnorm_le : ∀ t ∈ Set.Icc a r, ‖D t‖ ≤ M := by
    intro t ht
    exact le_csSup hEbdd ⟨t, ht, rfl⟩
  have hM0 : 0 ≤ M := by
    exact (norm_nonneg (D a)).trans
      (le_csSup hEbdd ⟨a, ⟨le_rfl, har⟩, rfl⟩)
  let K : ℝ := Real.exp (|eta ^ 2 - c * eta| * (r - a))
  have hK0 : 0 ≤ K := Real.exp_nonneg _
  have hmember_le : ∀ y ∈ E, y ≤ K * M * (r - a) := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have hpoint : ∀ q ∈ Set.uIoc a t,
        ‖Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q) (D q)‖ ≤
          K * M := by
      intro q hq
      rw [Set.uIoc_of_le ht.1] at hq
      have hq_ar : q ∈ Set.Icc a r :=
        ⟨hq.1.le, hq.2.trans ht.2⟩
      have hlag : t - q ∈ Set.Icc (0 : ℝ) (r - a) := by
        constructor <;> linarith [hq.1, hq.2, ht.1, ht.2]
      calc
        ‖Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q) (D q)‖ ≤
            K * ‖D q‖ := by
          simpa only [K] using
            exp_neg_smul_weightedMovingHeatL2Semigroup_norm_le_on_lag_window
              hlag (D q)
        _ ≤ K * M := mul_le_mul_of_nonneg_left (hnorm_le q hq_ar) hK0
    have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := t) hpoint
    have hDt : ‖D t‖ ≤ K * M * (t - a) := by
      rw [← hvolterra t ht] at hnorm_int
      simpa only [abs_of_nonneg (sub_nonneg.mpr ht.1)] using hnorm_int
    exact hDt.trans (by
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
        (mul_nonneg hK0 hM0))
  have hM_le : M ≤ K * M * (r - a) := csSup_le hEne hmember_le
  have hM : M = 0 := by
    dsimp only [K] at hshort hM_le
    nlinarith
  intro t ht
  apply norm_eq_zero.mp
  exact le_antisymm ((hnorm_le t ht).trans_eq hM) (norm_nonneg _)

/-- Two uniformly bounded trajectories with the same datum and forcing in
the damped restart equation agree on a short window. -/
theorem weightedMovingHeat_dampedRestart_unique_of_bounded_short
    {eta c a r BZ BY : ℝ}
    {Z Y F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r)
    (hZbound : ∀ t ∈ Set.Icc a r, ‖Z t‖ ≤ BZ)
    (hYbound : ∀ t ∈ Set.Icc a r, ‖Y t‖ ≤ BY)
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hYint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Y q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hYdamped : ∀ t ∈ Set.Icc a r,
      Y t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Y q + F q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r, Z t = Y t := by
  let D : ℝ → WholeLineRealL2 := fun t => Z t - Y t
  have hDnorm : ∀ t ∈ Set.Icc a r, ‖D t‖ ≤ BZ + BY := by
    intro t ht
    exact (norm_sub_le (Z t) (Y t)).trans
      (add_le_add (hZbound t ht) (hYbound t ht))
  have hDvolterra : ∀ t ∈ Set.Icc a r,
      D t = ∫ q in a..t,
        Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (D q) := by
    intro t ht
    have hZi := hZint t ht
    have hYi := hYint t ht
    change Z t - Y t = ∫ q in a..t,
      Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q - Y q)
    rw [hZdamped t ht, hYdamped t ht]
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hZi hYi]
    apply intervalIntegral.integral_congr
    intro q _hq
    simp only [← smul_sub, ← map_sub]
    congr 2
    abel
  have hDzero := weightedMovingHeat_dampedVolterra_eq_zero_of_bounded_short
    (eta := eta) (c := c) har hDnorm hDvolterra hshort
  intro t ht
  exact sub_eq_zero.mp (hDzero t ht)

/-- Ambient-window damping removal with a bounded actual trajectory.  All
candidate histories and its compact-window bound are constructed from the
uniform forcing budget.  Unlike the earlier wrapper, this theorem does not
assume continuity of the actual exact-weight state. -/
theorem
    weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_ambient_bounded_of_short
    {eta c L R a r K BZ : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hLa : L < a) (har : a ≤ r) (hrR : r < R)
    (hK : 0 ≤ K)
    (hF : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R)))
    (hZbound : ∀ t ∈ Set.Icc a r, ‖Z t‖ ≤ BZ)
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t := by
  have hFsmall : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K := by
    intro q hq
    exact hF q ⟨hLa.le.trans hq.1, hq.2.trans hrR.le⟩
  have hhist_small : ∀ t ∈ Set.Icc a r,
      AEStronglyMeasurable
        (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
        (volume.restrict (Set.Icc a t)) := by
    intro t ht
    apply (hhist_meas t).mono_measure
    apply Measure.restrict_mono
    · intro q hq
      rw [Set.uIoc_of_le (hLa.trans_le (har.trans hrR.le)).le]
      exact ⟨hLa.trans_le hq.1, hq.2.trans (ht.2.trans hrR.le)⟩
    · exact le_rfl
  have hscalarHistories : ∀ t ∈ Set.Icc a r,
      IntervalIntegrable
          (fun q => Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q) (F q))
          volume a t ∧
        IntervalIntegrable
          (fun q => (1 - Real.exp (-(t - q))) •
            weightedMovingHeatL2Semigroup eta c (t - q) (F q))
          volume a t := by
    intro t ht
    exact weightedMovingHeat_damped_histories_intervalIntegrable_of_uniform_norm_bound
      ht.1 hK (fun q hq => hF q
        ⟨hLa.le.trans hq.1, hq.2.trans (ht.2.trans hrR.le)⟩)
        (hhist_small t ht)
  have hnested : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t := by
    intro t ht
    have hinner : ∀ q ∈ Set.Icc a t, IntervalIntegrable
        (fun s => weightedMovingHeatL2Semigroup eta c (q - s) (F s))
        volume a q := by
      intro q hq
      exact weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_norm_bound
        hq.1 hK (fun s hs => hF s
          ⟨hLa.le.trans hs.1, hs.2.trans (hq.2.trans (ht.2.trans hrR.le))⟩)
          (hhist_small q ⟨hq.1, hq.2.trans ht.2⟩)
    have hterminal : AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Ioc a t)) :=
      (hhist_small t ht).mono_measure
        (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    have htriMeas :=
      weightedMovingHeat_triangleKernel_aestronglyMeasurable_of_terminal_history
        hterminal
    have hproduct :=
      weightedMovingHeat_triangleKernel_integrable_of_uniform_norm_bound
        ht.1 hK (fun s hs => hF s
          ⟨hLa.le.trans hs.1.le, hs.2.trans (ht.2.trans hrR.le)⟩) htriMeas
    exact weightedMovingHeat_nested_damped_history_intervalIntegrable_of_triangleKernel
      ht.1 hinner hproduct
  have htriangle : ∀ t ∈ Set.Icc a r,
      (∫ q in a..t, Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
      ∫ s in a..t, (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
    intro t ht
    have hterminal : AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Ioc a t)) :=
      (hhist_small t ht).mono_measure
        (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    exact weightedMovingHeat_triangleFubini_of_uniform_norm_bound
      ht.1 hK (fun s hs => hF s
        ⟨hLa.le.trans hs.1, hs.2.trans (ht.2.trans hrR.le)⟩)
      (fun q hq => hhist_small q ⟨hq.1, hq.2.trans ht.2⟩)
      (weightedMovingHeat_triangleKernel_aestronglyMeasurable_of_terminal_history
        hterminal)
  let Y : ℝ → WholeLineRealL2 :=
    weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F
  have hYcont : ContinuousOn Y (Set.Icc a r) := by
    exact weightedMovingHeatFullGeneratorCandidate_continuousOn_of_uniform_norm_bound
      (eta := eta) (c := c) hLa har hrR Z₀ hK hF hhist_meas
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hYcont.norm
  let BY : ℝ := max C 0
  have hYbound : ∀ t ∈ Set.Icc a r, ‖Y t‖ ≤ BY := by
    intro t ht
    exact (hC (Set.mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hYint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Y q + F q))
      volume a t := by
    intro t ht
    exact weightedMovingHeatFullGeneratorCandidate_damped_history_intervalIntegrable
      ht.1 Z₀ (hnested t ht) (hscalarHistories t ht).1
  have hYdamped : ∀ t ∈ Set.Icc a r,
      Y t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Y q + F q) := by
    intro t ht
    exact weightedMovingHeatFullGeneratorCandidate_damped_resolvent_identity_of_triangleFubini
      ht.1 Z₀ (hnested t ht) (hscalarHistories t ht).1
        (hscalarHistories t ht).2 (htriangle t ht)
  exact weightedMovingHeat_dampedRestart_unique_of_bounded_short har
    hZbound hYbound hZint hYint hZdamped hYdamped hshort

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.weightedMovingHeat_dampedVolterra_eq_zero_of_bounded_short
#print axioms
  ShenWork.Paper1.weightedMovingHeat_dampedRestart_unique_of_bounded_short
#print axioms
  ShenWork.Paper1.weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_ambient_bounded_of_short
