import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorShiftConvergence
import ShenWork.Paper1.WholeLineWeightedRegularityFreshDuhamelDerivative

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Right derivative of an exact-weight mild restart

The full mild candidate restarts at every nonnegative increment.  Combining
that algebraic identity with the right generator-domain theorem for the
current state and the fresh-Duhamel endpoint theorem gives its canonical
right time derivative.  No difference-quotient datum is carried.
-/

/-- The exact-weight full mild candidate satisfies the usual semigroup
restart identity.  The two terminal heat histories are the only explicit
Bochner-integrability hypotheses. -/
theorem weightedMovingHeatFullGeneratorCandidate_restart
    {eta c a t h : ℝ} (hat : a ≤ t) (hh : 0 ≤ h)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hhist_t : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hhist_th : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume a (t + h)) :
    weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F (t + h) =
      weightedMovingHeatL2Semigroup eta c h
          (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) +
        ∫ q in t..t + h,
          weightedMovingHeatL2Semigroup eta c (t + h - q) (F q) := by
  let G : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (t + h - q) (F q)
  let H : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (t - q) (F q)
  have hatth : a ≤ t + h := by linarith
  have htth : t ≤ t + h := by linarith
  have hGold : IntervalIntegrable G volume a t := by
    apply hhist_th.mono_set
    rw [Set.uIcc_of_le hatth, Set.uIcc_of_le hat]
    exact Set.Icc_subset_Icc_right htth
  have hGrecent : IntervalIntegrable G volume t (t + h) := by
    apply hhist_th.mono_set
    rw [Set.uIcc_of_le hatth, Set.uIcc_of_le htth]
    exact Set.Icc_subset_Icc_left hat
  have hcommute :
      weightedMovingHeatL2Semigroup eta c h
          (∫ q in a..t, H q) =
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c h (H q) := by
    simpa only [H] using
      ((weightedMovingHeatL2Semigroup eta c h).intervalIntegral_comp_comm
        hhist_t).symm
  have hold :
      weightedMovingHeatL2Semigroup eta c h
          (∫ q in a..t, H q) = ∫ q in a..t, G q := by
    rw [hcommute]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hat] at hq
    have hadd := weightedMovingHeatL2Semigroup_add
      (eta := eta) (c := c) hh (sub_nonneg.mpr hq.2)
    have happ := congrArg
      (fun L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => L (F q)) hadd
    simpa only [ContinuousLinearMap.comp_apply, H, G,
      show h + (t - q) = t + h - q by ring] using happ
  have hhom :
      weightedMovingHeatL2Semigroup eta c h
          (weightedMovingHeatL2Semigroup eta c (t - a) Z₀) =
        weightedMovingHeatL2Semigroup eta c (t + h - a) Z₀ := by
    have hadd := weightedMovingHeatL2Semigroup_add
      (eta := eta) (c := c) hh (sub_nonneg.mpr hat)
    have happ := congrArg
      (fun L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => L Z₀) hadd
    simpa only [ContinuousLinearMap.comp_apply,
      show h + (t - a) = t + h - a by ring] using happ
  unfold weightedMovingHeatFullGeneratorCandidate
  rw [map_add, hhom]
  change
    weightedMovingHeatL2Semigroup eta c (t + h - a) Z₀ +
        ∫ q in a..t + h, G q =
      weightedMovingHeatL2Semigroup eta c (t + h - a) Z₀ +
        weightedMovingHeatL2Semigroup eta c h (∫ q in a..t, H q) +
          ∫ q in t..t + h, G q
  rw [hold, ← intervalIntegral.integral_add_adjacent_intervals hGold hGrecent]
  abel

/-- The fresh Duhamel history has right derivative equal to the current
forcing value. -/
theorem weightedMovingHeatL2_freshDuhamel_hasDerivWithinAt_zero
    {eta c t : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : ContinuousAt F t)
    (hhist : ∀ h, 0 < h → IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume t (t + h)) :
    HasDerivWithinAt
      (fun h : ℝ => ∫ q in t..t + h,
        weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      (F t) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext h
    simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨hh, hne⟩
      exact lt_of_le_of_ne hh (Ne.symm hne)
    · intro hh
      exact ⟨hh.le, ne_of_gt hh⟩
  rw [hset]
  have htend := weightedMovingHeatL2_freshDuhamel_slope_tendsto hF hhist
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [slope_def_module]
  simp only [add_zero, intervalIntegral.integral_same, sub_zero]

/-- A full exact-weight mild restart has the canonical right derivative:
the generator value of its current state plus the current forcing. -/
theorem weightedMovingHeatFullGeneratorCandidate_hasDerivWithinAt_right
    {eta c a t theta H K : ℝ}
    (hat : a < t) (htheta : 0 < theta)
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hFbound : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a t, ∀ q ∈ Set.Icc a t,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hhist_t : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hbase_meas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      (volume.restrict (Set.Ioc (0 : ℝ) (t - a))))
    (hshift_meas : ∀ e, 0 < e → e ≤ t - a →
      AEStronglyMeasurable
        (fun r => weightedMovingHeatL2Generator eta c r
          (F (t + e - r)))
        (volume.restrict (Set.Icc e (t - a + e))))
    (hF : ContinuousAt F t)
    (hhist_full : ∀ h, 0 < h → IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume a (t + h)) :
    HasDerivWithinAt
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F + F t)
      (Set.Ici t) t := by
  let C : ℝ → WholeLineRealL2 :=
    weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F
  let Fresh : ℝ → WholeLineRealL2 := fun h =>
    ∫ q in t..t + h,
      weightedMovingHeatL2Semigroup eta c (t + h - q) (F q)
  have hsem :=
    weightedMovingHeatL2Semigroup_fullGeneratorCandidate_hasDerivWithinAt_zero
      (F := F) (Z₀ := Z₀) hat htheta hH hK hFbound hFholder
      hhist_t hbase_meas hshift_meas
  have hhist_fresh : ∀ h, 0 < h → IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume t (t + h) := by
    intro h hh
    apply (hhist_full h hh).mono_set
    rw [Set.uIcc_of_le (by linarith [hat] : a ≤ t + h),
      Set.uIcc_of_le (by linarith : t ≤ t + h)]
    exact Set.Icc_subset_Icc_left hat.le
  have hfresh : HasDerivWithinAt Fresh (F t) (Set.Ici 0) 0 := by
    exact weightedMovingHeatL2_freshDuhamel_hasDerivWithinAt_zero hF hhist_fresh
  have hsum : HasDerivWithinAt
      (fun h : ℝ =>
        weightedMovingHeatL2Semigroup eta c h (C t) + Fresh h)
      (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F + F t)
      (Set.Ici 0) 0 := hsem.add hfresh
  have hshift : HasDerivWithinAt (fun h : ℝ => C (t + h))
      (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F + F t)
      (Set.Ici 0) 0 := by
    apply hsum.congr
    · intro h hh
      change 0 ≤ h at hh
      rcases hh.eq_or_lt with rfl | hh
      · simp only [Fresh, add_zero, intervalIntegral.integral_same,
          add_zero, weightedMovingHeatL2Semigroup_zero,
          ContinuousLinearMap.one_apply]
      · exact weightedMovingHeatFullGeneratorCandidate_restart
          (F := F) (Z₀ := Z₀) hat.le hh.le hhist_t
          (hhist_full h hh)
    · simp only [Fresh, add_zero, intervalIntegral.integral_same,
        add_zero, weightedMovingHeatL2Semigroup_zero,
        ContinuousLinearMap.one_apply]
  have hsub : HasDerivWithinAt (fun r : ℝ => r - t) 1 (Set.Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hmaps : MapsTo (fun r : ℝ => r - t) (Set.Ici t) (Set.Ici 0) := by
    intro r hr
    change t ≤ r at hr
    exact sub_nonneg.mpr hr
  have hcomp := hshift.scomp_of_eq t hsub hmaps (by ring)
  have heq :
      ((fun h : ℝ => C (t + h)) ∘ fun r : ℝ => r - t) = C := by
    funext r
    simp only [Function.comp_apply]
    congr 1
    ring
  rw [heq] at hcomp
  simpa only [one_smul, C] using hcomp

section AxiomAudit

#print axioms weightedMovingHeatFullGeneratorCandidate_restart
#print axioms weightedMovingHeatL2_freshDuhamel_hasDerivWithinAt_zero
#print axioms weightedMovingHeatFullGeneratorCandidate_hasDerivWithinAt_right

end AxiomAudit

end ShenWork.Paper1
