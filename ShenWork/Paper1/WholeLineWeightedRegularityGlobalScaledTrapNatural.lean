import ShenWork.Paper1.WholeLineWeightedRegularityScaledTrapFamilyNatural

open Set

noncomputable section

namespace ShenWork.Paper1

/-!
# The common scaled trap on the canonical global orbit

The late-window trap is constructed on the phase-normalized fixed point
issued from the `n`-th restart datum.  This file records the exact closed
second-half-window identity with the glued global orbit.  The right endpoint
is not covered by an `Ico` cell formula; it is discharged separately through
the overlap of consecutive canonical segments.
-/

/-- On the closed second half of segment `n`, the glued global trajectory is
exactly that segment.  The endpoint `r = step` uses the overlap with segment
`n+1`, rather than an invalid closed-cell specialization of an `Ico` lemma. -/
theorem wholeLineCauchyGlobalBUC_eq_segment_second_half_closed
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hrstep : r ≤ wholeLineCauchyGlobalStep p u₀) :
    wholeLineCauchyGlobalBUC p u₀
        (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r) =
      wholeLineCauchyGlobalSegment p u₀ n
        ⟨wholeLineCauchyGlobalStep p u₀ + r,
          add_nonneg (wholeLineCauchyGlobalStep_pos p u₀).le hr0,
          by
            rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
            linarith⟩ := by
  let step := wholeLineCauchyGlobalStep p u₀
  have hstep : 0 < step := wholeLineCauchyGlobalStep_pos p u₀
  rcases lt_or_eq_of_le hrstep with hrlt | rfl
  · have htcell : ((n : ℝ) + 1) * step + r ∈
        Set.Ico (((n + 1 : ℕ) : ℝ) * step)
          ((((n + 1 : ℕ) : ℝ) + 1) * step) := by
      constructor
      · push_cast
        linarith
      · push_cast
        linarith
    have hcell := wholeLineCauchyGlobalBUC_eq_preferred_on_cell
      p u₀ (n + 1) htcell
    have hpred : (n + 1).pred = n := by rfl
    rw [hpred] at hcell
    have hlocal : ((n : ℝ) + 1) * step + r - (n : ℝ) * step =
        step + r := by ring
    rw [hlocal] at hcell
    rw [hcell]
    exact wholeLineBUCTrajectoryExtend_eq
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le _
        ⟨add_nonneg hstep.le hr0,
          by
            dsimp only [step]
            rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
            linarith⟩
  · have htcell : ((n : ℝ) + 1) * step + step ∈
        Set.Ico (((n + 2 : ℕ) : ℝ) * step)
          ((((n + 2 : ℕ) : ℝ) + 1) * step) := by
      constructor
      · push_cast
        nlinarith
      · push_cast
        nlinarith
    have hcell := wholeLineCauchyGlobalBUC_eq_preferred_on_cell
      p u₀ (n + 2) htcell
    have hpred : (n + 2).pred = n + 1 := by rfl
    rw [hpred] at hcell
    have hlocal : ((n : ℝ) + 1) * step + step -
        ((n + 1 : ℕ) : ℝ) * step = step := by
      push_cast
      ring
    rw [hlocal] at hcell
    have hover := wholeLineCauchyGlobalSegment_overlap_apply
      p hregime u₀ hu₀ n hstep.le le_rfl
    rw [hover]
    rw [hcell]
    exact wholeLineBUCTrajectoryExtend_eq
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le _
        ⟨hstep.le,
          by
            dsimp only [step]
            rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
            linarith⟩

/-- The phase-normalized fixed point on the second half of restart `n` is
the global co-moving slice at the corresponding absolute time. -/
theorem wholeLineCauchyGlobal_coMoving_eq_translatedSegment_second_half_closed
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hrstep : r ≤ wholeLineCauchyGlobalStep p u₀) :
    let datum := wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n
    let Traj := wholeLineCauchyBUCMildFixedPoint p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    let q : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1
          (x + c * s)
    (fun x => wholeLineCauchyGlobalU p u₀
        (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
        (x + c * (((n : ℝ) + 1) *
          wholeLineCauchyGlobalStep p u₀ + r))) =
      q (wholeLineCauchyGlobalStep p u₀ + r) := by
  dsimp only
  let step := wholeLineCauchyGlobalStep p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let d := c * ((n : ℝ) * step)
  let z : Set.Icc (0 : ℝ) H :=
    ⟨step + r, add_nonneg (wholeLineCauchyGlobalStep_pos p u₀).le hr0,
      by
        dsimp only [H, step]
        rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
        linarith⟩
  have hext : wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyBUCMildFixedPoint p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n)
          (wholeLineCauchyGlobalSegmentTime_rate p u₀)) (step + r) =
      wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z := by
    exact wholeLineBUCTrajectoryExtend_eq
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le _ z.2
  have htranslate :
      wholeLineCauchyBUCMildFixedPoint p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n)
          (wholeLineCauchyGlobalSegmentTime_rate p u₀) =
        wholeLineBUCTrajectorySpatialTranslate
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le d
          (wholeLineCauchyGlobalSegment p u₀ n) := by
    dsimp only [d, step, wholeLineCauchyGlobalTranslatedDatumIndex,
      wholeLineCauchyGlobalSegment]
    exact wholeLineCauchyBUCMildFixedPoint_spatialTranslate p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalDatum p u₀ n)
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
  funext x
  rw [show wholeLineCauchyGlobalU p u₀
      (((n : ℝ) + 1) * step + r) =
        (wholeLineCauchyGlobalBUC p u₀
          (((n : ℝ) + 1) * step + r)).1 by rfl]
  rw [wholeLineCauchyGlobalBUC_eq_segment_second_half_closed
    p hregime u₀ hu₀ n hr0 hrstep]
  rw [hext, htranslate]
  simp only [wholeLineBUCTrajectorySpatialTranslate_apply]
  congr 1
  dsimp only [d, step]
  ring

#print axioms wholeLineCauchyGlobalBUC_eq_segment_second_half_closed
#print axioms
  wholeLineCauchyGlobal_coMoving_eq_translatedSegment_second_half_closed

end ShenWork.Paper1
