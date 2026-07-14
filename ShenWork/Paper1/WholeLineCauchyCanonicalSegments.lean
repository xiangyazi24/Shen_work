import ShenWork.Paper1.WholeLineCauchyCanonicalRestart

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Uniform canonical segments in the stable regime

A single clamp and a single positive construction time are selected from the
stable ceiling of the original datum.  Recursive midpoint restart data then
generate overlapping canonical segments.  Every datum and every segment
retains the same nonnegative stable box.
-/

def wholeLineCauchyGlobalClamp (p : CMParams) (u₀ : WholeLineBUC) : ℝ :=
  wholeLineCauchyStableCeiling p u₀ + 1

theorem wholeLineCauchyGlobalClamp_pos (p : CMParams) (u₀ : WholeLineBUC) :
    0 < wholeLineCauchyGlobalClamp p u₀ := by
  have hC : 0 < wholeLineCauchyStableCeiling p u₀ :=
    (norm_nonneg u₀).trans_lt (wholeLineCauchyStableCeiling_gt_norm p u₀)
  dsimp [wholeLineCauchyGlobalClamp]
  linarith

noncomputable def wholeLineCauchyGlobalSegmentTime
    (p : CMParams) (u₀ : WholeLineBUC) : ℝ :=
  Classical.choose (exists_pos_time_wholeLineCauchyBUCRate_and_displacement
    p (wholeLineCauchyGlobalClamp_pos p u₀).le one_pos)

theorem wholeLineCauchyGlobalSegmentTime_pos
    (p : CMParams) (u₀ : WholeLineBUC) :
    0 < wholeLineCauchyGlobalSegmentTime p u₀ :=
  (Classical.choose_spec
    (exists_pos_time_wholeLineCauchyBUCRate_and_displacement
      p (wholeLineCauchyGlobalClamp_pos p u₀).le one_pos)).1

theorem wholeLineCauchyGlobalSegmentTime_rate
    (p : CMParams) (u₀ : WholeLineBUC) :
    wholeLineCauchyBUCMildRate p (wholeLineCauchyGlobalClamp p u₀)
        (wholeLineCauchyGlobalSegmentTime p u₀) < 1 :=
  (Classical.choose_spec
    (exists_pos_time_wholeLineCauchyBUCRate_and_displacement
      p (wholeLineCauchyGlobalClamp_pos p u₀).le one_pos)).2.1

theorem wholeLineCauchyGlobalSegmentTime_displacement
    (p : CMParams) (u₀ : WholeLineBUC) :
    wholeLineCauchyBUCMildDisplacement p (wholeLineCauchyGlobalClamp p u₀)
        (wholeLineCauchyGlobalSegmentTime p u₀) < 1 :=
  (Classical.choose_spec
    (exists_pos_time_wholeLineCauchyBUCRate_and_displacement
      p (wholeLineCauchyGlobalClamp_pos p u₀).le one_pos)).2.2

def wholeLineCauchyGlobalStep (p : CMParams) (u₀ : WholeLineBUC) : ℝ :=
  wholeLineCauchyGlobalSegmentTime p u₀ / 2

theorem wholeLineCauchyGlobalStep_pos (p : CMParams) (u₀ : WholeLineBUC) :
    0 < wholeLineCauchyGlobalStep p u₀ := by
  dsimp [wholeLineCauchyGlobalStep]
  linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]

theorem wholeLineCauchyBUCMildRate_mono
    (p : CMParams) {M S T : ℝ} (hM : 0 ≤ M)
    (hS : 0 ≤ S) (hST : S ≤ T) :
    wholeLineCauchyBUCMildRate p M S ≤
      wholeLineCauchyBUCMildRate p M T := by
  have hT : 0 ≤ T := hS.trans hST
  have hsqrt : Real.sqrt S ≤ Real.sqrt T := Real.sqrt_le_sqrt hST
  have hflux : 0 ≤
      (2 / Real.sqrt (4 * Real.pi)) * wholeLineCauchyFluxLip p M := by
    have := wholeLineCauchyFluxLip_nonneg p hM
    positivity
  have hreact : 0 ≤ 1 + reactionLip p.α M := by
    linarith [reactionLip_nonneg p.hα hM]
  unfold wholeLineCauchyBUCMildRate
  gcongr

theorem wholeLineCauchyGlobalStep_rate
    (p : CMParams) (u₀ : WholeLineBUC) :
    wholeLineCauchyBUCMildRate p (wholeLineCauchyGlobalClamp p u₀)
        (wholeLineCauchyGlobalStep p u₀) < 1 := by
  apply lt_of_le_of_lt
    (wholeLineCauchyBUCMildRate_mono p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalStep_pos p u₀).le ?_)
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)
  dsimp [wholeLineCauchyGlobalStep]
  linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]

def wholeLineCauchyGlobalDatum
    (p : CMParams) (u₀ : WholeLineBUC) : ℕ → WholeLineBUC
  | 0 => u₀
  | n + 1 =>
      let H := wholeLineCauchyGlobalSegmentTime p u₀
      let δ := wholeLineCauchyGlobalStep p u₀
      let U := wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀ n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
      U ⟨δ, (wholeLineCauchyGlobalStep_pos p u₀).le,
        by dsimp [δ, H, wholeLineCauchyGlobalStep];
           linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]⟩

def wholeLineCauchyGlobalSegment
    (p : CMParams) (u₀ : WholeLineBUC) (n : ℕ) :
    WholeLineBUCTrajectory (wholeLineCauchyGlobalSegmentTime p u₀) :=
  wholeLineCauchyBUCMildFixedPoint p
    (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalDatum p u₀ n)
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)

/-- Any datum in the original stable box generates one physical canonical
segment which stays in both the clamp box and the sharper stable box. -/
theorem wholeLineCauchyCanonicalSegment_bounds_of_datum
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ w : WholeLineBUC)
    (hw0 : ∀ x, 0 ≤ w.1 x)
    (hwC : ∀ x, w.1 x ≤ wholeLineCauchyStableCeiling p u₀) :
    let U := wholeLineCauchyBUCMildFixedPoint p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le w
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    (∀ z x, (U z).1 x ∈ Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalClamp p u₀)) ∧
    (∀ z x, (U z).1 x ≤ wholeLineCauchyStableCeiling p u₀) := by
  dsimp only
  let C := wholeLineCauchyStableCeiling p u₀
  let M := wholeLineCauchyGlobalClamp p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let U : WholeLineBUCTrajectory H :=
    wholeLineCauchyBUCMildFixedPoint p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le w
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
  have hC0 : 0 ≤ C :=
    (wholeLineCauchyStableCeiling_one_le hregime u₀).trans' zero_le_one
  have hwnorm : ‖w‖ ≤ C := by
    change ‖w.1‖ ≤ C
    apply (BoundedContinuousFunction.norm_le hC0).2
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
    exact hwC x
  have hupper : ∀ z : Set.Icc (0 : ℝ) H, ∀ x, (U z).1 x ≤ M := by
    intro z x
    let Q : WholeLineBUC := wholeLineCauchyHeatBUCTotal z.1 w
    have hdist : dist (U z) Q ≤
        wholeLineCauchyBUCMildDisplacement p M H := by
      simpa [U, M, H, Q] using
        wholeLineCauchyBUCMildFixedPoint_dist_homogeneous_le p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le w
          (wholeLineCauchyGlobalSegmentTime_rate p u₀) z
    have hpoint : |(U z).1 x - Q.1 x| ≤
        wholeLineCauchyBUCMildDisplacement p M H :=
      (WholeLineBUC.pointwise_abs_sub_le_dist (U z) Q x).trans hdist
    have hQnorm : ‖Q‖ ≤ ‖w‖ :=
      wholeLineCauchyHeatBUCTotal_norm_le_of_nonneg z.2.1 w
    exact (show (U z).1 x < M from by
      calc
        (U z).1 x ≤ Q.1 x + |(U z).1 x - Q.1 x| := by
          linarith [le_abs_self ((U z).1 x - Q.1 x)]
        _ ≤ ‖Q‖ + wholeLineCauchyBUCMildDisplacement p M H :=
          add_le_add (WholeLineBUC.apply_le_norm Q x) hpoint
        _ ≤ C + wholeLineCauchyBUCMildDisplacement p M H :=
          add_le_add (hQnorm.trans hwnorm) le_rfl
        _ < C + 1 := by
          simpa [M, H] using
            add_lt_add_left
              (wholeLineCauchyGlobalSegmentTime_displacement p u₀) C
        _ = M := by rfl).le
  have hnonneg : ∀ z : Set.Icc (0 : ℝ) H, ∀ x, 0 ≤ (U z).1 x := by
    intro z x
    simpa [U, M, H] using wholeLineCauchyBUCMildFixedPoint_nonnegative
      p (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀) w hw0
      (wholeLineCauchyGlobalSegmentTime_rate p u₀) z x
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M := fun z x => ⟨hnonneg z x, hupper z x⟩
  refine ⟨hstrip, ?_⟩
  intro z x
  have hclosed := wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
    p hregime (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀) w
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    (by simpa [U, M, H] using hstrip)
    (wholeLineCauchyStableCeiling_one_le hregime u₀)
    (wholeLineCauchyStableCeiling_margin hregime u₀) hwC
  have hext := wholeLineBUCTrajectoryExtend_eq
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le U z.2
  simpa [U, M, H, hext] using hclosed z.1 z.2 x

/-- Every recursively generated datum and segment remains in the same stable
box. -/
theorem wholeLineCauchyGlobalDatum_segment_bounds
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    ∀ n,
      ((∀ x, 0 ≤ (wholeLineCauchyGlobalDatum p u₀ n).1 x) ∧
        (∀ x, (wholeLineCauchyGlobalDatum p u₀ n).1 x ≤
          wholeLineCauchyStableCeiling p u₀)) ∧
      ((∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀)) ∧
        (∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ≤
          wholeLineCauchyStableCeiling p u₀)) := by
  intro n
  induction n with
  | zero =>
      have hdatum :
          (∀ x, 0 ≤ (wholeLineCauchyGlobalDatum p u₀ 0).1 x) ∧
          (∀ x, (wholeLineCauchyGlobalDatum p u₀ 0).1 x ≤
            wholeLineCauchyStableCeiling p u₀) := by
        constructor
        · simpa [wholeLineCauchyGlobalDatum] using hu₀
        · intro x
          simpa [wholeLineCauchyGlobalDatum] using
            (wholeLineCauchyStableCeiling_initial_lt p u₀ x).le
      refine ⟨hdatum, ?_⟩
      simpa [wholeLineCauchyGlobalSegment] using
        wholeLineCauchyCanonicalSegment_bounds_of_datum
          p hregime u₀ (wholeLineCauchyGlobalDatum p u₀ 0)
          hdatum.1 hdatum.2
  | succ n ih =>
      let δ := wholeLineCauchyGlobalStep p u₀
      let zδ : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
        ⟨δ, (wholeLineCauchyGlobalStep_pos p u₀).le,
          by dsimp [δ, wholeLineCauchyGlobalStep];
             linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]⟩
      have hdatum :
          (∀ x, 0 ≤ (wholeLineCauchyGlobalDatum p u₀ (n + 1)).1 x) ∧
          (∀ x, (wholeLineCauchyGlobalDatum p u₀ (n + 1)).1 x ≤
            wholeLineCauchyStableCeiling p u₀) := by
        constructor
        · intro x
          simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
            zδ, δ] using (ih.2.1 zδ x).1
        · intro x
          simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
            zδ, δ] using ih.2.2 zδ x
      refine ⟨by simpa [Nat.succ_eq_add_one] using hdatum, ?_⟩
      simpa [wholeLineCauchyGlobalSegment, Nat.succ_eq_add_one] using
        wholeLineCauchyCanonicalSegment_bounds_of_datum
          p hregime u₀ (wholeLineCauchyGlobalDatum p u₀ (n + 1))
          hdatum.1 hdatum.2

/-- Consecutive canonical segments agree on their common half-window. -/
theorem wholeLineCauchyGlobalSegment_overlap
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) (n : ℕ) :
    let H := wholeLineCauchyGlobalSegmentTime p u₀
    let δ := wholeLineCauchyGlobalStep p u₀
    wholeLineBUCTrajectoryShift
        (wholeLineCauchyGlobalStep_pos p u₀).le
        (wholeLineCauchyGlobalStep_pos p u₀).le
        (by dsimp [H, δ, wholeLineCauchyGlobalStep];
            linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀])
        (wholeLineCauchyGlobalSegment p u₀ n) =
      wholeLineBUCTrajectoryShift le_rfl
        (wholeLineCauchyGlobalStep_pos p u₀).le
        (by dsimp [H, δ, wholeLineCauchyGlobalStep];
            linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀])
        (wholeLineCauchyGlobalSegment p u₀ (n + 1)) := by
  dsimp only
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have hsum : δ + δ ≤ H := by
    dsimp [δ, H, wholeLineCauchyGlobalStep]
    linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]
  have hδH : δ ≤ H := by linarith [hδ, hsum]
  have hstripn : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x ∈
        Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    simpa [H] using
      (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.1
  have hold := wholeLineCauchyBUCMildFixedPoint_shift_eq
    p (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalDatum p u₀ n)
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    hδ hδ hsum (wholeLineCauchyGlobalStep_rate p u₀)
    (by simpa [wholeLineCauchyGlobalSegment, H] using hstripn)
  have hnew := wholeLineCauchyBUCMildFixedPoint_restrict_eq
    p (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalDatum p u₀ (n + 1))
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    hδ.le hδH (wholeLineCauchyGlobalStep_rate p u₀)
  have hdatum :
      wholeLineCauchyGlobalDatum p u₀ (n + 1) =
        wholeLineCauchyGlobalSegment p u₀ n
          ⟨δ, hδ.le, hδH⟩ := by
    simp [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment, δ, H]
  rw [hdatum] at hnew
  exact hold.trans hnew.symm

section WholeLineCauchyCanonicalSegmentsAxiomAudit

#print axioms wholeLineCauchyBUCMildRate_mono
#print axioms wholeLineCauchyCanonicalSegment_bounds_of_datum
#print axioms wholeLineCauchyGlobalDatum_segment_bounds
#print axioms wholeLineCauchyGlobalSegment_overlap

end WholeLineCauchyCanonicalSegmentsAxiomAudit

end ShenWork.Paper1
