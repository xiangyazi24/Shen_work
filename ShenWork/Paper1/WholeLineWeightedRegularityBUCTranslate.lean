import ShenWork.Paper1.WholeLineWeightedRegularityMild

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1


def wholeLineBUCTranslate (a : ℝ) (u : WholeLineBUC) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (fun x => u.1 (x + a))
    (u.2.comp (uniformContinuous_id.add uniformContinuous_const))
    ‖u‖ (fun x => WholeLineBUC.abs_apply_le_norm u (x + a))

@[simp] theorem wholeLineBUCTranslate_apply
    (a : ℝ) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineBUCTranslate a u).1 x = u.1 (x + a) := rfl

theorem wholeLineBUCTranslate_continuous (u : WholeLineBUC) :
    Continuous (fun a : ℝ => wholeLineBUCTranslate a u) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [Metric.continuousAt_iff]
  intro eps heps
  have hu : UniformContinuous (u.1 : ℝ → ℝ) := u.2
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨delta, hdelta, hmod⟩ := hu (eps / 2) (by linarith)
  refine ⟨delta, hdelta, ?_⟩
  intro b hab
  have hle : dist (wholeLineBUCTranslate b u).1
      (wholeLineBUCTranslate a u).1 ≤ eps / 2 := by
    rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
    intro x
    change dist (u.1 (x + b)) (u.1 (x + a)) ≤ eps / 2
    exact (hmod (by simpa [Real.dist_eq] using hab)).le
  exact hle.trans_lt (by linarith)

def wholeLineBUCTranslateTrajectory
    {T : ℝ} (_hT : 0 ≤ T) (c : ℝ) (u : WholeLineBUC) :
    WholeLineBUCTrajectory T :=
  ⟨fun z => wholeLineBUCTranslate (-c * z.1) u,
    (wholeLineBUCTranslate_continuous u).comp (by fun_prop)⟩

@[simp] theorem wholeLineBUCTranslateTrajectory_apply
    {T : ℝ} (hT : 0 ≤ T) (c : ℝ) (u : WholeLineBUC)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineBUCTranslateTrajectory hT c u z).1 x =
      u.1 (x - c * z.1) := by
  simp [wholeLineBUCTranslateTrajectory]
  congr 1

#print axioms wholeLineBUCTranslate_continuous
#print axioms wholeLineBUCTranslateTrajectory_apply

end ShenWork.Paper1
