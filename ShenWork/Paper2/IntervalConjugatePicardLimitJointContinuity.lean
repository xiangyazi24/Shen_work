/-
  Joint positive-time continuity of the canonical conjugate Picard limit from
  joint continuity of the iterates.

  The geometric contraction estimate is uniform simultaneously in time and
  space.  Hence it gives uniform convergence of the lifted joint fields on
  `(0,T] × [0,1]`; continuity of the limit then follows from the standard
  uniform-limit theorem.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Topology Set
open scoped Topology

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardIter conjugatePicardLimit)

noncomputable section

namespace ShenWork.Paper2

/-- Lifted joint field of a conjugate Picard iterate. -/
def conjugatePicardIterJoint (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q ↦ intervalDomainLift (conjugatePicardIter p u₀ n q.1) q.2

/-- Lifted joint field of the canonical conjugate Picard limit. -/
def conjugatePicardLimitJoint (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ intervalDomainLift (conjugatePicardLimit p u₀ T q.1) q.2

/-- The geometric Picard tail estimate gives uniform convergence of the lifted
joint fields on the whole positive-time physical slab. -/
theorem conjugatePicardIter_tendstoUniformlyOn_joint_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |conjugatePicardIter p u₀ (n + 1) t x -
          conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    TendstoUniformlyOn
      (fun n ↦ conjugatePicardIterJoint p u₀ n)
      (conjugatePicardLimitJoint p u₀ T) atTop
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    ShenWork.IntervalConjugatePicard.conjugatePicardIter_uniform_convergence
      p u₀ hT hK hK_nn hC₀ hbound ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn q hq
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  have htail := hN n hn q.1 ht.1 ht.2 ⟨q.2, hx⟩
  simpa [conjugatePicardIterJoint, conjugatePicardLimitJoint,
    intervalDomainLift, hx, Real.dist_eq, abs_sub_comm] using htail

/-- Uniform convergence plus joint continuity of every iterate gives joint
continuity of the canonical conjugate Picard limit on `(0,T] × [0,1]`. -/
theorem conjugatePicardLimit_jointContinuousOn_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |conjugatePicardIter p u₀ (n + 1) t x -
          conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hiter_joint : ∀ n,
      ContinuousOn (conjugatePicardIterJoint p u₀ n)
        (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (conjugatePicardLimitJoint p u₀ T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact
    (conjugatePicardIter_tendstoUniformlyOn_joint_Ioc
      p u₀ hT hK hK_nn hC₀ hbound).continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hiter_joint))

/-- Existence-data wrapper: the contraction data internally supply the uniform
geometric tail estimate.  The remaining input is exactly joint continuity of
the concrete Picard iterates. -/
theorem conjugatePicardLimit_jointContinuousOn_Ioc_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hiter_joint : ∀ n,
      ContinuousOn (conjugatePicardIterJoint p u₀ n)
        (Set.Ioc (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (conjugatePicardLimitJoint p u₀ D.T)
      (Set.Ioc (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hball_cont := fun n ↦
    ShenWork.IntervalConjugatePicard.conjugatePicardIter_ball p u₀
      D.hbase_ball D.hbase_nonneg D.hbase_cont D.hmapsTo D.hmapsTo_nn
      D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n ↦ (hball_cont n).1
  have hball_nn := fun n ↦ (hball_cont n).2.1
  have hcont_iterates := fun n ↦ (hball_cont n).2.2
  have hmeas_iterates :
      ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom :=
    ShenWork.IntervalConjugatePicard.conjugatePicardIter_geometric p u₀
      D.hK_nn hball hball_nn hcont_iterates hmeas_iterates D.hcontr
      D.hC₀ D.hbase_diff
  exact conjugatePicardLimit_jointContinuousOn_Ioc p u₀
    D.hT D.hK D.hK_nn D.hC₀ (fun n ↦ hgeom n) hiter_joint

/-- Joint positive-time continuity yields continuity of every fixed spatial
time slice. -/
theorem conjugatePicardLimit_timeSlice_continuousOn_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ}
    (hjoint : ContinuousOn (conjugatePicardLimitJoint p u₀ T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (x : intervalDomainPoint) :
    ContinuousOn (fun s ↦ conjugatePicardLimit p u₀ T s x)
      (Set.Ioc (0 : ℝ) T) := by
  have hpair : ContinuousOn (fun s : ℝ ↦ ((s, x.1) : ℝ × ℝ))
      (Set.Ioc (0 : ℝ) T) :=
    continuousOn_id.prodMk continuousOn_const
  have hmaps : MapsTo (fun s : ℝ ↦ ((s, x.1) : ℝ × ℝ))
      (Set.Ioc (0 : ℝ) T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact Set.mem_prod.mpr ⟨hs, x.2⟩
  have hcomp := hjoint.comp hpair hmaps
  simpa [Function.comp_def, conjugatePicardLimitJoint,
    intervalDomainLift, x.2] using hcomp

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugatePicardIter_tendstoUniformlyOn_joint_Ioc
#print axioms ShenWork.Paper2.conjugatePicardLimit_jointContinuousOn_Ioc
#print axioms ShenWork.Paper2.conjugatePicardLimit_jointContinuousOn_Ioc_of_data
