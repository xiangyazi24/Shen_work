/-
  Limit passage for the truncated positive-time gradient bootstrap.

  A common derivative envelope for every Picard iterate on one positive-time
  window gives a common spatial Lipschitz envelope at each time in the window.
  Pointwise convergence of the Picard iterates then passes that inequality to
  the truncated Picard limit.  No convergence of derivatives is needed.
-/

import ShenWork.Paper2.IntervalTruncatedGradientWindow

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (HasJointMeasurability)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedConjugatePicardIter
   truncatedConjugatePicardIter_ball
   truncatedConjugatePicardIter_geometric
   truncatedConjugatePicardLimit
   truncatedConjugatePicardIter_pointwise_convergent
   TruncatedConjugateMildExistenceData)
open ShenWork.Paper2.TruncatedGradientWindow

private theorem lift_continuousOn_Icc_of_continuous
    {g : intervalDomainPoint → ℝ} (hg : Continuous g) :
    ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hres : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift g) = g := by
    funext z
    obtain ⟨z, hz⟩ := z
    show intervalDomainLift g z = g ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [hres]
  exact hg

/-- A uniform iterate gradient bound on a window passes to a spatial
Lipschitz bound for the truncated Picard limit at every time in that window. -/
theorem truncatedPicardLimit_lipschitzOn_of_window_grad
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {lo hi t G : ℝ}
    (ht : 0 < t) (htT : t ≤ DT.T)
    (htlo : lo ≤ t) (hthi : t ≤ hi) (hG : 0 ≤ G)
    (hgrad : ∀ n : ℕ,
      IterGradOnWindow
        (fun n s => truncatedConjugatePicardIter p u₀ n s) lo hi n G) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |intervalDomainLift
          ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
        intervalDomainLift
          ((truncatedConjugatePicardLimit p u₀ DT.T) t) y|
        ≤ G * |x - y| := by
  have hiter_lip : ∀ n : ℕ,
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        |intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) x -
          intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) y|
          ≤ G * |x - y| := by
    intro n x hx y hy
    have hgt := hgrad n t htlo hthi
    let f : ℝ → ℝ :=
      intervalDomainLift (truncatedConjugatePicardIter p u₀ n t)
    have hda : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ f z := by
      intro z hz
      simpa [f] using hgt.2 z hz
    have hlip_open : LipschitzOnWith ⟨G, hG⟩ f (Set.Ioo (0 : ℝ) 1) :=
      Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (convex_Ioo (0 : ℝ) 1)
        (fun z hz => (hda z hz).hasDerivAt.hasDerivWithinAt)
        (fun z _ => by exact_mod_cast (hgt.1 z))
    have hcont_n : Continuous (truncatedConjugatePicardIter p u₀ n t) :=
      (truncatedConjugatePicardIter_ball p u₀ DT.hbase_ball DT.hbase_cont
        DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved n).2
        t ht htT
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
      simpa [f] using lift_continuousOn_Icc_of_continuous hcont_n
    have hlip_closed : LipschitzOnWith ⟨G, hG⟩ f (Set.Icc (0 : ℝ) 1) := by
      rw [← closure_Ioo (zero_ne_one' ℝ)]
      exact hlip_open.closure (by
        simpa [closure_Ioo (zero_ne_one' ℝ)] using hcont)
    have hdist := hlip_closed.dist_le_mul x hx y hy
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_mk] at hdist
  intro x hx y hy
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ DT.hbase_ball DT.hbase_cont
      DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates : ∀ n,
      HasJointMeasurability (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact DT.hbase_meas
    | succ n ih => exact DT.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ DT.hK_nn hball
    hcont_iterates hmeas_iterates DT.hcontr DT.hC₀ DT.hbase_diff
  have hconv := truncatedConjugatePicardIter_pointwise_convergent
    p u₀ DT.hK DT.hK_nn DT.hC₀ (fun n => hgeom n) t ht htT
  have hlim_x : Filter.Tendsto
      (fun n => intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) x)
      Filter.atTop (nhds (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x)) := by
    unfold intervalDomainLift truncatedConjugatePicardLimit
    simp only [dif_pos hx, ht, htT, and_self, ite_true]
    exact tendsto_nhds_limUnder (hconv ⟨x, hx⟩)
  have hlim_y : Filter.Tendsto
      (fun n => intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) y)
      Filter.atTop (nhds (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) y)) := by
    unfold intervalDomainLift truncatedConjugatePicardLimit
    simp only [dif_pos hy, ht, htT, and_self, ite_true]
    exact tendsto_nhds_limUnder (hconv ⟨y, hy⟩)
  have hlim_diff : Filter.Tendsto
      (fun n => |intervalDomainLift
          (truncatedConjugatePicardIter p u₀ n t) x -
        intervalDomainLift
          (truncatedConjugatePicardIter p u₀ n t) y|)
      Filter.atTop (nhds (|intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
        intervalDomainLift
          ((truncatedConjugatePicardLimit p u₀ DT.T) t) y|)) :=
    (hlim_x.sub hlim_y).abs
  exact le_of_tendsto hlim_diff
    (Filter.Eventually.of_forall (fun n => hiter_lip n x hx y hy))

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
