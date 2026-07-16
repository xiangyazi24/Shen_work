import ShenWork.Paper1.Theorem12Step4EnergyProducer
import ShenWork.Paper1.WholeLineWeightedRegularityBoundedDriftRestart
import ShenWork.Paper1.WholeLineWeightedRegularitySlice

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Co-moving PDE for the canonical global Cauchy solution

The glued global orbit is locally one preferred canonical fixed-point
segment at every positive time.  This file transports the segment's full
space-time derivative through that local identification and records the
exact paper-wave operator seen in a co-moving frame.
-/

/-- The canonical glued population has the full space-time derivative at
every positive time.  This is stronger than the separate differentiability
stored by `IsGlobalClassicalSolution` and is the chain-rule input needed for
moving barriers. -/
theorem wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t x : ℝ} (ht : 0 < t) :
    HasFDerivAt
      (fun q : ℝ × ℝ => wholeLineCauchyGlobalU p u₀ q.1 q.2)
      (deriv (fun s => wholeLineCauchyGlobalU p u₀ s x) t •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (wholeLineCauchyGlobalU p u₀ t) x •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, x) := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let a : ℝ := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
  let r : ℝ := t - a
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let Traj := wholeLineCauchyGlobalSegment p u₀ n
  let e : ℝ → ℝ → ℝ := fun s y =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 y
  have hr0 : 0 < r := by
    simpa [r, a, n, wholeLineCauchyGlobalLocalTime] using
      wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hrH : r < H := by
    simpa [r, a, n, H, wholeLineCauchyGlobalLocalTime] using
      wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le
  let zr : Set.Icc (0 : ℝ) H := ⟨r, hr0.le, hrH.le⟩
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ y,
      (Traj z).1 y ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    simpa [Traj, H] using
      (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.1
  have hlocal :=
    wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive
      p (M := wholeLineCauchyGlobalClamp p u₀) (T := H)
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalDatum p u₀ n)
      (wholeLineCauchyGlobalSegmentTime_rate p u₀) zr hr0 hrH
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa [Traj, H] using hstrip) x
  have hmap : HasFDerivAt (fun q : ℝ × ℝ => (q.1 - a, q.2))
      (ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) (t, x) := by
    have hfstMap : HasFDerivAt (fun q : ℝ × ℝ => q.1 - a)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (t, x) :=
      (hasFDerivAt_fst (p := (t, x))).sub_const a
    have hsndMap : HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (t, x) :=
      hasFDerivAt_snd
    exact hfstMap.prodMk hsndMap
  have htranslated : HasFDerivAt
      (fun q : ℝ × ℝ => e (q.1 - a) q.2)
      (deriv (fun s => e s x) r • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (e r) x • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, x) := by
    have hc := hlocal.comp (t, x) hmap
    simpa [e, Traj, H, zr, r, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] using hc
  have hevBUC := wholeLineCauchyGlobalBUC_eventuallyEq_preferred
    p hregime u₀ hu₀ ht
  have hev :
      (fun q : ℝ × ℝ => wholeLineCauchyGlobalU p u₀ q.1 q.2) =ᶠ[nhds (t, x)]
        fun q => e (q.1 - a) q.2 := by
    have hfst : Tendsto (fun q : ℝ × ℝ => q.1) (nhds (t, x)) (nhds t) :=
      continuousAt_fst
    filter_upwards [hfst.eventually hevBUC] with q hq
    exact congrArg (fun w : WholeLineBUC => w.1 q.2) hq
  have heqSlice : wholeLineCauchyGlobalU p u₀ t = e r := by
    funext y
    have hy := congrArg (fun w : WholeLineBUC => w.1 y) hevBUC.self_of_nhds
    simpa [e, Traj, H, n, a, r, wholeLineCauchyGlobalU] using hy
  have heqTime : deriv (fun s => wholeLineCauchyGlobalU p u₀ s x) t =
      deriv (fun s => e s x) r := by
    have hx := (wholeLineCauchyGlobalU_eventuallyEq_segment
      p hregime u₀ hu₀ ht x).deriv_eq
    simpa [n, a, r, e, Traj, H] using hx.trans
      (deriv_comp_sub_const (fun s => e s x) a t)
  rw [heqTime, heqSlice]
  exact htranslated.congr_of_eventuallyEq hev

/-- In a frame moving at speed `c`, the canonical global population solves
the diagonal paper-wave parabolic equation at every positive time. -/
theorem wholeLineCauchyGlobal_coMovingPath_hasDerivAt_paperWaveOperator
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt
      (fun s => coMovingPath c (wholeLineCauchyGlobalU p u₀) s x)
      (paperWaveOperator p c
        (coMovingPath c (wholeLineCauchyGlobalU p u₀) t)
        (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) x) t := by
  let u := wholeLineCauchyGlobalU p u₀
  let v := wholeLineCauchyGlobalV p u₀
  let q := coMovingPath c u t
  have hjoint := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
    p hregime u₀ hu₀ ht (x := x + c * t)
  have hpath : HasDerivAt (fun s => coMovingPath c u s x)
      (paper5CoMovingMaterialTime c u t x) t := by
    exact paper5CoMovingPath_hasDerivAt_of_joint (c := c) (t := t)
      (x := x) (u := u) (by simpa [u] using hjoint)
  have hclass : IsClassicalSolution p (t + 1) u v :=
    wholeLineCauchyGlobal_isGlobalClassicalSolution
      p hregime u₀ hu₀ (t + 1) (by linarith)
  have hmaterial := paper5CoMovingMaterialPDE_of_classical
    p (T := t + 1) (c := c) (t := t) (x := x)
      (u := u) (v := v) hclass ht (by linarith)
  have hv : coMovingPath c v t = frozenElliptic p q := by
    simpa [u, v, q] using wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
      p hregime u₀ hu₀ c ht.le
  have hmaterialFrozen : paper5CoMovingMaterialTime c u t x =
      frozenWaveOperator p c q q x := by
    rw [hv] at hmaterial
    simpa [frozenWaveOperator, q] using hmaterial
  have hqcb : IsCUnifBdd q := by
    simpa [q, u] using wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd
      p u₀ c t
  have hq0 : ∀ y, 0 ≤ q y := by
    intro y
    exact wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ ht.le
      (y + c * t)
  have hq2 : ContDiff ℝ 2 q := by
    simpa [q, u] using wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hregime u₀ hu₀ (c := c) ht
  have hqdiff : DifferentiableAt ℝ q x :=
    (hq2.differentiable (by norm_num)).differentiableAt
  have hVdiff : DifferentiableAt ℝ (deriv (frozenElliptic p q)) x :=
    frozenElliptic_deriv_differentiableAt p hqcb hq0 x
  have hqpow : DifferentiableAt ℝ (fun y => (q y) ^ p.m) x :=
    (hqdiff.hasDerivAt.rpow_const (Or.inr p.hm)).differentiableAt
  have hpaper : paperWaveOperator p c q q x = frozenWaveOperator p c q q x :=
    paperWaveOperator_eq_frozenWaveOperator_at_fixed_point
      p x hqcb hq0 hqdiff hVdiff hqpow
  convert hpath using 1
  rw [hmaterialFrozen, ← hpaper]

/-- Restarted form used by a dynamic plateau comparison.  The reference
time `t₀` may be zero; only the physical time `t₀+t` must be positive. -/
theorem wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c t₀ : ℝ) {t : ℝ} (ht : 0 < t₀ + t) (x : ℝ) :
    let q : ℝ → ℝ → ℝ := fun s y =>
      wholeLineCauchyGlobalU p u₀ (t₀ + s) (y + c * (t₀ + s))
    HasDerivAt (fun s => q s x)
      (paperWaveOperator p c (q t) (q t) x) t := by
  dsimp only
  have hraw := wholeLineCauchyGlobal_coMovingPath_hasDerivAt_paperWaveOperator
    p hregime u₀ hu₀ c ht x
  have hshift : HasDerivAt (fun s : ℝ => t₀ + s) 1 t := by
    simpa [add_comm] using (hasDerivAt_id t).const_add t₀
  have hc := hraw.comp t hshift
  simpa [coMovingPath] using hc

#print axioms wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
#print axioms wholeLineCauchyGlobal_coMovingPath_hasDerivAt_paperWaveOperator
#print axioms wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator

end ShenWork.Paper1
