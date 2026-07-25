import ShenWork.Paper1.WholeLineChiPosWeightedEntropyOrbit

open Filter MeasureTheory Real Set Topology
open scoped Interval

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

/-!
# Time derivative of the canonical weighted entropy

The finite-window weighted entropy is differentiated literally along the
canonical co-moving orbit.  The domination comes from the preferred local
fixed-point chart and its uniform positive-window bounds.
-/

private theorem wholeLineCauchyGlobalCoMovingUt_locally_bounded
    (p : CMParams) (u₀ : WholeLineBUC)
    (hregime : WholeLineCauchyCeilingRegime p)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
      ∀ s ∈ Metric.ball t δ, ∀ x,
        |wholeLineCauchyGlobalCoMovingUt p u₀ c s x| ≤ B := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let base : ℝ := (n : ℝ) * wholeLineCauchyGlobalStep p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let datum := wholeLineCauchyGlobalDatum p u₀ n
  let Traj := wholeLineCauchyGlobalSegment p u₀ n
  let e : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
  let left : ℝ := q / 2
  let right : ℝ := (q + H) / 2
  have hq0 : 0 < q := by
    simpa [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hqH : q < H := by
    simpa [q, H] using
      wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le
  have hleft : 0 < left := by dsimp [left]; positivity
  have hlr : left ≤ right := by dsimp [left, right]; linarith
  have hrightH : right < H := by dsimp [right]; linarith
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ)
        (wholeLineCauchyGlobalClamp p u₀) := by
    simpa [Traj, H] using
      (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.1
  have hstripWindow : ∀ s ∈ Set.Icc left right, ∀ x,
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    intro s hs x
    let z : Set.Icc (0 : ℝ) H :=
      ⟨s, hleft.le.trans hs.1, hs.2.trans hrightH.le⟩
    rw [wholeLineBUCTrajectoryExtend_eq
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj z.2]
    exact hstrip z x
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
      p (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le hleft hlr
      hrightH.le datum (wholeLineCauchyGlobalSegmentTime_rate p u₀)
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa [Traj, H, datum] using hstripWindow) with
    ⟨Bx, hBx, hxBound⟩
  rcases wholeLineCauchyBUCMildFixedPoint_time_deriv_bounded_positive_window
      p (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le hleft hlr
      hrightH datum (wholeLineCauchyGlobalSegmentTime_rate p u₀)
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa [Traj, H, datum] using hstrip) with
    ⟨Bt, hBt, htBound⟩
  have hev := wholeLineCauchyGlobalBUC_eventuallyEq_preferred
    p hregime u₀ hu₀ ht
  rcases Metric.mem_nhds_iff.1 hev with ⟨eps, heps, hepsEq⟩
  let δ := min (eps / 2) (min (q / 2) ((H - q) / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos heps)
      (lt_min (half_pos hq0) (half_pos (sub_pos.mpr hqH)))
  refine ⟨δ, Bt + |c| * Bx, hδ, by positivity, ?_⟩
  intro s hs x
  have hst : |s - t| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hs
  have hlocal : s - base ∈ Set.Icc left right := by
    have hbase : q = t - base := by
      simp [q, base, n, wholeLineCauchyGlobalLocalTime]
    constructor
    · have hδq : δ ≤ q / 2 :=
        (min_le_right _ _).trans (min_le_left _ _)
      dsimp [left]
      rw [hbase]
      linarith [neg_abs_le (s - t)]
    · have hδH : δ ≤ (H - q) / 2 :=
        (min_le_right _ _).trans (min_le_right _ _)
      dsimp [right]
      rw [hbase]
      linarith [le_abs_self (s - t)]
  have hs_eps : dist s t < eps / 2 := by
    rw [Real.dist_eq]
    exact hst.trans_le (min_le_left _ _)
  let localPath : ℝ → ℝ := fun r => e (r - base) (x + c * r)
  have heq :
      (fun r => coMovingPath c (wholeLineCauchyGlobalU p u₀) r x)
        =ᶠ[nhds s] localPath := by
    filter_upwards [Metric.ball_mem_nhds s (half_pos heps)] with r hr
    have hrt : dist r t < eps := by
      calc
        dist r t ≤ dist r s + dist s t := dist_triangle _ _ _
        _ < eps / 2 + eps / 2 := add_lt_add
          (by simpa using hr) hs_eps
        _ = eps := by ring
    have hBUC := hepsEq hrt
    have hx := congrArg (fun f : WholeLineBUC => f.1 (x + c * r)) hBUC
    simpa [localPath, e, Traj, base, n, coMovingPath] using hx
  let z : Set.Icc (0 : ℝ) H :=
    ⟨s - base, hleft.le.trans hlocal.1,
      hlocal.2.trans hrightH.le⟩
  have hz0 : 0 < z.1 := hleft.trans_le hlocal.1
  have hzH : z.1 < H := hlocal.2.trans_lt hrightH
  have hjoint := wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive
    p (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
    (wholeLineCauchyGlobalSegmentTime_rate p u₀) z hz0 hzH
    (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simpa [Traj, H, datum] using hstrip)
    (x + c * s)
  have hpoint : x + c * base + c * z.1 = x + c * s := by
    dsimp [z]
    ring
  have hmove := paper5CoMovingPath_hasDerivAt_of_joint
    (c := c) (t := z.1) (x := x + c * base) (u := e) (by
      rw [hpoint]
      simpa [e, Traj, z, base] using hjoint)
  have hshift : HasDerivAt (fun r : ℝ => r - base) 1 s := by
    simpa using (hasDerivAt_id s).sub_const base
  have hlocalDeriv : HasDerivAt localPath
      (paper5CoMovingMaterialTime c e z.1 (x + c * base)) s := by
    have hcomp := hmove.comp s hshift
    have hfun :
        (fun r => coMovingPath c e (r - base) (x + c * base)) =
          localPath := by
      funext r
      simp only [coMovingPath, localPath]
      congr 1
      ring
    change HasDerivAt
      (fun r => coMovingPath c e (r - base) (x + c * base))
      (paper5CoMovingMaterialTime c e z.1 (x + c * base) * 1) s at hcomp
    rw [hfun] at hcomp
    simpa using hcomp
  have hderivEq := heq.deriv_eq
  change |deriv
    (fun r => coMovingPath c (wholeLineCauchyGlobalU p u₀) r x) s| ≤ _
  rw [hderivEq, hlocalDeriv.deriv]
  have htB := htBound z.1 (by simpa [z] using hlocal) (x + c * s)
  have hxB := hxBound z.1 (by simpa [z] using hlocal) (x + c * s)
  unfold paper5CoMovingMaterialTime coMovingPath
  rw [deriv_comp_add_const]
  calc
    |deriv (fun r => e r (x + c * base + c * z.1)) z.1 +
        c * deriv (e z.1) (x + c * base + c * z.1)| ≤
        |deriv (fun r => e r (x + c * s)) z.1| +
          |c| * |deriv (e z.1) (x + c * s)| := by
      rw [hpoint]
      calc
        |deriv (fun r => e r (x + c * s)) z.1 +
            c * deriv (e z.1) (x + c * s)| ≤
            |deriv (fun r => e r (x + c * s)) z.1| +
              |c * deriv (e z.1) (x + c * s)| := abs_add_le _ _
        _ = |deriv (fun r => e r (x + c * s)) z.1| +
              |c| * |deriv (e z.1) (x + c * s)| := by rw [abs_mul]
    _ ≤ Bt + |c| * Bx := by
      exact add_le_add (by simpa [e, Traj, z] using htB)
        (mul_le_mul_of_nonneg_left
          (by simpa [e, Traj, z] using hxB) (abs_nonneg c))

/-- The weighted relative entropy on a finite spatial interval has the
literal time derivative represented by the entropy production integrand. -/
theorem wholeLineCauchyGlobalU_weighted_entropy_hasDerivAt
    (p : CMParams) (u₀ : WholeLineBUC)
    (hregime : WholeLineCauchyCeilingRegime p)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x) (hleft : StrictlyPositiveAtLeft u₀.1)
    (hp : p.m = 1 ∧ p.γ = 1 ∧ p.α = 1)
    (a b c ell : ℝ) (w w' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hw_pos : ∀ x, 0 < w x)
    (hw_deriv : ∀ x, HasDerivAt w (w' x) x)
    (hw'_cont : Continuous w')
    (hw_slow : ∀ x, |w' x| ≤ (1 / ell) * w x)
    (hab : a ≤ b) (hell : 0 < ell) :
    HasDerivAt
      (fun s => ∫ x in a..b,
        w x * chiOneRelativeEntropy
          (wholeLineCauchyGlobalCoMovingU p u₀ c s x))
      (∫ x in a..b,
        w x * chiOneEntropyMultiplier
          (wholeLineCauchyGlobalCoMovingU p u₀ c t x) *
            wholeLineCauchyGlobalCoMovingUt p u₀ c t x) t := by
  rcases wholeLineCauchyGlobalCoMovingUt_locally_bounded
      p u₀ hregime hu₀ c ht with ⟨δ₀, B, hδ₀, hB, hUt⟩
  let δ := min δ₀ (t / 2)
  have hδ : 0 < δ := lt_min hδ₀ (half_pos ht)
  have hδt : δ ≤ t / 2 := min_le_right _ _
  have htimePos : ∀ s ∈ Metric.ball t δ, 0 < s := by
    intro s hs
    have hsabs : |s - t| < δ := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hs
    linarith [neg_abs_le (s - t)]
  let K : Set (ℝ × ℝ) :=
    Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc a b
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hUcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        wholeLineCauchyGlobalCoMovingU p u₀ c q.1 q.2) K := by
    intro q hq
    have hqtime : 0 < q.1 := by
      have : t - δ ≤ q.1 := hq.1.1
      linarith
    have hjoint := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hregime u₀ hu₀ hqtime (x := q.2 + c * q.1)
    have hmap : DifferentiableAt ℝ
        (fun r : ℝ × ℝ => (r.1, r.2 + c * r.1)) q := by
      fun_prop
    simpa [wholeLineCauchyGlobalCoMovingU, coMovingPath] using
      (hjoint.differentiableAt.comp q hmap).continuousAt.continuousWithinAt
  have hUne : ∀ q ∈ K,
      wholeLineCauchyGlobalCoMovingU p u₀ c q.1 q.2 ≠ 0 := by
    intro q hq
    have hqtime : 0 < q.1 := by
      have : t - δ ≤ q.1 := hq.1.1
      linarith
    have hpos :
        0 < wholeLineCauchyGlobalCoMovingU p u₀ c q.1 q.2 := by
      simpa [wholeLineCauchyGlobalCoMovingU, coMovingPath] using
        wholeLineCauchyGlobal_pos_of_posAtBot
          p hregime u₀ hu₀ hleft hqtime (q.2 + c * q.1)
    exact hpos.ne'
  have hwcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hw_deriv x).continuousAt
  let factor : ℝ × ℝ → ℝ := fun q =>
    |w q.2| *
      (1 + |(wholeLineCauchyGlobalCoMovingU p u₀ c q.1 q.2)⁻¹|)
  have hfactor : ContinuousOn factor K := by
    dsimp only [factor]
    exact (hwcont.comp continuous_snd).abs.continuousOn.mul
      (continuousOn_const.add (hUcont.inv₀ hUne).abs)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hfactor
  let F : ℝ → ℝ → ℝ := fun s x =>
    w x * chiOneRelativeEntropy
      (wholeLineCauchyGlobalCoMovingU p u₀ c s x)
  let F' : ℝ → ℝ → ℝ := fun s x =>
    w x * chiOneEntropyMultiplier
      (wholeLineCauchyGlobalCoMovingU p u₀ c s x) *
        wholeLineCauchyGlobalCoMovingUt p u₀ c s x
  have hFmeas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable (F s) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hspos := htimePos s hs
    have hucont : Continuous
        (wholeLineCauchyGlobalCoMovingU p u₀ c s) :=
      (wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
        p hregime u₀ hu₀ (c := c) hspos).continuous
    have hent : Continuous (fun x => chiOneRelativeEntropy
        (wholeLineCauchyGlobalCoMovingU p u₀ c s x)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hpos :
          0 < wholeLineCauchyGlobalCoMovingU p u₀ c s x := by
        simpa [wholeLineCauchyGlobalCoMovingU, coMovingPath] using
          wholeLineCauchyGlobal_pos_of_posAtBot p hregime u₀ hu₀ hleft
            hspos (x + c * s)
      exact (chiOneRelativeEntropy_hasDerivAt hpos.ne').continuousAt.comp
        hucont.continuousAt
    exact (hwcont.mul hent).aestronglyMeasurable.restrict
  have hFint : IntervalIntegrable (F t) volume a b := by
    have hucont : Continuous
        (wholeLineCauchyGlobalCoMovingU p u₀ c t) :=
      (wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
        p hregime u₀ hu₀ (c := c) ht).continuous
    have hent : Continuous (fun x => chiOneRelativeEntropy
        (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hpos :
          0 < wholeLineCauchyGlobalCoMovingU p u₀ c t x := by
        simpa [wholeLineCauchyGlobalCoMovingU, coMovingPath] using
          wholeLineCauchyGlobal_pos_of_posAtBot p hregime u₀ hu₀ hleft
            ht (x + c * t)
      exact (chiOneRelativeEntropy_hasDerivAt hpos.ne').continuousAt.comp
        hucont.continuousAt
    simpa only [F] using (hwcont.mul hent).intervalIntegrable a b
  let d := wholeLineCauchyGlobalU_chiOneWeightedEntropySlice
    p u₀ hregime hu₀ hleft hp a b c ell w w' t ht hw_pos
      hw_deriv hw'_cont hw_slow hab hell
  have hmultCont : Continuous (fun x => chiOneEntropyMultiplier
      (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hu := d.u_deriv x
    exact (chiOneEntropyMultiplier_comp_hasDerivAt hu
      (d.u_pos x).ne').continuousAt
  have hF'meas : AEStronglyMeasurable (F' t)
      (volume.restrict (Set.uIoc a b)) := by
    exact ((hwcont.mul hmultCont).mul d.ut_continuous).aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      ∀ s ∈ Metric.ball t δ, ‖F' s x‖ ≤ |C| * B := by
    filter_upwards with x hx s hs
    have hsK : s ∈ Set.Icc (t - δ) (t + δ) := by
      have hsabs : |s - t| < δ := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hs
      constructor <;> linarith [neg_abs_le (s - t), le_abs_self (s - t)]
    have hxK : x ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hfac := hC (s, x) ⟨hsK, hxK⟩
    have hmult : |chiOneEntropyMultiplier
        (wholeLineCauchyGlobalCoMovingU p u₀ c s x)| ≤
        1 + |(wholeLineCauchyGlobalCoMovingU p u₀ c s x)⁻¹| := by
      unfold chiOneEntropyMultiplier
      simpa only [abs_one] using abs_sub (1 : ℝ)
        (wholeLineCauchyGlobalCoMovingU p u₀ c s x)⁻¹
    have hfac' : |w x| * (1 +
        |(wholeLineCauchyGlobalCoMovingU p u₀ c s x)⁻¹|) ≤ |C| := by
      have hfacC : |w x| * (1 +
          |(wholeLineCauchyGlobalCoMovingU p u₀ c s x)⁻¹|) ≤ C := by
        have hfactorC : factor (s, x) ≤ C :=
          (Real.le_norm_self (factor (s, x))).trans hfac
        simpa only [factor] using hfactorC
      exact hfacC.trans (le_abs_self C)
    have hUt' := hUt s
      (Metric.ball_subset_ball (min_le_left δ₀ (t / 2)) hs) x
    dsimp only [F']
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      |w x| * |chiOneEntropyMultiplier
          (wholeLineCauchyGlobalCoMovingU p u₀ c s x)| *
          |wholeLineCauchyGlobalCoMovingUt p u₀ c s x| ≤
          (|w x| * (1 +
            |(wholeLineCauchyGlobalCoMovingU p u₀ c s x)⁻¹|)) * B := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hmult (abs_nonneg (w x))) hUt'
          (abs_nonneg _) (by positivity)
      _ ≤ |C| * B := mul_le_mul_of_nonneg_right hfac' hB
  have hdiff : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      ∀ s ∈ Metric.ball t δ,
        HasDerivAt (fun q => F q x) (F' s x) s := by
    filter_upwards with x _hx s hs
    have hspos := htimePos s hs
    have huRaw := wholeLineCauchyGlobal_coMovingPath_hasDerivAt_paperWaveOperator
      p hregime u₀ hu₀ c hspos x
    have hu : HasDerivAt
        (fun q => wholeLineCauchyGlobalCoMovingU p u₀ c q x)
        (wholeLineCauchyGlobalCoMovingUt p u₀ c s x) s := by
      simpa [wholeLineCauchyGlobalCoMovingU,
        wholeLineCauchyGlobalCoMovingUt] using
          huRaw.differentiableAt.hasDerivAt
    have hchain := (chiOneRelativeEntropy_hasDerivAt
      ((wholeLineCauchyGlobal_pos_of_posAtBot p hregime u₀ hu₀ hleft
        hspos (x + c * s)).ne')).comp s hu
    have hconst : HasDerivAt (fun _q : ℝ => w x) 0 s :=
      hasDerivAt_const s _
    simpa only [F, F', zero_mul, zero_add, mul_assoc] using hconst.mul hchain
  have hraw :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := a) (b := b) (F := F) (F' := F')
      (x₀ := t) (s := Metric.ball t δ) (bound := fun _ => |C| * B)
      (Metric.ball_mem_nhds t hδ) hFmeas hFint hF'meas hbound
      intervalIntegrable_const hdiff).2
  simpa only [F, F'] using hraw

#print axioms wholeLineCauchyGlobalU_weighted_entropy_hasDerivAt

end ShenWork.Paper1
