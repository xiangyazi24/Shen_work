import ShenWork.Paper1.WholeLineWeightedRegularityRestart

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

def wholeLineTranslatedProfileBUC
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c t : ℝ) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (fun x => U (x - c * t))
    (hUunif.comp (by
      simpa only [id_eq] using
        (uniformContinuous_id.sub
          (uniformContinuous_const : UniformContinuous (fun _ : ℝ => c * t)))))
    M (fun x => hUM (x - c * t))

@[simp] theorem wholeLineTranslatedProfileBUC_apply
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c t x : ℝ) :
    (wholeLineTranslatedProfileBUC U hUunif M hUM c t).1 x =
      U (x - c * t) :=
  rfl

theorem wholeLineTranslatedProfileBUC_continuous
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c : ℝ) :
    Continuous (fun t : ℝ =>
      wholeLineTranslatedProfileBUC U hUunif M hUM c t) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuous_iff.mp hUunif (ε / 2) (half_pos hε)
  refine ⟨δ / (|c| + 1), div_pos hδ (by positivity), ?_⟩
  intro s hst
  have harg : ∀ x : ℝ,
      dist (x - c * s) (x - c * t) < δ := by
    intro x
    rw [Real.dist_eq, show (x - c * s) - (x - c * t) = c * (t - s) by ring,
      abs_mul]
    have hst' : |s - t| < δ / (|c| + 1) := by
      simpa [Real.dist_eq] using hst
    have hc_nonneg : 0 ≤ |c| := abs_nonneg c
    have hc_lt : |c| < |c| + 1 := by linarith
    have hmul_le : |c| * |s - t| ≤ (|c| + 1) * |s - t| :=
      mul_le_mul_of_nonneg_right hc_lt.le (abs_nonneg _)
    have hmul_lt : (|c| + 1) * |s - t| <
        (|c| + 1) * (δ / (|c| + 1)) :=
      mul_lt_mul_of_pos_left hst' (by positivity)
    have hmul : |c| * |s - t| < (|c| + 1) * (δ / (|c| + 1)) :=
      hmul_le.trans_lt hmul_lt
    rw [abs_sub_comm]
    rw [mul_div_cancel₀ δ (by positivity : |c| + 1 ≠ 0)] at hmul
    exact hmul
  change dist
      (wholeLineTranslatedProfileBUC U hUunif M hUM c s).1
      (wholeLineTranslatedProfileBUC U hUunif M hUM c t).1 < ε
  apply lt_of_le_of_lt (b := ε / 2)
  · rw [BoundedContinuousFunction.dist_le (half_pos hε).le]
    intro x
    change dist (U (x - c * s)) (U (x - c * t)) ≤ ε / 2
    exact (hmod (harg x)).le
  · linarith

def wholeLineTranslatedProfileTrajectory
    {T : ℝ} (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c : ℝ) :
    WholeLineBUCTrajectory T :=
  ⟨fun z => wholeLineTranslatedProfileBUC U hUunif M hUM c z.1,
    (wholeLineTranslatedProfileBUC_continuous U hUunif M hUM c).comp
      continuous_subtype_val⟩

@[simp] theorem wholeLineTranslatedProfileTrajectory_apply
    {T : ℝ} (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c : ℝ)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineTranslatedProfileTrajectory hT U hUunif M hUM c z).1 x =
      U (x - c * z.1) :=
  rfl

def wholeLineTranslatedProfileTrajectoryFrom
    {T : ℝ} (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c a : ℝ) :
    WholeLineBUCTrajectory T :=
  ⟨fun z => wholeLineTranslatedProfileBUC U hUunif M hUM c (a + z.1),
    (wholeLineTranslatedProfileBUC_continuous U hUunif M hUM c).comp
      (continuous_const.add continuous_subtype_val)⟩

@[simp] theorem wholeLineTranslatedProfileTrajectoryFrom_apply
    {T : ℝ} (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (M : ℝ) (hUM : ∀ x, |U x| ≤ M) (c a : ℝ)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M hUM c a z).1 x =
      U (x - c * (a + z.1)) :=
  rfl

theorem wholeLineTranslatedProfileTrajectoryFrom_mem_Icc
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (hUIcc : ∀ x, U x ∈ Set.Icc (0 : ℝ) M) (c a : ℝ)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M
      (fun y => by rw [abs_of_nonneg (hUIcc y).1]; exact (hUIcc y).2)
      c a z).1 x ∈ Set.Icc (0 : ℝ) M := by
  simpa using hUIcc (x - c * (a + z.1))

theorem wholeLineCauchyFluxSourceTrajectory_translatedProfile
    (p : CMParams) {M T s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (hUIcc : ∀ x, U x ∈ Set.Icc (0 : ℝ) M) (c a x : ℝ) :
    (wholeLineCauchyFluxSourceTrajectory p hM hT
      (wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M
        (fun y => by rw [abs_of_nonneg (hUIcc y).1]; exact (hUIcc y).2)
        c a) s).1 x =
      wholeLineChemotaxisFlux p U (x - c * (a + s)) := by
  let hUM : ∀ y, |U y| ≤ M := fun y => by
    rw [abs_of_nonneg (hUIcc y).1]
    exact (hUIcc y).2
  let W := wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M hUM c a
  have hext : wholeLineBUCTrajectoryExtend hT W s = W ⟨s, hs⟩ :=
    wholeLineBUCTrajectoryExtend_eq hT W hs
  rw [wholeLineCauchyFluxSourceTrajectory, hext,
    wholeLineCauchyTruncatedFluxBUC_apply]
  change wholeLineCauchyTruncatedFlux p M
      (fun y => U (y - c * (a + s))) x = _
  have hprofileIcc : ∀ y, U (y - c * (a + s)) ∈ Set.Icc (0 : ℝ) M :=
    fun y => hUIcc _
  rw [congrFun (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc
    p hM hprofileIcc) x]
  unfold wholeLineChemotaxisFlux
  have hUcb : IsCUnifBdd U :=
    WholeLineBUC.isCUnifBdd
      (wholeLineBUCOfUniformBound U hUunif M hUM)
  have hUnn : ∀ y, 0 ≤ U y := fun y => (hUIcc y).1
  have hshiftfun : (fun y => U (y - c * (a + s))) =
      fun y => U (y + (-c * (a + s))) := by
    funext y
    congr 1
    ring
  have hxshift : x - c * (a + s) = x + (-c * (a + s)) := by ring
  rw [hshiftfun, hxshift]
  rw [frozenElliptic_deriv_comp_add_const p hUcb hUnn
    (-c * (a + s)) x]

theorem wholeLineCauchyReactionSourceTrajectory_translatedProfile
    (p : CMParams) {M T s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (hUIcc : ∀ x, U x ∈ Set.Icc (0 : ℝ) M) (c a x : ℝ) :
    (wholeLineCauchyReactionSourceTrajectory p hM hT
      (wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M
        (fun y => by rw [abs_of_nonneg (hUIcc y).1]; exact (hUIcc y).2)
        c a) s).1 x =
      wholeLineCauchyShiftedReaction p U (x - c * (a + s)) := by
  let hUM : ∀ y, |U y| ≤ M := fun y => by
    rw [abs_of_nonneg (hUIcc y).1]
    exact (hUIcc y).2
  let W := wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M hUM c a
  have hext : wholeLineBUCTrajectoryExtend hT W s = W ⟨s, hs⟩ :=
    wholeLineBUCTrajectoryExtend_eq hT W hs
  rw [wholeLineCauchyReactionSourceTrajectory, hext,
    wholeLineCauchyTruncatedReactionBUC_apply]
  change wholeLineCauchyTruncatedReaction p M
      (fun y => U (y - c * (a + s))) x = _
  have hprofileIcc : ∀ y, U (y - c * (a + s)) ∈ Set.Icc (0 : ℝ) M :=
    fun y => hUIcc _
  rw [congrFun (wholeLineCauchyTruncatedReaction_eq_of_mem_Icc
    p hM hprofileIcc) x]
  rfl

theorem wholeLineTranslatedProfileTrajectoryFrom_isFixedPt
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hUunif : UniformContinuous U)
    (hUIcc : ∀ x, U x ∈ Set.Icc (0 : ℝ) M) (c a : ℝ)
    (hstationary : ∀ {t : ℝ}, 0 < t → ∀ x,
      U x = paper5MovingFrameHeatOp c t U x +
        (-p.χ) * (∫ r in (0 : ℝ)..t,
          paper5MovingFrameHeatGradOp c r
            (wholeLineChemotaxisFlux p U) x) +
        ∫ r in (0 : ℝ)..t,
          paper5MovingFrameHeatOp c r
            (wholeLineCauchyShiftedReaction p U) x) :
    let hUM : ∀ x, |U x| ≤ M := fun x => by
      rw [abs_of_nonneg (hUIcc x).1]
      exact (hUIcc x).2
    let u₀ := wholeLineTranslatedProfileBUC U hUunif M hUM c a
    let W := wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M hUM c a
    IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) W := by
  dsimp only
  let hUM : ∀ x, |U x| ≤ M := fun x => by
    rw [abs_of_nonneg (hUIcc x).1]
    exact (hUIcc x).2
  let u₀ := wholeLineTranslatedProfileBUC U hUunif M hUM c a
  let W := wholeLineTranslatedProfileTrajectoryFrom hT U hUunif M hUM c a
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  let r : ℝ := z.1
  by_cases hr0 : r = 0
  · subst r
    have hz0 : z = ⟨0, ⟨le_rfl, hT⟩⟩ := Subtype.ext hr0
    subst z
    simp [wholeLineCauchyBUCMildMap, wholeLineCauchyGradientDuhamelBUC,
      wholeLineCauchyValueDuhamelBUC, u₀, W]
  have hr : 0 < r := lt_of_le_of_ne z.2.1 (Ne.symm hr0)
  let x₀ : ℝ := x - c * (a + r)
  have hGint := wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
    p hM hT W hr.le
  have hRint := wholeLineCauchyValueBUCIntegrand_intervalIntegrable
    p hM hT W hr.le
  have hhom :
      (wholeLineCauchyHeatBUCTotal r u₀).1 x =
        paper5MovingFrameHeatOp c r U x₀ := by
    have htotal : wholeLineCauchyHeatBUCTotal r u₀ =
        wholeLineCauchyHeatBUC r hr u₀ := by
      simp [wholeLineCauchyHeatBUCTotal, hr]
    rw [htotal, wholeLineCauchyHeatBUC_apply]
    unfold paper5MovingFrameHeatOp
    have hshift := wholeLineCauchyHeatOp_eval_shift_eq_input_shift
      r (-c * a) U x
    have hinput : (fun y => U (y - c * a)) =
        fun y => U (y + (-c * a)) := by
      funext y
      congr 1
      ring
    change wholeLineCauchyHeatOp r (fun y => U (y - c * a)) x =
      wholeLineCauchyHeatOp r U (x₀ + c * r)
    rw [hinput, ← hshift]
    rw [show x + -c * a = x₀ + c * r by
      dsimp only [x₀, r]
      ring]
  have hGpoint : ∀ s ∈ Set.Ico (0 : ℝ) r,
      (wholeLineCauchyGradientBUCIntegrand p hM hT W r s).1 x =
        paper5MovingFrameHeatGradOp c (r - s)
          (wholeLineChemotaxisFlux p U) x₀ := by
    intro s hs
    have hlag : 0 < r - s := sub_pos.mpr hs.2
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1, hs.2.le.trans z.2.2⟩
    unfold wholeLineCauchyGradientBUCIntegrand
    have htotal : wholeLineCauchyHeatGradientBUCTotal (r - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT W s) =
        wholeLineCauchyHeatGradientBUC (r - s) hlag
          (wholeLineCauchyFluxSourceTrajectory p hM hT W s) := by
      simp [wholeLineCauchyHeatGradientBUCTotal, hlag]
    rw [htotal, wholeLineCauchyHeatGradientBUC_apply]
    unfold paper5MovingFrameHeatGradOp
    have hshift := wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
      (r - s) (-c * (a + s)) (wholeLineChemotaxisFlux p U) x
    have hsrc :
        (wholeLineCauchyFluxSourceTrajectory p hM hT W s).1 =
          fun y => wholeLineChemotaxisFlux p U (y + (-c * (a + s))) := by
      funext y
      rw [wholeLineCauchyFluxSourceTrajectory_translatedProfile
        p hM hT hsT U hUunif hUIcc c a y]
      congr 2
      ring
    rw [hsrc, ← hshift]
    rw [show x₀ + c * (r - s) = x - c * (a + s) by
      dsimp only [x₀, r]
      ring]
    rw [show x + -c * (a + s) = x - c * (a + s) by ring]
  have hRpoint : ∀ s ∈ Set.Ico (0 : ℝ) r,
      (wholeLineCauchyValueBUCIntegrand p hM hT W r s).1 x =
        paper5MovingFrameHeatOp c (r - s)
          (wholeLineCauchyShiftedReaction p U) x₀ := by
    intro s hs
    have hlag : 0 < r - s := sub_pos.mpr hs.2
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1, hs.2.le.trans z.2.2⟩
    unfold wholeLineCauchyValueBUCIntegrand
    have htotal : wholeLineCauchyHeatBUCTotal (r - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT W s) =
        wholeLineCauchyHeatBUC (r - s) hlag
          (wholeLineCauchyReactionSourceTrajectory p hM hT W s) := by
      simp [wholeLineCauchyHeatBUCTotal, hlag]
    rw [htotal, wholeLineCauchyHeatBUC_apply]
    unfold paper5MovingFrameHeatOp
    have hshift := wholeLineCauchyHeatOp_eval_shift_eq_input_shift
      (r - s) (-c * (a + s)) (wholeLineCauchyShiftedReaction p U) x
    have hsrc :
        (wholeLineCauchyReactionSourceTrajectory p hM hT W s).1 =
          fun y => wholeLineCauchyShiftedReaction p U
            (y + (-c * (a + s))) := by
      funext y
      rw [wholeLineCauchyReactionSourceTrajectory_translatedProfile
        p hM hT hsT U hUunif hUIcc c a y]
      congr 2
      ring
    rw [hsrc, ← hshift]
    rw [show x₀ + c * (r - s) = x - c * (a + s) by
      dsimp only [x₀, r]
      ring]
    rw [show x + -c * (a + s) = x - c * (a + s) by ring]
  let G : ℝ → ℝ := fun q => paper5MovingFrameHeatGradOp c q
    (wholeLineChemotaxisFlux p U) x₀
  let Q : ℝ → ℝ := fun q => paper5MovingFrameHeatOp c q
    (wholeLineCauchyShiftedReaction p U) x₀
  have hGchange :
      (∫ s in (0 : ℝ)..r,
          (wholeLineCauchyGradientBUCIntegrand p hM hT W r s).1 x) =
        ∫ q in (0 : ℝ)..r, G q := by
    calc
      _ = ∫ s in (0 : ℝ)..r, G (r - s) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume r] with s hne hs
        rw [Set.uIoc_of_le hr.le] at hs
        exact hGpoint s ⟨hs.1.le, lt_of_le_of_ne hs.2 hne⟩
      _ = _ := by
        simpa using (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := r) G r).symm
  have hRchange :
      (∫ s in (0 : ℝ)..r,
          (wholeLineCauchyValueBUCIntegrand p hM hT W r s).1 x) =
        ∫ q in (0 : ℝ)..r, Q q := by
    calc
      _ = ∫ s in (0 : ℝ)..r, Q (r - s) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume r] with s hne hs
        rw [Set.uIoc_of_le hr.le] at hs
        exact hRpoint s ⟨hs.1.le, lt_of_le_of_ne hs.2 hne⟩
      _ = _ := by
        simpa using (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := r) Q r).symm
  have hstat := hstationary hr x₀
  change
    (wholeLineCauchyHeatBUCTotal r u₀ +
      (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT W r +
      wholeLineCauchyValueDuhamelBUC p hM hT W r).1 x =
    (W z).1 x
  change (wholeLineCauchyHeatBUCTotal r u₀).1 x +
      (-p.χ) * (wholeLineCauchyGradientDuhamelBUC p hM hT W r).1 x +
      (wholeLineCauchyValueDuhamelBUC p hM hT W r).1 x = U x₀
  rw [wholeLineCauchyGradientDuhamelBUC_apply p hM hT W hr.le x,
    wholeLineCauchyValueDuhamelBUC_apply p hM hT W hr.le x,
    hhom, hGchange, hRchange]
  dsimp only [G, Q] at hstat ⊢
  exact hstat.symm

/-- The translated traveling-wave profile is a fixed point of the actual
clamped BUC mild map on every finite restart window.  The source bounds below
are exactly those consumed by the already proved stationary divergence mild
identity; in particular, this statement assumes no weighted spatial
derivative of the Cauchy solution. -/
theorem IsTravelingWave.translatedProfileTrajectoryFrom_isFixedPt
    (p : CMParams) {M T c a D E F FD R : ℝ}
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hT : 0 ≤ T) (hMChiM : MChi p ≤ M)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : ∀ t, 0 < t → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 t) :
    let hUM : ∀ x, |U x| ≤ M := fun x => by
      rw [abs_of_pos (hTW.U_pos x)]
      exact (hbound.le_MChi x).trans hMChiM
    let u₀ := wholeLineTranslatedProfileBUC
      U (travelingWave_U_uniformContinuous hTW hreg.U_cont) M hUM c a
    let W := wholeLineTranslatedProfileTrajectoryFrom hT
      U (travelingWave_U_uniformContinuous hTW hreg.U_cont) M hUM c a
    IsFixedPt (wholeLineCauchyBUCMildMap p
      (zero_le_one.trans
        ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChiM))
      hT u₀) W := by
  dsimp only
  have hM1 : 1 ≤ M :=
    (MChi_ge_one_of_travelingWave hTW hbound).trans hMChiM
  have hM : 0 ≤ M := zero_le_one.trans hM1
  have hUIcc : ∀ x, U x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨(hTW.U_pos x).le, (hbound.le_MChi x).trans hMChiM⟩
  apply wholeLineTranslatedProfileTrajectoryFrom_isFixedPt
    p hM hT U (travelingWave_U_uniformContinuous hTW hreg.U_cont)
      hUIcc c a
  intro t ht x
  have hVEq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg
  have hstat := IsTravelingWave.stationary_divergence_mild_identity
    p hTW hbound hreg ht hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
      (hgrad_int t ht x)
  simpa [wholeLineTravelingWaveFlux, wholeLineChemotaxisFlux, hVEq] using hstat

#print axioms wholeLineTranslatedProfileBUC_continuous
#print axioms wholeLineTranslatedProfileTrajectory
#print axioms wholeLineCauchyFluxSourceTrajectory_translatedProfile
#print axioms wholeLineCauchyReactionSourceTrajectory_translatedProfile
#print axioms wholeLineTranslatedProfileTrajectoryFrom_isFixedPt
#print axioms IsTravelingWave.translatedProfileTrajectoryFrom_isFixedPt

end ShenWork.Paper1
