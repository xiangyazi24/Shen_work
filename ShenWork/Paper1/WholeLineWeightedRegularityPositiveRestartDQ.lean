import ShenWork.Paper1.WholeLineWeightedRegularityDQCommutation
import ShenWork.Paper1.WholeLineCauchyNonnegativity

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction Interval

noncomputable section
namespace ShenWork.Paper1

theorem wholeLineBUC_intervalIntegrable_eval
    {a b : ℝ} {F : ℝ → WholeLineBUC}
    (hF : IntervalIntegrable F volume a b) (x : ℝ) :
    IntervalIntegrable (fun s => (F s).1 x) volume a b := by
  constructor
  · have hFi : Integrable F (volume.restrict (Set.Ioc a b)) := hF.1
    exact hFi.norm.mono'
      ((wholeLineBUCEvalCLM x).continuous.comp_aestronglyMeasurable
        hFi.aestronglyMeasurable)
      (Eventually.of_forall fun s => by
        simpa only [Real.norm_eq_abs] using
          WholeLineBUC.abs_apply_le_norm (F s) x)
  · have hFi : Integrable F (volume.restrict (Set.Ioc b a)) := hF.2
    exact hFi.norm.mono'
      ((wholeLineBUCEvalCLM x).continuous.comp_aestronglyMeasurable
        hFi.aestronglyMeasurable)
      (Eventually.of_forall fun s => by
        simpa only [Real.norm_eq_abs] using
          WholeLineBUC.abs_apply_le_norm (F s) x)

theorem spatialDifferenceQuotient_intervalIntegral
    {a b h x : ℝ} {F : ℝ → ℝ → ℝ}
    (hFx : IntervalIntegrable (fun s => F s x) volume a b)
    (hFxh : IntervalIntegrable (fun s => F s (x + h)) volume a b) :
    spatialDifferenceQuotient h (fun y => ∫ s in a..b, F s y) x =
      ∫ s in a..b, spatialDifferenceQuotient h (F s) x := by
  unfold spatialDifferenceQuotient
  change ((∫ s in a..b, F s (x + h)) -
      ∫ s in a..b, F s x) / h =
    ∫ s in a..b, (F s (x + h) - F s x) / h
  rw [← intervalIntegral.integral_sub hFxh hFx]
  simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]

theorem wholeLineCauchyFluxSourceTrajectory_eq_physical_of_strip
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (s : ℝ) :
    (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 =
      wholeLineChemotaxisFlux p
        (wholeLineBUCTrajectoryExtend hT U s).1 := by
  change wholeLineCauchyTruncatedFlux p M
      (wholeLineBUCTrajectoryExtend hT U s).1 = _
  apply wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM
  intro x
  exact hstrip (Set.projIcc 0 T hT s) x

theorem wholeLineCauchyReactionSourceTrajectory_eq_physical_of_strip
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (s : ℝ) :
    (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 =
      wholeLineCauchyShiftedReaction p
        (wholeLineBUCTrajectoryExtend hT U s).1 := by
  change wholeLineCauchyTruncatedReaction p M
      (wholeLineBUCTrajectoryExtend hT U s).1 = _
  apply wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM
  intro x
  exact hstrip (Set.projIcc 0 T hT s) x

theorem wholeLineCauchyCoMovingFluxSource_eq_physical_of_strip
    (p : CMParams) (c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M) (s : ℝ) :
    wholeLineCauchyCoMovingFluxSource p c hM hT U s =
      fun x => wholeLineChemotaxisFlux p
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s) := by
  funext x
  unfold wholeLineCauchyCoMovingFluxSource
  rw [wholeLineCauchyFluxSourceTrajectory_eq_physical_of_strip
    p hM hT U hstrip s]

theorem wholeLineCauchyCoMovingReactionSource_eq_physical_of_strip
    (p : CMParams) (c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M) (s : ℝ) :
    wholeLineCauchyCoMovingReactionSource p c hM hT U s =
      fun x => wholeLineCauchyShiftedReaction p
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s) := by
  funext x
  unfold wholeLineCauchyCoMovingReactionSource
  rw [wholeLineCauchyReactionSourceTrajectory_eq_physical_of_strip
    p hM hT U hstrip s]

def wholeLineCauchyCoMovingFluxSourceBUC
    (p : CMParams) (c : ℝ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s : ℝ) : WholeLineBUC :=
  wholeLineBUCTranslate (c * s)
    (wholeLineCauchyFluxSourceTrajectory p hM hT U s)

@[simp] theorem wholeLineCauchyCoMovingFluxSourceBUC_apply
    (p : CMParams) (c : ℝ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s x : ℝ) :
    (wholeLineCauchyCoMovingFluxSourceBUC p c hM hT U s).1 x =
      wholeLineCauchyCoMovingFluxSource p c hM hT U s x := by
  rfl

def wholeLineCauchyCoMovingReactionSourceBUC
    (p : CMParams) (c : ℝ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s : ℝ) : WholeLineBUC :=
  wholeLineBUCTranslate (c * s)
    (wholeLineCauchyReactionSourceTrajectory p hM hT U s)

@[simp] theorem wholeLineCauchyCoMovingReactionSourceBUC_apply
    (p : CMParams) (c : ℝ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s x : ℝ) :
    (wholeLineCauchyCoMovingReactionSourceBUC p c hM hT U s).1 x =
      wholeLineCauchyCoMovingReactionSource p c hM hT U s x := by
  rfl

theorem wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
    (p : CMParams) {M T a t c : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ha : 0 ≤ a) (hat : a ≤ t)
    (U : WholeLineBUCTrajectory T) (x : ℝ) :
    IntervalIntegrable (fun s =>
      paper5MovingFrameHeatGradOp c (t - s)
        (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x)
      volume a t := by
  have ht : 0 ≤ t := ha.trans hat
  have hfull := wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
    p hM hT U ht
  have hbase : IntervalIntegrable
      (wholeLineCauchyGradientBUCIntegrand p hM hT U t)
      volume a t := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hat, Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc_left ha
  let X : ℝ := x + c * t
  have heval := wholeLineBUC_intervalIntegrable_eval hbase X
  apply heval.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume t)] with s hs hne
  rw [Set.uIoc_of_le hat] at hs
  have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
  unfold wholeLineCauchyGradientBUCIntegrand
  have htotal : wholeLineCauchyHeatGradientBUCTotal (t - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s) =
      wholeLineCauchyHeatGradientBUC (t - s) hlag
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s) := by
    simp [wholeLineCauchyHeatGradientBUCTotal, hlag]
  rw [htotal, wholeLineCauchyHeatGradientBUC_apply]
  unfold paper5MovingFrameHeatGradOp wholeLineCauchyCoMovingFluxSource
  rw [show X = (x + c * (t - s)) + c * s by dsimp [X]; ring]
  exact wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
    (t - s) (c * s)
      (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1
      (x + c * (t - s))

theorem wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
    (p : CMParams) {M T a t c : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ha : 0 ≤ a) (hat : a ≤ t)
    (U : WholeLineBUCTrajectory T) (x : ℝ) :
    IntervalIntegrable (fun s =>
      paper5MovingFrameHeatOp c (t - s)
        (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x)
      volume a t := by
  have ht : 0 ≤ t := ha.trans hat
  have hfull := wholeLineCauchyValueBUCIntegrand_intervalIntegrable
    p hM hT U ht
  have hbase : IntervalIntegrable
      (wholeLineCauchyValueBUCIntegrand p hM hT U t)
      volume a t := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hat, Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc_left ha
  let X : ℝ := x + c * t
  have heval := wholeLineBUC_intervalIntegrable_eval hbase X
  apply heval.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume t)] with s hs hne
  rw [Set.uIoc_of_le hat] at hs
  have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
  unfold wholeLineCauchyValueBUCIntegrand
  have htotal : wholeLineCauchyHeatBUCTotal (t - s)
        (wholeLineCauchyReactionSourceTrajectory p hM hT U s) =
      wholeLineCauchyHeatBUC (t - s) hlag
        (wholeLineCauchyReactionSourceTrajectory p hM hT U s) := by
    simp [wholeLineCauchyHeatBUCTotal, hlag]
  rw [htotal, wholeLineCauchyHeatBUC_apply]
  unfold paper5MovingFrameHeatOp wholeLineCauchyCoMovingReactionSource
  rw [show X = (x + c * (t - s)) + c * s by dsimp [X]; ring]
  exact wholeLineCauchyHeatOp_eval_shift_eq_input_shift
    (t - s) (c * s)
      (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1
      (x + c * (t - s))

/-- Exact spatial-DQ identity on a positive canonical restart window.  The
sources are still named through the canonical source trajectories; the two
clamp-removal lemmas above identify them with the physical sources. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_restart_spatialDQ_identity
    (p : CMParams) {M T a q c d x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hq : 0 < q) (haq : a + q ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
    let zaq : Set.Icc (0 : ℝ) T :=
      ⟨a + q, (add_pos ha hq).le, haq⟩
    spatialDifferenceQuotient d
        (fun y => (U zaq).1 (y + c * (a + q))) x =
      paper5MovingFrameHeatOp c q
        (spatialDifferenceQuotient d
          (fun y => (U za).1 (y + c * a))) x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (spatialDifferenceQuotient d
            (wholeLineCauchyCoMovingFluxSource p c hM hT U s)) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (spatialDifferenceQuotient d
            (wholeLineCauchyCoMovingReactionSource p c hM hT U s)) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
  let zaq : Set.Icc (0 : ℝ) T :=
    ⟨a + q, (add_pos ha hq).le, haq⟩
  let H₀ : ℝ → ℝ := fun y =>
    paper5MovingFrameHeatOp c q
      (fun z => (U za).1 (z + c * a)) y
  let G : ℝ → ℝ → ℝ := fun s y =>
    paper5MovingFrameHeatGradOp c (a + q - s)
      (wholeLineCauchyCoMovingFluxSource p c hM hT U s) y
  let Q : ℝ → ℝ → ℝ := fun s y =>
    paper5MovingFrameHeatOp c (a + q - s)
      (wholeLineCauchyCoMovingReactionSource p c hM hT U s) y
  have hrestart (y : ℝ) :
      (U zaq).1 (y + c * (a + q)) =
        H₀ y + (-p.χ) * (∫ s in a..(a + q), G s y) +
          ∫ s in a..(a + q), Q s y := by
    simpa [U, za, zaq, H₀, G, Q] using
      wholeLineCauchyBUCMildFixedPoint_coMoving_restart_identity
        p hM hT u₀ hsmall ha hq haq hstrip (c := c) (x := y)
  have hhom : spatialDifferenceQuotient d H₀ x =
      paper5MovingFrameHeatOp c q
        (spatialDifferenceQuotient d
          (fun y => (U za).1 (y + c * a))) x := by
    let ustart : WholeLineBUC := wholeLineBUCTranslate (c * a) (U za)
    simpa [H₀, ustart] using
      spatialDifferenceQuotient_paper5MovingFrameHeatOp
        hq c d ustart x
  have hGx : IntervalIntegrable (fun s => G s x) volume a (a + q) := by
    simpa [G] using
      wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
        p hM hT ha.le (le_add_of_nonneg_right hq.le) U x
  have hGxd : IntervalIntegrable (fun s => G s (x + d)) volume a (a + q) := by
    simpa [G] using
      wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
        p hM hT ha.le (le_add_of_nonneg_right hq.le) U (x + d)
  have hGdq₀ := spatialDifferenceQuotient_intervalIntegral hGx hGxd
  have hGcomm :
      (∫ s in a..(a + q), spatialDifferenceQuotient d (G s) x) =
        ∫ s in a..(a + q),
          paper5MovingFrameHeatGradOp c (a + q - s)
            (spatialDifferenceQuotient d
              (wholeLineCauchyCoMovingFluxSource p c hM hT U s)) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    let Fs : WholeLineBUC :=
      wholeLineCauchyCoMovingFluxSourceBUC p c hM hT U s
    simpa [G, Fs] using
      spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
        hlag c d Fs x
  have hGdq : spatialDifferenceQuotient d
        (fun y => ∫ s in a..(a + q), G s y) x =
      ∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (spatialDifferenceQuotient d
            (wholeLineCauchyCoMovingFluxSource p c hM hT U s)) x := by
    exact hGdq₀.trans hGcomm
  have hQx : IntervalIntegrable (fun s => Q s x) volume a (a + q) := by
    simpa [Q] using
      wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
        p hM hT ha.le (le_add_of_nonneg_right hq.le) U x
  have hQxd : IntervalIntegrable (fun s => Q s (x + d)) volume a (a + q) := by
    simpa [Q] using
      wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
        p hM hT ha.le (le_add_of_nonneg_right hq.le) U (x + d)
  have hQdq₀ := spatialDifferenceQuotient_intervalIntegral hQx hQxd
  have hQcomm :
      (∫ s in a..(a + q), spatialDifferenceQuotient d (Q s) x) =
        ∫ s in a..(a + q),
          paper5MovingFrameHeatOp c (a + q - s)
            (spatialDifferenceQuotient d
              (wholeLineCauchyCoMovingReactionSource p c hM hT U s)) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    let Rs : WholeLineBUC :=
      wholeLineCauchyCoMovingReactionSourceBUC p c hM hT U s
    simpa [Q, Rs] using
      spatialDifferenceQuotient_paper5MovingFrameHeatOp
        hlag c d Rs x
  have hQdq : spatialDifferenceQuotient d
        (fun y => ∫ s in a..(a + q), Q s y) x =
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (spatialDifferenceQuotient d
            (wholeLineCauchyCoMovingReactionSource p c hM hT U s)) x := by
    exact hQdq₀.trans hQcomm
  calc
    spatialDifferenceQuotient d
        (fun y => (U zaq).1 (y + c * (a + q))) x =
      spatialDifferenceQuotient d
        (fun y => H₀ y + (-p.χ) * (∫ s in a..(a + q), G s y) +
          ∫ s in a..(a + q), Q s y) x := by
        congr 1
        funext y
        exact hrestart y
    _ = spatialDifferenceQuotient d H₀ x +
        (-p.χ) * spatialDifferenceQuotient d
          (fun y => ∫ s in a..(a + q), G s y) x +
        spatialDifferenceQuotient d
          (fun y => ∫ s in a..(a + q), Q s y) x := by
      unfold spatialDifferenceQuotient
      ring
    _ = _ := by rw [hhom, hGdq, hQdq]

/-- The same exact restart-DQ identity with the global clamp eliminated from
both nonlinear source legs. -/
theorem wholeLineCauchyBUCMildFixedPoint_physical_coMoving_restart_spatialDQ_identity
    (p : CMParams) {M T a q c d x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hq : 0 < q) (haq : a + q ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
    let zaq : Set.Icc (0 : ℝ) T :=
      ⟨a + q, (add_pos ha hq).le, haq⟩
    spatialDifferenceQuotient d
        (fun y => (U zaq).1 (y + c * (a + q))) x =
      paper5MovingFrameHeatOp c q
        (spatialDifferenceQuotient d
          (fun y => (U za).1 (y + c * a))) x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (spatialDifferenceQuotient d (fun y =>
            wholeLineChemotaxisFlux p
              (wholeLineBUCTrajectoryExtend hT U s).1 (y + c * s))) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (spatialDifferenceQuotient d (fun y =>
            wholeLineCauchyShiftedReaction p
              (wholeLineBUCTrajectoryExtend hT U s).1 (y + c * s))) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have hbase :=
    wholeLineCauchyBUCMildFixedPoint_coMoving_restart_spatialDQ_identity
      p hM hT u₀ hsmall ha hq haq hstrip (c := c) (d := d) (x := x)
  dsimp only at hbase ⊢
  have hF (s : ℝ) :
      wholeLineCauchyCoMovingFluxSource p c hM hT U s =
        fun y => wholeLineChemotaxisFlux p
          (wholeLineBUCTrajectoryExtend hT U s).1 (y + c * s) :=
    wholeLineCauchyCoMovingFluxSource_eq_physical_of_strip
      p c hM hT U hstrip s
  have hR (s : ℝ) :
      wholeLineCauchyCoMovingReactionSource p c hM hT U s =
        fun y => wholeLineCauchyShiftedReaction p
          (wholeLineBUCTrajectoryExtend hT U s).1 (y + c * s) :=
    wholeLineCauchyCoMovingReactionSource_eq_physical_of_strip
      p c hM hT U hstrip s
  dsimp [U] at hF hR
  simp_rw [hF, hR] at hbase
  exact hbase

#print axioms wholeLineBUC_intervalIntegrable_eval
#print axioms spatialDifferenceQuotient_intervalIntegral
#print axioms wholeLineCauchyFluxSourceTrajectory_eq_physical_of_strip
#print axioms wholeLineCauchyReactionSourceTrajectory_eq_physical_of_strip
#print axioms wholeLineCauchyCoMovingFluxSource_eq_physical_of_strip
#print axioms wholeLineCauchyCoMovingReactionSource_eq_physical_of_strip
#print axioms wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
#print axioms wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
#print axioms
  wholeLineCauchyBUCMildFixedPoint_coMoving_restart_spatialDQ_identity
#print axioms
  wholeLineCauchyBUCMildFixedPoint_physical_coMoving_restart_spatialDQ_identity

end ShenWork.Paper1
