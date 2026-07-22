import ShenWork.Paper1.WholeLineChiLargeWeightedL2Smoothing
import ShenWork.Paper1.WholeLineMaximalBUCImport
import ShenWork.Paper1.WholeLineCauchyBUCOffSupport

/-!
# Stage 3 of the whole-line large-sensitivity bootstrap

This file turns the uniformly-local moment and the resolver-gradient bound
into a time-uniform bound for the chemotaxis Duhamel history.  It uses the
shifted generator `Δ - I`; the remaining time kernel is therefore integrable
on `(0,∞)` when the localization rate is strictly below one.
-/

open Filter MeasureTheory Real Set Topology
open intervalIntegral

noncomputable section

namespace ShenWork.Paper1

/-- The shifted logistic source is bounded from above independently of the
size of a nonnegative state.  Its negative part need not be bounded this way.
-/
theorem wholeLineCauchyShiftedReaction_le_four_of_nonneg
    (p : CMParams) {u : ℝ → ℝ} (hu0 : ∀ x, 0 ≤ u x) (x : ℝ) :
    wholeLineCauchyShiftedReaction p u x ≤ 4 := by
  rw [wholeLineCauchyShiftedReaction_eq]
  by_cases hu2 : u x ≤ 2
  · calc
      u x * (2 - (u x) ^ p.α) ≤ u x * 2 := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_self 2 (Real.rpow_nonneg (hu0 x) p.α)) (hu0 x)
      _ ≤ 4 := by nlinarith
  · have h2u : 2 ≤ u x := le_of_not_ge hu2
    have h1u : 1 ≤ u x := by linarith
    have hpow : u x ≤ (u x) ^ p.α := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le h1u p.hα)
    have hfactor : 2 - (u x) ^ p.α ≤ 0 := by linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (hu0 x) hfactor).trans (by norm_num)

/-- Infinite-time mass of the weighted `L² → L∞` derivative kernel. -/
def wholeLineWeightedHeatDerivL2TimeMass (κ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-t) * wholeLineWeightedHeatDerivL2NormBound t κ

theorem wholeLineWeightedHeatDerivL2TimeMass_nonneg (κ : ℝ) :
    0 ≤ wholeLineWeightedHeatDerivL2TimeMass κ := by
  unfold wholeLineWeightedHeatDerivL2TimeMass
  exact integral_nonneg fun t => mul_nonneg (Real.exp_nonneg _)
    (by
      unfold wholeLineWeightedHeatDerivL2NormBound
      exact Real.rpow_nonneg
        (mul_nonneg
          (wholeLineWeightedHeatDerivL2PointConstant_nonneg t κ)
          (Real.sqrt_nonneg _)) _)

/-- One heat-gradient slice of the chemotaxis flux, with the damping factor
from the generator `Δ-I` restored. -/
theorem wholeLineCauchyHeatGradOp_abs_le_of_localMoment
    (p : CMParams) {P κ K L τ : ℝ}
    (hP0 : 0 ≤ P) (hP2m : 2 * p.m ≤ P)
    (hκ : 0 < κ) (hL : 0 ≤ L) (hτ : 0 < τ)
    {u : ℝ → ℝ} (huC : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hfluxC : Continuous (wholeLineChemotaxisFlux p u))
    (hgrad : ∀ y, |deriv (frozenElliptic p u) y| ≤ L)
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) ≤ K) :
    |wholeLineCauchyHeatGradOp τ (wholeLineChemotaxisFlux p u) x| ≤
      Real.exp (-τ) * wholeLineWeightedHeatDerivL2NormBound τ κ *
        (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) := by
  have hraw := weighted_chemotaxisFlux_convolution_abs_le
    p hP0 hP2m hκ hL hτ huC hu0 hfluxC hgrad x hmoment
  unfold wholeLineCauchyHeatGradOp
  rw [MeasureTheory.integral_const_mul, abs_mul,
    abs_of_nonneg (Real.exp_nonneg (-τ))]
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hraw (Real.exp_nonneg (-τ)))

/-- The entire chemotaxis Duhamel history is bounded uniformly in terminal
time.  The endpoint singularity is harmless because the exponent is `3/4`.
The separate interval-integrability hypothesis is supplied automatically by
any continuous BUC source on a finite orbit segment. -/
theorem wholeLineCauchyGradientDuhamel_abs_le_of_uniform_localMoment
    (p : CMParams) {P κ K L t : ℝ}
    (hP0 : 0 ≤ P) (hP2m : 2 * p.m ≤ P)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (ht : 0 < t)
    {u : ℝ → ℝ → ℝ}
    (huC : ∀ s ∈ Set.Ioo (0 : ℝ) t, IsCUnifBdd (u s))
    (hu0 : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ y, 0 ≤ u s y)
    (hfluxC : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (wholeLineChemotaxisFlux p (u s)))
    (hgrad : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ y,
      |deriv (frozenElliptic p (u s)) y| ≤ L)
    (hmoment : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ x : ℝ,
      (∫ y : ℝ, (u s y) ^ P * localizingWeightAt κ x y) ≤ K)
    (hgradInt : ∀ x : ℝ, IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s)
        (wholeLineChemotaxisFlux p (u s)) x) volume 0 t)
    (x : ℝ) :
    |wholeLineCauchyGradientDuhamel
        (fun s => wholeLineChemotaxisFlux p (u s)) t x| ≤
      wholeLineWeightedHeatDerivL2TimeMass κ *
        (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) := by
  let k : ℝ → ℝ := fun τ =>
    Real.exp (-τ) * wholeLineWeightedHeatDerivL2NormBound τ κ
  let A : ℝ := (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (by positivity) _
  have hkIoi : IntegrableOn k (Set.Ioi 0) := by
    simpa [k] using
      damped_wholeLineWeightedHeatDerivL2NormBound_integrableOn_Ioi
        hκ.le hκ1
  have hkIci : IntegrableOn k (Set.Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hkIoi
  have huIcc : Set.uIcc (0 : ℝ) t ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le ht.le]
    exact fun _ h => h.1
  have hkInt : IntervalIntegrable k volume 0 t :=
    (hkIci.mono_set huIcc).intervalIntegrable
  have hkCompInt : IntervalIntegrable (fun s => k (t - s)) volume 0 t := by
    simpa using (hkInt.comp_sub_left t).symm
  have hmajorInt : IntervalIntegrable (fun s => k (t - s) * A)
      volume 0 t := hkCompInt.mul_const A
  have hne0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := Measure.ae_ne volume 0
  have hnet : ∀ᵐ s : ℝ ∂volume, s ≠ t := Measure.ae_ne volume t
  have hae :
      (fun s : ℝ =>
        |wholeLineCauchyHeatGradOp (t - s)
          (wholeLineChemotaxisFlux p (u s)) x|) ≤ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) t)]
      (fun s => k (t - s) * A) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne0, hnet] with s hs0 hst hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hst⟩
    simpa [k, A, mul_assoc] using
      (wholeLineCauchyHeatGradOp_abs_le_of_localMoment
        p hP0 hP2m hκ hL (sub_pos.mpr hsIoo.2)
        (huC s hsIoo) (hu0 s hsIoo) (hfluxC s hsIoo)
        (hgrad s hsIoo) x (hmoment s hsIoo x))
  have hk0 : ∀ᵐ τ ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ k τ := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Filter.Eventually.of_forall fun τ _ =>
      mul_nonneg (Real.exp_nonneg _)
        (by
          unfold wholeLineWeightedHeatDerivL2NormBound
          exact Real.rpow_nonneg
            (mul_nonneg
              (wholeLineWeightedHeatDerivL2PointConstant_nonneg τ κ)
              (Real.sqrt_nonneg _)) _)
  have hkInterval_le :
      (∫ τ in (0 : ℝ)..t, k τ) ≤ ∫ τ in Set.Ioi (0 : ℝ), k τ := by
    rw [intervalIntegral.integral_of_le ht.le]
    exact setIntegral_mono_set hkIoi hk0
      (Filter.Eventually.of_forall fun τ hτ => Set.Ioc_subset_Ioi_self hτ)
  calc
    |wholeLineCauchyGradientDuhamel
        (fun s => wholeLineChemotaxisFlux p (u s)) t x| ≤
        ∫ s in (0 : ℝ)..t,
          |wholeLineCauchyHeatGradOp (t - s)
            (wholeLineChemotaxisFlux p (u s)) x| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, k (t - s) * A :=
      intervalIntegral.integral_mono_ae_restrict ht.le
        (hgradInt x).abs hmajorInt hae
    _ = A * ∫ τ in (0 : ℝ)..t, k τ := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_comp_sub_left]
      simp only [sub_self, tsub_zero]
      ring
    _ ≤ A * ∫ τ in Set.Ioi (0 : ℝ), k τ :=
      mul_le_mul_of_nonneg_left hkInterval_le hA0
    _ = wholeLineWeightedHeatDerivL2TimeMass κ * A := by
      unfold wholeLineWeightedHeatDerivL2TimeMass
      dsimp [k]
      ring

/-! ## The one-sided logistic history -/

/-- The damping in `Δ-I` turns the size-independent upper bound `4` for the
shifted logistic source into the same size-independent bound for its entire
Duhamel history. -/
theorem wholeLineCauchyValueHistory_le_four
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hFupper : ∀ s y, (F s).1 y ≤ 4)
    (x : ℝ) :
    wholeLineCauchyValueHistory F t x ≤ 4 := by
  let base : ℝ → ℝ := fun r => 4 * Real.exp (-r)
  let target : ℝ → ℝ := fun s =>
    wholeLineCauchyHeatOp (t - s) (F s).1 x
  have htargetInt : IntervalIntegrable target volume 0 t := by
    simpa [target] using
      wholeLineCauchyValueHistory_intervalIntegrable hF ht hM hFnorm x
  have hbaseIoi : IntegrableOn base (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
    have h' := h.const_mul (4 : ℝ)
    simpa [base] using h'
  have hbaseIci : IntegrableOn base (Set.Ici (0 : ℝ)) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hbaseIoi
  have huIcc : Set.uIcc (0 : ℝ) t ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le ht.le]
    exact fun _ h => h.1
  have hbaseInt : IntervalIntegrable base volume 0 t :=
    (hbaseIci.mono_set huIcc).intervalIntegrable
  have hmajorInt : IntervalIntegrable (fun s => base (t - s)) volume 0 t := by
    simpa using (hbaseInt.comp_sub_left t).symm
  have hnet : ∀ᵐ s : ℝ ∂volume, s ≠ t := Measure.ae_ne volume t
  have hae : target ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) t)]
      (fun s => base (t - s)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hnet] with s hst hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    change wholeLineCauchyHeatOp (t - s) (F s).1 x ≤
      4 * Real.exp (-(t - s))
    have hupper := modifiedSemigroup_upper_bound
      (f := (F s).1) (M := (4 : ℝ)) (Mf := M)
      (hFupper s)
      (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s))
      (F s).1.continuous.aestronglyMeasurable hlag x
    simpa [wholeLineCauchyHeatOp, mul_comm] using hupper
  have hbase0 : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ base r := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Filter.Eventually.of_forall fun r _ => by
      dsimp [base]
      positivity
  have hinterval_le :
      (∫ r in (0 : ℝ)..t, base r) ≤
        ∫ r in Set.Ioi (0 : ℝ), base r := by
    rw [intervalIntegral.integral_of_le ht.le]
    exact setIntegral_mono_set hbaseIoi hbase0
      (Filter.Eventually.of_forall fun r hr => Set.Ioc_subset_Ioi_self hr)
  have hmass : (∫ r in Set.Ioi (0 : ℝ), base r) = 4 := by
    have hexp := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
    dsimp [base]
    rw [MeasureTheory.integral_const_mul]
    norm_num at hexp ⊢
    exact hexp
  calc
    wholeLineCauchyValueHistory F t x = ∫ s in (0 : ℝ)..t, target s := rfl
    _ ≤ ∫ s in (0 : ℝ)..t, base (t - s) :=
      intervalIntegral.integral_mono_ae_restrict ht.le
        htargetInt hmajorInt hae
    _ = ∫ r in (0 : ℝ)..t, base r := by
      rw [intervalIntegral.integral_comp_sub_left]
      simp only [sub_self, tsub_zero]
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), base r := hinterval_le
    _ = 4 := hmass

/-! ## Assembly on one finite BUC trajectory -/

/-- The mild map at time `t` only sees the trajectory on `[0,t]`. -/
theorem wholeLineCauchyMildMap_congr_on_Icc
    (p : CMParams) (u₀ : ℝ → ℝ) {U W : ℝ → ℝ → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hUW : ∀ s ∈ Set.Icc (0 : ℝ) t, U s = W s) (x : ℝ) :
    wholeLineCauchyMildMap p u₀ U t x =
      wholeLineCauchyMildMap p u₀ W t x := by
  by_cases ht0 : t = 0
  · subst t
    simp [wholeLineCauchyMildMap]
  · have hchem : wholeLineCauchyChemDuhamel p U t x =
        wholeLineCauchyChemDuhamel p W t x := by
      unfold wholeLineCauchyChemDuhamel wholeLineCauchyGradientDuhamel
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      change wholeLineCauchyHeatGradOp (t - s)
        (wholeLineChemotaxisFlux p (U s)) x =
          wholeLineCauchyHeatGradOp (t - s)
            (wholeLineChemotaxisFlux p (W s)) x
      rw [hUW s hs]
    have hreaction : wholeLineCauchyReactionDuhamel p U t x =
        wholeLineCauchyReactionDuhamel p W t x := by
      unfold wholeLineCauchyReactionDuhamel wholeLineCauchyValueDuhamel
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [hUW s hs]
    simp only [wholeLineCauchyMildMap, if_neg ht0, hchem, hreaction]

/-- Stage 3 on a finite orbit segment.  Although `M` is used to package the
continuous nonlinear sources in `BUC(ℝ)`, it disappears from the resulting
bound.  This is the continuation-relevant feature of the estimate. -/
theorem wholeLineFiniteBUCTrajectory_norm_le_of_uniform_localMoment
    (p : CMParams) {P κ K M T : ℝ}
    (hχ : 0 ≤ p.χ) (hPγ : p.γ ≤ P) (hP2m : 2 * p.m ≤ P)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (hmoment : ∀ z : Set.Icc (0 : ℝ) T, 0 < z.1 → ∀ x : ℝ,
      (∫ y : ℝ, ((U z).1 y) ^ P * localizingWeightAt κ x y) ≤ K)
    (hmild : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      (U z).1 x = wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT.le U t).1 y)
        z.1 x)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1) :
    ‖U z‖ ≤
      ‖u₀‖ + p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
        (wholeLineChiLargeGradientConstant κ K ^ 2 *
          (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4 := by
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT.le U
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT.le U
  let L : ℝ := wholeLineChiLargeGradientConstant κ K
  have hL : 0 ≤ L := by
    dsimp [L, wholeLineChiLargeGradientConstant]
    positivity
  have hextStrip (s x : ℝ) : ue s x ∈ Set.Icc (0 : ℝ) M := by
    dsimp [ue, wholeLineBUCTrajectoryExtend]
    exact hstrip (Set.projIcc 0 T hT.le s) x
  have hueC (s : ℝ) : IsCUnifBdd (ue s) := by
    exact WholeLineBUC.isCUnifBdd (wholeLineBUCTrajectoryExtend hT.le U s)
  have hue0 (s x : ℝ) : 0 ≤ ue s x := (hextStrip s x).1
  have hFfun (s : ℝ) : (F s).1 = wholeLineChemotaxisFlux p (ue s) := by
    apply funext
    intro x
    change wholeLineCauchyTruncatedFlux p M
      (wholeLineBUCTrajectoryExtend hT.le U s).1 x =
        wholeLineChemotaxisFlux p (ue s) x
    exact congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM (hextStrip s)) x
  have hRfun (s : ℝ) : (R s).1 = wholeLineCauchyShiftedReaction p (ue s) := by
    apply funext
    intro x
    change wholeLineCauchyTruncatedReaction p M
      (wholeLineBUCTrajectoryExtend hT.le U s).1 x =
        wholeLineCauchyShiftedReaction p (ue s) x
    exact congrFun
      (wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM (hextStrip s)) x
  have hFcont : Continuous F := by
    exact wholeLineCauchyFluxSourceTrajectory_continuous p hM hT.le U
  have hRcont : Continuous R := by
    exact wholeLineCauchyReactionSourceTrajectory_continuous p hM hT.le U
  have hMF : 0 ≤ M ^ p.m * M ^ p.γ := by positivity
  have hFnorm : ∀ s, ‖F s‖ ≤ M ^ p.m * M ^ p.γ := by
    intro s
    exact wholeLineCauchyTruncatedFluxBUC_norm_le p hM _
  have hMR : 0 ≤ M + M * (1 + M ^ p.α) := by positivity
  have hRnorm : ∀ s, ‖R s‖ ≤ M + M * (1 + M ^ p.α) := by
    intro s
    exact wholeLineCauchyTruncatedReactionBUC_norm_le p hM _
  have hmomentU : ∀ s ∈ Set.Ioo (0 : ℝ) z.1, ∀ x : ℝ,
      (∫ y : ℝ, (ue s y) ^ P * localizingWeightAt κ x y) ≤ K := by
    intro s hs x
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1.le, hs.2.le.trans z.2.2⟩
    have hext := wholeLineBUCTrajectoryExtend_eq hT.le U hsT
    simpa [ue, hext] using hmoment ⟨s, hsT⟩ hs.1 x
  have hgradU : ∀ s ∈ Set.Ioo (0 : ℝ) z.1, ∀ x : ℝ,
      |deriv (frozenElliptic p (ue s)) x| ≤ L := by
    intro s hs x
    exact frozenElliptic_deriv_abs_le_of_localMoment p hPγ hκ hκ1.le
      (hueC s) (hue0 s) (hmomentU s hs) x
  have hfluxCU : ∀ s ∈ Set.Ioo (0 : ℝ) z.1,
      Continuous (wholeLineChemotaxisFlux p (ue s)) := by
    intro s _hs
    rw [← hFfun s]
    exact (F s).1.continuous
  have hgradInt : ∀ x : ℝ, IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (z.1 - s)
        (wholeLineChemotaxisFlux p (ue s)) x) volume 0 z.1 := by
    intro x
    have hraw := wholeLineCauchyGradientHistory_intervalIntegrable
      hFcont hz hMF hFnorm x
    simpa only [hFfun] using hraw
  have hchem :=
    wholeLineCauchyGradientDuhamel_abs_le_of_uniform_localMoment
      p (P := P) (κ := κ) (K := K) (L := L)
      (t := z.1) (by linarith [p.hm]) hP2m hκ hκ1 hK hL hz
      (fun s _ => hueC s) (fun s _ => hue0 s) hfluxCU hgradU
      hmomentU hgradInt
  have hchemEq (x : ℝ) : wholeLineCauchyGradientHistory F z.1 x =
      wholeLineCauchyGradientDuhamel
        (fun s => wholeLineChemotaxisFlux p (ue s)) z.1 x := by
    unfold wholeLineCauchyGradientHistory wholeLineCauchyGradientDuhamel
    simp_rw [hFfun]
  have hRupper : ∀ s y, (R s).1 y ≤ 4 := by
    intro s y
    rw [hRfun]
    exact wholeLineCauchyShiftedReaction_le_four_of_nonneg p (hue0 s) y
  have hvalue : ∀ x, wholeLineCauchyValueHistory R z.1 x ≤ 4 := by
    intro x
    exact wholeLineCauchyValueHistory_le_four hRcont hz hMR hRnorm hRupper x
  have hvalueEq (x : ℝ) : wholeLineCauchyValueHistory R z.1 x =
      wholeLineCauchyValueDuhamel
        (fun s => wholeLineCauchyShiftedReaction p (ue s)) z.1 x := by
    unfold wholeLineCauchyValueHistory wholeLineCauchyValueDuhamel
    simp_rw [hRfun]
    rw [intervalIntegral.integral_of_le hz.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  let C : ℝ := ‖u₀‖ + p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
      (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4
  have hC : 0 ≤ C := by
    have hmass0 := wholeLineWeightedHeatDerivL2TimeMass_nonneg κ
    have hroot0 : 0 ≤
        (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_nonneg (by positivity) _
    dsimp [C]
    exact add_nonneg
      (add_nonneg (norm_nonneg u₀)
        (mul_nonneg (mul_nonneg hχ hmass0) hroot0))
      (by norm_num)
  change ‖(U z).1‖ ≤ _
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (hstrip z x).1]
  have hheat : |wholeLineCauchyHeatOp z.1 u₀.1 x| ≤ ‖u₀‖ := by
    exact wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
      (M := ‖u₀‖) (f := u₀.1)
      (fun y => WholeLineBUC.abs_apply_le_norm u₀ y)
      (norm_nonneg u₀) u₀.1.continuous.aestronglyMeasurable hz.le x
  have hformula : (U z).1 x =
      wholeLineCauchyHeatOp z.1 u₀.1 x +
        (-p.χ) * wholeLineCauchyGradientHistory F z.1 x +
          wholeLineCauchyValueHistory R z.1 x := by
    rw [hmild z x, wholeLineCauchyMildMap, if_neg hz.ne',
      wholeLineCauchyChemDuhamel, wholeLineCauchyReactionDuhamel,
      hchemEq, hvalueEq]
  have hchemUpper :
      (-p.χ) * wholeLineCauchyGradientHistory F z.1 x ≤
        p.χ * (wholeLineWeightedHeatDerivL2TimeMass κ *
          (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ)) := by
    calc
      (-p.χ) * wholeLineCauchyGradientHistory F z.1 x ≤
          |(-p.χ) * wholeLineCauchyGradientHistory F z.1 x| :=
        le_abs_self _
      _ = p.χ * |wholeLineCauchyGradientHistory F z.1 x| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hχ]
      _ ≤ p.χ * (wholeLineWeightedHeatDerivL2TimeMass κ *
          (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hχ
        rw [hchemEq]
        exact hchem x
  rw [hformula]
  dsimp [C]
  have hheatUpper := (le_abs_self
    (wholeLineCauchyHeatOp z.1 u₀.1 x)).trans hheat
  calc
    wholeLineCauchyHeatOp z.1 u₀.1 x +
          -p.χ * wholeLineCauchyGradientHistory F z.1 x +
        wholeLineCauchyValueHistory R z.1 x ≤
      ‖u₀‖ + p.χ *
          (wholeLineWeightedHeatDerivL2TimeMass κ *
            (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ)) + 4 :=
      add_le_add (add_le_add hheatUpper hchemUpper) (hvalue x)
    _ = ‖u₀‖ + p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
          (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4 := by ring

/-! ## Maximal-orbit continuation interface -/

/-- The exact Stage-1 statement still needed on maximal critical orbits.
The constant may depend on the datum and orbit, but is uniform in time below
the maximal horizon and uniform in the translated spatial centre. -/
def WholeLineLargeChiMaximalLocalMomentBound
    (p : CMParams) (P κ : ℝ) : Prop :=
  ∀ (u₀ : ℝ → ℝ), PaperNonnegativeInitialDatum u₀ →
    ∀ (Tmax : WithTop ℝ) (U : ℝ → WholeLineBUC),
      IsWholeLineMaximalBUCOrbit p u₀ Tmax U →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ, 0 < t → (t : WithTop ℝ) < Tmax → ∀ x : ℝ,
          (∫ y : ℝ, ((U t).1 y) ^ P *
            localizingWeightAt κ x y) ≤ K

/-- Once Stage 1 is available on maximal orbits, the estimates above supply
the a-priori BUC bound required by the blow-up alternative. -/
theorem wholeLineLargeChiAPrioriBound_of_maximalLocalMoment
    (p : CMParams) {P κ : ℝ}
    (hχ : 0 ≤ p.χ) (hPγ : p.γ ≤ P) (hP2m : 2 * p.m ≤ P)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (Hmoment : WholeLineLargeChiMaximalLocalMomentBound p P κ) :
    WholeLineLargeChiAPrioriBound p := by
  intro u₀ hu₀ Tmax U horbit
  obtain ⟨K, hK, hmoment⟩ := Hmoment u₀ hu₀ Tmax U horbit
  obtain ⟨_hTmax, hdatum, _htrace, hcont, _hclass, hmild,
    hnonneg, _hblowup⟩ := horbit
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  let L : ℝ := wholeLineChiLargeGradientConstant κ K
  let C : ℝ := ‖w‖ + p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
      (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4
  refine ⟨C, ?_⟩
  intro t ht htmax
  by_cases htzero : t = 0
  · subst t
    have hUzero : U 0 = w := by
      apply Subtype.ext
      apply BoundedContinuousFunction.ext
      intro x
      simpa [w] using hdatum x
    rw [hUzero]
    dsimp [C]
    have hmass0 := wholeLineWeightedHeatDerivL2TimeMass_nonneg κ
    have hL0 : 0 ≤ L := by
      dsimp [L, wholeLineChiLargeGradientConstant]
      positivity
    have hroot0 : 0 ≤ (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_nonneg (by positivity) _
    have htail : 0 ≤ p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
        (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4 :=
      add_nonneg (mul_nonneg (mul_nonneg hχ hmass0) hroot0)
        (by norm_num)
    calc
      ‖w‖ ≤ ‖w‖ +
          (p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
            (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4) :=
        le_add_of_nonneg_right htail
      _ = ‖w‖ + p.χ * wholeLineWeightedHeatDerivL2TimeMass κ *
          (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) + 4 := by ring
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    have hcontT := hcont t ht htmax
    let Traj : WholeLineBUCTrajectory t :=
      ⟨fun z => U z.1, hcontT.restrict⟩
    have hnormCont : ContinuousOn (fun s : ℝ => ‖U s‖)
        (Set.Icc (0 : ℝ) t) := hcontT.norm
    obtain ⟨B, hB⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) t)).bddAbove_image hnormCont
    let M : ℝ := max B 0
    have hM : 0 ≤ M := le_max_right _ _
    have hTrajNorm : ∀ z : Set.Icc (0 : ℝ) t, ‖Traj z‖ ≤ M := by
      intro z
      have hzB : ‖U z.1‖ ≤ B :=
        hB (Set.mem_image_of_mem (fun s => ‖U s‖) z.2)
      exact hzB.trans (le_max_left _ _)
    have hstrip : ∀ z : Set.Icc (0 : ℝ) t, ∀ x,
        (Traj z).1 x ∈ Set.Icc (0 : ℝ) M := by
      intro z x
      have hzmax : (z.1 : WithTop ℝ) < Tmax :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr z.2.2) htmax
      constructor
      · exact hnonneg z.1 x z.2.1 hzmax
      · exact (WholeLineBUC.apply_le_norm (Traj z) x).trans (hTrajNorm z)
    have hmomentTraj : ∀ z : Set.Icc (0 : ℝ) t, 0 < z.1 → ∀ x : ℝ,
        (∫ y : ℝ, ((Traj z).1 y) ^ P *
          localizingWeightAt κ x y) ≤ K := by
      intro z hz x
      have hzmax : (z.1 : WithTop ℝ) < Tmax :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr z.2.2) htmax
      simpa [Traj] using hmoment z.1 hz hzmax x
    have hmildTraj : ∀ z : Set.Icc (0 : ℝ) t, ∀ x : ℝ,
        (Traj z).1 x = wholeLineCauchyMildMap p w.1
          (fun q y => (wholeLineBUCTrajectoryExtend ht Traj q).1 y)
          z.1 x := by
      intro z x
      have hzmax : (z.1 : WithTop ℝ) < Tmax :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr z.2.2) htmax
      have hraw := hmild t htpos htmax z.1 z.2 x
      have hagree : ∀ s ∈ Set.Icc (0 : ℝ) z.1,
          (fun q y => (U q).1 y) s =
            (fun q y => (wholeLineBUCTrajectoryExtend ht Traj q).1 y) s := by
        intro s hs
        have hsT : s ∈ Set.Icc (0 : ℝ) t :=
          ⟨hs.1, hs.2.trans z.2.2⟩
        funext y
        change (U s).1 y =
          (wholeLineBUCTrajectoryExtend ht Traj s).1 y
        rw [wholeLineBUCTrajectoryExtend_eq ht Traj hsT]
        rfl
      have hcongr := wholeLineCauchyMildMap_congr_on_Icc
        p u₀ z.2.1 hagree x
      calc
        (Traj z).1 x = (U z.1).1 x := rfl
        _ = wholeLineCauchyMildMap p u₀
            (fun q y => (U q).1 y) z.1 x := hraw
        _ = wholeLineCauchyMildMap p u₀
            (fun q y => (wholeLineBUCTrajectoryExtend ht Traj q).1 y)
              z.1 x := hcongr
        _ = wholeLineCauchyMildMap p w.1
            (fun q y => (wholeLineBUCTrajectoryExtend ht Traj q).1 y)
              z.1 x := by rfl
    let zt : Set.Icc (0 : ℝ) t := ⟨t, ht, le_rfl⟩
    have hbound := wholeLineFiniteBUCTrajectory_norm_le_of_uniform_localMoment
      p hχ hPγ hP2m hκ hκ1 hK hM htpos w Traj hstrip
        hmomentTraj hmildTraj zt htpos
    simpa [Traj, zt, C, L] using hbound

section AxiomAudit

#print axioms wholeLineCauchyShiftedReaction_le_four_of_nonneg
#print axioms wholeLineWeightedHeatDerivL2TimeMass_nonneg
#print axioms wholeLineCauchyHeatGradOp_abs_le_of_localMoment
#print axioms wholeLineCauchyGradientDuhamel_abs_le_of_uniform_localMoment
#print axioms wholeLineCauchyValueHistory_le_four
#print axioms wholeLineCauchyMildMap_congr_on_Icc
#print axioms wholeLineFiniteBUCTrajectory_norm_le_of_uniform_localMoment
#print axioms wholeLineLargeChiAPrioriBound_of_maximalLocalMoment

end AxiomAudit

end ShenWork.Paper1
