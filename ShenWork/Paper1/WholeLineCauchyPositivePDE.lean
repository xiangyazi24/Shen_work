import ShenWork.Paper1.WholeLineCauchyTerminalAverages
import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-- Differentiate a fixed value-history interval from the right of its terminal
time.  The zero-lag slice is removed only almost everywhere. -/
theorem wholeLineCauchyValueOld_hasDerivWithinAt
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M delta x : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) {bound : ℝ → ℝ}
    (hboundInt : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ s, 0 < s → s < t → ∀ q ∈ Set.Icc t (t + delta),
      |wholeLineCauchyHeatHessOp (q - s) (F s).1 x -
        wholeLineCauchyHeatOp (q - s) (F s).1 x| ≤ bound s) :
    HasDerivWithinAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatOp (q - s) (F s).1 x)
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatHessOp (t - s) (F s).1 x -
          wholeLineCauchyHeatOp (t - s) (F s).1 x))
      (Set.Icc t (t + delta)) t := by
  let S : Set ℝ := Set.Icc t (t + delta)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  let G : ℝ → ℝ → ℝ := fun s q =>
    wholeLineCauchyHeatOp (q - s) (F s).1 x
  let G' : ℝ → ℝ → ℝ := fun s q =>
    wholeLineCauchyHeatHessOp (q - s) (F s).1 x -
      wholeLineCauchyHeatOp (q - s) (F s).1 x
  have hSconv : Convex ℝ S := by
    dsimp [S]
    exact convex_Icc t (t + delta)
  have htS : t ∈ S := by
    dsimp [S]
    exact ⟨le_rfl, le_add_of_nonneg_right hdelta.le⟩
  have hGmeas : ∀ q ∈ S, AEStronglyMeasurable (fun s => G s q) μ := by
    intro q _hq
    exact (wholeLineCauchyHeatOp_s_dependent_aestronglyMeasurable hF q x).restrict
  have hGint : Integrable (fun s => G s t) μ := by
    have hi := wholeLineCauchyValueHistory_intervalIntegrable hF ht hM hFnorm x
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hi).integrable
  have hG'meas : AEStronglyMeasurable (fun s => G' s t) μ := by
    exact ((wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF t x).sub
      (wholeLineCauchyHeatOp_s_dependent_aestronglyMeasurable hF t x)).restrict
  have hboundInt' : Integrable bound μ := by
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hboundInt).integrable
  have hGbound : ∀ᵐ s ∂μ, ∀ q ∈ S, |G' s q| ≤ bound s := by
    rw [show μ = volume.restrict (Set.Ioc (0 : ℝ) t) by rfl]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [Measure.ae_ne volume t] with s hst hs
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    exact fun q hq => hbound s hs.1 hst' q hq
  have hGdiff : ∀ᵐ s ∂μ, ∀ q ∈ S,
      HasDerivWithinAt (fun q => G s q) (G' s q) S q := by
    rw [show μ = volume.restrict (Set.Ioc (0 : ℝ) t) by rfl]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [Measure.ae_ne volume t] with s hst hs
    intro q hq
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    have hlag : 0 < q - s := sub_pos.mpr (hst'.trans_le hq.1)
    have hf_bound : ∀ y, |(F s).1 y| ≤ M := fun y =>
      (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
    have hbase := wholeLineCauchyHeatOp_time_hasDerivAt
      hlag hM (F s).1.continuous.aestronglyMeasurable hf_bound x
    have hlin : HasDerivAt (fun w : ℝ => w - s) 1 q := by
      simpa using (hasDerivAt_id q).sub_const s
    have hcomp : HasDerivAt (fun q => G s q) (G' s q) q := by
      simpa [G, G', Function.comp_def] using hbase.comp q hlin
    exact hcomp.hasDerivWithinAt
  have hraw :=
    ShenWork.IntervalMildPicardRegularityEndpoint.hasDerivWithinAt_integral_of_dominated_loc_var
      hSconv htS hGmeas hGint hG'meas hGbound hboundInt' hGdiff
  simpa [G, G', μ, intervalIntegral.integral_of_le ht.le] using hraw

/-- Differentiate a fixed gradient-history interval from the right of its
terminal time.  The zero-lag slice is removed only almost everywhere. -/
theorem wholeLineCauchyGradientOld_hasDerivWithinAt
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M delta x : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) {bound : ℝ → ℝ}
    (hboundInt : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ s, 0 < s → s < t → ∀ q ∈ Set.Icc t (t + delta),
      |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x -
        wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤ bound s) :
    HasDerivWithinAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatGradOp (q - s) (F s).1 x)
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 x))
      (Set.Icc t (t + delta)) t := by
  let S : Set ℝ := Set.Icc t (t + delta)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  let G : ℝ → ℝ → ℝ := fun s q =>
    wholeLineCauchyHeatGradOp (q - s) (F s).1 x
  let G' : ℝ → ℝ → ℝ := fun s q =>
    wholeLineCauchyHeatThirdOp (q - s) (F s).1 x -
      wholeLineCauchyHeatGradOp (q - s) (F s).1 x
  have hSconv : Convex ℝ S := by
    dsimp [S]
    exact convex_Icc t (t + delta)
  have htS : t ∈ S := by
    dsimp [S]
    exact ⟨le_rfl, le_add_of_nonneg_right hdelta.le⟩
  have hGmeas : ∀ q ∈ S, AEStronglyMeasurable (fun s => G s q) μ := by
    intro q _hq
    exact (wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF q x).restrict
  have hGint : Integrable (fun s => G s t) μ := by
    have hi := wholeLineCauchyGradientHistory_intervalIntegrable hF ht hM hFnorm x
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hi).integrable
  have hG'meas : AEStronglyMeasurable (fun s => G' s t) μ := by
    exact ((wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable hF t x).sub
      (wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF t x)).restrict
  have hboundInt' : Integrable bound μ := by
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hboundInt).integrable
  have hGbound : ∀ᵐ s ∂μ, ∀ q ∈ S, |G' s q| ≤ bound s := by
    rw [show μ = volume.restrict (Set.Ioc (0 : ℝ) t) by rfl]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [Measure.ae_ne volume t] with s hst hs
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    exact fun q hq => hbound s hs.1 hst' q hq
  have hGdiff : ∀ᵐ s ∂μ, ∀ q ∈ S,
      HasDerivWithinAt (fun q => G s q) (G' s q) S q := by
    rw [show μ = volume.restrict (Set.Ioc (0 : ℝ) t) by rfl]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [Measure.ae_ne volume t] with s hst hs
    intro q hq
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    have hlag : 0 < q - s := sub_pos.mpr (hst'.trans_le hq.1)
    have hf_bound : ∀ y, |(F s).1 y| ≤ M := fun y =>
      (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
    have hbase := wholeLineCauchyHeatGradOp_time_hasDerivAt
      hlag hM (F s).1.continuous.aestronglyMeasurable hf_bound x
    have hlin : HasDerivAt (fun w : ℝ => w - s) 1 q := by
      simpa using (hasDerivAt_id q).sub_const s
    have hcomp : HasDerivAt (fun q => G s q) (G' s q) q := by
      simpa [G, G', Function.comp_def] using hbase.comp q hlin
    exact hcomp.hasDerivWithinAt
  have hraw :=
    ShenWork.IntervalMildPicardRegularityEndpoint.hasDerivWithinAt_integral_of_dominated_loc_var
      hSconv htS hGmeas hGint hG'meas hGbound hboundInt' hGdiff
  simpa [G, G', μ, intervalIntegral.integral_of_le ht.le] using hraw

/-- The fixed old part of the reaction Duhamel history is differentiable from
the right at every positive physical time. -/
theorem wholeLineCauchyReactionValueOld_time_hasDerivWithinAt_positive
    (p : CMParams) {M T theta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    HasDerivWithinAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatOp (q - s) (R s).1 x)
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatHessOp (t - s) (R s).1 x -
          wholeLineCauchyHeatOp (t - s) (R s).1 x))
      (Set.Icc t (t + 1)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < t / 2 := by positivity
  rcases exists_wholeLineCauchyReactionSourceTrajectory_window_Ctheta
      p hM hT hhalf htT.le u₀ hsmall htheta0 htheta1 with
    ⟨HR, hHR, hRholder⟩
  let Cearly : ℝ :=
    (5 * Real.sqrt 2 / 2) * (t / 2) ^ (-(1 : ℝ)) * MR
  let Wtheta : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR + MR
  have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
  have hWtheta : 0 ≤ Wtheta := by
    dsimp [Wtheta]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0
    have hscaled := (hk.const_mul Wtheta).mul_const HR
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly + MR) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, add_assoc, add_left_comm, add_comm, mul_assoc] using
      hconst.add hscaled
  have hbound : ∀ s, 0 < s → s < t → ∀ q ∈ Set.Icc t (t + 1),
      |wholeLineCauchyHeatHessOp (q - s) (R s).1 x -
        wholeLineCauchyHeatOp (q - s) (R s).1 x| ≤ bound s := by
    intro s _hs0 hst q hq
    have hlag : 0 < q - s := sub_pos.mpr (hst.trans_le hq.1)
    have hbaseLag : t - s ≤ q - s := sub_le_sub_right hq.1 s
    have hf_bound : ∀ y, |(R s).1 y| ≤ MR := fun y =>
      (WholeLineBUC.abs_apply_le_norm (R s) y).trans (hRnorm s)
    have hheat := wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
      hf_bound hMR (R s).1.continuous.aestronglyMeasurable hlag.le x
    have hhess : |wholeLineCauchyHeatHessOp (q - s) (R s).1 x| ≤
        Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR := by
      by_cases hsHalf : s ≤ t / 2
      · have hlagHalf : t / 2 ≤ q - s := by linarith
        have hpow : (q - s) ^ (-(1 : ℝ)) ≤
            (t / 2) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
        have hglobal := wholeLineCauchyHeatHessOp_abs_le (x := x)
          hlag hMR (R s).1.continuous.aestronglyMeasurable hf_bound
        calc
          |wholeLineCauchyHeatHessOp (q - s) (R s).1 x| ≤
              5 * Real.sqrt 2 / 2 * (q - s) ^ (-(1 : ℝ)) * MR := hglobal
          _ ≤ Cearly := by
            dsimp [Cearly]
            gcongr
          _ ≤ Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR := by
            exact le_add_of_nonneg_right
              (mul_nonneg (mul_nonneg hWtheta
                (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)) hHR)
      · have hsWindow : s ∈ Set.Icc (t / 2) t :=
          ⟨le_of_not_ge hsHalf, hst.le⟩
        have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
          hlag htheta0 htheta1 hHR
          (R s).1.continuous.aestronglyMeasurable hf_bound
          (hRholder s hsWindow) (x := x)
        have hexp : -1 + theta / 2 ≤ 0 := by linarith
        have hpow : (q - s) ^ (-1 + theta / 2 : ℝ) ≤
            (t - s) ^ (-1 + theta / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hst) hbaseLag hexp
        calc
          |wholeLineCauchyHeatHessOp (q - s) (R s).1 x| ≤
              Wtheta * (q - s) ^ (-1 + theta / 2 : ℝ) * HR := by
            simpa [Wtheta] using hcancel
          _ ≤ Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR := by
            gcongr
          _ ≤ Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR := by
            exact le_add_of_nonneg_left hCearly
    calc
      |wholeLineCauchyHeatHessOp (q - s) (R s).1 x -
          wholeLineCauchyHeatOp (q - s) (R s).1 x| ≤
          |wholeLineCauchyHeatHessOp (q - s) (R s).1 x| +
            |wholeLineCauchyHeatOp (q - s) (R s).1 x| := abs_sub _ _
      _ ≤ (Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR) + MR :=
        add_le_add hhess hheat
      _ = bound s := rfl
  simpa [R, U] using wholeLineCauchyValueOld_hasDerivWithinAt
    hRcont ht hMR one_pos hRnorm hboundInt hbound

/-- The fixed old part of the divergence Duhamel history is differentiable
from the right at every positive physical time. -/
theorem wholeLineCauchyFluxGradientOld_time_hasDerivWithinAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    HasDerivWithinAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatGradOp (q - s) (F s).1 x)
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 x))
      (Set.Icc t (t + 1)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < t / 2 := by positivity
  have hhalfLe : t / 2 ≤ t := by linarith
  have hstripWindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hhalf.le.trans hs.1, hs.2.trans htT.le⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U hsT]
    exact hstrip ⟨s, hsT⟩ x
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT hhalf hhalfLe htT.le u₀ hsmall
        htheta0 htheta1 heta0 heta1 hrel hstripWindow with
    ⟨rho, HFd, hrho0, hrho1, hHFd, hFdHolder⟩
  let DF : ℝ := HFd + 2 * MF
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  let C3 : ℝ := heatThirdTailConstant
  let CearlyThird : ℝ := C3 * (t / 2) ^ (-(3 / 2 : ℝ)) * MF
  let CearlyGrad : ℝ :=
    (2 / Real.sqrt (4 * Real.pi)) * MF * (t / 2) ^ (-(1 / 2 : ℝ))
  let Wrho : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho
  let bound : ℝ → ℝ := fun s =>
    CearlyThird + CearlyGrad +
      Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd + DF
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hCearlyThird : 0 ≤ CearlyThird := by
    dsimp [CearlyThird]
    positivity
  have hCearlyGrad : 0 ≤ CearlyGrad := by
    dsimp [CearlyGrad]
    positivity
  have hWrho : 0 ≤ Wrho := by
    dsimp [Wrho]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg rho
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) hrho0
    have hscaled := (hk.const_mul Wrho).mul_const HFd
    have hconst : IntervalIntegrable
        (fun _ : ℝ => CearlyThird + CearlyGrad + DF) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, add_assoc, add_left_comm, add_comm, mul_assoc] using
      hconst.add hscaled
  have hbound : ∀ s, 0 < s → s < t → ∀ q ∈ Set.Icc t (t + 1),
      |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x -
        wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤ bound s := by
    intro s hs0 hst q hq
    have hlag : 0 < q - s := sub_pos.mpr (hst.trans_le hq.1)
    have hbaseLag : t - s ≤ q - s := sub_le_sub_right hq.1 s
    have hf_bound : ∀ y, |(F s).1 y| ≤ MF := fun y =>
      (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
    have hthirdGrad :
        |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| +
            |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
          CearlyThird + CearlyGrad +
            Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd + DF := by
      by_cases hsHalf : s ≤ t / 2
      · have hlagHalf : t / 2 ≤ q - s := by linarith
        have hpowThird : (q - s) ^ (-(3 / 2 : ℝ)) ≤
            (t / 2) ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
        have hthirdRaw := wholeLineCauchyHeatThirdOp_abs_le (x := x)
          hlag hMF (F s).1.continuous.aestronglyMeasurable hf_bound
        have hthird : |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| ≤
            CearlyThird := by
          calc
            |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| ≤
                (C3 / ((q - s) * Real.sqrt (q - s))) * MF := by
              simpa [C3] using hthirdRaw
            _ = C3 * (q - s) ^ (-(3 / 2 : ℝ)) * MF := by
              rw [div_eq_mul_inv, ← one_div,
                one_div_mul_sqrt_eq_rpow_neg_three_half hlag]
            _ ≤ CearlyThird := by
              dsimp [CearlyThird]
              gcongr
        have hpowGrad : (q - s) ^ (-(1 / 2 : ℝ)) ≤
            (t / 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
        have hgradRaw := wholeLineCauchyHeatGradOp_norm_le_rpow
          hlag hMF hf_bound x
        have hgrad : |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
            CearlyGrad := by
          rw [Real.norm_eq_abs] at hgradRaw
          calc
            |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
                2 / Real.sqrt (4 * Real.pi) * MF *
                  (q - s) ^ (-(1 / 2 : ℝ)) := hgradRaw
            _ ≤ CearlyGrad := by
              dsimp [CearlyGrad]
              gcongr
        calc
          |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| +
              |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
              CearlyThird + CearlyGrad := add_le_add hthird hgrad
          _ ≤ CearlyThird + CearlyGrad +
              Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd + DF := by
            have hrecent : 0 ≤
                Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd :=
              mul_nonneg (mul_nonneg hWrho
                (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)) hHFd
            linarith
      · have hsWindow : s ∈ Set.Icc (t / 2) t :=
          ⟨le_of_not_ge hsHalf, hst.le⟩
        let zs : Set.Icc (0 : ℝ) T :=
          ⟨s, hs0.le, hst.le.trans htT.le⟩
        have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
          wholeLineBUCTrajectoryExtend_eq hT U zs.2
        have hsStrip : ∀ y, (U zs).1 y ∈ Set.Icc (0 : ℝ) M := hstrip zs
        have hFdDeriv : ∀ y,
            HasDerivAt (F s).1 (deriv (F s).1 y) y := by
          intro y
          have h := wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
            p hM hT u₀ hsmall zs hs0 hsStrip y
          simpa [F, U] using h.differentiableAt.hasDerivAt
        have hFdHold : ∀ y w,
            |deriv (F s).1 y - deriv (F s).1 w| ≤
              HFd * |y - w| ^ rho := by
          intro y w
          simpa [F, U] using hFdHolder s hsWindow y w
        have hFdCont : Continuous (deriv (F s).1) :=
          wholeLineContinuous_of_holder hrho0 hHFd hFdHold
        have hFdBound : ∀ y, |deriv (F s).1 y| ≤ DF := by
          intro y
          exact deriv_abs_le_of_bounded_of_deriv_holder
            hHFd hrho0 hf_bound
            (fun w => (hFdDeriv w).differentiableAt) hFdHold y
        have hthirdEq := wholeLineCauchyHeatThirdOp_eq_hessOp_deriv (x := x)
          hlag hf_bound hFdBound hFdDeriv hFdCont
        have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
          hlag hrho0 hrho1 hHFd
          hFdCont.aestronglyMeasurable hFdBound hFdHold (x := x)
        have hexp : -1 + rho / 2 ≤ 0 := by linarith
        have hpow : (q - s) ^ (-1 + rho / 2 : ℝ) ≤
            (t - s) ^ (-1 + rho / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hst) hbaseLag hexp
        have hthird : |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| ≤
            Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
          rw [hthirdEq]
          calc
            |wholeLineCauchyHeatHessOp (q - s) (deriv (F s).1) x| ≤
                Wrho * (q - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
              simpa [Wrho] using hcancel
            _ ≤ Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
              gcongr
        have hgradEq := wholeLineCauchyHeatGradOp_eq_heatOp_deriv (x := x)
          hlag hf_bound hFdBound hFdDeriv hFdCont
        have hgrad : |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤ DF := by
          rw [hgradEq]
          exact wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
            hFdBound hDF hFdCont.aestronglyMeasurable hlag.le x
        calc
          |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| +
              |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
              Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd + DF :=
            add_le_add hthird hgrad
          _ ≤ CearlyThird + CearlyGrad +
              Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd + DF := by
            linarith
    exact (abs_sub _ _).trans hthirdGrad
  simpa [F, U] using wholeLineCauchyGradientOld_hasDerivWithinAt
    hFcont ht hMF one_pos hFnorm hboundInt hbound

/-- The BUC-valued reaction history evaluates to the scalar history used by
the spatial and time derivative capstones. -/
theorem wholeLineCauchyValueDuhamelBUC_apply_eq_history
    (p : CMParams) {M T q : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hq : 0 < q) (x : ℝ) :
    (wholeLineCauchyValueDuhamelBUC p hM hT U q).1 x =
      wholeLineCauchyValueHistory
        (wholeLineCauchyReactionSourceTrajectory p hM hT U) q x := by
  rw [wholeLineCauchyValueDuhamelBUC_apply p hM hT U hq.le x]
  unfold wholeLineCauchyValueHistory
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume q] with s hne hs
  rw [Set.uIoc_of_le hq.le] at hs
  exact wholeLineCauchyValueBUCIntegrand_apply_eq_of_lt
    p hM hT U (lt_of_le_of_ne hs.2 hne) x

/-- The BUC-valued divergence history evaluates to the scalar history used by
the spatial and time derivative capstones. -/
theorem wholeLineCauchyGradientDuhamelBUC_apply_eq_history
    (p : CMParams) {M T q : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hq : 0 < q) (x : ℝ) :
    (wholeLineCauchyGradientDuhamelBUC p hM hT U q).1 x =
      wholeLineCauchyGradientHistory
        (wholeLineCauchyFluxSourceTrajectory p hM hT U) q x := by
  rw [wholeLineCauchyGradientDuhamelBUC_apply p hM hT U hq.le x]
  unfold wholeLineCauchyGradientHistory
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume q] with s hne hs
  rw [Set.uIoc_of_le hq.le] at hs
  exact wholeLineCauchyGradientBUCIntegrand_apply_eq_of_lt
    p hM hT U (lt_of_le_of_ne hs.2 hne) x

/-- Split the scalar reaction history at an earlier positive time while
retaining the recent window as a BUC-valued integral. -/
theorem wholeLineCauchyValueHistory_eq_old_add_recent
    (p : CMParams) {M T t q : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 < t) (htq : t < q) (x : ℝ) :
    wholeLineCauchyValueHistory
        (wholeLineCauchyReactionSourceTrajectory p hM hT U) q x =
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatOp (q - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 x) +
      (∫ s in t..q,
        wholeLineCauchyValueBUCIntegrand p hM hT U q s).1 x := by
  let G : ℝ → WholeLineBUC :=
    wholeLineCauchyValueBUCIntegrand p hM hT U q
  have hq : 0 < q := ht.trans htq
  have hfull : IntervalIntegrable G volume 0 q :=
    wholeLineCauchyValueBUCIntegrand_intervalIntegrable p hM hT U hq.le
  have hold : IntervalIntegrable G volume 0 t := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le ht.le, Set.uIcc_of_le hq.le]
    exact Set.Icc_subset_Icc_right htq.le
  have hrecent : IntervalIntegrable G volume t q := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le htq.le, Set.uIcc_of_le hq.le]
    exact Set.Icc_subset_Icc_left ht.le
  have holdApply :
      (∫ s in (0 : ℝ)..t, G s).1 x =
        ∫ s in (0 : ℝ)..t,
          wholeLineCauchyHeatOp (q - s)
            (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 x := by
    rw [wholeLineBUC_intervalIntegral_apply hold x]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.le] at hs
    exact wholeLineCauchyValueBUCIntegrand_apply_eq_of_lt
      p hM hT U (hs.2.trans_lt htq) x
  calc
    wholeLineCauchyValueHistory
        (wholeLineCauchyReactionSourceTrajectory p hM hT U) q x =
        (wholeLineCauchyValueDuhamelBUC p hM hT U q).1 x :=
      (wholeLineCauchyValueDuhamelBUC_apply_eq_history
        p hM hT U hq x).symm
    _ = (∫ s in (0 : ℝ)..q, G s).1 x := rfl
    _ = ((∫ s in (0 : ℝ)..t, G s) + ∫ s in t..q, G s).1 x := by
      rw [intervalIntegral.integral_add_adjacent_intervals hold hrecent]
    _ = (∫ s in (0 : ℝ)..t, G s).1 x + (∫ s in t..q, G s).1 x := rfl
    _ = _ := by rw [holdApply]

/-- Split the scalar divergence history at an earlier positive time while
retaining the recent window as a BUC-valued integral. -/
theorem wholeLineCauchyGradientHistory_eq_old_add_recent
    (p : CMParams) {M T t q : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 < t) (htq : t < q) (x : ℝ) :
    wholeLineCauchyGradientHistory
        (wholeLineCauchyFluxSourceTrajectory p hM hT U) q x =
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatGradOp (q - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x) +
      (∫ s in t..q,
        wholeLineCauchyGradientBUCIntegrand p hM hT U q s).1 x := by
  let G : ℝ → WholeLineBUC :=
    wholeLineCauchyGradientBUCIntegrand p hM hT U q
  have hq : 0 < q := ht.trans htq
  have hfull : IntervalIntegrable G volume 0 q :=
    wholeLineCauchyGradientBUCIntegrand_intervalIntegrable p hM hT U hq.le
  have hold : IntervalIntegrable G volume 0 t := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le ht.le, Set.uIcc_of_le hq.le]
    exact Set.Icc_subset_Icc_right htq.le
  have hrecent : IntervalIntegrable G volume t q := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le htq.le, Set.uIcc_of_le hq.le]
    exact Set.Icc_subset_Icc_left ht.le
  have holdApply :
      (∫ s in (0 : ℝ)..t, G s).1 x =
        ∫ s in (0 : ℝ)..t,
          wholeLineCauchyHeatGradOp (q - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x := by
    rw [wholeLineBUC_intervalIntegral_apply hold x]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.le] at hs
    exact wholeLineCauchyGradientBUCIntegrand_apply_eq_of_lt
      p hM hT U (hs.2.trans_lt htq) x
  calc
    wholeLineCauchyGradientHistory
        (wholeLineCauchyFluxSourceTrajectory p hM hT U) q x =
        (wholeLineCauchyGradientDuhamelBUC p hM hT U q).1 x :=
      (wholeLineCauchyGradientDuhamelBUC_apply_eq_history
        p hM hT U hq x).symm
    _ = (∫ s in (0 : ℝ)..q, G s).1 x := rfl
    _ = ((∫ s in (0 : ℝ)..t, G s) + ∫ s in t..q, G s).1 x := by
      rw [intervalIntegral.integral_add_adjacent_intervals hold hrecent]
    _ = (∫ s in (0 : ℝ)..t, G s).1 x + (∫ s in t..q, G s).1 x := rfl
    _ = _ := by rw [holdApply]

/-- The reaction Duhamel history has the correct right derivative at every
strictly interior positive time. -/
theorem wholeLineCauchyReactionValueHistory_time_hasDerivWithinAt_positive
    (p : CMParams) {M T theta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    HasDerivWithinAt
      (fun q : ℝ => wholeLineCauchyValueHistory R q x)
      ((∫ s in (0 : ℝ)..t,
          (wholeLineCauchyHeatHessOp (t - s) (R s).1 x -
            wholeLineCauchyHeatOp (t - s) (R s).1 x)) +
        (R t).1 x)
      (Set.Icc t (t + 1)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let old : ℝ → ℝ := fun q => ∫ s in (0 : ℝ)..t,
    wholeLineCauchyHeatOp (q - s) (R s).1 x
  let S : Set ℝ := Set.Icc t (t + 1)
  change HasDerivWithinAt
    (fun q : ℝ => wholeLineCauchyValueHistory R q x)
    ((∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatHessOp (t - s) (R s).1 x -
          wholeLineCauchyHeatOp (t - s) (R s).1 x)) +
      (R t).1 x) S t
  have hold := wholeLineCauchyReactionValueOld_time_hasDerivWithinAt_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1 x
  change HasDerivWithinAt old
    (∫ s in (0 : ℝ)..t,
      (wholeLineCauchyHeatHessOp (t - s) (R s).1 x -
        wholeLineCauchyHeatOp (t - s) (R s).1 x)) S t at hold
  have holdSlope := hasDerivWithinAt_iff_tendsto_slope.mp hold
  have hrecentBUC := wholeLineCauchyValueRecentAverage_tendsto
    p hM hT U ht
  have heval : Tendsto (wholeLineBUCEvalCLM x) (𝓝 (R t)) (𝓝 ((R t).1 x)) :=
    (wholeLineBUCEvalCLM x).continuous.continuousAt
  have hrecentH : Tendsto
      (fun h : ℝ => wholeLineBUCEvalCLM x
        (h⁻¹ • ∫ s in t..(t + h),
          wholeLineCauchyValueBUCIntegrand p hM hT U (t + h) s))
      (𝓝[>] (0 : ℝ)) (𝓝 ((R t).1 x)) := by
    exact heval.comp hrecentBUC
  have hsub : Tendsto (fun q : ℝ => q - t)
      (𝓝[S \ {t}] t) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        ((continuousAt_id.sub continuousAt_const).mono_left inf_le_left :
          Tendsto (fun q : ℝ => q - t) (𝓝[S \ {t}] t) (𝓝 (t - t)))
    · filter_upwards [self_mem_nhdsWithin] with q hq
      have hne : q ≠ t := by simpa using hq.2
      exact sub_pos.mpr (lt_of_le_of_ne hq.1.1 hne.symm)
  have hrecentQ : Tendsto
      (fun q : ℝ => wholeLineBUCEvalCLM x
        ((q - t)⁻¹ • ∫ s in t..q,
          wholeLineCauchyValueBUCIntegrand p hM hT U q s))
      (𝓝[S \ {t}] t) (𝓝 ((R t).1 x)) := by
    have haddsub : ∀ q : ℝ, t + (q - t) = q := by intro q; ring
    have hfun :
        (fun q : ℝ => wholeLineBUCEvalCLM x
          ((q - t)⁻¹ • ∫ s in t..q,
            wholeLineCauchyValueBUCIntegrand p hM hT U q s)) =
        (fun h : ℝ => wholeLineBUCEvalCLM x
          (h⁻¹ • ∫ s in t..(t + h),
            wholeLineCauchyValueBUCIntegrand p hM hT U (t + h) s)) ∘
          (fun q : ℝ => q - t) := by
      funext q
      simp only [Function.comp_apply, haddsub]
    rw [hfun]
    exact hrecentH.comp hsub
  have hadd := holdSlope.add hrecentQ
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine Tendsto.congr' ?_ hadd
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hne : q ≠ t := by simpa using hq.2
  have htq : t < q := lt_of_le_of_ne hq.1.1 hne.symm
  have hsplit := wholeLineCauchyValueHistory_eq_old_add_recent
    p hM hT U ht htq x
  rw [slope_def_module, slope_def_module, hsplit]
  have htold : wholeLineCauchyValueHistory R t x = old t := rfl
  rw [htold]
  change (q - t)⁻¹ * (old q - old t) +
      (q - t)⁻¹ * (∫ s in t..q,
        wholeLineCauchyValueBUCIntegrand p hM hT U q s).1 x =
    (q - t)⁻¹ *
      ((old q + (∫ s in t..q,
        wholeLineCauchyValueBUCIntegrand p hM hT U q s).1 x) - old t)
  ring

/-- The divergence Duhamel history has the correct right derivative at every
strictly interior positive time. -/
theorem wholeLineCauchyFluxGradientHistory_time_hasDerivWithinAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    HasDerivWithinAt
      (fun q : ℝ => wholeLineCauchyGradientHistory F q x)
      ((∫ s in (0 : ℝ)..t,
          (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
            wholeLineCauchyHeatGradOp (t - s) (F s).1 x)) +
        deriv (F t).1 x)
      (Set.Icc t (t + 1)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let old : ℝ → ℝ := fun q => ∫ s in (0 : ℝ)..t,
    wholeLineCauchyHeatGradOp (q - s) (F s).1 x
  let S : Set ℝ := Set.Icc t (t + 1)
  change HasDerivWithinAt
    (fun q : ℝ => wholeLineCauchyGradientHistory F q x)
    ((∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 x)) +
      deriv (F t).1 x) S t
  have hold := wholeLineCauchyFluxGradientOld_time_hasDerivWithinAt_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  change HasDerivWithinAt old
    (∫ s in (0 : ℝ)..t,
      (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
        wholeLineCauchyHeatGradOp (t - s) (F s).1 x)) S t at hold
  have holdSlope := hasDerivWithinAt_iff_tendsto_slope.mp hold
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
  let Dt := wholeLineCauchyFluxDerivativeBUCPositive p hM hT u₀ hsmall zt ht
    htheta0 htheta1 heta0 heta1 hrel (hstrip zt)
  have hrecentBUC : Tendsto
      (fun h : ℝ => h⁻¹ • ∫ s in t..(t + h),
        wholeLineCauchyGradientBUCIntegrand p hM hT U (t + h) s)
      (𝓝[>] (0 : ℝ)) (𝓝 Dt) := by
    simpa [U, zt, Dt] using
      wholeLineCauchyGradientRecentAverage_tendsto_fixedPoint
        p hM hT u₀ hsmall ht htT htheta0 htheta1
          heta0 heta1 hrel hstrip
  have hDt : Dt.1 x = deriv (F t).1 x := by
    simp [Dt, F, U, zt]
  have heval : Tendsto (wholeLineBUCEvalCLM x) (𝓝 Dt) (𝓝 (Dt.1 x)) :=
    (wholeLineBUCEvalCLM x).continuous.continuousAt
  have hrecentH : Tendsto
      (fun h : ℝ => wholeLineBUCEvalCLM x
        (h⁻¹ • ∫ s in t..(t + h),
          wholeLineCauchyGradientBUCIntegrand p hM hT U (t + h) s))
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv (F t).1 x)) := by
    simpa [hDt] using heval.comp hrecentBUC
  have hsub : Tendsto (fun q : ℝ => q - t)
      (𝓝[S \ {t}] t) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        ((continuousAt_id.sub continuousAt_const).mono_left inf_le_left :
          Tendsto (fun q : ℝ => q - t) (𝓝[S \ {t}] t) (𝓝 (t - t)))
    · filter_upwards [self_mem_nhdsWithin] with q hq
      have hne : q ≠ t := by simpa using hq.2
      exact sub_pos.mpr (lt_of_le_of_ne hq.1.1 hne.symm)
  have hrecentQ : Tendsto
      (fun q : ℝ => wholeLineBUCEvalCLM x
        ((q - t)⁻¹ • ∫ s in t..q,
          wholeLineCauchyGradientBUCIntegrand p hM hT U q s))
      (𝓝[S \ {t}] t) (𝓝 (deriv (F t).1 x)) := by
    have haddsub : ∀ q : ℝ, t + (q - t) = q := by intro q; ring
    have hfun :
        (fun q : ℝ => wholeLineBUCEvalCLM x
          ((q - t)⁻¹ • ∫ s in t..q,
            wholeLineCauchyGradientBUCIntegrand p hM hT U q s)) =
        (fun h : ℝ => wholeLineBUCEvalCLM x
          (h⁻¹ • ∫ s in t..(t + h),
            wholeLineCauchyGradientBUCIntegrand p hM hT U (t + h) s)) ∘
          (fun q : ℝ => q - t) := by
      funext q
      simp only [Function.comp_apply, haddsub]
    rw [hfun]
    exact hrecentH.comp hsub
  have hadd := holdSlope.add hrecentQ
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine Tendsto.congr' ?_ hadd
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hne : q ≠ t := by simpa using hq.2
  have htq : t < q := lt_of_le_of_ne hq.1.1 hne.symm
  have hsplit := wholeLineCauchyGradientHistory_eq_old_add_recent
    p hM hT U ht htq x
  rw [slope_def_module, slope_def_module, hsplit]
  have htold : wholeLineCauchyGradientHistory F t x = old t := rfl
  rw [htold]
  change (q - t)⁻¹ * (old q - old t) +
      (q - t)⁻¹ * (∫ s in t..q,
        wholeLineCauchyGradientBUCIntegrand p hM hT U q s).1 x =
    (q - t)⁻¹ *
      ((old q + (∫ s in t..q,
        wholeLineCauchyGradientBUCIntegrand p hM hT U q s).1 x) - old t)
  ring

/-- The flux third-kernel history is genuinely interval-integrable at every
strictly interior positive time.  The recent half-window uses Gaussian
integration by parts and the common Holder modulus of the flux derivative. -/
theorem wholeLineCauchyFluxThirdHistory_intervalIntegrable_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)
      volume 0 t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < t / 2 := by positivity
  have hhalfLe : t / 2 ≤ t := by linarith
  have hstripWindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hhalf.le.trans hs.1, hs.2.trans htT.le⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U hsT]
    exact hstrip ⟨s, hsT⟩ x
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT hhalf hhalfLe htT.le u₀ hsmall
        htheta0 htheta1 heta0 heta1 hrel hstripWindow with
    ⟨rho, HFd, hrho0, hrho1, hHFd, hFdHolder⟩
  let DF : ℝ := HFd + 2 * MF
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  let C3 : ℝ := heatThirdTailConstant
  let Cearly : ℝ := C3 * (t / 2) ^ (-(3 / 2 : ℝ)) * MF
  let Wrho : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
  have hWrho : 0 ≤ Wrho := by
    dsimp [Wrho]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg rho
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) hrho0
    have hscaled := (hk.const_mul Wrho).mul_const HFd
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  have hbound : ∀ s, 0 ≤ s → s < t →
      ‖wholeLineCauchyHeatThirdOp (t - s) (F s).1 x‖ ≤ bound s := by
    intro s hs0 hst
    have hlag : 0 < t - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ t / 2
    · have hlagHalf : t / 2 ≤ t - s := by linarith
      have hpow : (t - s) ^ (-(3 / 2 : ℝ)) ≤
          (t / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hraw := wholeLineCauchyHeatThirdOp_abs_le
        hlag hMF (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s))
        (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatThirdOp (t - s) (F s).1 x| ≤
            (C3 / ((t - s) * Real.sqrt (t - s))) * MF := by
          simpa [C3] using hraw
        _ = C3 * (t - s) ^ (-(3 / 2 : ℝ)) * MF := by
          rw [div_eq_mul_inv, ← one_div,
            one_div_mul_sqrt_eq_rpow_neg_three_half hlag]
        _ ≤ Cearly := by
          dsimp [Cearly]
          gcongr
        _ ≤ bound s := by
          dsimp [bound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hWrho
              (Real.rpow_nonneg hlag.le _)) hHFd)
    · have hsWindow : s ∈ Set.Icc (t / 2) t :=
        ⟨le_of_not_ge hsHalf, hst.le⟩
      have hspos : 0 < s := hhalf.trans_le hsWindow.1
      let zs : Set.Icc (0 : ℝ) T :=
        ⟨s, hspos.le, hst.le.trans htT.le⟩
      have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT U zs.2
      have hsStrip : ∀ y, (U zs).1 y ∈ Set.Icc (0 : ℝ) M := hstrip zs
      have hFdDeriv : ∀ y, HasDerivAt (F s).1 (deriv (F s).1 y) y := by
        intro y
        have h := wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
          p hM hT u₀ hsmall zs hspos hsStrip y
        simpa [F, U] using h.differentiableAt.hasDerivAt
      have hFdHold : ∀ y w,
          |deriv (F s).1 y - deriv (F s).1 w| ≤
            HFd * |y - w| ^ rho := by
        intro y w
        simpa [F, U] using hFdHolder s hsWindow y w
      have hFdCont : Continuous (deriv (F s).1) :=
        wholeLineContinuous_of_holder hrho0 hHFd hFdHold
      have hFbound : ∀ y, |(F s).1 y| ≤ MF := by
        intro y
        exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
      have hFdBound : ∀ y, |deriv (F s).1 y| ≤ DF := by
        intro y
        exact deriv_abs_le_of_bounded_of_deriv_holder
          hHFd hrho0 hFbound
          (fun w => (hFdDeriv w).differentiableAt) hFdHold y
      have hthirdEq := wholeLineCauchyHeatThirdOp_eq_hessOp_deriv
        (f := (F s).1) (x := x) hlag hFbound hFdBound hFdDeriv hFdCont
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag hrho0 hrho1 hHFd hFdCont.aestronglyMeasurable
        hFdBound hFdHold (x := x)
      rw [Real.norm_eq_abs, hthirdEq]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (deriv (F s).1) x| ≤
            Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
          simpa [Wrho] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith
  change IntervalIntegrable
    (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
    volume 0 t
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
    (g := bound) hboundInt
    (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable
      hFcont t x).restrict ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards with s hs
  rw [Set.uIoc_of_le ht.le] at hs
  rcases lt_or_eq_of_le hs.2 with hst | rfl
  · exact hbound s hs.1.le hst
  · rw [sub_self, wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos le_rfl]
    simp only [norm_zero]
    dsimp [bound]
    exact add_nonneg hCearly
      (mul_nonneg (mul_nonneg hWrho
        (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)) hHFd)

/-- The reaction Hessian history is genuinely interval-integrable at every
strictly interior positive time. -/
theorem wholeLineCauchyReactionHessianHistory_intervalIntegrable_positive
    (p : CMParams) {M T theta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (x : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s)
        (wholeLineCauchyReactionSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)
      volume 0 t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < t / 2 := by positivity
  rcases exists_wholeLineCauchyReactionSourceTrajectory_window_Ctheta
      p hM hT hhalf htT.le u₀ hsmall htheta0 htheta1 with
    ⟨HR, hHR, hRholder⟩
  let Cearly : ℝ :=
    (5 * Real.sqrt 2 / 2) * (t / 2) ^ (-(1 : ℝ)) * MR
  let Wtheta : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR
  have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
  have hWtheta : 0 ≤ Wtheta := by
    dsimp [Wtheta]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0
    have hscaled := (hk.const_mul Wtheta).mul_const HR
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  have hbound : ∀ s, 0 ≤ s → s < t →
      ‖wholeLineCauchyHeatHessOp (t - s) (R s).1 x‖ ≤ bound s := by
    intro s hs0 hst
    have hlag : 0 < t - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ t / 2
    · have hlagHalf : t / 2 ≤ t - s := by linarith
      have hpow : (t - s) ^ (-(1 : ℝ)) ≤
          (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hglobal := wholeLineCauchyHeatHessOp_abs_le
        hlag hMR (R s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (R s) y).trans (hRnorm s))
        (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (R s).1 x| ≤
            ((5 * Real.sqrt 2 / 2) * (t - s) ^ (-(1 : ℝ))) * MR := hglobal
        _ ≤ Cearly := by
          dsimp [Cearly]
          gcongr
        _ ≤ bound s := by
          dsimp [bound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hWtheta
              (Real.rpow_nonneg hlag.le _)) hHR)
    · have hsWindow : s ∈ Set.Icc (t / 2) t :=
        ⟨le_of_not_ge hsHalf, hst.le⟩
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag htheta0 htheta1 hHR
        (R s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (R s) y).trans (hRnorm s))
        (hRholder s hsWindow) (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (R s).1 x| ≤
            Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * HR := by
          simpa [Wtheta] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith
  change IntervalIntegrable
    (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
    volume 0 t
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
    (g := bound) hboundInt
    (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable
      hRcont t x).restrict ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards with s hs
  rw [Set.uIoc_of_le ht.le] at hs
  rcases lt_or_eq_of_le hs.2 with hst | rfl
  · exact hbound s hs.1.le hst
  · rw [sub_self, wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl]
    simp only [norm_zero]
    dsimp [bound]
    exact add_nonneg hCearly
      (mul_nonneg (mul_nonneg hWtheta
        (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)) hHR)

/-- All four positive-time source histories needed for generator cancellation
are genuinely interval-integrable. -/
theorem wholeLineCauchy_actualSource_generator_intervalIntegrable_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x)
        volume 0 t ∧
      IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
        volume 0 t ∧
      IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatOp (t - s) (R s).1 x)
        volume 0 t ∧
      IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
        volume 0 t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hgrad := wholeLineCauchyGradientHistory_intervalIntegrable
    hFcont ht hMF hFnorm x
  have hthird := wholeLineCauchyFluxThirdHistory_intervalIntegrable_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  have hvalue := wholeLineCauchyValueHistory_intervalIntegrable
    hRcont ht hMR hRnorm x
  have hhess := wholeLineCauchyReactionHessianHistory_intervalIntegrable_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1 x
  change IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x)
      volume 0 t ∧
    IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
      volume 0 t ∧
    IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatOp (t - s) (R s).1 x)
      volume 0 t ∧
    IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
      volume 0 t
  exact ⟨hgrad, hthird, hvalue, hhess⟩

/-- The canonical clamped fixed point has the expected right time derivative
at every strictly interior positive time.  The terminal contributions are the
current shifted reaction and the current spatial derivative of the flux. -/
theorem wholeLineCauchyBUCMildFixedPoint_time_hasDerivWithinAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    HasDerivWithinAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
      ((wholeLineCauchyHeatHessOp t u₀.1 x -
          wholeLineCauchyHeatOp t u₀.1 x) +
        (-p.χ) * ((∫ s in (0 : ℝ)..t,
          (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
            wholeLineCauchyHeatGradOp (t - s) (F s).1 x)) +
          deriv (F t).1 x) +
        ((∫ s in (0 : ℝ)..t,
          (wholeLineCauchyHeatHessOp (t - s) (R s).1 x -
            wholeLineCauchyHeatOp (t - s) (R s).1 x)) +
          (R t).1 x))
      (Set.Icc t (min (t + 1) T)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let S : Set ℝ := Set.Icc t (min (t + 1) T)
  have hu₀bound : ∀ y, |u₀.1 y| ≤ ‖u₀‖ := fun y =>
    WholeLineBUC.abs_apply_le_norm u₀ y
  have hheat := wholeLineCauchyHeatOp_time_hasDerivAt
    ht (norm_nonneg u₀) u₀.1.continuous.aestronglyMeasurable hu₀bound x
  have hflux := wholeLineCauchyFluxGradientHistory_time_hasDerivWithinAt_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  have hreaction :=
    wholeLineCauchyReactionValueHistory_time_hasDerivWithinAt_positive
      p hM hT u₀ hsmall ht htT htheta0 htheta1 x
  have hSsub : S ⊆ Set.Icc t (t + 1) := by
    dsimp [S]
    exact Set.Icc_subset_Icc le_rfl (min_le_left _ _)
  have hfluxS := hflux.mono hSsub
  have hreactionS := hreaction.mono hSsub
  have hheatS : HasDerivWithinAt
      (fun q : ℝ => wholeLineCauchyHeatOp q u₀.1 x)
      (wholeLineCauchyHeatHessOp t u₀.1 x -
        wholeLineCauchyHeatOp t u₀.1 x) S t :=
    hheat.hasDerivWithinAt
  have hrhs :=
    (hheatS.add (hfluxS.const_mul (-p.χ))).add hreactionS
  have heq : ∀ q ∈ S,
      (wholeLineBUCTrajectoryExtend hT U q).1 x =
        wholeLineCauchyHeatOp q u₀.1 x +
          (-p.χ) * wholeLineCauchyGradientHistory F q x +
          wholeLineCauchyValueHistory R q x := by
    intro q hq
    have hq0 : 0 < q := ht.trans_le hq.1
    have hqT : q ≤ T := hq.2.trans (min_le_right _ _)
    let zq : Set.Icc (0 : ℝ) T := ⟨q, hq0.le, hqT⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U zq.2]
    simpa [U, F, R, zq] using
      wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
        p hM hT u₀ hsmall zq x hq0
  change HasDerivWithinAt
    (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x) _ S t
  exact hrhs.congr heq (heq t ⟨le_rfl, le_min
    (le_add_of_nonneg_right zero_le_one) htT.le⟩)

/-- Generator cancellation identifies the canonical fixed point's right time
derivative with its spatial second derivative, shifted reaction, and flux
divergence. -/
theorem wholeLineCauchyBUCMildFixedPoint_right_generator_pde
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    HasDerivWithinAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
      (deriv (fun xi : ℝ => deriv (fun w : ℝ => (U zt).1 w) xi) x -
        (U zt).1 x + (-p.χ) * deriv (F t).1 x + (R t).1 x)
      (Set.Icc t (min (t + 1) T)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
  let S : Set ℝ := Set.Icc t (min (t + 1) T)
  have htime := wholeLineCauchyBUCMildFixedPoint_time_hasDerivWithinAt_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  change HasDerivWithinAt
    (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
    ((wholeLineCauchyHeatHessOp t u₀.1 x -
        wholeLineCauchyHeatOp t u₀.1 x) +
      (-p.χ) * ((∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 x)) +
        deriv (F t).1 x) +
      ((∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatHessOp (t - s) (R s).1 x -
          wholeLineCauchyHeatOp (t - s) (R s).1 x)) +
        (R t).1 x)) S t at htime
  have hstripWindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ y,
      (wholeLineBUCTrajectoryExtend hT U s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hs0 : 0 ≤ s := (half_pos ht).le.trans hs.1
    have hsT : s ≤ T := hs.2.trans htT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U zs.2]
    exact hstrip zs y
  have hspace :=
    (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
      p hM hT u₀ hsmall zt ht htheta0 htheta1
        heta0 heta1 hrel hstripWindow x).deriv
  change deriv (fun xi : ℝ => deriv (fun w : ℝ => (U zt).1 w) xi) x =
    wholeLineCauchyHeatHessOp t u₀.1 x +
      (-p.χ) * (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) +
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (R s).1 x) at hspace
  have hfix := wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
    p hM hT u₀ hsmall zt x ht
  change (U zt).1 x = wholeLineCauchyHeatOp t u₀.1 x +
      (-p.χ) * wholeLineCauchyGradientHistory F t x +
      wholeLineCauchyValueHistory R t x at hfix
  rcases wholeLineCauchy_actualSource_generator_intervalIntegrable_positive
      p hM hT u₀ hsmall ht htT htheta0 htheta1
        heta0 heta1 hrel hstrip x with
    ⟨hgrad, hthird, hvalue, hhess⟩
  unfold wholeLineCauchyGradientHistory wholeLineCauchyValueHistory at hfix
  rw [intervalIntegral.integral_sub hthird hgrad,
    intervalIntegral.integral_sub hhess hvalue] at htime
  have hgenerator :
      (wholeLineCauchyHeatHessOp t u₀.1 x -
          wholeLineCauchyHeatOp t u₀.1 x) +
        (-p.χ) * ((∫ s in (0 : ℝ)..t,
          wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) -
          (∫ s in (0 : ℝ)..t,
            wholeLineCauchyHeatGradOp (t - s) (F s).1 x) +
          deriv (F t).1 x) +
        ((∫ s in (0 : ℝ)..t,
          wholeLineCauchyHeatHessOp (t - s) (R s).1 x) -
          (∫ s in (0 : ℝ)..t,
            wholeLineCauchyHeatOp (t - s) (R s).1 x) +
          (R t).1 x) =
      deriv (fun xi : ℝ => deriv (fun w : ℝ => (U zt).1 w) xi) x -
        (U zt).1 x + (-p.χ) * deriv (F t).1 x + (R t).1 x := by
    rw [hspace, hfix]
    ring
  rw [hgenerator] at htime
  exact htime

/-- On a physical strip, the canonical fixed point satisfies the original
parabolic equation from the right at every strictly interior positive time. -/
theorem wholeLineCauchyBUCMildFixedPoint_right_physical_pde
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    HasDerivWithinAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
      (deriv (fun xi : ℝ => deriv (fun w : ℝ => (U zt).1 w) xi) x -
        p.χ * deriv (wholeLineChemotaxisFlux p (U zt).1) x +
        wholeLineLogisticSource p (U zt).1 x)
      (Set.Icc t (min (t + 1) T)) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
  have hpde := wholeLineCauchyBUCMildFixedPoint_right_generator_pde
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  change HasDerivWithinAt
    (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
    (deriv (fun xi : ℝ => deriv (fun w : ℝ => (U zt).1 w) xi) x -
      (U zt).1 x + (-p.χ) * deriv (F t).1 x + (R t).1 x)
    (Set.Icc t (min (t + 1) T)) t at hpde
  have hext : wholeLineBUCTrajectoryExtend hT U t = U zt :=
    wholeLineBUCTrajectoryExtend_eq hT U zt.2
  have hfluxEq : (F t).1 = wholeLineChemotaxisFlux p (U zt).1 := by
    funext y
    simpa [F, wholeLineCauchyFluxSourceTrajectory, hext] using congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM (hstrip zt)) y
  have hreactionEq : (R t).1 = wholeLineCauchyShiftedReaction p (U zt).1 := by
    funext y
    simpa [R, wholeLineCauchyReactionSourceTrajectory, hext] using congrFun
      (wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM (hstrip zt)) y
  rw [hfluxEq, hreactionEq] at hpde
  convert hpde using 1
  simp only [wholeLineCauchyShiftedReaction]
  ring

section WholeLineCauchyPositivePDEAxiomAudit

#print axioms wholeLineCauchyValueOld_hasDerivWithinAt
#print axioms wholeLineCauchyGradientOld_hasDerivWithinAt
#print axioms wholeLineCauchyReactionValueOld_time_hasDerivWithinAt_positive
#print axioms wholeLineCauchyFluxGradientOld_time_hasDerivWithinAt_positive
#print axioms wholeLineCauchyValueDuhamelBUC_apply_eq_history
#print axioms wholeLineCauchyGradientDuhamelBUC_apply_eq_history
#print axioms wholeLineCauchyValueHistory_eq_old_add_recent
#print axioms wholeLineCauchyGradientHistory_eq_old_add_recent
#print axioms wholeLineCauchyReactionValueHistory_time_hasDerivWithinAt_positive
#print axioms wholeLineCauchyFluxGradientHistory_time_hasDerivWithinAt_positive
#print axioms wholeLineCauchyFluxThirdHistory_intervalIntegrable_positive
#print axioms wholeLineCauchyReactionHessianHistory_intervalIntegrable_positive
#print axioms wholeLineCauchy_actualSource_generator_intervalIntegrable_positive
#print axioms wholeLineCauchyBUCMildFixedPoint_time_hasDerivWithinAt_positive
#print axioms wholeLineCauchyBUCMildFixedPoint_right_generator_pde
#print axioms wholeLineCauchyBUCMildFixedPoint_right_physical_pde

end WholeLineCauchyPositivePDEAxiomAudit

end ShenWork.Paper1
