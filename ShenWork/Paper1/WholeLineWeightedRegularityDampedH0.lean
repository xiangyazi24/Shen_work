import ShenWork.Paper1.WholeLineWeightedRegularityCanonicalH0
import ShenWork.PDE.RestartedMildSmoothing

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

/-!
# Finite-horizon weighted H0 by time damping

The cap kernel has an integrable inverse-square-root singularity.  On a long
finite window its undamped mass need not be smaller than one.  Multiplication
of the scalar history by `exp (-lambda * t)` inserts a positive spectral gap
in elapsed time.  The Gamma-integral infrastructure in
`PDE.RestartedMildSmoothing` then makes that damped mass arbitrarily small.
-/

/-- A common nonnegative coefficient majorizes the regular and singular
parts of the cap kernel. -/
def capMildKernelCommonConstant
    (p : CMParams) (M eta c T : ℝ) : ℝ :=
  max (capMildKernelConstant p M eta c T)
    (capMildKernelInvSqrtConstant p M eta c T)

/-- The explicit scalar radius for the exponentially damped Volterra ball. -/
def capMildDampedBallRadius
    (p : CMParams) (M T eta c B₀ lambda : ℝ) : ℝ :=
  (2 * capMildGrowthBound eta c T * B₀) /
    (1 - ShenWork.PDE.restartedKernelMassPositive
      (capMildKernelCommonConstant p M eta c T)
      (1 / 2 : ℝ) lambda)

theorem capMildKernelCommonConstant_nonneg
    (p : CMParams) {M eta c T : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta) (hT : 0 ≤ T) :
    0 ≤ capMildKernelCommonConstant p M eta c T := by
  exact (capMildKernelConstant_nonneg p hM heta hT c).trans
    (le_max_left _ _)

/-- The positive-gap Gamma mass of the common cap kernel tends to zero as
the artificial time-damping rate tends to infinity. -/
theorem tendsto_capMildDampedKernelMass_atTop_zero
    (C : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        ShenWork.PDE.restartedKernelMassPositive C (1 / 2 : ℝ) lambda)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun lambda : ℝ => 1 / lambda) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun lambda : ℝ => lambda⁻¹) atTop (nhds 0))
  have hrpow : Tendsto (fun lambda : ℝ => lambda ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only using tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))
  have hconst : Tendsto (fun _ : ℝ => C) atTop (nhds C) :=
    tendsto_const_nhds
  unfold ShenWork.PDE.restartedKernelMassPositive
  simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    zero_add, zero_mul, add_zero, mul_zero] using
    (hconst.mul
      (hinv.add (hrpow.mul_const (Real.Gamma (1 / 2 : ℝ)))))

/-- A positive artificial damping rate can always be chosen so that the
common cap-kernel mass is strictly below one. -/
theorem exists_pos_capMildDampedKernelMass_lt_one
    (C : ℝ) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ShenWork.PDE.restartedKernelMassPositive
        C (1 / 2 : ℝ) lambda < 1 := by
  have hlim := tendsto_capMildDampedKernelMass_atTop_zero C
  have hlt : ∀ᶠ lambda in atTop,
      ShenWork.PDE.restartedKernelMassPositive
        C (1 / 2 : ℝ) lambda < 1 :=
    (tendsto_order.1 hlim).2 _ zero_lt_one
  have hboth : ∀ᶠ lambda in atTop,
      ShenWork.PDE.restartedKernelMassPositive
          C (1 / 2 : ℝ) lambda < 1 ∧ 0 < lambda :=
    hlt.and (eventually_gt_atTop (0 : ℝ))
  rcases hboth.exists with ⟨lambda, hlambda, hpos⟩
  exact ⟨lambda, hpos, hlambda⟩

/-- Exponentially growing histories see only the positive-gap Gamma mass of
the elapsed-time cap kernel. -/
theorem intervalIntegral_capKernel_mul_exp_le_dampedMass
    {C0 C1 lambda t : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hlambda : 0 < lambda)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        (C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ))) *
          Real.exp (lambda * s)) ≤
      Real.exp (lambda * t) *
        ShenWork.PDE.restartedKernelMassPositive
          (max C0 C1) (1 / 2 : ℝ) lambda := by
  let base : ℝ → ℝ := fun r =>
    (C0 + C1 * r ^ (-(1 / 2 : ℝ))) * Real.exp (-lambda * r)
  let major : ℝ → ℝ :=
    ShenWork.PDE.restartedSmoothingKernel
      (max C0 C1) (1 / 2 : ℝ) lambda
  have hcommon : 0 ≤ max C0 C1 := hC0.trans (le_max_left _ _)
  have hbaseInt : IntervalIntegrable base volume 0 t := by
    have hpow : IntervalIntegrable
        (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) volume 0 t :=
      ShenWork.PDE.rpow_neg_intervalIntegrable (by norm_num)
    have hkernel : IntervalIntegrable
        (fun r : ℝ => C0 + C1 * r ^ (-(1 / 2 : ℝ))) volume 0 t :=
      intervalIntegral.intervalIntegrable_const.add (hpow.const_mul C1)
    exact hkernel.mul_continuousOn (by fun_prop)
  have hmajorInt : IntervalIntegrable major volume 0 t := by
    simpa only [major] using
      (ShenWork.PDE.restartedSmoothingKernel_intervalIntegrable_positive
        (C := max C0 C1) (theta := (1 / 2 : ℝ))
        (nu := lambda) (T := t) (by norm_num) (by norm_num) hlambda ht)
  have hpoint : ∀ r ∈ Set.Icc (0 : ℝ) t, base r ≤ major r := by
    intro r hr
    have hrpow : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr.1 _
    have hcoef : C0 + C1 * r ^ (-(1 / 2 : ℝ)) ≤
        max C0 C1 * (1 + r ^ (-(1 / 2 : ℝ))) := by
      calc
        C0 + C1 * r ^ (-(1 / 2 : ℝ)) ≤
            max C0 C1 + max C0 C1 * r ^ (-(1 / 2 : ℝ)) :=
          add_le_add (le_max_left _ _)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hrpow)
        _ = max C0 C1 * (1 + r ^ (-(1 / 2 : ℝ))) := by ring
    dsimp only [base, major, ShenWork.PDE.restartedSmoothingKernel]
    exact mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
  have hbase_le : (∫ r in (0 : ℝ)..t, base r) ≤
      ShenWork.PDE.restartedKernelMassPositive
        (max C0 C1) (1 / 2 : ℝ) lambda := by
    calc
      (∫ r in (0 : ℝ)..t, base r) ≤
          ∫ r in (0 : ℝ)..t, major r :=
        intervalIntegral.integral_mono_on ht hbaseInt hmajorInt hpoint
      _ ≤ ShenWork.PDE.restartedKernelMassPositive
          (max C0 C1) (1 / 2 : ℝ) lambda := by
        simpa only [major] using
          (ShenWork.PDE.restartedSmoothingKernel_integral_le_positive
            hcommon (by norm_num : 0 < (1 / 2 : ℝ))
              (by norm_num : (1 / 2 : ℝ) < 1) hlambda ht)
  have hrewrite :
      (∫ s in (0 : ℝ)..t,
          (C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ))) *
            Real.exp (lambda * s)) =
        Real.exp (lambda * t) * ∫ r in (0 : ℝ)..t, base r := by
    have hchange :
        (∫ s in (0 : ℝ)..t, base (t - s)) =
          ∫ r in (0 : ℝ)..t, base r := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := t) base t)
    calc
      (∫ s in (0 : ℝ)..t,
          (C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ))) *
            Real.exp (lambda * s)) =
          ∫ s in (0 : ℝ)..t,
            Real.exp (lambda * t) * base (t - s) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        dsimp only [base]
        rw [show lambda * s = lambda * t + (-lambda * (t - s)) by ring,
          Real.exp_add]
        ring
      _ = Real.exp (lambda * t) *
          ∫ s in (0 : ℝ)..t, base (t - s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.exp (lambda * t) *
          ∫ r in (0 : ℝ)..t, base r := by rw [hchange]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hbase_le (Real.exp_nonneg _)

/-! ## The concrete one-step estimate retaining a variable history -/

/-- Variant of the canonical history producer which retains the actual
time-dependent scalar majorant in the final Volterra integral.  The extra
constant `B` is used only for Bochner integrability of the concrete source
histories; it does not replace `r s` in the output estimate. -/
theorem exists_capWeighted_coMoving_bucMildMap_differenceL2_of_variable_cap_history
    (p : CMParams) {M T eta R c B₀ B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (U₂ U₁ : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (hr : ∀ s, s < z.1 → 0 ≤ r s)
    (hr_closed : ∀ s ∈ Set.Icc (0 : ℝ) z.1, 0 ≤ r s)
    (hr_int : IntervalIntegrable r volume 0 z.1)
    (hkr_int : IntervalIntegrable
      (fun s : ℝ => (z.1 - s) ^ (-(1 / 2 : ℝ)) * r s)
      volume 0 z.1)
    (hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) z.1, s < z.1 → r s ≤ B) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1
              (x + c * z.1) -
            (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1
              (x + c * z.1))) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c T * B₀ +
        ∫ s in (0 : ℝ)..z.1,
          (capMildKernelConstant p M eta c T +
            capMildKernelInvSqrtConstant p M eta c T *
              (z.1 - s) ^ (-(1 / 2 : ℝ))) * r s := by
  let FG := capWeightedPicardChemotaxisBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ z.1
  let hFG2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
    p hM hT heta heta_one U₂ U₁ hr hclose henergy
  let ZG := wholeLineRealL2Section
    (fun s x => (FG s).1 x)
    (fun s => (FG s).1.continuous.aestronglyMeasurable)
    hFG2
  let FR := capWeightedPicardReactionBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ z.1
  let hFR2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
    p hM hT heta U₂ U₁ hr hclose henergy
  let ZR := wholeLineRealL2Section
    (fun s x => (FR s).1 x)
    (fun s => (FR s).1.continuous.aestronglyMeasurable)
    hFR2
  let CG0 : ℝ := 2 * capMildGrowthBound eta c T * eta *
    Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)
  let CR0 : ℝ := 2 * capMildGrowthBound eta c T *
    (1 + reactionLip p.α M)
  let C1 : ℝ := capMildKernelInvSqrtConstant p M eta c T
  let gG : ℝ → ℝ := fun s =>
    (CG0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ))) * r s
  let gR : ℝ → ℝ := fun s => CR0 * r s
  have hCG0 : 0 ≤ CG0 := by
    dsimp [CG0, capMildGrowthBound]
    unfold capWeightedChemotaxisOperatorSquareConstant
      capWeightedFluxSquareConstant
    positivity
  have hCR0 : 0 ≤ CR0 := by
    dsimp [CR0, capMildGrowthBound]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (add_nonneg zero_le_one (reactionLip_nonneg p.hα hM))
  have hC1 : 0 ≤ C1 :=
    capMildKernelInvSqrtConstant_nonneg p hM heta hT c
  have hZGint : IntervalIntegrable ZG volume 0 z.1 := by
    simpa only [ZG, FG, hFG2] using
      capWeightedPicardChemotaxisL2History_intervalIntegrable_of_uniform_cap
        p hM hT hz.le z.2.2 heta heta_one hB U₂ U₁
          hr hclose henergy hrB
  have hZRint : IntervalIntegrable ZR volume 0 z.1 := by
    simpa only [ZR, FR, hFR2] using
      capWeightedPicardReactionL2History_intervalIntegrable_of_uniform_cap
        p hM hT hz.le z.2.2 heta hB U₂ U₁
          hr hclose henergy hrB
  have hgGint : IntervalIntegrable gG volume 0 z.1 := by
    have h0 := hr_int.const_mul CG0
    have h1 := hkr_int.const_mul C1
    rw [show gG = fun s : ℝ => CG0 * r s +
        C1 * ((z.1 - s) ^ (-(1 / 2 : ℝ)) * r s) by
      funext s
      dsimp only [gG]
      ring]
    exact h0.add h1
  have hgRint : IntervalIntegrable gR volume 0 z.1 := by
    simpa only [gR] using hr_int.const_mul CR0
  have hZG : ∀ s ∈ Set.Icc (0 : ℝ) z.1, ‖ZG s‖ ≤ gG s := by
    intro s hs
    by_cases hst : s < z.1
    · have hnorm := capWeightedPicardChemotaxisL2History_norm_le
        p hM hT z.2.2 heta heta_one U₂ U₁
          hr hclose henergy hs hst
      simpa only [ZG, FG, hFG2, gG, CG0, C1] using hnorm
    · have hFs : FG s = 0 := by
        simp [FG, capWeightedPicardChemotaxisBUCHistoryIio, hst]
      have hZs : ZG s = 0 := by
        apply Lp.ext
        filter_upwards [wholeLineRealL2Section_coe_ae
          (fun q x => (FG q).1 x)
          (fun q => (FG q).1.continuous.aestronglyMeasurable) hFG2 s]
          with x hx
        rw [hx]
        simp [hFs]
      rw [hZs, norm_zero]
      exact mul_nonneg
        (add_nonneg hCG0
          (mul_nonneg hC1 (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)))
        (hr_closed s hs)
  have hZR : ∀ s ∈ Set.Icc (0 : ℝ) z.1, ‖ZR s‖ ≤ gR s := by
    intro s hs
    by_cases hst : s < z.1
    · have hnorm := capWeightedPicardReactionL2History_norm_le
        p hM hT z.2.2 heta U₂ U₁ hr hclose henergy hs hst
      simpa only [ZR, FR, hFR2, gR, CR0] using hnorm
    · have hFs : FR s = 0 := by
        simp [FR, capWeightedPicardReactionBUCHistoryIio, hst]
      have hZs : ZR s = 0 := by
        apply Lp.ext
        filter_upwards [wholeLineRealL2Section_coe_ae
          (fun q x => (FR q).1 x)
          (fun q => (FR q).1.continuous.aestronglyMeasurable) hFR2 s]
          with x hx
        rw [hx]
        simp [hFs]
      rw [hZs, norm_zero]
      exact mul_nonneg hCR0 (hr_closed s hs)
  have hZGrep : (((∫ s in (0 : ℝ)..z.1, ZG s) : WholeLineRealL2) :
      ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x * (-p.χ) *
        ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)) := by
    simpa only [ZG, FG, hFG2] using
      capWeightedPicardChemotaxisL2History_integral_rep_of_uniform_cap
        p hM hT hz.le z.2.2 heta heta_one hB U₂ U₁
          hr hclose henergy hrB
  have hZRrep : (((∫ s in (0 : ℝ)..z.1, ZR s) : WholeLineRealL2) :
      ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x *
        ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)) := by
    simpa only [ZR, FR, hFR2] using
      capWeightedPicardReactionL2History_integral_rep_of_uniform_cap
        p hM hT hz.le z.2.2 heta hB U₂ U₁
          hr hclose henergy hrB
  rcases exists_capWeighted_coMoving_bucMildMap_differenceL2_of_history
      p hM heta hT hB₀ R u₀₂ u₀₁ U₂ U₁ z hz
      hdata_meas hdata_cap hdata_energy ZG ZR gG gR
      hZGint hZRint hgGint hgRint hZG hZR hZGrep hZRrep with
    ⟨Z, hZrep, hZbound⟩
  refine ⟨Z, hZrep, hZbound.trans_eq ?_⟩
  congr 1
  apply intervalIntegral.integral_congr
  intro s _hs
  dsimp only [gG, gR, CG0, CR0, C1, capMildKernelConstant]
  ring

/-! ## Damped Picard family on an arbitrary finite window -/

/-- A positive time-damping gap turns the concrete cap Picard family into a
single exponentially growing scalar ball on any finite horizon. -/
theorem exists_bound_capWeighted_coMoving_bucMildPicardFrom_differenceL2_le_damped
    (p : CMParams) {M T eta R c B₀ lambda : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hlambda : 0 < lambda)
    (hq : ShenWork.PDE.restartedKernelMassPositive
      (capMildKernelCommonConstant p M eta c T)
      (1 / 2 : ℝ) lambda < 1)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2) :
    ∃ B : ℝ,
      B = capMildDampedBallRadius p M T eta c B₀ lambda ∧
      B₀ ≤ B ∧ 0 ≤ B ∧
      ∀ n : ℕ, ∀ z : Set.Icc (0 : ℝ) T,
        ∃ Z : WholeLineRealL2,
          ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
            capWeightSqrt eta R x *
              ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                  (x + c * z.1) -
                (W z).1 (x + c * z.1))) ∧
          ‖Z‖ ≤ B * Real.exp (lambda * z.1) := by
  let C0 : ℝ := capMildKernelConstant p M eta c T
  let C1 : ℝ := capMildKernelInvSqrtConstant p M eta c T
  let C : ℝ := capMildKernelCommonConstant p M eta c T
  let q : ℝ := ShenWork.PDE.restartedKernelMassPositive
    C (1 / 2 : ℝ) lambda
  let G : ℝ := capMildGrowthBound eta c T
  let A : ℝ := 2 * G * B₀
  let B : ℝ := A / (1 - q)
  let BT : ℝ := B * Real.exp (lambda * T)
  have hC0 : 0 ≤ C0 := capMildKernelConstant_nonneg p hM heta hT c
  have hC1 : 0 ≤ C1 :=
    capMildKernelInvSqrtConstant_nonneg p hM heta hT c
  have hC : 0 ≤ C := capMildKernelCommonConstant_nonneg p hM heta hT
  have hq0 : 0 ≤ q := by
    dsimp only [q, ShenWork.PDE.restartedKernelMassPositive]
    have hgamma : 0 ≤ Real.Gamma (1 - (1 / 2 : ℝ)) :=
      Real.Gamma_nonneg_of_nonneg (by norm_num)
    positivity
  have hd : 0 < 1 - q := sub_pos.mpr hq
  have hG : 1 ≤ G := by
    dsimp only [G, capMildGrowthBound]
    apply Real.one_le_exp
    exact mul_nonneg (by positivity) hT
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg hA hd.le
  have hB₀B : B₀ ≤ B := by
    apply (le_div_iff₀ hd).2
    dsimp only [A, B, G]
    have hqB₀ : 0 ≤ q * B₀ := mul_nonneg hq0 hB₀
    nlinarith
  have hscalar : A + q * B = B := by
    have hdne : 1 - q ≠ 0 := ne_of_gt hd
    dsimp only [B]
    field_simp
    ring
  have hBT : 0 ≤ BT := by
    dsimp only [BT]
    positivity
  refine ⟨B, ?_, hB₀B, hB, ?_⟩
  · rfl
  intro n
  induction n with
  | zero =>
      intro z
      refine ⟨0, ?_, ?_⟩
      · filter_upwards [] with x
        simp [wholeLineCauchyBUCMildPicardFrom]
      · exact (norm_zero.trans_le
          (mul_nonneg hB (Real.exp_nonneg _)))
  | succ n ih =>
      intro z
      by_cases hz0 : z.1 = 0
      · have hz : z = ⟨0, le_rfl, hT⟩ := Subtype.ext hz0
        subst z
        let Zd := wholeLineRealL2OfSqIntegrable
          (fun x : ℝ => capWeightSqrt eta R x *
            (u₀₂.1 x - u₀₁.1 x))
          ((capWeightSqrt_continuous eta R).mul
            (u₀₂.1.continuous.sub u₀₁.1.continuous)).aestronglyMeasurable
          (by
            refine hdata_cap.congr (ae_of_all _ ?_)
            intro x
            exact (capWeightSqrt_mul_sq_eq eta R x
              (u₀₂.1 x - u₀₁.1 x)).symm)
        have hZdrep : ((Zd : ℝ → ℝ) =ᵐ[volume] fun x : ℝ =>
            capWeightSqrt eta R x * (u₀₂.1 x - u₀₁.1 x)) :=
          wholeLineRealL2OfSqIntegrable_coe_ae _ _ _
        have hZdnorm : ‖Zd‖ ≤ B * Real.exp (lambda * (0 : ℝ)) := by
          rw [mul_zero, Real.exp_zero, mul_one]
          apply (sq_le_sq₀ (norm_nonneg Zd) hB).mp
          rw [wholeLineRealL2OfSqIntegrable_norm_sq]
          calc
            (∫ x : ℝ,
                (capWeightSqrt eta R x *
                  (u₀₂.1 x - u₀₁.1 x)) ^ 2) =
                ∫ x : ℝ, capWeight eta R x *
                  |u₀₂.1 x - u₀₁.1 x| ^ 2 := by
              apply integral_congr_ae
              exact ae_of_all _ (fun x =>
                capWeightSqrt_mul_sq_eq eta R x
                  (u₀₂.1 x - u₀₁.1 x))
            _ ≤ B₀ ^ 2 := hdata_energy
            _ ≤ B ^ 2 := (sq_le_sq₀ hB₀ hB).2 hB₀B
        refine ⟨Zd, ?_, hZdnorm⟩
        filter_upwards [hZdrep] with x hx
        simpa only [Nat.succ_eq_add_one,
          wholeLineCauchyBUCMildPicardFrom_succ,
          wholeLineCauchyBUCMildMap_zero_eq_data p hM hT u₀₂,
          wholeLineCauchyBUCMildFixedReference_zero_eq_data p hM hT u₀₁ W hfixed,
          mul_zero, add_zero] using hx
      · have hz : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz0)
        let r : ℝ → ℝ := fun s =>
          if s < 0 then Real.exp (eta * |c * s|) * B₀
          else B * Real.exp (lambda * s)
        have hr : ∀ s, s < z.1 → 0 ≤ r s := by
          intro s _hs
          dsimp only [r]
          split_ifs
          · exact mul_nonneg (Real.exp_pos _).le hB₀
          · exact mul_nonneg hB (Real.exp_nonneg _)
        have hr_closed : ∀ s ∈ Set.Icc (0 : ℝ) z.1, 0 ≤ r s := by
          intro s hs
          simp only [r, if_neg (not_lt.mpr hs.1)]
          exact mul_nonneg hB (Real.exp_nonneg _)
        have hr_int : IntervalIntegrable r volume 0 z.1 := by
          have hBexp_cont : Continuous (fun s : ℝ =>
              B * Real.exp (lambda * s)) := by fun_prop
          refine IntervalIntegrable.congr ?_
            (hBexp_cont.intervalIntegrable _ _)
          intro s hs
          rw [Set.uIoc_of_le hz.le] at hs
          simp only [r, if_neg (not_lt.mpr hs.1.le)]
        have hkr_int : IntervalIntegrable
            (fun s : ℝ => (z.1 - s) ^ (-(1 / 2 : ℝ)) * r s)
            volume 0 z.1 := by
          have hBexp_cont : Continuous (fun s : ℝ =>
              B * Real.exp (lambda * s)) := by fun_prop
          refine IntervalIntegrable.congr ?_
            (intervalIntegrable_invSqrt_sub.mul_continuousOn
              hBexp_cont.continuousOn)
          intro s hs
          rw [Set.uIoc_of_le hz.le] at hs
          simp only [r, if_neg (not_lt.mpr hs.1.le)]
        have hrBT : ∀ s ∈ Set.Icc (0 : ℝ) z.1, s < z.1 → r s ≤ BT := by
          intro s hs _hst
          simp only [r, if_neg (not_lt.mpr hs.1)]
          have hsexp : Real.exp (lambda * s) ≤ Real.exp (lambda * T) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (hs.2.trans z.2.2) hlambda.le
          exact mul_le_mul_of_nonneg_left hsexp hB
        have hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
            |(wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s).1
                  (x + c * s) -
              (wholeLineBUCTrajectoryExtend hT W s).1 (x + c * s)| ^ 2) := by
          intro s hs
          by_cases hs0 : s ≤ 0
          · have hextP : wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s =
                wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n
                  ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            have hextW : wholeLineBUCTrajectoryExtend hT W s =
                W ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            by_cases hn0 : n = 0
            · subst n
              simp [hextP, hextW, wholeLineCauchyBUCMildPicardFrom]
            · rw [hextP, hextW,
                wholeLineCauchyBUCMildPicardFrom_zero_eq_data_of_ne_zero
                  p hM hT u₀₂ W n hn0,
                wholeLineCauchyBUCMildFixedReference_zero_eq_data
                  p hM hT u₀₁ W hfixed]
              by_cases hsneg : s < 0
              · exact (capWeight_shift_sq_integrable_and_integral_le
                    (d := c * s) heta
                    (u₀₂.1.continuous.sub u₀₁.1.continuous)
                    hdata_cap).1
              · have hs_eq : s = 0 := le_antisymm hs0 (not_lt.mp hsneg)
                subst s
                simpa using hdata_cap
          · have hspos : 0 < s := lt_of_not_ge hs0
            have hsT : s ≤ T := (le_of_lt hs).trans z.2.2
            let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT⟩
            obtain ⟨Zs, hZsrep, hZsnorm⟩ := ih zs
            have hBs : 0 ≤ B * Real.exp (lambda * s) :=
              mul_nonneg hB (Real.exp_nonneg _)
            have hsenergy := capEnergy_of_wholeLineRealL2_rep
              hBs Zs hZsrep hZsnorm
            rw [wholeLineBUCTrajectoryExtend_eq hT _ zs.2,
              wholeLineBUCTrajectoryExtend_eq hT W zs.2]
            simpa only [zs] using hsenergy.1
        have henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
            |(wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s).1
                  (x + c * s) -
              (wholeLineBUCTrajectoryExtend hT W s).1 (x + c * s)| ^ 2) ≤
                (r s) ^ 2 := by
          intro s hs
          by_cases hs0 : s ≤ 0
          · have hextP : wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s =
                wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n
                  ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            have hextW : wholeLineBUCTrajectoryExtend hT W s =
                W ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            by_cases hn0 : n = 0
            · subst n
              simp [hextP, hextW, wholeLineCauchyBUCMildPicardFrom,
                sq_nonneg (r s)]
            · rw [hextP, hextW,
                wholeLineCauchyBUCMildPicardFrom_zero_eq_data_of_ne_zero
                  p hM hT u₀₂ W n hn0,
                wholeLineCauchyBUCMildFixedReference_zero_eq_data
                  p hM hT u₀₁ W hfixed]
              by_cases hsneg : s < 0
              · have hshift := capWeight_shift_sq_integrable_and_integral_le
                    (d := c * s) heta
                    (u₀₂.1.continuous.sub u₀₁.1.continuous)
                    hdata_cap
                calc
                  (∫ x : ℝ, capWeight eta R x *
                      |u₀₂.1 (x + c * s) - u₀₁.1 (x + c * s)| ^ 2) ≤
                      Real.exp (2 * eta * |c * s|) *
                        ∫ x : ℝ, capWeight eta R x *
                          |u₀₂.1 x - u₀₁.1 x| ^ 2 := hshift.2
                  _ ≤ Real.exp (2 * eta * |c * s|) * B₀ ^ 2 :=
                    mul_le_mul_of_nonneg_left hdata_energy (Real.exp_pos _).le
                  _ = (r s) ^ 2 := by
                    simp only [r, if_pos hsneg]
                    rw [mul_pow, ← Real.exp_nat_mul]
                    congr 2
                    ring
              · have hs_eq : s = 0 := le_antisymm hs0 (not_lt.mp hsneg)
                subst s
                simp only [mul_zero, add_zero, r, lt_self_iff_false, ↓reduceIte,
                  Real.exp_zero, mul_one]
                exact hdata_energy.trans ((sq_le_sq₀ hB₀ hB).2 hB₀B)
          · have hspos : 0 < s := lt_of_not_ge hs0
            have hsT : s ≤ T := (le_of_lt hs).trans z.2.2
            let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT⟩
            obtain ⟨Zs, hZsrep, hZsnorm⟩ := ih zs
            have hBs : 0 ≤ B * Real.exp (lambda * s) :=
              mul_nonneg hB (Real.exp_nonneg _)
            have hsenergy := capEnergy_of_wholeLineRealL2_rep
              hBs Zs hZsrep hZsnorm
            rw [wholeLineBUCTrajectoryExtend_eq hT _ zs.2,
              wholeLineBUCTrajectoryExtend_eq hT W zs.2]
            simpa only [zs, r, if_neg (not_lt.mpr hspos.le)] using hsenergy.2
        rcases
            exists_capWeighted_coMoving_bucMildMap_differenceL2_of_variable_cap_history
              p hM hT heta heta_one hB₀ hBT u₀₂ u₀₁
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) W z hz
                hdata_meas hdata_cap hdata_energy hr hr_closed hr_int hkr_int
                hclose henergy hrBT with
          ⟨Z, hZrep, hZnorm⟩
        have hkernel :
            (∫ s in (0 : ℝ)..z.1,
              (C0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ))) * r s) ≤
              B * Real.exp (lambda * z.1) * q := by
          have hbase := intervalIntegral_capKernel_mul_exp_le_dampedMass
            hC0 hC1 hlambda hz.le
          have heq :
              (∫ s in (0 : ℝ)..z.1,
                (C0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ))) * r s) =
                B * (∫ s in (0 : ℝ)..z.1,
                  (C0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ))) *
                    Real.exp (lambda * s)) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le hz.le] at hs
            simp only [r, if_neg (not_lt.mpr hs.1)]
            ring
          rw [heq]
          have hmul := mul_le_mul_of_nonneg_left hbase hB
          simpa only [C, q, C0, C1, capMildKernelCommonConstant,
            mul_assoc] using hmul
        have hexpone : 1 ≤ Real.exp (lambda * z.1) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hlambda.le z.2.1)
        have hfinal :
            A + B * Real.exp (lambda * z.1) * q ≤
              B * Real.exp (lambda * z.1) := by
          calc
            A + B * Real.exp (lambda * z.1) * q ≤
                A * Real.exp (lambda * z.1) +
                  B * Real.exp (lambda * z.1) * q := by
              have hAexp : A ≤ A * Real.exp (lambda * z.1) := by
                simpa only [mul_one] using
                  (mul_le_mul_of_nonneg_left hexpone hA)
              exact add_le_add hAexp le_rfl
            _ = (A + q * B) * Real.exp (lambda * z.1) := by ring
            _ = B * Real.exp (lambda * z.1) := by rw [hscalar]
        refine ⟨Z, ?_, ?_⟩
        · rw [hfixed] at hZrep
          simpa only [Nat.succ_eq_add_one,
            wholeLineCauchyBUCMildPicardFrom_succ] using hZrep
        · apply hZnorm.trans
          have hadd : A +
                (∫ s in (0 : ℝ)..z.1,
                  (C0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ))) * r s) ≤
              A + B * Real.exp (lambda * z.1) * q :=
            add_le_add le_rfl hkernel
          exact (by simpa only [A, C0, C1] using hadd.trans hfinal)

/-! ## Fatou passage and exact-weight cap exhaustion -/

/-- At a fixed cap, the damped Picard family passes to the canonical BUC
fixed point with the same explicit exponentially growing radius. -/
theorem exists_capWeighted_coMoving_mildFixedPoint_differenceL2_le_damped
    (p : CMParams) {M T eta R c B₀ lambda : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hlambda : 0 < lambda)
    (hq : ShenWork.PDE.restartedKernelMassPositive
      (capMildKernelCommonConstant p M eta c T)
      (1 / 2 : ℝ) lambda < 1)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (z : Set.Icc (0 : ℝ) T) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ∧
      ‖Z‖ ≤ capMildDampedBallRadius p M T eta c B₀ lambda *
        Real.exp (lambda * z.1) := by
  rcases
      exists_bound_capWeighted_coMoving_bucMildPicardFrom_differenceL2_le_damped
        p hM hT heta heta_one hB₀ hlambda hq u₀₂ u₀₁ W hfixed
          hdata_meas hdata_cap hdata_energy with
    ⟨B, hBdef, _hB₀B, hB, hpicard⟩
  let Bz : ℝ := B * Real.exp (lambda * z.1)
  have hBz : 0 ≤ Bz := by
    dsimp only [Bz]
    exact mul_nonneg hB (Real.exp_nonneg _)
  have hpicard_energy : ∀ n : ℕ,
      Integrable (fun x : ℝ =>
        (capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ^ 2) ≤ Bz ^ 2 := by
    intro n
    obtain ⟨Zn, hZnrep, hZnnorm⟩ := hpicard n z
    have hraw := capEnergy_of_wholeLineRealL2_rep hBz Zn hZnrep hZnnorm
    constructor
    · refine hraw.1.congr (ae_of_all _ ?_)
      intro x
      exact (capWeightSqrt_mul_sq_eq eta R x
        ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
          (x + c * z.1) - (W z).1 (x + c * z.1))).symm
    · calc
        (∫ x : ℝ,
          (capWeightSqrt eta R x *
            ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                (x + c * z.1) -
              (W z).1 (x + c * z.1))) ^ 2) =
            ∫ x : ℝ, capWeight eta R x *
              |(wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                  (x + c * z.1) -
                (W z).1 (x + c * z.1)| ^ 2 := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x =>
            capWeightSqrt_mul_sq_eq eta R x
              ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                (x + c * z.1) - (W z).1 (x + c * z.1)))
        _ ≤ Bz ^ 2 := hraw.2
  have hlimit :=
    exists_capWeighted_mildFixedPoint_differenceL2_of_picard_uniform
      p hM hT heta hBz u₀₂ hsmall W z
      (fun n => by
        simpa only [wholeLineCauchyBUCMildPicardFrom] using
          (hpicard_energy n).1)
      (fun n => by
        simpa only [wholeLineCauchyBUCMildPicardFrom] using
          (hpicard_energy n).2)
  simpa only [Bz, hBdef] using hlimit

/-- Monotone cap exhaustion upgrades the finite-cap damped estimate to the
exact exponential weight, quantitatively and at every slice of the restart
window. -/
theorem coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_damped
    (p : CMParams) {M T eta c B₀ lambda : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 < eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hlambda : 0 < lambda)
    (hq : ShenWork.PDE.restartedKernelMassPositive
      (capMildKernelCommonConstant p M eta c T)
      (1 / 2 : ℝ) lambda < 1)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (z : Set.Icc (0 : ℝ) T) :
    Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1)| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1)| ^ 2) ≤
        (capMildDampedBallRadius p M T eta c B₀ lambda *
          Real.exp (lambda * z.1)) ^ 2 := by
  let D : ℝ := capMildDampedBallRadius p M T eta c B₀ lambda
  let Bz : ℝ := D * Real.exp (lambda * z.1)
  have hD : 0 ≤ D := by
    dsimp only [D, capMildDampedBallRadius]
    have hG : 0 ≤ capMildGrowthBound eta c T := by
      unfold capMildGrowthBound
      exact (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hG) hB₀)
      (sub_nonneg.mpr hq.le)
  have hBz : 0 ≤ Bz := by
    dsimp only [Bz]
    exact mul_nonneg hD (Real.exp_nonneg _)
  let w : ℝ → ℝ := fun x =>
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
        (x + c * z.1) -
      (W z).1 (x + c * z.1)
  have hw : Continuous w := by
    dsimp only [w]
    exact ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1.continuous.comp
      (continuous_id.add continuous_const)).sub
        ((W z).1.continuous.comp (continuous_id.add continuous_const))
  have hdata_cont : Continuous (fun y : ℝ => u₀₂.1 y - u₀₁.1 y) :=
    u₀₂.1.continuous.sub u₀₁.1.continuous
  have hcap_rep : ∀ n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (n : ℝ) x * w x) ∧ ‖Z‖ ≤ Bz := by
    intro n
    have hdata_cap : Integrable (fun y : ℝ =>
        capWeight eta (n : ℝ) y * |u₀₂.1 y - u₀₁.1 y| ^ 2) :=
      capWeight_mul_sq_integrable_of_full hdata_cont hdata_full
    have hdata_cap_energy :
        (∫ y : ℝ, capWeight eta (n : ℝ) y *
          |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2 := by
      calc
        (∫ y : ℝ, capWeight eta (n : ℝ) y *
            |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤
            ∫ y : ℝ, Real.exp (2 * eta * y) *
              |u₀₂.1 y - u₀₁.1 y| ^ 2 := by
          apply integral_mono hdata_cap hdata_full
          intro y
          exact mul_le_mul_of_nonneg_right
            (capWeight_le_full eta (n : ℝ) y) (sq_nonneg _)
        _ ≤ B₀ ^ 2 := hdata_energy
    simpa only [w, Bz, D] using
      exists_capWeighted_coMoving_mildFixedPoint_differenceL2_le_damped
        p hM hT heta.le heta_one hB₀ hlambda hq u₀₂ u₀₁ W hfixed
          hsmall hdata_cont.measurable hdata_cap hdata_cap_energy z
  have hcap_int : ∀ n : ℕ,
      Integrable (fun x : ℝ => capWeight eta (n : ℝ) x * |w x| ^ 2) := by
    intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hcap_rep n
    exact (capEnergy_of_wholeLineRealL2_rep hBz Z hZrep hZnorm).1
  have hcap_bound : ∀ n : ℕ,
      (∫ x : ℝ, capWeight eta (n : ℝ) x * |w x| ^ 2) ≤ Bz ^ 2 := by
    intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hcap_rep n
    exact (capEnergy_of_wholeLineRealL2_rep hBz Z hZrep hZnorm).2
  have hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2) :=
    fullWeightedL2_integrable_of_uniform_cap
      (C := Bz ^ 2) heta hw hcap_int hcap_bound
  change Integrable (fun x : ℝ => Real.exp (2 * eta * x) * |w x| ^ 2) ∧
    (∫ x : ℝ, Real.exp (2 * eta * x) * |w x| ^ 2) ≤ Bz ^ 2
  refine ⟨hfull, ?_⟩
  exact le_of_tendsto (tentEnergy_mono_limit heta hw hfull)
    (Eventually.of_forall hcap_bound)

/-- Fully discharged finite-horizon exact-weight H0 propagation.  The
artificial damping rate and the resulting uniform radius are constructed
internally, so no weighted closed-ball or cap-kernel smallness assumption is
left in the interface. -/
theorem exists_bound_coMoving_mildFixedPoint_difference_fullWeightedL2_finiteHorizon
    (p : CMParams) {M T eta c B₀ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 < eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
          |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1)| ^ 2) ∧
        (∫ x : ℝ, Real.exp (2 * eta * x) *
          |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1)| ^ 2) ≤ B ^ 2 := by
  let C : ℝ := capMildKernelCommonConstant p M eta c T
  rcases exists_pos_capMildDampedKernelMass_lt_one C with
    ⟨lambda, hlambda, hqC⟩
  have hq : ShenWork.PDE.restartedKernelMassPositive
      (capMildKernelCommonConstant p M eta c T)
      (1 / 2 : ℝ) lambda < 1 := by
    simpa only [C] using hqC
  let D : ℝ := capMildDampedBallRadius p M T eta c B₀ lambda
  let B : ℝ := D * Real.exp (lambda * T)
  have hD : 0 ≤ D := by
    dsimp only [D, capMildDampedBallRadius]
    have hG : 0 ≤ capMildGrowthBound eta c T := by
      unfold capMildGrowthBound
      exact (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hG) hB₀)
      (sub_nonneg.mpr hq.le)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg hD (Real.exp_nonneg _)
  refine ⟨B, hB, ?_⟩
  intro z
  have hzbound :=
    coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_damped
      p hM hT heta heta_one hB₀ hlambda hq u₀₂ u₀₁ W hfixed hsmall
        hdata_full hdata_energy z
  refine ⟨hzbound.1, hzbound.2.trans ?_⟩
  have hexp : Real.exp (lambda * z.1) ≤ Real.exp (lambda * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left z.2.2 hlambda.le
  have hDz : D * Real.exp (lambda * z.1) ≤ B := by
    dsimp only [B]
    exact mul_le_mul_of_nonneg_left hexp hD
  simpa only [D] using (sq_le_sq₀
    (mul_nonneg hD (Real.exp_nonneg _)) hB).2 hDz

end ShenWork.Paper1

#print axioms ShenWork.Paper1.capMildKernelCommonConstant_nonneg
#print axioms ShenWork.Paper1.tendsto_capMildDampedKernelMass_atTop_zero
#print axioms ShenWork.Paper1.exists_pos_capMildDampedKernelMass_lt_one
#print axioms ShenWork.Paper1.intervalIntegral_capKernel_mul_exp_le_dampedMass
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_bucMildMap_differenceL2_of_variable_cap_history
#print axioms
  ShenWork.Paper1.exists_bound_capWeighted_coMoving_bucMildPicardFrom_differenceL2_le_damped
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_mildFixedPoint_differenceL2_le_damped
#print axioms
  ShenWork.Paper1.coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_damped
#print axioms
  ShenWork.Paper1.exists_bound_coMoving_mildFixedPoint_difference_fullWeightedL2_finiteHorizon
