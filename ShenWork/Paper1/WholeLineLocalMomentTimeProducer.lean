import ShenWork.Paper1.WholeLineLocalMomentBound
import ShenWork.Paper1.WholeLineWeightedRegularityUnweightedSecondBound

open Filter Function MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time differentiation of canonical local moments

On a compact positive-time subwindow, the canonical mild fixed point and its
ordinary time derivative are uniformly bounded in space.  The translated
localizing weight is dominated by a centred exponential, so the time
derivative of `u ^ P` admits an integrable majorant independent of the nearby
time variable.  This supplies the concrete `WholeLineLocalMomentTimeData`
used by the local-moment energy identity.
-/

/-- The canonical mild fixed point supplies the dominated time-differentiation
package for every positive interior time and every translated localizing
weight. -/
noncomputable def wholeLineCauchyBUCMildFixedPoint_localMomentTimeData
    (p : CMParams) {M T P κ t x₀ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hP : 1 < P) (hκ : 0 < κ)
    (ht0 : 0 < t) (htT : t < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    WholeLineLocalMomentTimeData P κ t x₀ u
      (fun s x => deriv (fun r : ℝ => u r x) s) := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbT : b < T := by dsimp [b]; linarith
  have hBtExists :=
    wholeLineCauchyBUCMildFixedPoint_time_deriv_bounded_positive_window
      p hM hT ha hab hbT u₀ hsmall
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip
  let Bt : ℝ := Classical.choose hBtExists
  have hBt : 0 ≤ Bt := (Classical.choose_spec hBtExists).1
  have htBound := (Classical.choose_spec hBtExists).2
  have hkExists := localizingWeightAt_decay hκ x₀
  let k : ℝ := Classical.choose hkExists
  have hk : 0 < k := (Classical.choose_spec hkExists).1
  have hweight := (Classical.choose_spec hkExists).2
  let δ : ℝ := min (t / 2) ((T - t) / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by linarith)
  let C : ℝ := |P| * M ^ (P - 1) * Bt
  let bound : ℝ → ℝ := fun x => C * Real.exp (-k * |x|)
  have hP0 : 0 ≤ P := by linarith
  have hPm10 : 0 ≤ P - 1 := by linarith
  have hball : ∀ s ∈ Metric.ball t δ, s ∈ Set.Icc a b := by
    intro s hs
    have hsabs : |s - t| < δ := by
      simpa only [Real.dist_eq] using hs
    have hsneg : -δ < s - t := (abs_lt.mp hsabs).1
    have hspos : s - t < δ := (abs_lt.mp hsabs).2
    have hδleft : δ ≤ t / 2 := min_le_left _ _
    have hδright : δ ≤ (T - t) / 2 := min_le_right _ _
    constructor <;> dsimp [a, b] <;> linarith
  have hslice : ∀ s, IsCUnifBdd (u s) := by
    intro s
    exact WholeLineBUC.isCUnifBdd
      (wholeLineBUCTrajectoryExtend hT Traj s)
  have hujoint : Continuous (fun q : ℝ × ℝ => u q.1 q.2) := by
    have heval : Continuous (fun q : WholeLineBUC × ℝ => q.1.1 q.2) := by
      fun_prop
    exact heval.comp (Continuous.prodMk
      ((wholeLineBUCTrajectoryExtend_continuous hT Traj).comp continuous_fst)
      continuous_snd)
  have htimeMeas : Measurable
      (fun x : ℝ => deriv (fun r : ℝ => u r x) t) := by
    have hparam : Continuous
        (Function.uncurry (fun x : ℝ => fun r : ℝ => u r x)) := by
      simpa only [Function.uncurry_apply_pair] using
        hujoint.comp (continuous_snd.prodMk continuous_fst)
    have hall := measurable_deriv_with_param hparam
    simpa only [Function.uncurry_apply_pair] using
      hall.comp (measurable_id.prodMk measurable_const)
  refine
    { δ := δ
      bound := bound
      hδ := hδ
      integrand_aeStronglyMeasurable := ?_
      integrand_integrable := ?_
      derivative_aeStronglyMeasurable := ?_
      derivative_bound := ?_
      bound_integrable := ?_
      hasDerivAt_u := ?_ }
  · filter_upwards [] with s
    exact (((Real.continuous_rpow_const hP0).comp (hslice s).1).mul
      continuous_localizingWeightAt).aestronglyMeasurable
  · exact wholeLineLocalLpIntegrable_of_isCUnifBdd
      hP0 hκ (hslice t)
  · have huPowMeas : Measurable (fun x : ℝ => (u t x) ^ (P - 1)) :=
      ((Real.continuous_rpow_const hPm10).comp (hslice t).1).measurable
    exact (measurable_const.mul
      ((huPowMeas.mul htimeMeas).mul
        continuous_localizingWeightAt.measurable)).aestronglyMeasurable
  · filter_upwards [] with x
    intro s hs
    have hsIcc : s ∈ Set.Icc a b := hball s hs
    have hs0 : 0 ≤ s := ha.le.trans hsIcc.1
    have hsT : s ≤ T := hsIcc.2.trans hbT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj s = Traj zs :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zs.2
    have huIcc : u s x ∈ Set.Icc (0 : ℝ) M := by
      simpa only [u, hext, Traj] using hstrip zs x
    have huPow : (u s x) ^ (P - 1) ≤ M ^ (P - 1) :=
      Real.rpow_le_rpow huIcc.1 huIcc.2 hPm10
    have hut : |deriv (fun r : ℝ => u r x) s| ≤ Bt := by
      simpa only [u, Traj] using htBound s hsIcc x
    have hpowNonneg : 0 ≤ (u s x) ^ (P - 1) :=
      Real.rpow_nonneg huIcc.1 _
    have hMPowNonneg : 0 ≤ M ^ (P - 1) := Real.rpow_nonneg hM _
    have hcore :
        (u s x) ^ (P - 1) * |deriv (fun r : ℝ => u r x) s| ≤
          M ^ (P - 1) * Bt :=
      mul_le_mul huPow hut (abs_nonneg _) hMPowNonneg
    have hwpos : 0 < localizingWeightAt κ x₀ x :=
      localizingWeightAt_pos κ x₀ x
    have hdom :
        ((u s x) ^ (P - 1) * |deriv (fun r : ℝ => u r x) s|) *
            localizingWeightAt κ x₀ x ≤
          (M ^ (P - 1) * Bt) * Real.exp (-k * |x|) := by
      exact (mul_le_mul_of_nonneg_right hcore hwpos.le).trans
        (mul_le_mul_of_nonneg_left (hweight x)
          (mul_nonneg hMPowNonneg hBt))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hpowNonneg, abs_of_pos hwpos]
    dsimp only [bound, C]
    nlinarith [abs_nonneg P, Real.exp_pos (-k * |x|)]
  · have hexp : Integrable (fun x : ℝ => Real.exp (-k * |x|)) := by
      simpa only [zero_sub, abs_neg] using
        (kernel_exp_neg_mul_abs_integrable hk (0 : ℝ))
    exact hexp.const_mul C
  · filter_upwards [] with x
    intro s hs
    have hsIcc : s ∈ Set.Icc a b := hball s hs
    have hs0 : 0 < s := ha.trans_le hsIcc.1
    have hsT : s < T := hsIcc.2.trans_lt hbT
    have hraw :=
      wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
        p hM hT u₀ hsmall hs0 hsT
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip x
    have hraw' : HasDerivAt (fun r : ℝ => u r x)
        (deriv (fun r : ℝ => u r x) s) s := by
      have h := hraw.congr_deriv hraw.deriv.symm
      simpa only [u, Traj] using h
    exact hraw'

/-- Propositional compatibility wrapper for the concrete time-data producer. -/
theorem wholeLineCauchyBUCMildFixedPoint_exists_localMomentTimeData
    (p : CMParams) {M T P κ t x₀ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hP : 1 < P) (hκ : 0 < κ)
    (ht0 : 0 < t) (htT : t < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    ∃ H : WholeLineLocalMomentTimeData P κ t x₀ u
      (fun s x => deriv (fun r : ℝ => u r x) s), True := by
  dsimp only
  exact ⟨wholeLineCauchyBUCMildFixedPoint_localMomentTimeData
    p hM hT hP hκ ht0 htT u₀ hsmall hstrip, trivial⟩

/-- Consequently, the canonical weighted local moment has the derivative
obtained by differentiating `u ^ P` under the integral sign. -/
theorem wholeLineCauchyBUCMildFixedPoint_localLpMoment_hasDerivAt
    (p : CMParams) {M T P κ t x₀ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hP : 1 < P) (hκ : 0 < κ)
    (ht0 : 0 < t) (htT : t < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    HasDerivAt (fun s : ℝ => wholeLineLocalLpMoment P κ u s x₀)
      (P * ∫ x : ℝ, (u t x) ^ (P - 1) *
        deriv (fun r : ℝ => u r x) t * localizingWeightAt κ x₀ x) t := by
  dsimp only
  exact (wholeLineCauchyBUCMildFixedPoint_localMomentTimeData
    p hM hT hP hκ ht0 htT u₀ hsmall hstrip).hasDerivAt hP

section AxiomAudit

#print axioms wholeLineCauchyBUCMildFixedPoint_localMomentTimeData
#print axioms wholeLineCauchyBUCMildFixedPoint_exists_localMomentTimeData
#print axioms wholeLineCauchyBUCMildFixedPoint_localLpMoment_hasDerivAt

end AxiomAudit

end ShenWork.Paper1
