/-
  ShenWork/PDE/IntervalFullKernelDuhamelSup.lean

  **T2 — sup bound for the full-kernel coupled Duhamel operator.**

  Full-kernel analogue of `intervalFullDuhamelOperator_bound_of_source_bound` /
  `intervalCoupledDuhamel_lift_abs_le`: the full-Neumann-kernel Duhamel image is
  `L∞`-bounded by `H + C·T`, resting on the full-kernel `L∞` contraction
  `intervalFullSemigroupOperator_Linfty_bound` (T2-h).  This is the sup conjunct of
  the `_clean_full` snapshot.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelDuhamelGradEq

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain ShenWork.IntervalDomainExistence

/-- **Pointwise sup bound for the full-kernel coupled Duhamel operator.** -/
theorem intervalFullKernelDuhamelOperator_bound
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {H C T : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (_hint : MeasureTheory.IntegrableOn
      (fun s => intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume) :
    |intervalFullKernelCoupledDuhamelOperator p R u₀ u t x| ≤ H + C * T := by
  rw [intervalFullKernelCoupledDuhamelOperator]
  have hinit :
      |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| ≤ H :=
    intervalFullSemigroupOperator_Linfty_bound ht hH
      (intervalDomainLift_abs_le hH hu₀) x.1
  have hint_bound :
      |∫ s in Set.Icc (0 : ℝ) t,
        intervalFullSemigroupOperator (t - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1| ≤ C * T := by
    have hae_bound : ∀ᵐ s ∂MeasureTheory.volume,
        s ∈ Set.Icc (0 : ℝ) t →
          ‖intervalFullSemigroupOperator (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1‖ ≤ C := by
      have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ t := by
        simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
      filter_upwards [hne] with s hs_ne hs_mem
      rw [Real.norm_eq_abs]
      have hs0 : 0 ≤ s := hs_mem.1
      have hsT : s ≤ T := le_trans hs_mem.2 htT
      have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
      exact intervalFullSemigroupOperator_Linfty_bound hts_pos hC
        (hsource s hs0 hsT) x.1
    have hvol_fin : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ := measure_Icc_lt_top
    have hstep :
        ‖∫ s in Set.Icc (0 : ℝ) t,
          intervalFullSemigroupOperator (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1‖ ≤
          C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' hvol_fin hae_bound
    have hvol_eq : MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) = t := by
      simp [MeasureTheory.Measure.real, Real.volume_Icc, ht.le]
    calc |∫ s in Set.Icc (0 : ℝ) t,
          intervalFullSemigroupOperator (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1|
        = ‖∫ s in Set.Icc (0 : ℝ) t,
            intervalFullSemigroupOperator (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) := hstep
      _ = C * t := by rw [hvol_eq]
      _ ≤ C * T := mul_le_mul_of_nonneg_left htT hC
  calc
    |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
        ∫ s in Set.Icc (0 : ℝ) t,
          intervalFullSemigroupOperator (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1|
        ≤ |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| +
          |∫ s in Set.Icc (0 : ℝ) t,
            intervalFullSemigroupOperator (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1| :=
          abs_add_le _ _
    _ ≤ H + C * T := add_le_add hinit hint_bound

/-- **Lift form of the full-kernel Duhamel sup bound** (the sup conjunct of
`_clean_full`). -/
theorem intervalFullKernelDuhamel_lift_abs_le
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {H C T : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hint : ∀ x : intervalDomainPoint,
      MeasureTheory.IntegrableOn
        (fun s => intervalFullSemigroupOperator (t - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
        (Set.Icc 0 t) MeasureTheory.volume) :
    ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift
          (fun y : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p R u₀ u t y) x| ≤ H + C * T := by
  intro x hx
  have hpt :
      intervalDomainLift
          (fun y : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p R u₀ u t y) x =
        intervalFullKernelCoupledDuhamelOperator p R u₀ u t ⟨x, hx⟩ := by
    unfold intervalDomainLift
    simp [hx]
  rw [hpt]
  exact intervalFullKernelDuhamelOperator_bound p R u₀ u
    hH hC hu₀ hsource ht htT ⟨x, hx⟩ (hint ⟨x, hx⟩)

end ShenWork.IntervalNeumannFullKernel
