/-
  Analytic atoms for the positive-time truncated gradient bootstrap.

  The window wiring in `IntervalTruncatedPositiveTimeBootstrap` needs two
  restart-gradient facts:

  * the zero-th iterate is uniformly gradient-bounded on a positive window;
  * the successor iterate satisfies the restarted affine gradient estimate.

  Both are standard heat-semigroup/IBP/Duhamel restart facts, but the repository
  does not yet expose the bounded-measurable Chapman-Kolmogorov and B-form
  restart split in a directly reusable form.  This file gives those obligations
  precise names so the bootstrap wiring can consume them without anonymous
  local holes.
-/

import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.Paper2.IntervalConjugateKernelIBP
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.Paper2.IntervalTruncatedGradientWindow
import ShenWork.Paper2.IntervalTruncatedLeftProfileWiring
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedConjugatePicardIter
   truncatedLogisticLifted TruncatedConjugateMildExistenceData)
open ShenWork.Paper2.TruncatedGradientWindow

private theorem rpow_neg_half_eq_inv_sqrt {τ : ℝ} (hτ : 0 < τ) :
    τ ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt τ := by
  have hhalf : τ ^ ((1 : ℝ) / 2) = Real.sqrt τ := by
    rw [Real.rpow_div_two_eq_sqrt 1 hτ.le, Real.rpow_one]
  rw [show (-(1 / 2) : ℝ) = -((1 : ℝ) / 2) by norm_num,
    Real.rpow_neg hτ.le, hhalf, one_div]

private theorem truncatedConjugatePicardIter_zero_lift_deriv_abs_le
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {τ M : ℝ} (hτ : 0 < τ)
    (hmeas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hbound : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M)
    (x : ℝ) :
    |deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) x|
      ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * τ ^ (-(1 / 2) : ℝ) * M := by
  have hM_nonneg : 0 ≤ M := (abs_nonneg (intervalDomainLift u₀ 0)).trans (hbound 0)
  have hRhs_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * τ ^ (-(1 / 2) : ℝ) * M := by
    exact mul_nonneg
      (mul_nonneg
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
        (Real.rpow_nonneg hτ.le _)) hM_nonneg
  let Uconst : ℝ → intervalDomainPoint → ℝ :=
    fun _ => truncatedConjugatePicardIter p u₀ 0 τ
  rcases lt_or_ge x 0 with hx0 | hx0
  · have hzero :
        deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) x = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Iio
          Uconst 0 hx0)
    rw [hzero, abs_zero]
    exact hRhs_nonneg
  rcases lt_or_ge 1 x with hx1 | hx1
  · have hzero :
        deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) x = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Ioi
          Uconst 0 hx1)
    rw [hzero, abs_zero]
    exact hRhs_nonneg
  rcases eq_or_lt_of_le hx0 with rfl | hx0lt
  · have hzero :
        deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) 0 = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_left
          Uconst 0)
    rw [hzero, abs_zero]
    exact hRhs_nonneg
  rcases eq_or_lt_of_le hx1 with hx1eq | hx1lt
  · subst x
    have hzero :
        deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) 1 = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_right
          Uconst 0)
    rw [hzero, abs_zero]
    exact hRhs_nonneg
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0lt, hx1lt⟩
  have hEq : Set.EqOn
      (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ))
      (fun y : ℝ => intervalFullSemigroupOperator τ (intervalDomainLift u₀) y)
      (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    simp [truncatedConjugatePicardIter, intervalDomainLift, hy]
  have hderiv_eq :
      deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) x =
        deriv (fun y : ℝ =>
          intervalFullSemigroupOperator τ (intervalDomainLift u₀) y) x :=
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eqOn_Ioo_of_semigroup
      (t := τ) (f := intervalDomainLift u₀)
      (g := truncatedConjugatePicardIter p u₀ 0 τ) hEq hxIoo
  rw [hderiv_eq]
  exact
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
      hτ hmeas hbound x

/-- Zero-th truncated Picard iterate gradient bound on a positive window.

Analytic content: use positive-time restart/Chapman-Kolmogorov for the heat
semigroup, then apply the `L∞ -> W^{1,∞}` full-kernel bound to the restarted
datum, whose sup norm is controlled by `DT.hbase_ball`.  The final comparison is
the elementary parameter inequality putting the result below
`truncWindowFixedG`. -/
theorem truncatedConjugatePicardIter_zero_window_gradient
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    {A_L A_F B_F a lo hi : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F)
    (_ha_pos : 0 < a) (_ha_lt_lo : a < lo) (_hlo_le_hi : lo ≤ hi)
    (_hhiT : hi ≤ DT.T)
    (_hBcontr : truncWindowB B_F p.χ₀ a hi < 1) :
    IterGradOnWindow U lo hi 0
      (truncWindowFixedG DT.M A_L A_F B_F p.χ₀ a lo hi) := by
  intro τ hτlo _hτhi x
  have hτ_pos : 0 < τ := lt_of_lt_of_le (lt_trans _ha_pos _ha_lt_lo) hτlo
  have hloa_pos : 0 < lo - a := sub_pos.mpr _ha_lt_lo
  have hloa_le_τ : lo - a ≤ τ := by linarith
  have hK_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hM_nonneg : 0 ≤ DT.M := le_of_lt DT.hM
  have hheat :
      |deriv (intervalDomainLift (U 0 τ)) x|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * τ ^ (-(1 / 2) : ℝ) * DT.M := by
    rw [hU 0 τ]
    exact truncatedConjugatePicardIter_zero_lift_deriv_abs_le
      hτ_pos DT.hbase_lift_meas DT.hbase_lift_bound x
  have hsing :
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * τ ^ (-(1 / 2) : ℝ) * DT.M
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (lo - a) * DT.M := by
    calc
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * τ ^ (-(1 / 2) : ℝ) * DT.M
          = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              / Real.sqrt τ * DT.M := by
            rw [rpow_neg_half_eq_inv_sqrt hτ_pos]
            ring
      _ = (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * DT.M) / Real.sqrt τ := by ring
      _ ≤ (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * DT.M) / Real.sqrt (lo - a) :=
            div_le_div_of_nonneg_left (mul_nonneg hK_nonneg hM_nonneg)
              (Real.sqrt_pos_of_pos hloa_pos)
              (Real.sqrt_le_sqrt hloa_le_τ)
      _ = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              / Real.sqrt (lo - a) * DT.M := by ring
  have hL_nonneg : 0 ≤ A_L + |p.χ₀| * A_F :=
    add_nonneg _hAL_nonneg (mul_nonneg (abs_nonneg p.χ₀) _hAF_nonneg)
  have hsrc_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * (2 * Real.sqrt (hi - a)) * (A_L + |p.χ₀| * A_F) := by
    exact mul_nonneg
      (mul_nonneg hK_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
      hL_nonneg
  have hA_nonneg :
      0 ≤ truncWindowA DT.M A_L A_F p.χ₀ a lo hi := by
    unfold truncWindowA
    exact add_nonneg
      (mul_nonneg
        (div_nonneg hK_nonneg (Real.sqrt_nonneg _)) hM_nonneg)
      hsrc_nonneg
  have hA_ge_sing :
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          / Real.sqrt (lo - a) * DT.M
        ≤ truncWindowA DT.M A_L A_F p.χ₀ a lo hi := by
    unfold truncWindowA
    exact le_add_of_nonneg_right hsrc_nonneg
  have hB_nonneg : 0 ≤ truncWindowB B_F p.χ₀ a hi := by
    unfold truncWindowB
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hK_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        (abs_nonneg p.χ₀))
      _hBF_nonneg
  have hA_le_fixed :
      truncWindowA DT.M A_L A_F p.χ₀ a lo hi
        ≤ truncWindowFixedG DT.M A_L A_F B_F p.χ₀ a lo hi := by
    unfold truncWindowFixedG
    have hden_pos : 0 < 1 - truncWindowB B_F p.χ₀ a hi := by linarith
    rw [le_div_iff₀ hden_pos]
    nlinarith [mul_nonneg hA_nonneg hB_nonneg]
  exact hheat.trans (hsing.trans (hA_ge_sing.trans hA_le_fixed))

/-- Zero-th truncated Picard iterate left-profile gradient bound on `(0, lo]`.

This is the left-window analogue of
`truncatedConjugatePicardIter_zero_window_gradient`; it supplies the singular
`Cg*M/sqrt(t)` profile needed before the fixed positive restart window. -/
theorem truncatedConjugatePicardIter_zero_left_profile
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    {A_L A_F B_F lo : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hlo_pos : 0 < lo)
    (_hBcontr : truncLeftB B_F p.χ₀ lo < 1) :
    IterGradLeftProfile U DT.M A_L A_F B_F p.χ₀ lo 0 := by
  intro τ hτ _hτlo x
  have hK_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hM_nonneg : 0 ≤ DT.M := le_of_lt DT.hM
  have hheat :
      |deriv (intervalDomainLift (U 0 τ)) x|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * τ ^ (-(1 / 2) : ℝ) * DT.M := by
    rw [hU 0 τ]
    exact truncatedConjugatePicardIter_zero_lift_deriv_abs_le
      hτ DT.hbase_lift_meas DT.hbase_lift_bound x
  have hsing :
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * τ ^ (-(1 / 2) : ℝ) * DT.M
        ≤ truncLeftSingularC DT.M / Real.sqrt τ := by
    have hsing_eq :
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * τ ^ (-(1 / 2) : ℝ) * DT.M
          = truncLeftSingularC DT.M / Real.sqrt τ := by
      calc
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * τ ^ (-(1 / 2) : ℝ) * DT.M
            = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
                / Real.sqrt τ * DT.M := by
              rw [rpow_neg_half_eq_inv_sqrt hτ]
              ring
        _ = truncLeftSingularC DT.M / Real.sqrt τ := by
              unfold truncLeftSingularC
              ring
    exact hsing_eq.le
  have hD_nonneg :
      0 ≤ truncLeftD DT.M A_L A_F B_F p.χ₀ lo := by
    exact ShenWork.Paper2.TruncatedGradientWindow.truncLeftD_nonneg
      hM_nonneg _hAL_nonneg _hAF_nonneg _hBF_nonneg _hlo_pos.le _hBcontr
  have hprofile :
      truncLeftSingularC DT.M / Real.sqrt τ
        ≤ truncLeftProfile DT.M A_L A_F B_F p.χ₀ lo τ := by
    unfold truncLeftProfile
    exact le_add_of_nonneg_right hD_nonneg
  exact hheat.trans (hsing.trans hprofile)

/-- Successor truncated Picard iterate affine gradient step on a positive window.

Analytic content: restart the B-form Duhamel map at time `a`; rewrite the
conjugate-kernel leg by `intervalConjugateKernelOperator_eq_semigroup_deriv`;
differentiate the homogeneous and Duhamel legs; bound the homogeneous restart
piece by the full-kernel gradient estimate and the source piece by
`gradDuhamel_shifted_sup_bound`. -/
theorem truncatedConjugatePicardIter_succ_window_gradient
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a lo hi G : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (_ha_nonneg : 0 ≤ a) (_ha_lt_lo : a < lo)
    (_hlo_le_hi : lo ≤ hi) (_hhiT : hi ≤ DT.T) :
    ∀ n : ℕ,
      (∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
        |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) →
        IterGradOnWindow U lo hi (n + 1)
          (truncWindowAffine DT.M A_L A_F B_F p.χ₀ a lo hi G) := by
  -- The hypotheses `hU` and `hSrc` identify the abstract wiring variables with
  -- the actual truncated Picard iterates and the post-IBP source.
  intro n hsrc
  sorry

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
