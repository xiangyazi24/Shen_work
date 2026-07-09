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
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity
import ShenWork.PDE.IntervalSemigroupAtZero

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedConjugatePicardIter
   truncatedConjugateDuhamelMap
   truncatedLogisticLifted truncatedLogisticLocal
   TruncatedConjugateMildExistenceData)
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

private theorem truncatedConjugatePicardIter_zero_lift_differentiableAt_Ioo
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {τ M : ℝ} (hτ : 0 < τ)
    (hmeas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hbound : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ
      (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)) x := by
  have hEqOn : Set.EqOn
      (intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ))
      (fun y : ℝ => intervalFullSemigroupOperator τ (intervalDomainLift u₀) y)
      (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    simp [truncatedConjugatePicardIter, intervalDomainLift, hy]
  have hEq :
      intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 τ)
        =ᶠ[𝓝 x]
      (fun y : ℝ => intervalFullSemigroupOperator τ (intervalDomainLift u₀) y) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      (hEqOn.mono Set.Ioo_subset_Icc_self)
  exact
    (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      hτ hmeas hbound x).differentiableAt.congr_of_eventuallyEq hEq

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
  intro τ hτlo _hτhi
  have hτ_pos : 0 < τ := lt_of_lt_of_le (lt_trans _ha_pos _ha_lt_lo) hτlo
  have hloa_pos : 0 < lo - a := sub_pos.mpr _ha_lt_lo
  have hloa_le_τ : lo - a ≤ τ := by linarith
  have hK_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hM_nonneg : 0 ≤ DT.M := le_of_lt DT.hM
  refine ⟨fun x => by
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
    exact hheat.trans (hsing.trans (hA_ge_sing.trans hA_le_fixed)),
    fun x hx => by
      rw [hU 0 τ]
      exact truncatedConjugatePicardIter_zero_lift_differentiableAt_Ioo
        hτ_pos DT.hbase_lift_meas DT.hbase_lift_bound hx⟩

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
  intro τ hτ _hτlo
  have hK_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hM_nonneg : 0 ≤ DT.M := le_of_lt DT.hM
  refine ⟨fun x => by
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
    exact hheat.trans (hsing.trans hprofile),
    fun x hx => by
      rw [hU 0 τ]
      exact truncatedConjugatePicardIter_zero_lift_differentiableAt_Ioo
        hτ DT.hbase_lift_meas DT.hbase_lift_bound hx⟩

/-!
The next helper is the remaining analytic restart atom.

It packages the non-algebraic part of the successor step: restart the B-form
Picard iterate at time `a`, use the B-kernel integration-by-parts identity to
rewrite the chemotaxis leg as a standard full-kernel Duhamel source with
`Src`, differentiate the homogeneous and Duhamel legs, and apply the full-kernel
gradient estimates.  The theorem below consumes this atom and proves the window
monotonicity and constant arithmetic without any further analytic gap.
-/

private def truncatedWindowedSource
    (Src : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (a hi : ℝ) : ℝ → ℝ → ℝ :=
  fun s y => if a ≤ s ∧ s ≤ hi then Src n s y else 0

private theorem intervalDomainLift_deriv_eq_zero_off_Ioo
    (g : intervalDomainPoint → ℝ) {x : ℝ}
    (hx : x ∉ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift g) x = 0 := by
  let Uconst : ℝ → intervalDomainPoint → ℝ := fun _ => g
  rcases lt_or_ge x 0 with hx0 | hx0
  · simpa [Uconst] using
      (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Iio
        Uconst 0 hx0)
  rcases lt_or_ge 1 x with hx1 | hx1
  · simpa [Uconst] using
      (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Ioi
        Uconst 0 hx1)
  rcases eq_or_lt_of_le hx0 with hx_eq | hx_pos
  · subst hx_eq
    simpa [Uconst] using
      (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_left
        Uconst 0)
  rcases eq_or_lt_of_le hx1 with hx_eq | hx_lt_one
  · subst hx_eq
    simpa [Uconst] using
      (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_right
        Uconst 0)
  · exact False.elim (hx ⟨hx_pos, hx_lt_one⟩)

private theorem truncatedWindowedSource_integrable_of_source_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ s, Integrable (truncatedWindowedSource Src n a hi s) (intervalMeasure 1) := by
  have hCsrc_nonneg :
      0 ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    unfold truncWindowSourceCL
    exact add_nonneg _hAL_nonneg
      (mul_nonneg (abs_nonneg p.χ₀)
        (add_nonneg _hAF_nonneg (mul_nonneg _hBF_nonneg _hG_nonneg)))
  have hmeas_iterates : ∀ k,
      ShenWork.IntervalMildPicard.HasJointMeasurability
        (truncatedConjugatePicardIter p u₀ k) := by
    intro k
    induction k with
    | zero => exact DT.hbase_meas
    | succ k ih => exact DT.hmeas_preserved _ ih
  have hU_meas_n : Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (U n q.1) q.2) := by
    have hfield :
        (fun q : ℝ × ℝ => intervalDomainLift (U n q.1) q.2)
          =
        (fun q : ℝ × ℝ =>
          intervalDomainLift (truncatedConjugatePicardIter p u₀ n q.1) q.2) := by
      funext q
      rw [hU n q.1]
    rw [hfield]
    exact hmeas_iterates n
  intro s
  by_cases hs : a ≤ s ∧ s ≤ hi
  · have hlift_meas : Measurable (fun y : ℝ => intervalDomainLift (U n s) y) :=
      hU_meas_n.comp measurable_prodMk_left
    have hpos_meas : Measurable
        (fun y : ℝ => positivePart (intervalDomainLift (U n s) y)) := by
      simpa [positivePart] using hlift_meas.max measurable_const
    have hpow_meas : Measurable
        (fun y : ℝ => (positivePart (intervalDomainLift (U n s) y)) ^ p.α) := by
      have hrpow : Measurable (fun r : ℝ => r ^ p.α) := by fun_prop
      exact hrpow.comp hpos_meas
    have hlog_meas : Measurable (fun y : ℝ =>
        truncatedLogisticLifted p (U n s) y) := by
      simpa [truncatedLogisticLifted, truncatedLogisticLocal] using
        hlift_meas.mul (measurable_const.sub (measurable_const.mul hpow_meas))
    have hflux_deriv_meas : Measurable (fun y : ℝ =>
        deriv (truncatedChemFluxLifted p (U n s)) y) :=
      measurable_deriv _
    have hsrc_meas : Measurable (fun y : ℝ =>
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y) :=
      hlog_meas.sub (measurable_const.mul hflux_deriv_meas)
    have hSrc_fun :
        (fun y : ℝ => Src n s y)
          =
        (fun y : ℝ =>
          truncatedLogisticLifted p (U n s) y
            - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y) := by
      funext y
      exact hSrc n s y
    have hwin_eq :
        truncatedWindowedSource Src n a hi s = Src n s := by
      funext y
      simp [truncatedWindowedSource, hs]
    refine ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := truncWindowSourceCL A_L A_F B_F p.χ₀ G) ?_ ?_
    · rw [hwin_eq]
      change AEStronglyMeasurable (fun y : ℝ => Src n s y) (intervalMeasure 1)
      rw [hSrc_fun]
      exact hsrc_meas.aestronglyMeasurable
    · intro y
      rw [hwin_eq]
      exact hsrc s hs.1 hs.2 y
  · refine ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := truncWindowSourceCL A_L A_F B_F p.χ₀ G) ?_ ?_
    · have hwin_eq :
          truncatedWindowedSource Src n a hi s = fun _ : ℝ => 0 := by
        funext y
        simp [truncatedWindowedSource, hs]
      rw [hwin_eq]
      exact measurable_const.aestronglyMeasurable
    · intro y
      simp [truncatedWindowedSource, hs, hCsrc_nonneg]

private theorem truncatedConjugatePicardIter_succ_restart_meas_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    {_a τ : ℝ}
    (_ha_nonneg : 0 ≤ _a) (ha_lt_τ : _a < τ) (hτT : τ ≤ DT.T)
    (n : ℕ) :
    AEStronglyMeasurable (intervalDomainLift (U (n + 1) _a)) (intervalMeasure 1)
      ∧ ∀ y : ℝ, |intervalDomainLift (U (n + 1) _a) y| ≤ DT.M := by
  have haT : _a ≤ DT.T := (le_of_lt ha_lt_τ).trans hτT
  have hball_cont_succ :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedConjugatePicardIter_ball
      p u₀ DT.hbase_ball DT.hbase_cont
      DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved (n + 1)
  have hrestart_meas :
      AEStronglyMeasurable (intervalDomainLift (U (n + 1) _a)) (intervalMeasure 1) := by
    by_cases ha0 : _a = 0
    · have hzero :
        intervalDomainLift (U (n + 1) _a) = fun _ : ℝ => 0 := by
        subst _a
        funext y
        rw [hU (n + 1) 0]
        simp [truncatedConjugatePicardIter, truncatedConjugateDuhamelMap,
          ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero]
      rw [hzero]
      exact measurable_const.aestronglyMeasurable
    · have ha_pos : 0 < _a := lt_of_le_of_ne _ha_nonneg (Ne.symm ha0)
      have hcont : Continuous (U (n + 1) _a) := by
        rw [hU (n + 1) _a]
        exact hball_cont_succ.2 _a ha_pos haT
      exact
        ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
          hcont
  have hrestart_bound :
      ∀ y : ℝ, |intervalDomainLift (U (n + 1) _a) y| ≤ DT.M := by
    by_cases ha0 : _a = 0
    · have hzero :
        intervalDomainLift (U (n + 1) _a) = fun _ : ℝ => 0 := by
        subst _a
        funext y
        rw [hU (n + 1) 0]
        simp [truncatedConjugatePicardIter, truncatedConjugateDuhamelMap,
          ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero]
      intro y
      rw [hzero]
      simpa using (le_of_lt DT.hM)
    · have ha_pos : 0 < _a := lt_of_le_of_ne _ha_nonneg (Ne.symm ha0)
      intro y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
      · rw [intervalDomainLift, dif_pos hy, hU (n + 1) _a]
        exact hball_cont_succ.1 _a ha_pos haT ⟨y, hy⟩
      · rw [intervalDomainLift, dif_neg hy, abs_zero]
        exact le_of_lt DT.hM
  exact ⟨hrestart_meas, hrestart_bound⟩

/- Residual: value-level restart after the B-form successor definition is split
at `a` and the conjugate-kernel leg has been converted by spatial IBP to the
full-kernel source `Src`.  The statement is intentionally interior-only:
`intervalDomainLift` is the zero extension outside `[0,1]`, whereas the full
Neumann semigroup is a periodic/even full-space field. -/
private theorem truncatedConjugatePicardIter_succ_restart_value_identity_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (U (n + 1) τ) x =
        intervalFullSemigroupOperator (τ - a)
          (intervalDomainLift (U (n + 1) a)) x
          + ∫ s in a..τ,
              intervalFullSemigroupOperator (τ - s)
                (truncatedWindowedSource Src n a hi s) x := by
  sorry

/- Residual: spatial Leibniz rule for a shifted full-kernel Duhamel integral.
This is the analytic dominated-convergence step with the integrable
`(τ-s)^(-1/2)` singularity. -/
private theorem shiftedFullDuhamel_hasDerivAt_residual
    {a τ C : ℝ} (ha_lt_τ : a < τ)
    {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    (hC_nonneg : 0 ≤ C)
    (hq_sup : ∀ s y, |q s y| ≤ C) :
    ∀ x : ℝ,
      HasDerivAt
        (fun z : ℝ =>
          ∫ s in a..τ, intervalFullSemigroupOperator (τ - s) (q s) z)
        (∫ s in a..τ,
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - s) (q s) z) x)
        x := by
  sorry

/- Residual: prove the shifted full-kernel gradient integrand is interval-integrable
from the windowed truncated B-form source package.  This is the measurable
dominated-convergence half of the spatial Leibniz argument. -/
private theorem truncatedConjugatePicardIter_succ_gradientIntegrand_intervalIntegrable_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ x : ℝ, IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ =>
          intervalFullSemigroupOperator (τ - s)
            (truncatedWindowedSource Src n a hi s) z) x)
      volume a τ := by
  sorry

private theorem truncatedConjugatePicardIter_succ_restart_hasDerivAt_Ioo_core
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift (U (n + 1) τ))
        (deriv
            (fun z : ℝ =>
              intervalFullSemigroupOperator (τ - a)
                (intervalDomainLift (U (n + 1) a)) z) x
          + ∫ s in a..τ, deriv
              (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - s)
                  (truncatedWindowedSource Src n a hi s) z) x)
        x := by
  intro x hx
  have hτa_pos : 0 < τ - a := sub_pos.mpr ha_lt_τ
  rcases truncatedConjugatePicardIter_succ_restart_meas_bound
      (p := p) (u₀ := u₀) DT U hU ha_pos.le ha_lt_τ hτT n with
    ⟨hrestart_meas, hrestart_bound⟩
  have hq_int :
      ∀ s, Integrable (truncatedWindowedSource Src n a hi s) (intervalMeasure 1) :=
    truncatedWindowedSource_integrable_of_source_bound
      DT U hU Src hSrc _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg n hsrc
  have hCsrc_nonneg :
      0 ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    unfold truncWindowSourceCL
    exact add_nonneg _hAL_nonneg
      (mul_nonneg (abs_nonneg p.χ₀)
        (add_nonneg _hAF_nonneg (mul_nonneg _hBF_nonneg _hG_nonneg)))
  have hwin_sup :
      ∀ s y, |truncatedWindowedSource Src n a hi s y|
        ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    intro s y
    by_cases hs : a ≤ s ∧ s ≤ hi
    · simpa [truncatedWindowedSource, hs] using hsrc s hs.1 hs.2 y
    · simp [truncatedWindowedSource, hs, hCsrc_nonneg]
  have hhom :
      HasDerivAt
        (fun z : ℝ =>
          intervalFullSemigroupOperator (τ - a)
            (intervalDomainLift (U (n + 1) a)) z)
        (deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - a)
              (intervalDomainLift (U (n + 1) a)) z) x)
        x :=
    by
      have h :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
          hτa_pos hrestart_meas hrestart_bound x
      rw [h.deriv]
      exact h
  have hduh :
      HasDerivAt
        (fun z : ℝ =>
          ∫ s in a..τ,
            intervalFullSemigroupOperator (τ - s)
              (truncatedWindowedSource Src n a hi s) z)
        (∫ s in a..τ, deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - s)
              (truncatedWindowedSource Src n a hi s) z) x)
        x :=
    shiftedFullDuhamel_hasDerivAt_residual ha_lt_τ hq_int
      hCsrc_nonneg hwin_sup x
  have hmodel :
      HasDerivAt
        (fun z : ℝ =>
          intervalFullSemigroupOperator (τ - a)
            (intervalDomainLift (U (n + 1) a)) z
            + ∫ s in a..τ,
                intervalFullSemigroupOperator (τ - s)
                  (truncatedWindowedSource Src n a hi s) z)
        (deriv
            (fun z : ℝ =>
              intervalFullSemigroupOperator (τ - a)
                (intervalDomainLift (U (n + 1) a)) z) x
          + ∫ s in a..τ, deriv
              (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - s)
                  (truncatedWindowedSource Src n a hi s) z) x)
        x := hhom.add hduh
  have hvalue_on : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (U (n + 1) τ) z =
        intervalFullSemigroupOperator (τ - a)
          (intervalDomainLift (U (n + 1) a)) z
          + ∫ s in a..τ,
              intervalFullSemigroupOperator (τ - s)
                (truncatedWindowedSource Src n a hi s) z :=
    truncatedConjugatePicardIter_succ_restart_value_identity_residual
      DT U hU Src hSrc
      _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
      ha_pos ha_lt_τ hτhi hτT n hsrc
  have heq :
      intervalDomainLift (U (n + 1) τ)
        =ᶠ[𝓝 x]
      (fun z : ℝ =>
        intervalFullSemigroupOperator (τ - a)
          (intervalDomainLift (U (n + 1) a)) z
          + ∫ s in a..τ,
              intervalFullSemigroupOperator (τ - s)
                (truncatedWindowedSource Src n a hi s) z) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) hvalue_on
  exact hmodel.congr_of_eventuallyEq heq

/- Residual: prove the restarted B-form Picard identity after the conjugate-kernel
IBP conversion, then differentiate the homogeneous and shifted Duhamel legs. -/
private theorem truncatedConjugatePicardIter_succ_restart_deriv_identity_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (intervalDomainLift (U (n + 1) τ)) x =
        deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - a)
              (intervalDomainLift (U (n + 1) a)) z) x
          + ∫ s in a..τ, deriv
              (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - s)
                  (truncatedWindowedSource Src n a hi s) z) x := by
  intro x hx
  exact
    (truncatedConjugatePicardIter_succ_restart_hasDerivAt_Ioo_core
      DT U hU Src hSrc
      _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
      ha_pos ha_lt_τ hτhi hτT n hsrc x hx).deriv

/- Residual: prove the value-level restarted B-form identity on the open
interior and justify the full-kernel spatial Leibniz step as a genuine
`HasDerivAt`.  This is stronger than the `deriv` equality above: it records that
the derivative exists at the interior point, with the same restarted derivative
RHS. -/
private theorem truncatedConjugatePicardIter_succ_restart_hasDerivAt_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift (U (n + 1) τ))
        (deriv
            (fun z : ℝ =>
              intervalFullSemigroupOperator (τ - a)
                (intervalDomainLift (U (n + 1) a)) z) x
          + ∫ s in a..τ, deriv
              (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - s)
                  (truncatedWindowedSource Src n a hi s) z) x)
        x := by
  exact
    truncatedConjugatePicardIter_succ_restart_hasDerivAt_Ioo_core
      DT U hU Src hSrc
      _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
      ha_pos ha_lt_τ hτhi hτT n hsrc

/- Residual: prove interior differentiability of the successor truncated Picard
slice from the restarted B-form identity and full-kernel smoothing. -/
private theorem truncatedConjugatePicardIter_succ_interior_differentiableAt_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift (U (n + 1) τ)) x := by
  intro x hx
  exact
    (truncatedConjugatePicardIter_succ_restart_hasDerivAt_residual
      DT U hU Src hSrc
      _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
      ha_pos ha_lt_τ hτhi hτT n hsrc x hx).differentiableAt

/- Analytic helper sorry, isolated from the arithmetic estimate below.

This is the precise restart/IBP/Leibniz package needed by the raw gradient
atom: restart the successor Picard iterate at time `a`, replace the B-kernel
leg by the post-IBP full-kernel source on the active window, and justify the
spatial derivative under the shifted Duhamel integral. -/
private theorem truncatedConjugatePicardIter_succ_restart_gradient_split
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    AEStronglyMeasurable (intervalDomainLift (U (n + 1) a)) (intervalMeasure 1)
      ∧ (∀ y : ℝ, |intervalDomainLift (U (n + 1) a) y| ≤ DT.M)
      ∧ (∀ s, Integrable (truncatedWindowedSource Src n a hi s) (intervalMeasure 1))
      ∧ (∀ x : ℝ, IntervalIntegrable
          (fun s : ℝ => deriv
            (fun z : ℝ =>
              intervalFullSemigroupOperator (τ - s)
                (truncatedWindowedSource Src n a hi s) z) x)
          volume a τ)
      ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1,
          deriv (intervalDomainLift (U (n + 1) τ)) x =
            deriv
              (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - a)
                  (intervalDomainLift (U (n + 1) a)) z) x
              + ∫ s in a..τ, deriv
                  (fun z : ℝ =>
                    intervalFullSemigroupOperator (τ - s)
                      (truncatedWindowedSource Src n a hi s) z) x)
        ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1,
            DifferentiableAt ℝ (intervalDomainLift (U (n + 1) τ)) x := by
    rcases truncatedConjugatePicardIter_succ_restart_meas_bound
        (p := p) (u₀ := u₀) DT U hU ha_pos.le ha_lt_τ hτT n with
      ⟨hrestart_meas, hrestart_bound⟩
    have hq_int :
        ∀ s, Integrable (truncatedWindowedSource Src n a hi s) (intervalMeasure 1) :=
      truncatedWindowedSource_integrable_of_source_bound
        DT U hU Src hSrc _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg n hsrc
    have hg_int :
        ∀ x : ℝ, IntervalIntegrable
            (fun s : ℝ => deriv
              (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - s)
                  (truncatedWindowedSource Src n a hi s) z) x)
            volume a τ :=
      truncatedConjugatePicardIter_succ_gradientIntegrand_intervalIntegrable_residual
        DT U hU Src hSrc
        _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
        ha_pos ha_lt_τ hτhi hτT n hsrc
    have hsplit :
        ∀ x ∈ Set.Ioo (0 : ℝ) 1,
            deriv (intervalDomainLift (U (n + 1) τ)) x =
              deriv
                (fun z : ℝ =>
                  intervalFullSemigroupOperator (τ - a)
                    (intervalDomainLift (U (n + 1) a)) z) x
                + ∫ s in a..τ, deriv
                    (fun z : ℝ =>
                      intervalFullSemigroupOperator (τ - s)
                        (truncatedWindowedSource Src n a hi s) z) x :=
      truncatedConjugatePicardIter_succ_restart_deriv_identity_residual
        DT U hU Src hSrc
        _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
        ha_pos ha_lt_τ hτhi hτT n hsrc
    have hdiff :
        ∀ x ∈ Set.Ioo (0 : ℝ) 1,
            DifferentiableAt ℝ (intervalDomainLift (U (n + 1) τ)) x :=
      truncatedConjugatePicardIter_succ_interior_differentiableAt_residual
        DT U hU Src hSrc
        _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
        ha_pos ha_lt_τ hτhi hτT n hsrc
    exact ⟨hrestart_meas, hrestart_bound, hq_int, hg_int, hsplit, hdiff⟩

private theorem truncatedConjugatePicardIter_succ_restart_gradient_raw
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (hU : ∀ n s, U n s = truncatedConjugatePicardIter p u₀ n s)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (hSrc : ∀ n s y,
      Src n s y =
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y)
    {A_L A_F B_F a hi G τ : ℝ}
    (_hAL_nonneg : 0 ≤ A_L) (_hAF_nonneg : 0 ≤ A_F)
    (_hBF_nonneg : 0 ≤ B_F) (_hG_nonneg : 0 ≤ G)
    (ha_pos : 0 < a) (ha_lt_τ : a < τ)
    (hτhi : τ ≤ hi) (hτT : τ ≤ DT.T)
    (n : ℕ)
    (hsrc : ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) :
    (∀ x : ℝ,
      |deriv (intervalDomainLift (U (n + 1) τ)) x|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (τ - a) * DT.M
          + ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * (2 * Real.sqrt (τ - a))
            * truncWindowSourceCL A_L A_F B_F p.χ₀ G)
    ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (intervalDomainLift (U (n + 1) τ)) x := by
  have hτa_pos : 0 < τ - a := sub_pos.mpr ha_lt_τ
  have hK_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hM_nonneg : 0 ≤ DT.M := le_of_lt DT.hM
  have hCsrc_nonneg :
      0 ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    unfold truncWindowSourceCL
    exact add_nonneg _hAL_nonneg
      (mul_nonneg (abs_nonneg p.χ₀)
        (add_nonneg _hAF_nonneg (mul_nonneg _hBF_nonneg _hG_nonneg)))
  have hwin_sup :
      ∀ s y, |truncatedWindowedSource Src n a hi s y|
        ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    intro s y
    by_cases hs : a ≤ s ∧ s ≤ hi
    · simpa [truncatedWindowedSource, hs] using hsrc s hs.1 hs.2 y
    · simp [truncatedWindowedSource, hs, hCsrc_nonneg]
  rcases truncatedConjugatePicardIter_succ_restart_gradient_split
      DT U hU Src hSrc
      _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
      ha_pos ha_lt_τ hτhi hτT n hsrc with
    ⟨hrestart_meas, hrestart_bound, hq_int, hg_int, hsplit, hdiff⟩
  refine ⟨?_, hdiff⟩
  intro x
  have hhom :
      |deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - a)
              (intervalDomainLift (U (n + 1) a)) z) x|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (τ - a) * DT.M := by
    have h :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
        hτa_pos hrestart_meas hrestart_bound x
    calc
      |deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - a)
              (intervalDomainLift (U (n + 1) a)) z) x|
          ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * (τ - a) ^ (-(1 / 2) : ℝ) * DT.M := h
      _ = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              / Real.sqrt (τ - a) * DT.M := by
            rw [rpow_neg_half_eq_inv_sqrt hτa_pos]
            ring
  have hduh :
      |∫ s in a..τ, deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator (τ - s)
              (truncatedWindowedSource Src n a hi s) z) x|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * (2 * Real.sqrt (τ - a))
            * truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    exact
      ShenWork.Paper2.TruncatedGradientWindow.gradDuhamel_shifted_sup_bound
        (a := a) (t := τ) (T := τ) ha_pos.le ha_lt_τ le_rfl
        (q := truncatedWindowedSource Src n a hi) hq_int
        hCsrc_nonneg hwin_sup x (hg_int x)
  have hRhs_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (τ - a) * DT.M
          + ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * (2 * Real.sqrt (τ - a))
            * truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    exact add_nonneg
      (mul_nonneg
        (div_nonneg hK_nonneg (Real.sqrt_nonneg _)) hM_nonneg)
      (mul_nonneg
        (mul_nonneg hK_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        hCsrc_nonneg)
  by_cases hxIoo : x ∈ Set.Ioo (0 : ℝ) 1
  · rw [hsplit x hxIoo]
    exact (abs_add_le _ _).trans (add_le_add hhom hduh)
  · have hzero :
        deriv (intervalDomainLift (U (n + 1) τ)) x = 0 :=
      intervalDomainLift_deriv_eq_zero_off_Ioo (U (n + 1) τ) hxIoo
    rw [hzero, abs_zero]
    exact hRhs_nonneg

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
    (ha_pos : 0 < a) (_ha_lt_lo : a < lo)
    (_hlo_le_hi : lo ≤ hi) (_hhiT : hi ≤ DT.T) :
    ∀ n : ℕ,
      (∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
        |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) →
        IterGradOnWindow U lo hi (n + 1)
          (truncWindowAffine DT.M A_L A_F B_F p.χ₀ a lo hi G) := by
  -- The hypotheses `hU` and `hSrc` identify the abstract wiring variables with
  -- the actual truncated Picard iterates and the post-IBP source.
  intro n hsrc τ hτlo hτhi
  have hK_nonneg :
      0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hM_nonneg : 0 ≤ DT.M := le_of_lt DT.hM
  have hCsrc_nonneg :
      0 ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    unfold truncWindowSourceCL
    exact add_nonneg _hAL_nonneg
      (mul_nonneg (abs_nonneg p.χ₀)
        (add_nonneg _hAF_nonneg (mul_nonneg _hBF_nonneg _hG_nonneg)))
  have hlo_a_pos : 0 < lo - a := sub_pos.mpr _ha_lt_lo
  have hτa : a < τ := lt_of_lt_of_le _ha_lt_lo hτlo
  have hτ_a_pos : 0 < τ - a := sub_pos.mpr hτa
  have hlo_a_le_τ_a : lo - a ≤ τ - a := sub_le_sub_right hτlo a
  have hτ_a_le_hi_a : τ - a ≤ hi - a := sub_le_sub_right hτhi a
  have hτT : τ ≤ DT.T := hτhi.trans _hhiT
  have hraw :=
    truncatedConjugatePicardIter_succ_restart_gradient_raw
      (p := p) (u₀ := u₀) DT U hU Src hSrc
      (A_L := A_L) (A_F := A_F) (B_F := B_F)
      (a := a) (hi := hi) (G := G) (τ := τ)
      _hAL_nonneg _hAF_nonneg _hBF_nonneg _hG_nonneg
      ha_pos hτa hτhi hτT n hsrc
  refine ⟨fun x => ?_, hraw.2⟩
  have hhom :
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          / Real.sqrt (τ - a) * DT.M
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (lo - a) * DT.M := by
    calc
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          / Real.sqrt (τ - a) * DT.M
          = (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * DT.M) / Real.sqrt (τ - a) := by ring
      _ ≤ (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * DT.M) / Real.sqrt (lo - a) :=
            div_le_div_of_nonneg_left (mul_nonneg hK_nonneg hM_nonneg)
              (Real.sqrt_pos_of_pos hlo_a_pos)
              (Real.sqrt_le_sqrt hlo_a_le_τ_a)
      _ = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (lo - a) * DT.M := by ring
  have hduh :
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * (2 * Real.sqrt (τ - a))
          * truncWindowSourceCL A_L A_F B_F p.χ₀ G
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * (2 * Real.sqrt (hi - a))
            * truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
    have hsqrt : Real.sqrt (τ - a) ≤ Real.sqrt (hi - a) :=
      Real.sqrt_le_sqrt hτ_a_le_hi_a
    have hfactor :
        0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * 2 * truncWindowSourceCL A_L A_F B_F p.χ₀ G := by
      exact mul_nonneg (mul_nonneg hK_nonneg (by norm_num)) hCsrc_nonneg
    calc
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * (2 * Real.sqrt (τ - a))
          * truncWindowSourceCL A_L A_F B_F p.χ₀ G
          =
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * 2 * truncWindowSourceCL A_L A_F B_F p.χ₀ G)
            * Real.sqrt (τ - a) := by ring
      _ ≤
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * 2 * truncWindowSourceCL A_L A_F B_F p.χ₀ G)
            * Real.sqrt (hi - a) :=
          mul_le_mul_of_nonneg_left hsqrt hfactor
      _ =
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * (2 * Real.sqrt (hi - a))
          * truncWindowSourceCL A_L A_F B_F p.χ₀ G := by ring
  calc
    |deriv (intervalDomainLift (U (n + 1) τ)) x|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (τ - a) * DT.M
          + ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * (2 * Real.sqrt (τ - a))
            * truncWindowSourceCL A_L A_F B_F p.χ₀ G := hraw.1 x
    _ ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            / Real.sqrt (lo - a) * DT.M
          + ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * (2 * Real.sqrt (hi - a))
            * truncWindowSourceCL A_L A_F B_F p.χ₀ G := add_le_add hhom hduh
    _ = truncWindowAffine DT.M A_L A_F B_F p.χ₀ a lo hi G := by
      unfold truncWindowAffine truncWindowA truncWindowB truncWindowSourceCL
      ring

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
