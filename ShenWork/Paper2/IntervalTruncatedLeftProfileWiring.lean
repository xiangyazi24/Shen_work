/-
  Wiring layer for the left Volterra profile.

  This file keeps the structural induction separate from the analytic
  obligations.  The analytic work supplies `hbase`, `hsource_of_profile`, and
  `hkernel_step`; the wiring turns those into the left-window gradient bound
  consumed by `TruncatedGradientWindowWiring.hleft`.
-/

import ShenWork.Paper2.IntervalTruncatedLeftProfile

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedGradientWindow

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-- Pointwise gradient control by the left Volterra profile on `(0, lo]`. -/
abbrev IterGradLeftProfile
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (M A_L A_F B_F chi lo : ℝ) (n : ℕ) : Prop :=
  ∀ tau, 0 < tau → tau ≤ lo → ∀ x : ℝ,
    |deriv (intervalDomainLift (U n tau)) x|
      ≤ truncLeftProfile M A_L A_F B_F chi lo tau

/-- The left profile `P(t) = C / sqrt(t) + D` is decreasing in positive time. -/
theorem truncLeftProfile_anti_mono_time
    {M A_L A_F B_F chi lo tau sigma : ℝ}
    (hM : 0 ≤ M) (htau : 0 < tau) (hts : tau ≤ sigma) :
    truncLeftProfile M A_L A_F B_F chi lo sigma
      ≤ truncLeftProfile M A_L A_F B_F chi lo tau := by
  unfold truncLeftProfile truncLeftSingularC
  have hdiv :
      heatGradientLinftyLinftyConstant * M / Real.sqrt sigma
        ≤ heatGradientLinftyLinftyConstant * M / Real.sqrt tau :=
    div_le_div_of_nonneg_left
    (mul_nonneg heatGradientLinftyLinftyConstant_nonneg hM)
    (Real.sqrt_pos_of_pos htau)
    (Real.sqrt_le_sqrt hts)
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hdiv (truncLeftD M A_L A_F B_F chi lo)

/-- Convert profile control on `(0, lo]` into a flat bound on `[a, lo]`. -/
theorem IterGradOnWindow.of_left_profile
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {M A_L A_F B_F chi a lo G : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a)
    (hprofile : ∀ n : ℕ, IterGradLeftProfile U M A_L A_F B_F chi lo n)
    (hPaG : truncLeftProfile M A_L A_F B_F chi lo a ≤ G) :
    ∀ n : ℕ, IterGradOnWindow U a lo n G := by
  intro n t hat htlo x
  have htpos : 0 < t := lt_of_lt_of_le ha hat
  exact ((hprofile n t htpos htlo x).trans
    ((truncLeftProfile_anti_mono_time (M := M) (A_L := A_L) (A_F := A_F)
      (B_F := B_F) (chi := chi) (lo := lo) hM ha hat).trans hPaG))

/-- Analytic inputs needed to propagate the left Volterra profile. -/
structure TruncatedLeftProfileWiring
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (M A_L A_F B_F chi lo : ℝ) : Prop where
  hbase : IterGradLeftProfile U M A_L A_F B_F chi lo 0
  hsource_of_profile : ∀ n : ℕ,
    IterGradLeftProfile U M A_L A_F B_F chi lo n →
      ∀ s, 0 < s → s ≤ lo → ∀ y : ℝ,
        |Src n s y| ≤
          truncLeftSourceConst A_L A_F chi
            + truncLeftBeta B_F chi
              * truncLeftProfile M A_L A_F B_F chi lo s
  hkernel_step : ∀ n : ℕ,
    (∀ s, 0 < s → s ≤ lo → ∀ y : ℝ,
      |Src n s y| ≤
        truncLeftSourceConst A_L A_F chi
          + truncLeftBeta B_F chi
            * truncLeftProfile M A_L A_F B_F chi lo s) →
      IterGradLeftProfile U M A_L A_F B_F chi lo (n + 1)

/-- Structural induction for the left Volterra profile. -/
theorem truncLeftProfile_all_of_wiring
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {Src : ℕ → ℝ → ℝ → ℝ}
    {M A_L A_F B_F chi lo : ℝ}
    (W : TruncatedLeftProfileWiring U Src M A_L A_F B_F chi lo) :
    ∀ n : ℕ, IterGradLeftProfile U M A_L A_F B_F chi lo n := by
  intro n
  induction n with
  | zero => exact W.hbase
  | succ n IH =>
      exact W.hkernel_step n (W.hsource_of_profile n IH)

end ShenWork.Paper2.TruncatedGradientWindow
